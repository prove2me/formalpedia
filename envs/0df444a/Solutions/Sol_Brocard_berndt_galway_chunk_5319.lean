-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5319
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:28:44.930759+00:00
-- url     : https://prove2.me/submissions/64b812f1-5ca4-4904-bc03-31d31431f0d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 956474820 ≤ n < 956654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 956476070 1250 956474820 956474833
    0x60906150405060f2701060903030e040203100618082407090e060d170a0c02010e0301151404060510020106140913060b0a0f03030206190b06040b07050a080304060509 73
    0x3003040182c1d0411512550080503c006001103414646640380721100c11520580118031703250003007810120260b01c42030009100000c100b06058100496446411003030301c00754610b203000040100c10b04564452007080006498189203484000d90503800500071f1402603070004c00044600c8812107030f80a001c51500d5509202140c80706001c0e8410344c00312040080a010f09a44d03e4040000c000401407084e901c80c02882046262402c0050007400a41a242c03500940d140c400d000041006001114940c0603a140c19030032445002e5a1b0300c1701088801d5403181480e000280004a1b02807da44c1d030099070070990024400c444241c0641195041c2d54602400074000b604510401892080c280c03180e00714441854031510118583d034002c04030240f00a0018192075954004031341076803030140d1042d40140c1003501070213020180f98900e855070f03540d850f0301030119103502c0d03002078040d01c114403542100000018411b800c0220034451403c0c0c0c10303004540d1a07100d03d400e05000d0040c040464480400d0700a40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 956477320 1250 956476070 956476111
    0x80c031305040e0c01020706050a030609090b1609080a1b0518010e0603030a120b0d050706050a0206090703032109170901020c01080c040909020a030605180d09060c030e04020c060906 80
    0x4e0307004201e403059005104842c54440e0070b54466015a0a8100b05034503030030081588101e03030080e0032400e407150011306410314101321000703820740140210004000b032104040041d20070006035000c034070360008201100c9420010f00c1076400181580252307001f2801e09a00da41181400000342d0407a100c0908242d415034941c01019100e210f000c01d0a03011800044402c0c1900c0300a42c07091880c00c0d4003a222408030b1110b6187c030381c40c0034031a920050000c1c00004210340c807589c1c140b2085401c00020001071280d542166000782031201c2c0044801803d8101b5800203944d83c080381c00c040015500000706a400d0544051003c2c00d60380320680707050140c4103800e02c0008651007181854401c4001c08070440c01c141c2030000d03002c003400040000340ea00c00b90f0799102001040b8207110342030154410b0b00d0301c1e402c0e00f004803440d0b9040800e0782081380103000985070308002c07050300302c1c10502060b035041c070700344149940c0080050028006d030648440584550001c1000100340090b03482d0284a208141318080000c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 956478570 1250 956477320 956477323
    0xb010602240c160f020915041a0303030708190e16050108100e06060d020c061605070b07030203070c06151802072001020a0206070b0415020421080c031305040e 70
    0x26100454a00303002c120390203c2054000c42400d842e072090b81c502c0006911500040c8410383d0a9580040030011078100c0c0c807440c942445030002140e0040c541300c400000400000e905c80c0001024003080c041c12000045c101824181284a415072544042001411684103150380d0b2049402410f00b00b140311f040845c41d0760040c01680d1003907201c40d4947e0715a50a003444880d0040000e00740c541c02803c18001580312101600241c0070501c591001007015141c2800c800180c0c0b2030f0465000c050010401c81140440e60300803109501002909015a030303615984e604441201041d00042e1001e450a00040410003d04013100106c66100d9801c1410000b40030103007080744a0743c00010700703414183e48091894070941c0d003070444441050060311600c90f1181c001c11103951042e00704a0301d0241080c2000100580e081c94030121107840e42c4110305060814807500b20070f6582c212040350030ba40100340e80041201c00c03070032030701f9a083e000c055a44507502c0101105013030482d03004552140e0b0030070506090500c1c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 956479820 1250 956478570 956478643
    0x41509150e061602010e180a0501090b01021c0219060c080603030a0e010c0606050a0e010e071d0108130818090901020702010509060d020706151502070305060718030b010602 76
    0x1002000c0529080c100510a441d085003c00700324188903c44048801c0e41d56105006000040c3c00b0300283c000d45440d03e001c3c0100c0c2c40c140c1007420307424685000c018841c1d90010b00b0404409103506690544e2817060b80a074905007100300b800440000c0003511904202d150b070403600c201e60440d02c0e6841c5540325802090788a01600640360002186514006407540c07040680e440c0403030007500000f0305540c8404c00320f0461000307a048800501d0300c0d00d00400920f001d02001c0c1da404071882c984007480850758a03210a0804010452034100300c555408610310010f62550300a07001d03400742500765620074410045482d9034400300424420796070800011030818042c02298500e80e41603582516001064080000d10b8021b9803a42840c10340c24444a000500144200042090b16156410025207410380b00340311580e24030100070440d0001201003000a40c0007601c103400081608101400300c0400000800001d000c0d800a0410403004000003201313600815a80749c801d9001640c0d061a080070201c040c071014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 956481070 1250 956479820 956479847
    0x12031b050619060e10170a0201091a0c060f060a060c08070618140105060901090209130b0409151a060403120815031618060e0c03070504150915 63
    0xc0000303000842e8000d4224808040c41140e8000148003922020807145000c01282d00001403810300134248842004009031400200b204c800408840c0c1060380001c1c031508042c881c0d4035642d450507483e03003203002e00042603c0b04401220b0440d030062400b0045020440703004d4030400d009120010010850904c034110291050b170700600810300c0c00d5001d80e03c000040c22415413010360039001d0740c0e0745400100304100c0100105400000400d450a0150401c0710100c01a446118071900c1000709a03900d450301c00040c0704503031000c54000703002401000850094030284400600b0840d440c555201040314680c890701c0c03801c50b18030704422b1810a180c20700c503180c4200d000103400030310800a40b401c03180c403580b905940810402c5280134140c00c018042403a06000b214603c2c08640a9801404031000309030400c9607034006d804080c06403e01c1c00c103201f60b21001c09003d2150443e80040000c09690040c42118001e0148c207070081281104010000e20103100c03401083c000708680c6180c01c0c944c030b01c6100a4505403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 956482320 1250 956481070 956481073
    0x140709080312100807030f061a010c0b040809130218030a0201170603070905070519030c12090f0506040f1509110609150a02030c011121041103060112031b05 69
    0x501c160074588048040101403c40c418000e240218011005002000c020f500c81c0c88943e600704a2403602c0000d440d10142d42900d0702d08807005080040e81e022008030019074003c1c0c1141c0f129111414070074601d2180c52840d64015001c10200c44520b01d0310ba0003825150313180a410801e0440344000c054031200310710341c0640014603080145621002610f25243c200800404070390303440340c1d103103c0038066400464645000c141c0125414840000101c0d0750445101d4520b0100720084d4810700160504c200c001c03a5145d1155030702c03042c10803c000e03403400050352500401120f401e8070302480d185041c0301c80150201d07041c101a022010b40003070f89000e007100c0301d03074404c20800c0000300c11010310403250814800d459104054065074601c8110080061038030424a601a59982e11b042503101d003920086101204801d808216207200d840604c0240d80b18402c0400b000640e030344503400c085100c000c0000c286d903854000c490000402502813100070040610a881d411401c4071050340003500103e540c17402500d213 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 956483570 1250 956482320 956482327
    0x230403030332090a0213091b0e011503020f161707080403141006060f020c03070f090b01111204060e060a0e27090703051203070518221407090803 64
    0x88a0000d082c81d030b000766181c0031a0040348031a000075000a0000a44508082d5038890b800d0600c201c03c818458511300e045e0640c41998030741212441c44400510034030004400c2240400c0185100350100d6030715008151119840356414440102d4442442000301c9440d50482c0c9500c0812030308400752500d03c0e0300240d01d03506252a54903011100000303c00d0300c040b6401410300340401e01803039121340d00107030084e0366850420b501c941d940a80b030a04c2d01a1018420f5000c1c00c41000f04041a40005081c1d905608000c10360001140059561141080800000d8000d20b450810044100000b0b001140c0e8240da07080d500110720028004140304402414000880c100e500819909010600c0301a041c4e03c2c09005c41d0783c0b410701e41c49440d001020344101134290801c0e4002c0040c402d003040500d03680d5003000c00c000d00d1400c1840010b0006c0c03003851042220035046e1441926550380c0c25002c51545480c0001c507155003249512414020520301c4003610b180c845d120f02007600244180c5100c000c0d0303040e00000b54503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 956484820 1250 956483570 956483651
    0x1203020c130902130c12140105040b0f0a0e150f06032a040b0909070f0f081b0c010902120102040b07020d0503130612050109140f072304030303 63
    0x1104020402080c1d55503118640c000060725024607101c2c54400c01c0340005110b10302400300402c103102d0011128006802d044820002d03500342140b040c11035408960001d907000401005c20007950b40c03505d646030f100e031644000007089022050228410b0b108444125448a07005c1c0401095000c071450994000d03200340002820229040e03001d29451138140d0407000704040100c5104020360080c0c000010b1384002240003981030601612598004a030350034940c1d001d0710640c01c000c188902900c92402003060100109861388101e10300000c480c001424030507a11583c0c007440c180a8208003000320b01468119008181381c10042c03081e80d0030382d11002c900030302d030000c03a808011025160f020705a4040c04200661107480320400006c00082c80b403501c4000c3c142840300a81012100305070701000840d070818140c818100280030101e03500a05082e030078142130721002ca0444a0911906a811000b1010404009a10300700b002510459110b55428045030003070040c040081c00200fa4100704448180d4603011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 956486070 1250 956484820 956484829
    0x60905221122030320010b040f0f0605091302010f0e0310090b1303140705070e010e040c1401080a0c051605031b010e030f0a050d020301090219081303030507020c06040b0c06011203020c 81
    0x805c0c0d0660b00008114254040c00041c01ca550559060740c0540e44d6201c984081a800c2c040c00d0000d010494640c01580f4184402211602035460002c1c1006903400d05145802d0141ca0703105800d903800b43c1100c00001481869600a060b081c1d401c1c0e0340c072403910b000140140940003031610303500e92603583c0b9101c603601212003c990717400401c0c04942c2401a00380120f003014408041600800b50785903e207980d4249418510704800d00c87e0440681c3c0404820400d4081c0d81090b04c00d6001592418005608105114100c441d07000d0841070b0f603080400304060500340200003000d46240100e1034603000040c0c611802d610300701c0e404c00784c01040e544c105011013213441c6070010103000c0311051810a41c1c64200d070b0181c40412a4001d80002e004181e0129280c10b400140e0024000440c40c6803c05140a09201581c42c40038031403078600a08041d112070010328010b20078081081040400380c42a03407103a4407070507000a10703000791b4903010461040000000300b41da2903490941400380c060b0084e010980c414018071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 956487320 1250 956486070 956486117
    0x307050d21090803160504080307080307091707031202030a1d15030a0515060702030c12030f07060504060c03051e0403020c0d061a09010609052211220303 68
    0x800c18492240d8516520481a008034503495201c3d50050343e4925010041c10f900403150b02a0108003c2c09110500c4000390000c100e034407440d0030a00e0a03032650f503210070840b4003003816001501c50710039000200071020800030390941583d114070f84c01041840003503c2269240140c282200000d00754582508030703c03020b020325140035400a089888880e45800c2800c885178401d440d9194410340e01c1c030402502c10440f2890b10b103a00011106c440c58242c50b6000287d40d04030030400306104112003c12206504801c004036420715881c03260700d941702c04550400c180100340c2114182c681c10300b8068a1710040d84a417003070350f11a020584501c4007078584851880710305107008000728194410a400744640355a5902050313030706445840080b4500345400c0503040804a42d14002d80036000b00310051118a8110920306c00b41e45040e0f45c8490540d607900c2d0000c141c04c500240c0700c0300c01032800d2008002114220300604281d104005980c061099404003040c1c00308440c400a00060004803074424110b5030728102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 956488570 1250 956487320 956487347
    0x10810051c0515070f02010504030917010902030601060c0b09010902061611031f0e0c100c0503070c1d07050c03030a0b0d17180102010b0d060b1504080a0605090307050d 74
    0x5581d511950300d20f840d0180010008041100031401c0206096100181801c1c0d0040351009100c20700f02660080c0031107080f402035100990a0341c401d03500440b000d40c4041c02460300101140c400d940c0d9084040d0440203e114251421406000000d01700c4005000d000c00d03159028008500d402e2410002006007952030504031800c92424504e40500d80c0c040040e9580404c0c49080d050000d01d00400701401c4030380100320702005030071800c110b03c16540c031048008242c55041c10404010200340c90201d04500c10351100800181040c513000c10044441d07200e428016002002d20340702602c8845050300c40d809403039098070466200300005019105240c0200c27061a1020b03100108005442c0d0b0786004004119011b44201580407500c2c0c200030160040061118400380020000c41c2500030105c3d001d409d1a11000d04101d07224140001243c41c1c00e01d00c60864418500010b440740e891303551841c0c580d042080140e407018200300119036404004007c1b203045c3d0390701c94000c0c0301206448106036040d0110710312 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 956489820 1250 956488570 956488609
    0x605070f0b0a020a1d0d0b2701050601111203041b0801090b150d0213150b130e0703110d050c1c05010e090a080d021c1a0301060501081005 61
    0x1900e000060741540180c2c024a0803103005070315160903000c001d007860070031804680902d01c2841898090b444603040c401c09190040d07480d0f6103ea44400c08003c01e4031404030f0b002210f5440840600c1c1c44041035000c140165002d136110105981c007002501d9541c541e04070300f0440c07010b003000807600140162000302e200041e20040e03009001d6861a0030781c00c40740d4102054034001e050342e040107007502c0c44504c1c03488000c1c1e044500414481080d0041800c048016030000b100b207a6911345000441d01404040d0000d1800048281c0e46182480300310301102c50038402c5a0703c10851801140c00c00b4000d0068001220501803020308165901010002414003c0c0440980920820a41907600c60f4207690510076809440040381c50751424110903c1280c0003028265590444205140000d440100721080e0210080003d84c03140f58030240003203010500c07011607081524020401d0324a1000840941c1c454800728020801c03213948200640d0401412248800c0310f1072201020710440c6000d0704407141c042003011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 956491070 1250 956489820 956489843
    0x11010e12150c031009021e04061709240a0b030d05040906060e151b120c10050106080708040c08030706140a0b0102030406050d0f140105030f0c0607020d05030d14240901060507 77
    0xa9801f695405900084005840c1452120f400501c141a964104080c42c0c020100c61124182e110003071079a8150416079010004085410303041c1c250403980e4242402015210350f20b6100c2d02c0608254042c1c81424806401c119001481900030442e18002000141000a903403558048002d020f900c50080c0c4030840d81c443e052281c0b408020040d91914405000b021541c69035840e00080c50505102100d800300350502005000ca41d07030107440e880d04824141400c10b01900c50346031858a901e029080325020340300c00314100043c1300312030700400b0b11645940c20b0a9029210b128003001612034001c8000c1c0581d1081004100c032078450f4000301060b0810501c00969400c80b510071781e0640b0101806480b4001c1c3d010018440b40c507061003440b14401ca0745000f8244031403d40013081d038500a0005c044d02c14101c1c00b0311081030000a200701c0c2c00206004108104103070f080305413650780282c2900d000000610303e621000841c095150320301d100002c02043c800090380382c410304440030303400070030b0490784040240c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 956492320 1250 956491070 956491117
    0x60f151507061d030418020c0c1519030c03050106030c0905100e03190203060708100510141306110c03030d0c09030c030818090c030411010e12150c03100902 69
    0x9210341c0304030941c0805107640c0e51801461006e0605444c2200214030320408c605140d101d000070b03c2c5442000292241100039500c00c07640703c82801425400300c403441550103d0740c65141e043d408a0780e4603036a80c800300708507602c62008408840c0c811440c1400300e400c43e40c06200754030b401c0708101d640042a15091900c0c00711072000c80d06104041c5600e4002c840702d101001d04501d0f062007625400032081c54021901e1400c201c400d4500411480380c1030140386d0b0400121200343c400e03100c5641c000f02076594039940b10048a20442403101920500c00011280e031440036041401241300810550001d004604004905803408020001c541880003409040000040041c04001c02100218010342400361140c0e146441c0f0034880403404407203031040801000308101016510b054a4020380c2110070b55145030b40c80750040c0c03030b05045181043c3d0b000c80c034026002e0340b80400060b041d1030b0694017942c40c141e68075058001d1205000a40d07080b12000040321060001d0003903503001d0070701d80740128804002800c07003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 956493570 1250 956492320 956492351
    0x140705030a08040509090d080103110f090403050715020315040209120a03081021060c09090e0d0318020315091614100c0b0703110d0509060f15150706 66
    0x15a0740442da14680410200700d9450002041d6620145440150460614070b40e00141500030500008002084155918015444030001214440006040e10300c140c00c141c00d010b402c98011200441e5501040c40d2906104c0700903000b0799001c2c66268894246980750101003002a42220340c01c142c004144241402600c10204541305002e8040e45841210303041290300a1000722103500080840004142d40e0b070044c00707500c940c10f124150004000200e201c010a01200c03c4d42e5950b000c80507183c20188044100741c4081054890400c07251000c000b0b407000c42c040804400c060280c06941a00000e00c0751507101010281f49901420000035650701164090000e1b600301d00c3e80d0442e403d40b85000349021524242101900000c8015040030a405d14a60359a0010700d40020b2564081588504c46804243e80003029520000000802408036261649450395176480848003007122100b04000724404980307811100c00750001c0604a155640850b400352801503000172f400729611562242d00e40d007800e41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 956494820 1250 956493570 956493583
    0x102030f0705491b050c090a020406030c0905181801020304050601050406120f082a0307061d0624060a0e09010b0a091206090804030b070305011a0714070503 69
    0xc0c0c500003203406110780910704103030841801034150b294607070390500e526503600245440030315000d4600c0001340200034944142040072008200b5004440f42c018840140c559130064815907980f550200100c0656250484902c1d84504c29950000340300c0c8400320300300f00c2c2c124005d030748003048034003501090444e2032a4070708a130701c1220180e680d078000d000148981e2800780140f0000b400300401e4061081e110b9280c541c1c8010002900814415000034806d80601c3c584c0001e00280c0d0000a003110400c1c96072140301d40726440b2180864903e40b80c020307071171392003240c958146c02d13200b0b034000040900ea603540d42e912004448092010080b041c41102c921001c1c0e580000070305100500d6a41d030301a10100e0b5080c06481c14060708441d524001c14806503480c40d501040c52402c035404510b00102081c0c0c1820003030004c00c00038002400b8038400003030210511640514150145140d580c0070046a80e0307030385001030f858848405500d000c0030104019000314406488000042c407001e07060714101d9542d1400280f4040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 956496070 1250 956494820 956494873
    0x10504090c171509010614090d0302070b040e0a0506060403170d1e0c0909231906030b0f07140304110f0a09090203150114090702030706050f06030f0a020102030f0705 73
    0x302c030b40c20783e00d41c03418200809401070215050030152443c3d15500d031100340c01107801647c0a94440b2000d601410700c200800001014800342c03507540d035500c604100024070022079621460301d013014042102c504045e4101ca0480742c0000c03032416003800d0b28005c1d40d0991f00c011801c04403c1c0d110b075200700151010740d034529510b2041810009485c1c14041001d4507020141e88100c0d0542e2621400703802200c40014849002c51113a050300b60156159035844981499504844010626003440401008a190070603402110860305a490715955880100c0321640c9000c501e810000c01880442d0016180d0104443d02c500010a44d40e031980c0003a002c07905074000c40c1c0c0070b0701845441c4d000c8042541800e11003010446d00841d02519103604006c5000c0c05020a19911402203134032800140c3c84610a1040d280c400c0e0b03115805001e142003904400905007000c0e07a01c103102c2c0c0580c0220707200e036103000100d07580003c0d41a009141003881010030480745410031141aa01400b5407001054481c89103039003543c1c1138 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 956497320 1250 956496070 956496091
    0x90d0522050603190c02010915020702061b01090c0b0715021b15010f0f03020a0b22140f041b031e0540020609130513051b010504090c17 60
    0x11541691484d041e262081d8000c001c1da40340c582a10003044210f00c41c0c944c003484100000d660752101c0d1000c10399900c9191b41010800044800c4011100d46c103400071105980960040c50f503050300e50310310391058441d4400090048407441503680a05226401801510b280c5080c8140e068070401052820007010a4400110110000062200071607a04a240240c40007403949505c039030450380400c41c21030f00c034003408103142001300d00920080c1303003444800c030600000f50101150a80d01c2d2000700c4d4035910001e14038440c01e2040c52600850405202e00703e10108040820b072400240c16034141c0003070100103c2e403145d07405d982c440301000446501030140140b0b90b0551000a41d401200024941400d481c0d06c515201a4007041010101c6c5a80710030303100c00c4d0100c8500e991040c5210014180ca4880900d134480700e030903d8200301c00400003d0f81c4001040c001d03015581100030b2791211700044a15510300758045031080c0800d025070000c17540226052446400d00c0c40c5100090400500450011105080c2c1c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 956498570 1250 956497320 956497351
    0x10050904050d020709061a070204091a0106090b0c0628020a0801090b0307050a0911070f030f020c01180608040203010e070b0408280305070c0308040909050105090d0522050603 77
    0x90550410034a070007041744d11000c00c0b02508240120111100940030840d40c40d030042520b40543d9540c0e4414000e569110840b9111810303a4804d41d01101000d104220100f007812800080c0c80c81132004585644c0009400b41046644004110940004009070540035840b629010444504144002c0801000e2510b40d240b00358500844001524000e500310786c001e410140d401c00c201d0303d801c00140240c036001000800c030030030642d46098141c05526400760030080c02490401c181030b0084d0340c52910700c50365400d4411000c8044e00544921000b83d08141603002c0d51002013040ca07220700c00d13094006200500124110094501da40d140110a41000420031400642001862000c000b241c00c0f41340b0460b040700718018012103850040038400c901070240623000900d402040341660100000c0c540c48408130343c569480d181e0000042aa80c0c104460b0b561a0001090400a00140001943c0c1e400e90b00d00d0b290903585c1e03560016543d802c203000d410700495030b0b40108480e511031010b0341c03081c07908103103d00c42d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 956499820 1250 956498570 956498593
    0xf0603140a020a080c0603221203091101092402030720030d091d0901020c06191107020d140a06050112060c1b080a0c0206040906090b010206090d081005090405 70
    0x410320f42944500c02950000d21071103900d4442c5000e03039078000e000744955960750381840441c680818440100802c60080c050110300c0d544e8041c2e03c00100750740151400c402c03c0400c0001541d045440b40600c082080c204591881c44000c10404c0400ca82110300c183d07402c1c485141e483d60340c0406468000c1d000c0494030031404060341403c04c0f0102503600c041c6020f601d0140b9000304100ca414811022040e43c11092000450300c0000350106d40b50104c8203000c40c0c50a242a150709840e2054420031894802e082040300d00b4900c5ca0b00060320001c5400a0044008500c00d07030754201601c45088032030130385000c1c4000c600081401482081d00801d0711070144c9020445924003a0201e5440454480502129911000004021008600c40380c0e910840300c980c0c0e00300da45c01c1a03805112405001754071080001e00400e0561440c0c00510856802510034440c8004217401a03885500032075490300c07603030701c8410000e0701c2c14840c54880d0f8020050b03001300c3e5107031600c0d0400301311910005c990a8409920486403503a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 956501070 1250 956499820 956499829
    0xb010f06020f06070c0f03050c060411191d04020418050604020f0d1e0311010e010204080f0105010302060d0b040b100e090f1e0c09300d050405040f0603140a02 70
    0x1e2142c0301180141c02580f03810040600540102000138180c29907018aa00806015000310f400040824046800c1440d0500d868003150850320002402010310341003400400740c4003003030301080d80c2c0e0080c204038050350f00b03c84881030900018000c1e6440303526491003c4950100f0680a120f0034000d8028054030301d00b900602003041c10000c1d21501442401c9515000f19049007042e85a55008504d007140d114814102121401a5008a00302d5035180c0700701031a410f4030540c003c008942c240e06c00c0e2210720501e00c0c0650f088035000d100181d04081c0801003001000f031154400c02c1e5040004000180048500001c01e03504007500d079060001c074580380d85c000e00f54076200005c5a0b0200d06520080141c0c80d1950407980a100c1c10b24102c034040011201149652024200b5240317004d0000c0d207280703080d070040401140700c140040d1000c0c0408000c41c8008070340110210358019003480d5501d03004c0c03030207281c0024400241244109002429687e050210018072540d90a04490341d11100509400b543c500410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 956502320 1250 956501070 956501083
    0x51308190e0904120f030e25050306010308090603040615030c17010504050c04110408161805070801140d0605040803060f030a050c21120a110d0210180b010f0602 71
    0x1e845824540104000200649140c0241002c41d20300768241c2c040510085d005090030035406401e50082c103100c1e0321420b0000d1956004000a0300f040f4400642d40c40c123068540342c00380006400391200f0860101c1905041c0c00030740e0414810000054010b10143c503401182c4020f410403207603400d9001003003000944c0c07428141d4130100c80d0f2008010300d003401d558442da1041c018201500407070700c0e0340442c080110300b90151401008044240d0b0100b01c1041001c0c0e0718458030303000c1d184201c040f0a010300107400c201e21641d80705e5a100d469103030041c0d00b040d9804001d6120f8011069000a0300312141001507400d005241c06148a06502c0f903d0b4203240040120788a240034115021f030f8030046040b40882d00000307403803080300010b88000c1a05122a000c44201d496250b80a40c0c0340e1040300c400701c2a540b0341d00c0080a280134181d0311124100c8842d4035883e26484506860710040e070006480340c04450329907010340214070032300b10807440d110400e40d10b02010030701c244d000f1420445040c5080040316014080e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 956503570 1250 956502320 956502347
    0x50105190f0c152a08061c08280c0b01361e0c0e04050c072f09070507031805030d030608061b0f09030c1e031c090905130819 55
    0x406403444c58960f030040013024002d14580c89019501e5280110030740e030302403007880b803a084940c99654900c4c11545030041501960743d240100440e01015015078498030102410690042c00500d099181980200034451008a103000f204550036a001e80109068000802d00109680128241224840e001c510201e40d5003a6030945003001007071b43e0340e558080322104010764115800100d64a13480a08204c42c06414001800c190001002c102e06030711b0500001050400341e09000d01515048082c0003103014140d88181c08503a040c01300e1400079001d96008451000103844038030201e60342e00006441c4c01041081100402d1b0b8034107003441078080c2885410ba00100b03140d180c03500141064400d410724842d4401e50100d842d40400c004d509035605115500000d2401007032541680c0340e048480c50304407000c2412034442e22440c0803460350b0a002d120f04040907422600c902d103499141070388201c06454020280aa400078000000b000559483c1c003800c0300ca0014040800003107108400070300f100001900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 956504820 1250 956503570 956503631
    0x31b0c031c020d0810080a05060f0105061204060207060b0307170f0d0e0613050409030518031f0c18080a0c1a04152102090a050105190f0c15 62
    0x100c03107103030540005072040039100030b00c0d20780b50030f5a8001c100000020b0680050301035000d40d058240602c1000950306004605c9a0310701281d50b6602e2040002c40d1140e62a0303800000c01e41c44c005404071310a41e002e0880c0c5405518042901101d03680000e0400f01150090306007103406c14070f01540420204550500e42840c2c5006001e00b00754a207018040c03444000350f80348900c0e0000303005041d00140c0c480c100c000707100c060400d10044000b0702d40940182c1040e4a00d0003a91200f649029030b9140004600150050070300c030462180801c01814005040e01c50416014404079030390b00c22005410611001c02000c008020300000754103031601407003207001644418440510700f09501c15503143e207000c6a04030348440345040350180c00400241d81c0d06899a454404000301c0314006070a080702c5400800d0720440403105464825200c0005540d03c0c045c4408146c00c030446071030082c02d01030144c4107401001c411424810070000c0c8503940c0707514100520f0042c00c050768032007900d03404508611f00d10300c180d24421403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 956506070 1250 956504820 956504863
    0x1514091005040c0e19020408032106010e01030e010e060c0306030d020601080d0c1515030c0909150b120f03040f0b0c15060609102a15020a02031b0c03 66
    0x3c4440152000f00d0141c00b05209683c000b1404081d84019130042c0d44101c41c006640341e540c0d558550392641c018140d50110026910f0125610104021031188201c0c0b050311401c000c02c40c403500440080c000d00724110040e66880450172040c0c0c0e820401a44a02202c8000350f0b500d240800501d0305240e0b8030b003052015940400018002c44401003a5071800c808a8600320181803d542001e0707078444c0004c80070000d800e103030042c035601e9104419801010349001d40d218091155486034280100e980540000d045282c50030300c003071072592050304a040e41c04001402802107074203151a1a0400100d0710700068543d0000500300440c41d440340400009000d89001b4a08107002c90000301e44422103209e00302c1301d00340c0900009029039985010f649400354046c000302130701c000485014181001c0d40103c41d80f000c600810400e03508554907400000650300203030804060b43c0006070040a90010708c010010760200b8005d403010b9503076005940b030125108000810010741c00f0000d0508043d2001c04081c0aa001758 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 956507320 1250 956506070 956506073
    0x23030f03032e030305031803040602031c06031a04060506100c230d090617010605040510020703060504060b1e010503060f0a08030705030405010815030a0b04151409100504 75
    0x80103690303104181440c4851201c10a40c10b001079007900c0340001040310900c200200505901038091403056504900c0d81d401c807000c441c405656802103200c2c07040140d004000140c4035602039815019510020f00d40421450b071203680b4491503a031840b6428028218141c2004207001c818018140c010500380d4007800c00c83c40d0400001c002c41d8441401901d0b40100900c2c224520343d1140355500000003600650341134011510b40140002c0603442500001200c2c4c071081040109a078044070f040310707002c2e01c1d20342c901440c140034072201d501c46954039030941c06501d900102043c1d507400383c14801d900c41c080000344944100200080842000c098030342c0801503046004170350360018202c2c1d0308844111551200b1a00187c002100780d101c60b04441e01900001c64080100500017014000741e034400d89950400c2c1e541d032104142c04861000c80b459055000884072000710754404104d41e0440c0c00b801c0c40f85590f071100b42403076054800061000c2140c0c8801020840007103c00c0c082c40204039441d0105000d04d0925 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 956508570 1250 956507320 956507323
    0x203070f0302031306021b01090305090f030105010e07180b070302070609060f090311030307060f0207060c0c080706020d0e0d1124040204050a0b09090a020f2211040f23030f 76
    0x90307000701246e038005150480218040003100e00030907004024804528146002003054011040941c0100c0c1e60310f01046052606000da681a500003142c0e114a07950307007407401c49518040c0d40b0000ca640500d810082407005903600100f0105002ea001444404d240003001000d00f401030340a1020081d59103141121580c3c06001107045940050030010380c140b424002074118030510718010442441c0c00e100807402074550b0090003900f401036404205140580d20f00743c8141c1400a40100080c104001290000d41285d0251440500c0c0000002e41c5802c80230185e880c009900d100d001c041048621004541c035410041d4002c0c1d000000c20428144003950728240810714040c00081c0310301d4827000004c203440c03402e0748040186040200104400e0400b030301e00c292100000c003002e0380590201d42c00b000da5402c04a040000d06c0204008242d0340030a0700b50081d00418201c60001607006d010080000c224030007551003409000290b0003d41107803000b544200240400b403a241380a03030000b41011184000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 956509820 1250 956508570 956508601
    0x204031e0309440a030c1403070303090210091212091a0705010e010b06040b0c150c07151820090114090a060f03021c0203100c030b04270203100c030203070f030203 72
    0x3410304105800d11080d00d08447e01714600c00c842c0e140c900c004900d0b0401d2580c0b60300310b0500741e4002c0c0d801c07451100420f0400ca0345041070b80580c400001e01c070040d290008005160b11100c114461801030078941d10b40003111003061203074080c103280c90750101c4c0d0392040c0b0500b0b00c40c20040781d2001000300103082440b0301280a0303025502c15205001c0010664240b011400c1c04103151000c0309640000d06440e04024864094200b00e000352048400350442200c4044035104003650601030405040c440d2545654040e030b040d240711010100040011a080b2294480be00018042e2404400a50815814100784003500030000c140090303090400d01c04010550440310303480d0036a0340613a102041590788030002c0c0026040040000d4051107100d407600c40c4032036240d0010050303150907901445401c6401c420030017a41e031002c0340502c0c03080358840c403440b00081001800300c0b501d202030152040001e00f600f596040b1003c0e0b40c00321011036000030803c85402c0d1301406a0704082c40500f411425400c100880306c22158 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 956511070 1250 956509820 956509823
    0x31317100902150a09120c060206100b0412030e0312210f0705090d1e0c06050c060a0e100203090601061e1b060e010c021506040204031e0309440a 64
    0x440001c8100c4030710721030481c400c0500115401d0605020031032401071440c0215108e4800180170f4140400c47c3c4050700d1041c40c0c00c85100030281402c09080901c14000103129800403400e202d901b145503111510203000b03209a00241200741d540f1204004104825881ca201c989000000c400b03003086a4107a800f800c8540105076858101d0b01e401c0d800c00420004c0c824418058516800150305889540780104001c000501c906a440006030ba101006c0e566402044205080c46c0c100e40c0000d010124a40d00c029200c1d41c16800319501d44821501002c200d910a172030409403500310074010b100707503608405c0e02e80d9131100b8082048440220380100918815030709801d202c10052541000c0180310309a0000800425054002c00584d40101406980c074903040760300b61044066100000c0c018030340b034400d4408994000c1701c81c0040411440c059581c05080040c00c50900c00e107500e021940460f01c07202102070400e0110080c54620303200d02c40c0d40a107a1010308100c030800c00b1a5240c903103000040740980985 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 956512320 1250 956511070 956511109
    0x1b150c1424060a0302030313150e0f010305150d061508062502120409050604060504021c052d150409110f18160e060301030302060f09031317100902 65
    0xb9261000091000c0300c4990019616100c04120b400d14103580800040031151050780f074600140d083c2c00f007a18404841d140c0035a10000c5280c42c107000e0f50280e0000740c2d1200381c03c560f00c03140c180d1050000781c0d0341005400946165503204001c1d0390318841c0303a911002501542c001042030b482e00448014034460204c881c0b004e40e502046003048041c1c000c001e0482d10039003400240d519a92945082d0008010403214180702d036050203800105030a040c401ca48031494507003144120311210348030f844090300c40034203801c400c404c0c015004c1000303107002d1400d0345c1819200c40f581801401c00c0710000ca003c200d52003019214034500b2181d0400140e80455140d00d24805413030500c54911030200264610f440d14150043c00640b4204000528a0082001002d6407031901c42c807004080c40d20070700c40580003d02008000d6404103000c1aa03010a001d041640120080100e07480c1c01034429482c8114030312503014004e00c0145ca08220002d0703006200f4a4180041d1000400c1014102c5d000540000c9680d92281c00c1d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 956513570 1250 956512320 956512393
    0xe0d0c022422080a11040516020d050901020f011802180c0427090501060602120f0301050d0f0f08030105092d0601031821020d0801031b150c14 63
    0x54001600d420042910b0019502101c2903402c100f04811740c0001c403240700b079180c01d000941c607000c094060141002180d00070405403100c4402505c251388184100360640c400d011b0300800b264024004c16055101da40e0318451800c1640c0305001c40c502d52500d0304980500c020b410018031001c100c1c00e031011600350014040040207078032401c0300c0b91035003020040061400d0194804c24031105410800449220b6400c807070600e03d10380d100c03040502629110803444501000100420b1504005410038a800b441c140701c190307015907403404881c3d0342c0144100e4001c803010004100701e10780401e4031503104101403400a5801c05030613456001050f000c508001c48884140070032400d910a40c8000d00c03514050030040d4050080c1d0030134500e2000029000c1000301c1c44035810004040c8085004500d2801c240c03140c441d140d0071661021a40440b6140004800f810480300007802513509401000b61505501c0d0040b001c80a81003004100d10f001c0080041580103d0b01500102000e40d01c0404000030315445212 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 956514820 1250 956513570 956513617
    0x11404032d330e01142409070203040b07030e010f111c12090c0302090703020703080f04170417010e011a06031f0611161202060304060e0d0c0224 64
    0x100b00c4090b0409034225140070380381e454020055000743c850740d2110201d00a0755a03056203800e86040d0341d84001d08034000002071900103040c42480701c0e4111000e80196400e090301e41c0d039040c080d500034180035030020341c0106101c4008e580190030350803960081d10f09803040c540d036800e6056030703900061406092214681074028150f40310b0721101406481062003402044801d0130b1410700f142803804244d1040c038102c0045070319140a8803c54080d1503260b00d428800e40d0b030b854a0100c00110040c0705440100d245000d03a0010215400108080c00c0c0941e00502d035403404156807030841e41e1070101182980c1c548401d03003002c445000030001c1038a0080b944a60340b40da4200740c0000300d90680c900c620413010b40304004a01990800c1e0441032070034100b0700716940300807005120040c00c01240300e00b1605603404450100942044402140e025010701c80100344540746202c00d516000c0c43c400c0e000000750783c0c0c0e1089021850110f0311822075800030310114662000916410400744940c0303e059003856140300c40d004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 956516070 1250 956514820 956514893
    0x50d140406081630060b040e0f070309080d1406090c03010b070201030605151c060e0a0c0e0a080c121506100207080d03060302040c0206040f11011404032d 68
    0x301324141c0700c22000c5015440e440c0440100c4286052101e185041110205610031038409071800c490880300890f0043e1140109070408000161802c070415481d07010000220b55603c1c0146200d04640100140d000c2d280c0c0e840204104014050501c180354070418441d03204175003410307681920600c2080d0740d505c130003174401031f4024003c079400319411911002c121007800c42c0c0fa001030000c1e00301403081c0307008060030301c00d050040368000d014800781d1074811800b0030407040296201c0b84401c0f0301403d0108070840031030006100d2441c0341c1e004a9203503008a4411466040482010302d02041c2c902c02403070805100380801c4007440c5d00030036441c0106521003e030701c4003e20811591006009102c03d13a00280003400c40280075011600044e4040c03401d000010b40300d603200088030761042d50820701440c0400d1301a6108009030002d04202810020031402100e0300c121214024001548200110001c8083d40784105803d660b004415510b4050002c802001080001d42030a84801e020342d07240c90101640301421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 956517320 1250 956516070 956516087
    0x207050f060d050405010e01061205100902040204091d160518093405010e091b040503120c0114010501080a091a07020a1a1302210109050d1404060816 66
    0x285003070b500380418001401010343c4104207454500000f800100d4440103024141c0800100040c040c2e406210201d21115a0368065004588020005441c09950356409010b55110001075403000c070820924042001c410000c40889806070151030346503a14000c00603a81103e00c2c104540c0e500c3c207840000e039811a00307000308141d640d140c00c4501106c0350402100d504d000303149810038407101010500440c00d503008450b03840301003c00400d2580d03269a003880b018030413036254860a040900c10710011910b46d5083c00385401e03a0280e05980303502e81c0b0090101500f07664040c00c1890f07044101e03500500860740d0081d1403980c004d1484101085c0210a0300c2d00200072800b84564104446401c41404402c80e8003043c0241d500b270184640b48003640d0b89035001c1d40803900035140052040131581d1004014108000e45c0703482d0302c0b002c8462125403507680001c1070075614441c030304880d9a040714511012080c2c1200d2500104000865011300f003034200040039280c0900503011181d80e000d40c8103149038507449150031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 956518570 1250 956517320 956517337
    0x6051911150a1515090806150616050d0507060605040209090f10120c080105160203160507080d050306030d0e01080a02030604090210091809150c271706070207050f06 73
    0x6a50f03199548440e0a811440400c1100001401c1d42e080000c0b4800005100d500481c0140c898440c00558201082002d41c00b904005883d0707000612a500031910a00801d0300541c0346454840e9102d145252140485245400c003c0c403c51050084000c1070300c5140c112544000308400c50241511410110600b0300c660b0340c01510164041d41d003076010012030070204011950740c1c0b00280021740ba0102103c4008c084a05590010380c0180140b03112210580c81c421782c51801582074407403d07034581d00340301d042812080728800400d000009100840c2020800a03551100c00d24000d40140b50f0000020f045200240c4009a41134003c40400c42d140e03074070b901444c18190f00405451001218070707800b424031200f03407050b8459543c0010f65003903aa17038140511000700d0380c003e555041141000c50360304010701d03a0024510422141c00050301070303030302c91003e001010803c9480b05c15680d464050040c0c00340305030a004aa141d0800d2050041ca6a00002c8c10303410740f1001c07910038800307455840224805004081a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 956519820 1250 956518570 956518601
    0x904020a14191b020f1302070605012c071b0816110a06030e07030f0516030302070e0c091807030b030d0c0203150601090303121506051911150a 63
    0x2d1200241d101000d1203051404240c80e104419290594500c080359848500650002c001d01c4020302a481d01303c01c46110395001c0c100041c2001c030700ea1200012036509070030140125140026069090780c41a4804480c4404289011080d1500e680018003580b22040d50707101c1c80081c0340c041e20411100c20150780c48031907440004c082aa04500f4205200d0104c0d002090003146064404111144203019128828840d5001454000d02c4d582d1290203817440048152003c2c064180c00000c0710b08103240c80300040d4000d500030b00d80c4a040c80c90a10840c1c00103401d40c200301404100c00601500c1c1c84510034031b10900e100c0014580d41d2464000e601400044280c16418050100081c06064000015004540c001c3c4d00b15842982c070125240100c107c16206503010680112082002030300c00c4841c40c0815600c1e00000c00c0042032400703a0180c2401d1500003c0c0401c001003560108a5000c0c100000e02118501e009150306100b0038034641c807641c010021004154884002036102c0c40a41c00c00c04480708240c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 956521070 1250 956519820 956519827
    0x70b03101212200a1704030b01171014010501030b040917130801050417071403030a091101030510050f0f0a030c08070603020306030607081305070e0604060909080904020a14 76
    0x2a00100c2c030545880590b01241e41c0d14014010400e50840d890b00d0f42e00444020441c0e40e01c2525a601c1800315a0050300c0d40640070080480002d04501886008000e2490b101c030000ea041d140ca241014101c1d101c998842d0701d401c1c1040034036901e251403981114001e00f00081c004e0055008200544491003001e0141d006075003400d91070b140144003c2c01c81c0b603019800d03191702c151504081c41c03d882055401a25001d503d100000321240440d004000c118402d56003441040c9a1200c9242140c0040368516109545d50103094280b09040b041161880e1003460f04101c289400003401135007080b940074150003890710b40c203100d04540f01c500041701911401480740590603924600100280011700030002580160340000074200d00900a8038040c10008000e04a582e4030f08600300c542c1c28006091400c880c0440110101085090103400301405840d0784145a41c90038109202c00d0345c00c0356000918251074500310350003240e101010f80c0d050781401c44000d80d4441e804041281c034406041d80b2070240a1001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 956522320 1250 956521070 956521073
    0x90d080a020f120310210b100e040305071a090a06051807030507080c03070e06041a061306030b01020d02070b2b0c0311070b2e060305040203060a090302070b031012 72
    0x4801642c4a0851280308140ba251910041141c200d0481d241d1b0900c0b03480c402c0c1c81c10019040b483c0040d80200c844400302d070116982c410042c0d24820a4500f540440c0d400503065003800018412207d0381880c901003d01a8180310808076540c0e92664400f400d900d5548012510b0611260004416021703413a0884800e07945a04000d41c1381c0803144205411480751454542090801040e0141200d020b0a4540c5680d07640070140130140000314009071004c0d212500718201691524003901d800c28600810034461410090040c00305c5a200d000c103030565024a210980d540e90000d005820344005407101c3c2d44030b0f010b07007000d030ba65000c03c400881c0700d020400c81c80b07060139241a80680d00c11841d580e014000e8040211101103140300701d25000d40070304007000c0042d225500d000c0c00312084908414513880300b03840c4103848101e2201544c00440c0066140c0050006600d001c100076900032102840c00c00204d072565a0280d6522303164801c41039072000110005d50022002400341d40200300e13000b180c0e480c01015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 956523570 1250 956522320 956522353
    0xb04050c0d050c042d0e011212171e0603010501150e04060b0307120501090207030507030e0a090e010b030c031612240606030e120f0d020c1006060f0203090d080a020f 73
    0x71704c25403100d0114203000003886449910010b048800c0004000b00d4244191518035210444400300d00a00c4524103440d440c01209140d030034071a9036501910f00305903201707020340040c030301c00500396038481c1c0c2c10300005004130400c031099020f15107402d00b000030b92b0301c0401c40820041c0800d944403070700042c008010861071580004600c40300b580d005074100320136a21081104220b00441c0e03405000100c003804080c0019000d40160041184020182c0000564400d04141134405d24280040705946a4024020b1130604200c410703418182140981491204640031414455042c861006242c0c41907076614240500c250340321260310070440c8070390140c000214211000d40303030b24407480d0002441e10491411040c3e01003a615694550340b405a0b1401d104900030400c0f64000702c0b0640d07081e41e0708001c4c20342042c82c10040d4074407890a011001c14010314107140500f04030145082030302035400810401a440d5901407031981b00d550703c12001900c4401c81c2c40b08030719096919007060b00d40d128908440e0220790300b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 956524820 1250 956523570 956523629
    0xa0308090a060201060f0b0d02120114120a08070b0c0708030f06100e0a42030501170309010c03030905032a070e0a1d0a030807030b04050c0d050c04 65
    0x203041c1c405800603680c46400300c1c01c0712014031490030021042d503424402c03112207800800038050354440240c20554030740380711014160b00780d02080003940480c03007207043d5040c5121540400d61220010b0b000b118540e403241500383c071035204001c21015100d000125641000020b0b070740000d8008102d261a07241c260f0380141c0c101d50070b454040c4200a03050007406580e129040028510341c0142c0181c40d85850483c1c0010625a0492030b000560410404510700550f00d8280c0103240c5d50f140c1e108100381d180d0b4500030301290410b0b04810712a44840c0d41e614040d02c0000200c82c5002c2d000e217000807410440b82811401041c8501005000740000246401128404424031000014450803041c1e0f29107605602c5903104001c2c031540c3c02c1e410541c0c0004042210315841080c02850342d0410450b0700c001c070401035041c03c11020f002c4001c0f4030042e0501118983c103101c0e0780314100c401d40b400c0240d414455070185840c0113102c0d00f4013450b82c8070000990400703801000d440084c8400c45241203810318140c900c045210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 956526070 1250 956524820 956524837
    0x717011b080910020f120a06080d080a0501050307060c08030901180f020a0506090a030b040f0c0e0a05090a08070210110d050a030b0603310b01120302010f0e0c040f06050a0308 77
    0x2143d481c151214401d944225100f0351710440c42d003407411108606001d01c01d00001c00721004070f60364800018011100b0b1244d401125620707511440d40f0f1804642c0e0404856040c0c203d83c2c080c0d40000d03024401c994100c02e0301541550007030000c6441e03079100b40d00310f800740c20800325081d07040400001c0c4004011040d000130311220300c01c45d69502041d03280c0051103658004e5440701070f400011500c0800207d01c20341d158581141c094101103202c4905c507158000301003401d44c80282080404401c104503c0c0c002e00c90f082d00001c1180180655907029112a81580038140d03010303100d02510541460058020807407502c03140002426200d6440244001410640002d0a090b0100e402e03d5503441040c6040011640300e5010001110001c000d02c1d100c501200a414900701240380615440f200401c01c3c0e002814000e1501e045920100102c0749002030035207680d50140d144150030560040001c8c400444c940704d41c03e609803800200c8500d000303981d101622080c3c7c85240c218480308004001c5c403403000010016903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 956527320 1250 956526070 956526073
    0x409080403050d03270f020303070b061503070f050318150a0b09060603040f02280f061d01110c0402070f03230a05070f12020a05100b030717011b0809 66
    0x200180442039059844194500903c601a82c1048050080f220640105d0502903c072090000703211368086851b5a00c201820350b00248000c0c1008400d24005000d40e9486a40368811800c60810200c042d00301e00490b0860014020040000394045c3c15a441d0601c105200e074044030404861819038110140c1d080e20901001030a011064405083c0001e50f00d0140340043e12807441c40c0d0b10354440e030110300b910100813a404203122000c600310514000840c075040c0104101c0104603031800d28000c1184815502c4001031040c0c41c42c11b90701c8441540c00a010301030085c00c01c0c45401d900c103d82c0d0b60810070600e00e00d6600c184045075410134811914a42008184280c95600e4594081c00342002d03401c407895500d0840c135000300030300c012191180d0082c200c582d108245020360109140c1d102520b03080000c8900700107030b11910640703082c81810080c1c4039004298220400c4021600070209403900c0c45d6010340581c1038480d08003c041e0394400d50020744200c82c01c034075440d400c1507540401050004250355034400fa = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 956528570 1250 956527320 956527333
    0x708071d06070615031401020424020604061d1002090f1807031a040603030203091305090d05070f0b1008070b090a03020904050c092701050601050306130b040908040305 74
    0x40c0203520a6050103200800440c1462190b039110006020100c048904070401400f000000441c2c1c1070511960045038400075849505202200010072400100c1d0f034680e01504006010781c94010039a59080768206a001c40d031404490214408200c900f140c02202c2c1c420700d1418035000c640d5501038401c14034102c8888242d184288108500d28070412610f801d40e070340301c801003054503010b070703000308210743c0c44800114202d40b0070310001e01100c0c1c081c0c2c01600580c2002841c90280e10340b103c80030025260f0001c08001e1790418400403a0303500301c2480751030700f4400c00180070400c1c080b2507400c0c0d0a41d960302003100c50851801034103001c903807107031486205060310411001190500425064030b203400b001600c8503100c2440c527020004074040c003400660302d901440910402c0c0340c80380503141c0d100384020240d50610016410401c24290b24550034265a1f9140c0403d000c2580ea0020880390410011074070365804811940d0200002c220344c1a20607440741c40c08840d00104080000540110303801441600d2030f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 956529820 1250 956528570 956528597
    0x131e0e060f030607230403030906030b01140a110309060d0c110f0d0f051204110f0f031024030b07090b03070806010f05250204110c06060409030e09070807 68
    0x100803070310445140d050b00041e0018090612507200220340303164103d040f2445100d900b0b01c0d00c550380e10039081030740020b211003001d005554050040c03100001c0d0078600084042071100080806004240c444000c204515001120064040055903d0440000d04059403801c10b81030000c000c01d043c144110101d01c0c0c0e003c600c3c1c1c1c00e0b400030800015030401503029100814042100310341c032190303450807102440700030f0007080d07200c160300c81c185d0340310f14400c05e1600e9121020704204210082d202c58801d1142c9000d11b510300309a100840c200b01281c80c15080850341c07424010741201c0c04103000220200000e401c0c00004140300c0242c880600070522612074860542e255140200c26200850f0307803001003180900420b000354490104504c0d48044c41c9801802c0402140076040c8510710410380000704a8020800700070b614091041d8100e03500040d06184c82d003854851001e481d800020600340c0b240d5601e034071240900d4040e52280544810042c07455105282c1f440001c2e000f840d05442440001d08281e100b01d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 956531070 1250 956529820 956529829
    0x10e031e0c030c15070204110c010f050a1508031213080a020a1e26041d100e0f0c070c05041b0305060f010504380a0f020606090606131e0e06 62
    0x3000b000300c02051610f030074911b0702444041c0c94034007128021031a04008101c00303240d080c8141d25681042d15804100c0381850786040080c2c0300201d90202c0342c10801401002034a10020032074064240034401c43e074855443c07181c5a002180f201801424441c0c00080d000006503000c1013580166108040d00200020880050b81041244101c020801c80303d04100060104600e001105240c0c42c0c0c0c2e8050b480d003030711006d91303008120503691210788c802d0004040c00045412079481324040d00815641020b1844c0c0030015805507100a80840765130a400106603091103108a8240c2c09014090420f100e40c480c0d464101d01890101c140901c0041e26142c00303d103481ca080310300b000000c08140e40e401d042c01c0c00c0108550494480c080d22014a9503042030403049641d9800121303e0790142c0d00c264680700c1402c0b150103002203c41e00207503005c43d0480010000140e907a407021035000407041d2a0151104076000c000751418803160803109014410744075a46a1403162295242903542502d40c1030300d107071211401c2c413 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 956532320 1250 956531070 956531089
    0x9030b130807020418050106091a0d1a090102090d03081f05010915020f0604050c01090812070311031c060503010c08010503030d0c090e0a02030a05010806070e010e031e0c030c 77
    0x10059441004408094603040d081081d1108018041d0517100d80ba903501c4a0844605a0101c43c0c803503150030f05038550107a910500f042d2007405075458a440c00540c1c0c2c80b80309080307a011904c0c8030b41000714042038510201754180c400c11354004d40704d01040c00702420090550141141c258100d08800810b10f6182d0004200741c0c1d08454041c2c480850f4035040640040d0040d0100c961141148120942c14004501c204032080c02240208003614403080050001814119a6007103080940d01c0b02543d500c0c0d400a01003242c007615054546a900d0542d103100c001d003140b00740b01190071030706030351a0000c0b0f46500b02d60188040300c4c0700710300810244003200000d48011400f48101036060b04103005000c898800350300f00c4e4081207418034024550b41d490351808140008181c4855213a65404401c001d18144184074030b602614030f2070000c180d545041c1d4001031030000707000401d81c100004071840c1d11403503c08100b6584e12400c984440202d4686640c0400d03511604954014828820604c08140d142044181e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 956533570 1250 956532320 956532323
    0xc05241e0a020f071506030501050c040e01140105040e070206150411030406050406090b040303050712060302300a14011104050a0b0901050d0e01090204050f01050622090c09030b13 79
    0x9a0601c0d519242808025048541140d03010502001032600041030342c3c9440001c4254402c00191a509504041e07007101c4c4010107a48180804010500501c08180d10b0581191084542c22212a4a080048500c0d004d02d900c0540507075004000d214440c0c0d0003051261281f640035910707003842c66042e803c10003651050008144208bc040010030003144094200304c2c1d006001d410045140c4803a03039514040c0c0d810803541500081d6480080c03144082d17000d01c626126180d0024184120741c29a00098403480c03030a41c04690b480000301c015282002180003142090901300c090310204d059600340440380c85000d059800c0303994a40400f20f01c24000030b078140d070241c2381c026001c400314a0500b481200076030720030705500b41400018485002d25400d0741c0510441e40403da0000714011066105010944170040e10700f0505040000050001d500c900083c0d850000c02c404110301200342d00500080c50f550950442c161090600d41c0090149401004c88800c9a204202c01071480e81c8000c00040706568000f030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 956534820 1250 956533570 956533621
    0xc0f03061511010e0609031305100503060609040e070b30010b13031704081c02060c09010c0f230a0c0308070822091a0d02100c0524 58
    0x116402014824140b00d100e08070a80d000103900107400080030700d031840490314004c4641c00020324802850303000f031810004080070384d164505603040c030001038031600009240300c1c001d0030041500002c60742e03140c0110403a1401701d01039491103030304c601d810500356000d40440b0700351804031001e07050500311004441d248010f030890003100c0340e400c00402c1c41c8940c1c0550151080c0b61118003002c40442c20310114104405143d0554640e2545007052403424a200014010510006143e5148140c1e401090203544034620401c015a80d80920b0016500d09860344c0c0040d10740701c8a42045010030035202d56405040c421501d1540c0c030b020300f02148690340c80b0603110050820240d040104002042213014201b41c5101d50350aa0030702d803e4030504074007a101003099440b82290000100b1200105d40b0640040700c4a008549140008103800304131111000e80c0004e001307410800500103800e216040a4505170f62080966605074202c00c01004600148002104d03c003c004001c00c02c840364400707582907892100c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 956536070 1250 956534820 956534849
    0x90d0e06120115020a05120a030b0103090510052701090311060405120f2203020a051503041407031707020a0e010312140d020f0403110f0a0b22090c0f0306 68
    0x243c0b886090760301c40d201c01040d48214444207000032001e02084e4003034210700d40950b8440310034040003015a09050f6615041c9460811000b0210b88003003500c00d102c4c020101c02003059110300f980c4180f000000024900040444180c460300d40006403c40004107020b9690407520624800705035894480907540207210758003282042d80780c40c4028010708410344410b4481c500b810414111b6910300001c0248180c413207043e0f17540c24811450140000405044143c2c1c2c920148446c3d0340a40646100c00341000d025040c3c142601c1040203000c0181d5406940c1c841c0d86c031a420102d010b0407503200d802a260480c8240034080c0e0210321003904025181c1229008042050000c042e400184c540c11200c010406540d03204000401030204070f0f00013001022000c681035650b032407640c20610500c40398003200c941701d4030501404021980c2d50346580000d94285402840e9940c10b01d40b043c0e08416240ba00742188003000020000d101d0380542c0c0805d414200940301d07a0760021039604101c04460312400307052100411031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 956537320 1250 956536070 956536079
    0x30d111903090201050d0e032d0423041e0c140a081003050f0a0b0606180105031909080a02060a0c05040603090302070b0d020306030d0e0901030303090f0209090d0e061201 75
    0xc2e000048100c1c01030400a2805250311559000e82c1c0c030313908101c940ba40c0001110401c0c0410300c008030141d1684070705420759031049000103070071501c500d2003040038071501d10389501441c1d90051918401d00800800400040c0c0c4880c034280d01c4640c2c0100320f415600e1414040c2d0b60100c0c02000004c6e05d48103109240c1e0714282d4803090684215002034100c4a00e45192680480002e4080004412030300d540c0000b00584801403034481680240182610f00510007800000708111082212005d00403090a0064403980e070182100c0c048003082c01c40030081801e0103403890034089400020050510231350b098030442d0b039840e5814815240c40002c40b0001943c00c000410129129620044009100c1d03c1a6119247d5a8902114503003110100704000e5a000041c4030b010300e070420140144404a081c000104003a001c0003800c4400c05110150525480301040070400c550415051062a0300814a101038105070035501d54a4030311002407004074400d105081081d142a0382500c50704030b40350f12903180980c09c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 956538570 1250 956537320 956537327
    0x4080c0a020a06020c03010e0f0a02121f0c03060603020307090504150324150602060109020307031d0c01090609050d12020f0a1109070c1e02060c070602030d1119 71
    0x1060064400d0066800305001a40c4805482c00200503950003032000302c0c0214101401c5860350004440c0a0b84024144074140502103040903180c1d0301101c218840e184e8510003141031503c030f450240c0400102c072940c1e0341503400d1075014040054860303804004041d203d100c29403c910041c0c80d03150204096040c104454134184c1c02500f40d803526040b141c0071490340c0760351710044401d80c400a038182001030344882034400f0580c454656004100c6400014141c5000d030302940342d90b41800b804c0d603103640000003c0e100174001e410031044100c01505208900341421002a11202070346940c6001480c0d00c100011101e04c03407428601543d4004007040d443c02c0640d1f81d0306100382c001ca8140b600b540141110b01c600c0700c8041c0030075110240076242c2c0a0041408e0010020140001401002440b5a51040ba00801c208170749110098071507041540d080305550000074068011b9002904580c42801d8011507116404000b504100d4840741c01800070b00b01081700a1000c0c00f40030b00702010001c40e11408c044040c80b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 956539820 1250 956538570 956538577
    0x1e0e011b060213030c0513112712010504030305160210050402190f1815031b0f0602010212010b0702010c0206031015091707050306010b0f120106020a21080408 70
    0x810740300140361044030010603106100580c03054980b5001104100b100c1d052401501c0401d0800000403c26480e1910346030b00540151240c000c262814a950b500d2078042040040000d01801000440c107802204200d5000c0c00382128111700290814020a103030412061602038000199000b820813a101580284001d08000340203983c81102c00c0a035041c4d1211035102c4a010380316130f91010304401d08000c1015500344240f202500e8091504034110b0f001074031425100c0030769921060007000034407422034000303050529420480f0501c4c0015000070305990158000c10308008400c1070030003542eaa0f080d4842c1180108400a03005c50940e01c1031500500c1d2031401140d03c511900304419100b0303150103942c9a01c0080d00ca6610114441d104148011010482410b1055042c84001c00340b1500702004079880310018441c80c21180b5001c55008014030340c60080d03070013158007401840c12960b507840e802940c0b400c50003002d0360341c036401681e5002011400d191034210260142c40d2018540c480c0c0d901d000a030390 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 956541070 1250 956539820 956539823
    0x9060619030f02030a022d0304020934020118080414010908010609021e03100312020a0813030308010e150f0d06150f0803070c0e070215071e0e011b 65
    0x5989030a881004040b5102641c00703050081c40060311885001241c1f4204d898104c40030000740c001404030001c2061480807240e0103581516620344644032104104a1400d40142d0307a9604007030301d10209040781c8240c40074909112141c1c003e006071310714150b10000444602c035000c0c1c03040004101c244070103492040c0844007284107142ca00004c0d6030301c1c0116030858000f038001000f6680c002400e40214001c50015585440d03c010100d4550b0901c40590712600070b1500c401040c0b02d400d0011408680e00a01400030215006003007160b90703608603003180003e05914041200400c114200102d0234104203e40c1d030380f003920030180300b40d42d030091041000080310043d100d20313a200c00600c07020310004001e0302807500300c000008c12811204c0c0c03d210010010034001c0e003082c0c1450f402440107801003601c980d20302e02250204507d40c002a141c0c0345040342010041c03c1c06070303080103810081c000c0d0740742c0c011604000504480b004003062040b00d01b00301c0350520b00c0c880050004200c65009a2118040da42d54601903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 956542320 1250 956541070 956541077
    0xd1202070b0c012412110103060b040e0a050a0c020703110a0b040806090c060c0a11040908040b0418060312050318010507091e050603071409040f0902010e09060619 72
    0x3107680e002110001c1e4000c400d0040a651240000c590326040311940202e9000544600c00c0c07514107203000c0f403002aa0a0b070000d01448812000340744140d0096110714003806690030aa950f0b15180c29503011403910541d25454810b01c0c010008034030501c24416140c080e0301d00e0317014286d490320f180c903845203a207103a81000383c1c0400b25510004124580c0c030024801454240c0242c8418507207604810300304040300318001e010328020400107109c060046043c81d0320660103800c5640b0721100101180041405100085c41e1840024000c02e0342c0613500017a06c21500d141c24400002403030030b0304c0f14060307a403544030007801c003502d00c10280003040c0507501850303010140d010940c184026001059003900c00550300513010605404051000f2010001071a04815803008022803043c504004140144001443e203401c1100c2c081102c0303c2d0f01c40034000c40b81c8000000b0400e100f0044400441802080c03607010880c085150811032560508040007100e00c5a0b80043c2090306004885c03c0c1112035090f02900e00040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 956543570 1250 956542320 956542333
    0x30c0a0b030403052206020c030d2c0d0609151a0d030302092d010c11040c0c151406040b0a0303141e040306052518030f03110c010e0d1202 61
    0x50b148000d1170409000c2c440034070754115468010040d06000c0114443c41c000d4000c0d01d5440d01c90f941003095103002e4105448591003c046070055001d03444404514958884c0d007444442c0e0601200d9000510f01c1da003e0030740040303420a500651070031101e41581040c4203102429400c1c3c040e00d8686031191a845c02400c0261600b82070000140b0149500400c01281031032015103543d05401030300c1c140d01c1da484213081c0a200ba00c40d5032928205e01603040c400310703c00d688130f020402d0380e1132084200c0300050354001000800013800701030090103400c001c2200a8425407200c00902d6601d4a4011001c1d8920064600d259050440d24103c03920300325882c02042c0f140c4100280d03402201141e0401d000c1c44a4801806d8603103055190540c195074014102020b031104240c80070740761810100341c40c00d0040450500864070131401a641043c40032035071010b0034026400c0700001c00d26030081c91194184080c641a44c5032a101500151610120a8142500410704440d80c0c0c1c0041c40a074400340c1501041e0049681 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 956544820 1250 956543570 956543587
    0xf031c0f09060e011401080307020303031f0e0a0c02060601090b03061504150503010503100204050306010b030910060b090301060527060402070c120c06030504080306061b07090c0e030c0a0b03040305 87
    0x7580c124080f426256950794400003089803a036a000c034050705102014628002c482c0c0c0000340d0340d00016011806400c0d072520b59213204000d60b00118002c03d690755030000c16180c0191844010304178580848094056800001c46c030b58841c1030141c0c161400c50b10000e0940d11010240803044240e14600070031048100310208448400390140c1101e48515503440350b071b0350304080906041408140c6120b290a0041c0003e010301c2d6808111a81510702c420549501c03030380d8000010f0300e0044861b035150710440c41c200d40070446080b18030043c80e4680040d0000c1c02901e0740c5405002684401c030503072004006030740100c5481e0b00d07104c100030b94100000410150800342940c0300c0e194440110f910030b0421601950f0008200304000c80300800408041c01e0420851410703031203031840d82c03000400c0703548501000140640141e81c1460340d11060491314003140d80c10f03516445041c00900172458403001280300c0340c80c0200302c0e05d00025000d150420290007404071600d800620705240e00090411005d0180c1445543d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 956546070 1250 956544820 956544833
    0x30115140f09031605031c030f09031116140103021803060a060501080f071b021f050a090b0c0318060c0303070e0a231e120604050f031c0f09 62
    0x1001c101112000c1d907440800c00200352038a40015101001d05078035030010450b44d64046094050201c040c4c552003001159401d044004101000070003178035925001e48501403541c000f071321900076228a000c948505600e032000c0c2c440c00b28184136881d0032201c012248001d55100e40c000d85a4080d0160382c4101d41d00c0c040000074104001100c000142d140e070b401d01001a50380c0003041d250024428122850303d410600c100410304100c403d138210350b0380200850f40045494074500590540151050880000c030182c5e03000b415540990701e01000220b089601060648a4808940c2d24081c8100218904454a00030164000c9403003600e81c0d01c00024481d0f47c1d80f00d1024030003076200341c10a0b0b5501d03002306440020455151303010740000c218014070a000090a04111751808180075044400c0008002c0340c5c14501c1d480f4084000301508140035000e0300700d042d00b00060941c000c034440e1082d156042e101060a41d603e008424601000000d12040c50b140d40086500413000d4914401011a0b0b4034a03940302d58 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 956547320 1250 956546070 956546077
    0x51216080a050921090a1d07140f0714010e010506030d0509010e1002030c0f0123070f0309020625060c14030c07030921020f0a05010903151b02030408190803011514 72
    0x802d240d01400d03200ca40e007001905c0c046d4450100d0178100690a8061200840ca02880c484d50652503000034641092100e099054008030cd803120003841600c0c0900903160203000150703407650103403295404c33000005028400b0313140c0301c0d881a0356003003481d0015000c00c2400c02c00310381000c1c150301040085890000e030501c01d40c2c03048101540040742d02598001c04501c01180f0001308604c1c0c1c0f00660500c2082c90b4000b032445150340c85840c003c21110b0443c0000351845c032424503a003044c03c2c082074420000c0c40160b0040e07803485003e242c0802481101000c01d0355400424021141418410400240901c40c8000a00303c100e010f444c000300b1003510341d040301d81c070142d001c0c0c4034501d1031010303882c150700b1807400070140041c10344107469010f0154070b13000005e0000380c110301004217810440954915007c0350b961101d40601c40383c0d03e40d00d501c2e6200220103502e81d8400d000300c8a0783d008240701c1003100708180c108000034a0b480010f00386142c1c03815100c13061011040c41c0b05010004448240005c6081713080c0034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 956548570 1250 956547320 956547329
    0x103030c050c1816030f0f0b0a0e060906012d361403010b030a03050301031e05062202150d0b0a120b0403051216080a050921090a 57
    0x4030011510241000d5150011110007030b0b115500d1a600f54001d100e50903640c5411102203d00c0d0404040c0c041030580c06070501c0c044030514689400c001045d092095040001c80c400199001c03030344a620340d490740e24508422524070f6002001400031810951044280301e1945134010110009454003070142030600958030603ea0020350b40c12003000e014140c4400b045045030502100c01c0d5949550003107240604805d03c03503000d440c7e40b00100031502c3d807002e4000c174142c07020003419904c1c002c40138540036189800a00065a82149407060680c1c28042030b590700c4551a00100282055501d01d9616980d100280610206644031104841c0042c4c8038501c0c80002e50101c0c201440c3c40b4240520000100e80160385140e00c16031505c03508001c01d4800640300d03850305401400d018074940e11410203882c248903400240070720301140c9081000204074841c200010820f1550381c0a000d0300e880ca00f45045ea90240e44100ba503400084002030340c030340c0f25422aa000828204d12030308010240e00002d0514106510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 956549820 1250 956548570 956548577
    0x52d03061522090506040c090b0d020c03161b08030f0f0702030609010506040516050415020102040e160815091501110d020a0605071112030c040b0d0b010f0306050310091a010303 78
    0x4043c0181c01450045030340c003403000e0f03404021031060f00703a001b45030301000c2c8245403007400e0015480358201d217950105d81d4410803c0f800c0325070f6020684d281403070700100302505548004012503c05c40914958000001b240d0300e450046040c441002602c50166000c040e142024050800903480141c400740031251180809000000e0700b0300d058018007040e00d5000344514810300b040c2c13a00e0041190083e0554041e01c02070554000600d0200f002030380280324070341000d0500301c240c500308010000d0b0f64030322802d00112583d401685464401c2c11400005109016a40c001d1280000072241c8080c42044948903105140c98070280461404090401c3c00c2d01c0035103801600421b0100d0f0074007440740a01ea81055483c581405015040d00c1184c0d2900c03070900030401c11090000104915078002400d03075015081e000c0143d9660503540860b40c0040070406495804280009000c0b203207140203110380d40c22200e001c3d01a00030f17551046018002040c03407481c21a0704000c541c03440709080d5583e002d0300380658402d84 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 956551070 1250 956549820 956549887
    0x3031b1b0c1f0c0602030c04030519140606010903030c03021005181204050312160803070302030405010f150b0c120c030307121505010c020303120403052d030615 71
    0x2002d004244089030729550045031180d4a1248007980a480c1c0000395404c0003005031240c03128103c910840c481d680c0040c02d070388600390755207440303030107803c41c00300007074450590445544825175030aa00d0300401c032403841c04070b60248800c1010038002c840342d84456103c3e1041c0ca122810100110003100d48c141c03059646101c0d03002240c141c0c400308002294520380300710031580c02c107480c090000380d44601c4003001000e050300114071403e22040324600781a1482d031003107000380c4918040d00c00800035003017282e003074401d5070130140d015205010034400e804042a120108030302c00c0d4100744090a90344d009913043c4a861090320040b040d45043c00b0081c111303880c00a405150380f403c001c0401040038001c4072109070002c0c5010100c4056040540c1c001d0203c036420300340989182001e00019081d4000c0518048144055000704410140c2c0440142140520103c0e581481c03502094a840900f0004039001080f62042021400b1450001004448074076405c0e40b040c542220182c2040c4400c000958a01c055078800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 956552320 1250 956551070 956551093
    0x2010c050709020c0c030a230a060c020a03030f0b01020c09150a0b121621060305060a050405070f03051f0e0d090e06120604032d1d06040803031b1b 65
    0x28000074040202c12001403c02100c0b80c0c65025802502c00e004020603200f4034074081d23039050300b40410244c4540103001004101425075010b51920b8190800b200003900d04103410304108078901c02d01d2640103041e401840078200794020703c000032134050900030030340b10000107003c00d9555500041c0050550701032034540710182601c000369118009031038040c100c034044084541103030f4003c0c8401c48200c0801e05c0d08a044080c0c0f40e80d0030082c02d4503040a4550b00920040100819503904040c0c043d0748220120342c2c00341e9652500002d003100034040240540c001158030280c0d400400e4102c052105082800600d8240e003410080c40c02103c0391603c4085100a00100103c3c0340d400340140e48410305a5240c842d8281800c115500e4000c0184000c0c1841419017081f10181c800242041e00c0b80443ca08007003034003174001800b070802c801203000e00e64a0500307804a4039190a0403405e0328200e501c040c00271402e41d26041c8a0030a85030f1003580e41e01c6014014400c00700328640451070f5403941410b4a0143c28000d019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 956553570 1250 956552320 956552323
    0x1e0c0c07061e090b030a0b06040902030103110a140d0201180b130e010603090c05010804170408010e120c0d1407021503070809011401050d020111060108030a1e091202010c050709020c 80
    0xb0803400000d1050340034080000e2010303101181e0307000c0c09001c0000f81e02414140050300501558101603070040c800300000c42040340c194201c0c0d112080840303010000e1075a41003e804c04074100080d01d500302c00b800014000550290f0380e080407010b05404004a465100d0003998142e4004e03440401c4050401c44042044200c3e0401d4140034100c945418400200b0325110280d070401c40d48555410405020001000d0182125824020500c211007072a030303e66848500c02e004e041a0780705030a060207848003154924801c0011260580c01480c040c08181c2c10481c802c0d6610b0a40000002c4a100b04110000040c1e5818550000c4400c50044854903400c0410300148210401403007030209078134000b481c09000850788000d80c1125400c03540008121032600c0104d82ca08564081e0807100e00c2208008150004080064540b100d466076a41d0200d443c0c425081c54400801517900011030b801a0041c03214031010b2070107148142c018140002640625607420345031044640c40014078650216820010860 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 956554820 1250 956553570 956553617
    0x200a0302010b1e0a06081e090d0e0117150111060c041410091415180f010801031104020a030e0a0308010305061003350a090509010e1e0c0c0706 63
    0x3040c2c0f98415103078509002c518850803d0240c0800d00c101c080000b031510082490071641d83c01c1c002c0b0500d9007414810b170055600c06101c0380b40000318000c1910340245520031003108400107044401d82a090302c0b2495207007518811030340a02c0c10098070190555000004000300c0d400f410703005001310758484c41c003e6481c40c030317502d00705065101d0304500701c0c001d141343e510024490a486050300710789a101c0d203001c001000040b0324103036200440004101012158180740c500c1104001c261010a421500d8100458240100340001040c1101c0310110171100c0c00e10354090a07403403205040c0080e000340a1f40082d80f034400c0e400d404800060f0420018010048140100b94200110081151030181190b507203c1c80702c035120381c1c1c0644095464a0000d5001420790312962242c0c038000250b035a0300c41001c002850b84910f4000c541c0500d02040001601d010720b0480f81e482800b100d0b880f50340f5052140d40074103e002018181198190f41400354080000040c04040010320061b00ca03180c00300f900b100894012407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 956556070 1250 956554820 956554849
    0x11040f0504020303072a0603020304120e03150c2503030c02011a040b030709052e0302060a0e130203010b0706140915180d0804020f090108030a200a0302010b 69
    0x6080c0401c0c4001600c002040d42c0ca01640b00001c0c0d02e07010440b820310070f098032202000050a204590000414582540c0103600840c01152800c5c1c0b03860440b0820f440c0400302d40760b0302d40c01d0b500483c0059014610354132001d80092000e64003502c0c0c004d001c81c0d00b822100b061001680300b00d452502d40c80406030507104941691603140000d02005d5a04481010400303422400240116100c5140c401c06507424032401c4090144d00c4410401d5040c5000300d540c1680c140800011814160080e003424581d124103600c0c00c895006000e903103040d05500044409507403424036190400d0716416070907041c8810340069070180c90450318103a2188020b0400d4010346011040000010014605002400902040c00124074040600e4106a501c0c2d5442e20710a0b060107100c0c11046008070349008584035407054000f400b03140215400700c0c200c1108400c1081c1c0801c20320518060368410417034400814041c1104941800b54500442c2284210043d01401c1244840d01100182d5482c080c0b40740c24a03000a4542b25503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 956557320 1250 956556070 956556101
    0x319030f0509070e010902070503090d0c060f020c0607031b12030b040c05040f06140708040e0f1e06011b020409060207021503071d0409021e0a060509010e120106050a031104 76
    0xc44c64203000c000048010f00814406139000100d1605000f002c10441d111400081c003510388100f02800c0000c0301034100d01074100040d510640c1085a684009500300325150010b111a280c4802c5a4080da0310210b6a0308035911a140c0c9010540071503006240d1181d04c51490310041141340d022410003085078400340040c002c0c06018481800380047c1c0c6d040c01c405460403414011011001076424004501500a000305800380000c1d010411511194010780030b651a402540e1264840040d0fa0300190036a403141d01c0041d0880001800c00e61003403001e01308151045011082400d0035401144c00d40302c09000a640c610740004540b01181808070713007820f49072030036002c2d5415401c201c1030003444000709150a01180c04251060385695031164000210f080d4010540380d0000b88810f01903007628000d01d102e41c40b40191510004550707000d41c0880e2a8990160f40c1d10001138851810050814420300d0882c1d00341d962a400803480303440d41e00c00d24001e14082d985c0148407584c2e1348108800d0704e001351504e1428 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 956558570 1250 956557320 956557333
    0x3030702061006022107020402040e01091a040e1009031e021b0d050a060903030f0204032306091905030408010c08090f150109051b0f090123040b0c0319030f0509 71
    0x5000003040014110710b55402c1c1e0743c0c6e92000e5000040180c01340390006503282c4104e000000703480c06a03502c0341281c0319550804940b0500d0000400c001c030345400110320311a802c84951841b0340401d0798840d80341ca0b4402e0805e5204840c0d8420a15480c41d000030540340941e001c0e210321a039a0321411282c22680c074003140d108892100c00e9507126168005104001c00c5140c6650482c010907000303030402d12401900312402c5441c0c95a0382080d42c02220707013160b036003100070b070000c0c07016030304403011410078418611a8000c21400800800784c984040c4e080304103a80500081c000401c1e200790a014001040c1c0c0305546140300c0c3c1c2040380001e424035004840e8181c56a02c01c10041d030042e502d49440034111402c3d681c0004081c3c0c1e500b4007503915240c111103075292110001036140401c0d50401c002c1d2200101c00c1c0e1328a0312010041030310706114101c40320b480580010500040040070b200000410b03040b0300c01c4044ea070600008005543d4161000e0402501103a251080286403c1e11880740b01e0384140c243c0e000700303039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 956559820 1250 956558570 956558593
    0xf0f030423012f0a0305030726060f0409050708010912030c0e0112020702040603080d0f2a050c07030b0402090901021612020a080d050405010e0a050606010e120303070206100602 78
    0x1a142508842160242c3c0070129041c02002420001180240704242e03045074100385002025035100700c41102c0880d21131901c4212941842120310b1400150080720001d6407200010000c414100848103940580c03502031520010f001401084002c0040c0d1001064001d42c51401001da1040903c0c440109454030080c001815802807148060b00001e08141003800c40740c89002002c2d07c681c10000c0d40050800c0e20000410008100504a03041c0005042124030071000c0210300703507004010b080c1c10001c1c01c18440c02001c8210341c8285042c40081c14203030302e0160301e17803004d03401d15401382c0c000d64490000c00100010350400d1314200c2d602c01c99443c001c40c038203c44019141b25600003520042c1002045090f03a4182900070030048041c560080c42698407407182c8650000500401c5404499035401c1005d0705004040c00510581c406920034007030a05a9200d400469101c83ea183c40260f02418800d044c0f8103040040c80198041d5403660701030443c43c5082030180080981c40d034489021035000704440d42c1d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 956561070 1250 956559820 956559827
    0x61309090c21020f0a0519090509011509020a0c0b0a060302040b0f3f060a110a0903060203060a030804030b0f0106110705060d0b10090306110405010903140f0f03042301 74
    0x2e60690704442c181e58035004034000c00c18240704da8000c0c5810000b00b040d00a02c1c41e04810b80002140c5002c0c9050041b9510702c8245400c0e28490000742042880540c000d1003c008039801404806803546803c80c007058003611210030281064400b42c034025513074801402942810701400c3c2e039491040d40c415181440441c0401e804d070402452241481481890b100801c1007403480100c44800071500440e2500c01c401c41036a211030f029502005514a01200d1615a0038008180c03000c086980d00c0340c3e03152600d9604c0300c00180d4030060200d0745c04450303403101000180c3d45002401c040c1d8051888410315142924204449140c107800020a004c1d01c140d4107501e0180004c0c000c4242d40003075030080c0d19500d40c1d0b5070340c0b00600b03c0f800c0340c1d0307600c10b01e0000080c04613031303200302076104407070041d0001e01000f038a045415840c3d104a009031030000702c45620500c0810050b088420342c050300042100c140751000086182803000c00b03800c0d40c0040d00005001c1003003080107100910b10740c185101d000706c0c81003044000b9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 956562320 1250 956561070 956561129
    0x71e1d0109180501050907080606090c0406050f0408030403080a1101150b0c0708071415120a0b060c010c030b041103241f020303010905010806060f0f061309090c 71
    0x9108541c2c840d5041004040d100c440d10500942c048000d04c501c0c01c080c80c040c1e4940809024041043c415132000801d6071810a040d980a144101c06251401d030078840107c401d80d0200305c141c0001401008001240102000103000460052948a0b280c00c50004002c0410350303441100c0303005a04001d1164000005030110f0005c8034200d0401980e03e020f81d0101a060108984c0150000d000d410000140c584a04401041e0000100d0b02801901848564960240a4800c2051401d00507400203019114030b60700c6a154051f0080070303e418240e003c100d46003134030007041100001945450f10030340d450904c0d0140c5901d025800c040c070b40c10351600d0705400d1082c81c6460340345450102040d00303060f02d540724070a85c440c0e80c104100306407400503500f4001a640b98001e2182010040c0740100000f1081800301c0c1d49070040c6001000000301145003000c100d07004001c2c50825611880402c1011001d00386002c00c00d000b00b042400103c8c03500801d081c0700b03620f8000c07548081c030440510840e141c1a01c0d03624284 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 956563570 1250 956562320 956562329
    0x1090c030e0102030a0605100c0314070c03061d070801022d07121d0a0302010e0108090118210207051c030201020702090a02130f0f18020903071e1d01 66
    0x14242841450032400340c140480203140a520004c00d10099000a030020b40c1583d42c20f840440310242c15920441e10111003101c06000200e04c1321030050070f0441800102003041c01058410031a0380c80340c603030704129010f03d811580c440c00c07080401c80308245d0070704c212001400510005c50804804081e20480800100701b408130300076441d4034405500ba064401d403400d241d00036024041d007500c1040b02500304421040d1000c001a401c000041d550f02d0601820000c0c1c0340c0c1a07543c00d0003c00700800544082d1806010102d80d9502d85012420100107452a05903003030048404030058400101e1800091404c3c4154100310340000c0c10900c4940c0300d003450780064480c1a509e03883d02c00e016007000c0f0300900846400a51000d1540e080c1300d48081103130080c211030900d400c1041e202c25a1116084680301403482124039a181ca40410081c50000c40300c3d06440354a0a0805454505040e002a050450f542c02c882c0c840b0b400e640d0f00a40d4483d070701d801840030b0401d807440001c1000e0558003418003a1030500c035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 956564820 1250 956563570 956563589
    0x7050301270905060f07230412030905150912030a0c08071b27060324180f150b0604170a0b0103080406171e10150302181801 55
    0x350104221980411100381d0004141ca084e4104140031150000b0150313000400115202e0340c1c2100c0a8420b02d03000c130218030004c0c003d40703450325005013802003d01a01c030540600900c0c3d00001391a0701c0d05d04902c03213a603008500c80e603600c180040802110507040d0728007850325031050082c1d1005070b80280341424526000b42105458203910300d440f0440d8840d01c45040640ba070302000018800a00040000340070441c1074284042c0b0b4002c083e00d2007220110f1001420240d07030010a0350100310090004181d03a00c0c00b03100414030030007105400050a880c048201d801d03c0321802200c040c842c103202e1002c440c041c504001e20805417980c0004603680030314010055881d8250441460020040050180056000520459541e500c2c01c05408641203481503101040c02c0060307070000c1d042a1361038540b14014440a90790f003203440d240e50168040e4020309102e4015031240e8085107905941d11240c0d6020700760790740560f40f0004445041c0c800350b010b488090155180002c00d8504c02d10741000e0b507041d109440e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 956566070 1250 956564820 956564879
    0x20901030212030c030406080a0c0305040f06150302041d0606091e0a0209130b0109051c1709130c1e050a031a1003050109050f0606041a09120a020907050301 69
    0x182c09055200389580302e12a4407001400107001500300030310510940f103104042204400004c810380a40d582200c00030550510101c0c00382c0000c500394800d042c0f0300440304516555585039400301e0129114070007401c112a6141c20b2007074506808028059000d141542ca00070542001c48010340074240c0d00750310b00000100803000605151407981a18a0540000e003e02c100d1440c59818000615060003c1400102564800b061a00317003a11041c0c0c500d243c05005582d405010b4540c401002c2c09120291a4800108815001682c401244402c480c81c013180008440c1e000c0b0002030249002002804281c21514424803011600a819a25159000d080c081000c520b408610012f01a1085260b64440700c20000020f000ea8568044d505852440b581023026458960f8030070f010700012030b8142d40c0404204024481030340240600c008461107028040e007441c4c140c81c00141407003400750900d0226809190030740190701d0803101c419000400d60030158a1541410042501000030301b240011305081003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 956567320 1250 956566070 956566099
    0x40b031f20070209010e0108070b070507050307030317240f03010b0324060d0203030f0f04030c0b03090c010f120c0c0512040f0914070309030e1801090c03090209010302 74
    0x1604022440444500e0203050700c000980c55200315000144280c2c058600480003280c104141d01d6820b05941d4202c008100342898910045050ba116070700807101801503100000d00390302c0400603100a5440784d19040306031919099100d40302c1400400c207006075144010041d107680d285880450002d101039503400e07060000003000ca400350400502864040c85205015090010800c0c502c03420380e061310707ca0070010f8aa610400c1484600c0b120701a6058000b00280c01036640380303c004120901000c4d54140c10a6525240c24000c034580f41d0044000700d000000300411403c1c1071110404012090a00d180f07402440d4400402c00e0410380750104120b0790702d01505c030146024441010450340e000d0102c41c0c4820501061200640103480790710f00480200c2c20108914000b40240308907960042c80918030b5a41d190b070220080c002500043d0203008240d084000745890700e100503048814460122000ea51600014034200e892801c502c0302018070b040030400050340e03001c0c00581143c1d0111401558018070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 956568570 1250 956567320 956567383
    0x150203060f030a14010608071503240303030c0e06070b04260d0b01020706020f060f0601051b07181401031403130e0103121e031d010e0304050906040b03 67
    0x16024050b03810f1044030400c42c10081c2e101c6000c607072890100700074812984d607801286c0c5d54050340d0282c04c035007030303441c10000750707582e200307030710000c20802880611801d80c000b0b0399044c80002610340042d000240c54114124000b9004681160346000503074205180c001c0e10b48414201c0b84010f84010500840361030f01c110b602e41000702545034036400c0741d400c5a03030790081603044000741080118240540a107400c00a004d070b00114800400b0503508015184543d14174254100303a6800400341414480140f00c0080700603408500400c900f20030400401d43c3d2030915445c685205d200d050200034040c1800031010424182c4070318141103c0e0f10040d00712901401811850071806800c82204114407105400601c0c1e015800056040340c0c000c0181282d168045d12048824140b01c0d95407007030104c001d8148400c102d103c1d500107905089034080e040b02420720312000909581c0c15000c02102c03980080740034001890000c0c5a00c0e0001c0c1c00b11400c001e4890440b02003a2210940742c0e44000402100c190001d80e1290b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 956569820 1250 956568570 956568589
    0x120c050c0304180525110114070809011104180504020307031a01060e09060a140307050a152d08100b031006020d111e0709020d06080f0a15020306 64
    0x903840107580c0c40300e89aa00d624002d08061003c05040f506220100e011001c26040c0004203100400b01072000c0840c00000351844180d54407115107035944e81289a40c1640b118805070b002d048599101d0300f5905209089034250380450403a00300303108081204204c010021f0641c24000c0340b24031b5011035590707182c1c00040d0401c8880d500c00f401101000900790340c000300342d6040c581031707400c0394688541c0200104c1c1802442902100c102d0f40144520900703001441c4241c41040440324014100d888040e10303940414901a0300d903202c080c00300503048020001c07075000f81842e60301d40740070074840c0340c410b48410728040302040c145546014020950042400c108140003000060709401010300c1c0e0b00d00741005680360000e0382e442000300601440c209650700510036508008083c00f004002c20384180e0308805440440540d203170840545c07160480010703520303000d4001703042e5000140a001400714604400c00d41014a40d4126072040d802840e050b10001d01d0184150310925500600140c50790754a42c0800c20015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 956571070 1250 956569820 956569837
    0x5032d1f14010f090b04030807021002010614062b1a0d0c0312090f0807150503040b07051b07080604050d05280c020319060f0c0206010515070f030504080616120c05 72
    0x41c0c1c0040c010041c4548003002707080e0a032090380d910100012000c2d049080310b00324040c09080250b40c00680b60b040c074003007000d001c00e084162407140138120361512500c9140c54004442440e19110491400d100034400d60b5030606010503030742e80b02030044a41d202c181d440494080140360643d81c003006030340c0d54403440a5002400f0046404200786403036903030b07807540c1c0c00e054800d01a401c0240700b8124200d03840781d130541f801240e100d4400015521040c0c0c0603100c6400c0b80c6500d01c0b160003525040c0c51030350000c03c4814020100b00000d0003407402d2030b0520304e007071001e2055420103100080008001007e51b02484038051914a84100150000c46c3c4003160042520503001e94117202d000880011500541881b5031040e12640e420005042042c01400945102240741c0307004d40c00030001044981040c3c807049034062480900141741c07004c281d450000712040f049040e400100c010030140180c440420146402804c2210886a006403402005120480c0c020034500071581f03e005905229015100b52407251 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 956572320 1250 956571070 956571089
    0x21130803010609030512040524091c060b03030c0a03030504110a140f03010b0f211207031418102d1d030a020105032d1f14010f09 57
    0x356502c107402011000d260100b9100c0c0c0c011690703003000c241e0030a0112012510f0140c80402c00192030b042c490900418840c440b603885c4020070001501e60366084003000520004400d4150b40c00b404d0070080201d80c8100c0c0424025481000071072100100020259120782c0d25140c0480c46558916009540090104100c0c0d0407400d141e02c08030f10100e001c4101d05110800f40d03814a00e0301c00b5401018213070340d40f0001c0540c1040301c501000035203042403501510300a59070494030305046500707035100d0700d02000807010080d4a0008900d100405502242054001c04198003040c01c0a49451030b2032716201001c42003501c01e05102e00c010050b00d00560540801003140600c000c61001c40e0712010060004040748440003422003404c0c440c552150148422850784050000c00c02a07030340b580151500d51014100c480542c00359050b000340704400340040d0300b800640101d40c100d5410003400c07035460840950200017040112001c140054400001d10b0040d040c02486e1403000304c07103d10310558958009d500f0801c200d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 956573570 1250 956572320 956572327
    0x212a0b03042010080c0f0f0d0203040b0a1401060c150e0706020c01020115051c061a010813021e1801030c060f020d090605090103060e1911211308 64
    0x9008041918240c468014421401002e0011041114400d8400e20000100b191003020680c1101d03850045e24503001c0561000303113400c050050900039a0010101001100d0300081013108000c40e80c02c119070403151603e403d0007003122345520f051a802e0140205070030800c10004040502020924040c21884070100030003403400c4d90040c0641786c0101e4001c00025204d288040081c55205200c2d40c807505101105000455050000700102404070320a500c8414203034410a40104105208440140051210780f402c4520070070009410240c00030240c40d0f0707910700b03081c001c2d0160b25070354003424044170020310b2000a242c40b00d002510030540c4059070302d40b0301180360001c01040710b501148070035600c1c1a151041c3c84040510100d940b000c164501340b0000c0d03903003141040050702031406010b100405041c080b0b0341680b0380c0c14002e4044402c0b9241038410b465040440e407804401e1140e030070818624000e940c60000140001030701900c0342036801c55404206000510650307405520800203503031290f00d0694 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 956574820 1250 956573570 956573573
    0x6050d0f141f0b060408061806010501111b040e031803100203130b1e0a020918130f02030a0c1214071a1e0a0207212a0b0304 55
    0x322002038280494540010600360540036200040303070342080c0905a002d03407900d505010003001801820283d590800c03401c2c04041002402844840e00c604444040005542d02c0040614038240341030340f10700e05008150520808810010130031460015009140e58007007003001000ca0002d001200c07100c61140000b20702041480c0c6100c00c10000728408800b11020600b0a06034070341244001c0d5094114940019030717507400100c4461280742d100140c070206008102d07601100840c6214102c0721008010340c005454100e901d81241558280d0b28800c404030000e14021482c1d00713000d10541009000f6295108007d400c41d6410480251203ea00c072a4540802d940c0340c40c2c3e10340c0e0400132401200d002445034507010b402d101c0010181c0480c0c8880600ba8101ea0280f00482040d500c09030340d03122a0700030000304c4888030b030340000100040b42c115801855070516040d8041c24858003207070501d40081040e06e0f0343d004074400e11500c2a10002814000074607074000d4109041107140c56124180d1070360044100310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 956576070 1250 956574820 956574833
    0x70b0c1314030a021909200a0c060e0a0605011e030503271201020a09080a051506010e03010e061906450605040b030a122a08211306050a06050d 63
    0x1c201c1b0007650b028070200f41d1100301c140c0c041c154084c107000301e10010301c00e031603885200e285a91100ca00070040040c440405030606030811b00c021006031501e41c0c4403001081410341c6040c229200b02e098416120500307086550b4552039101d1500d9402c1c03e804480303000c181656440c1e604025040c1300070101880948640c8582d8042d4200c85504400705228402c00034200d2000311713251050703a91200207032076107428684180c0700d100c501401d42810408081e01031880b03a1401d05c6880c0d2880e51101c014446031510158103c0b101402901454900c0d040440c10404401d050608118040b110070039508070302c1002d5044c40030503100e980100c24083c802103080314200842e9009a06503242030301c091003902103000c00d15135181c01c464002020000110740104400703108040d2000022100d0701910300007403003100c0d040d841000030300307080d0f548a13000150107100380f0990000740e0f800c44000d50140c5942c07612004000d082400314901404440d1500700107104009141c0c42940030b0b110040802c0240045030400c1c9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 956577320 1250 956576070 956576119
    0x1406040f0905180a03050a1812140d030903171315051b0705100b0301020906220501020d02060a0c0302040e0c0c010606020610051e06070503070b0c1314030a02 70
    0x10000b00c040382d102082c103d030004c91510540c9401d41c0304d480ca800d040680c01c50b200800351b0501d0320705000c1c0840c041200c0440c1001e0b8403445003d0150265003a144075002824900180030140074145003030422000260000703d603034200c1042042c1c5947d030b0341d100f0303204030a81c090704003000f000c49c80380b030440300e5035030100c0c1c0c3c425401010081308458091880028901c55840781c480003a1035907118460b022030204040d040174890200160000d800c1c001000003140fa1600800c1401550b802001740450b001c03400f031440e960080c0340c248000e0070018801c4034003a4403000d0140905001ca610380c044911807034040e404840040507054010360349464124100c070300c0c980000380c14552030b5080200020764a0710000c0e10f14012103840c0b0741000060300d08000c010827400c80c25040c3c40720702807984402c09151307625030192038078501500145d5510b901034503100380014401080c152020405100015a8a002c1a01c034026206040c0125094042d4100000d14107581351600a40c411440c0c51400150303a010001d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 956578570 1250 956577320 956577331
    0x5061303020d0903150e0c0901090c120c0f0f111c020d03050c1c06080318100c08090d0228081515010503040c03061109150309071406040f0905 63
    0x7601c220b141181c10458044007248405071a458028001400b464030942c408801183c071081100c0c0d041c8225008903005680903070111011700e036610724060305c0e26008600c440c610a4103010403c0007114101c3d0203000c05450040e10820864080348585001d1301858481603d24420800c031480d8081e00340b00c0310078110381c44a05000602907200d00300307140d6000380526401003000c040b00700d081400c02e1004140340785100c00f0344680640c0b03901002610801c00d00003858040100d80c050f084104416080c4220f012000302c1c040100107046980c6400b140380703201a22000c0d581195000c000b0103040c000180b580350b00300c2000141c078029545c0d41c040c001142022000703c81c40325003a10003410115001003441401200d0782240d0504126031500c00d984136034003c40d401449800e010420648076210b00003114a090311142d01e48400007407400040c904441821003564140d8200b030310f11329043c01842c1d1a90420303c240035400000700d0244082c2c3e5242019100a0020280102d0031180e0f03900c06140034240036543c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 956579820 1250 956578570 956578573
    0x4030f02040f02090102120a031d060403020c090408030402060904020408030d0c1b02030c06030406060b041e0530011d06060f190b090621090d0302190c050a0506130302 74
    0x9854001c0180f07000352114041e050f00075248009a0441641581d408518100201a52820040740c00e280c0745180e05031840e0680010b240d145028a4041e01c0d010002d60072601c43c041d48010800002d00e000b0803079600c02e506907055a1100406004680a0301854001080c58040402c0d414441d01c810350100c2c41444180d554940100f5a42d003030305226040001d8041d4040d000b036025600b003130030100011600b041c82124001241d80d541e112290300f5401540011000307652101e941c40c45031450b28800c6024103405c03154040403848034042c11555130102c2c038036294000305d00218900740700000e511040490b0600c610780403420f1032855020780c442c102115000e2080302440181000b500784414075044004c00041d40b03280ca0760405200710825040558100c1d0300100411045450909641c55603d8045040343c25000d20309100c49030302c0c103108c0d4562021082500c1841201d58031101c2854400740070716281404030701c0c14034500f08a0300b0100c01c4030010341140300f100b0034061614022038028820b80e00950 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 956581070 1250 956579820 956579831
    0x9050d0f020f09060310150e07020717060c04090903020c0a120b15010503070804140a2d1203020f07061d120a050403060b0303120405030a030f15090b130204030f0204 73
    0x50820151050980750036415620403259050019001e81c00601f0402c10f4858098260f607803800c0c00464000200c5040e40142c00180082050444180741d02ca81c4a400300701400d214900402480250b000f80d10540940d1500c40c903242052500030700c03041c80c0d0034001a241e40c100719200c0700300c03d2113018032000458081c040000000c901c0b020a0300d006904260582d01c0601c0c6840364941101c282d84098400e4592608060a0410305a401c210030000903204800c01080c862032981d02e03c4040c0c000803440320040440300d0148001031204280c403003114081d0304005881f4102d40b4104041ea0040280042c00b00e0324120b0008030030f4221200e1880b40e1460b007000c46804002c40c00c2d00c1103260150600c4040459805e1205000280c05038001442c1c0b490007404032402c101e602c551031664580706540c1502d180d040000c011526036414011002e403c8000c100c240070450043e00400315141e00e82c031410b06055510740c8140c4082d6540260030403c2c15079204113548441e180c0c140f90f100101102d108a05c80e07071a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 956582320 1250 956581070 956581099
    0x70c2915222f070311151914040506010302150f160b090a0312020d1e0615020703020112020c03040b0a210e03070308090c0402040311180f13020109050d0f02 69
    0x81125891890402d400a05010b0a5a003e859480444010421500482406200d181d142d410414403c80f008114801100c4480d403000c0d044408440704201c90906d06010080461400985141100e0341a14203240d42c66140301c4403400c3e0701845040c120007400c0011400600a51103102402050066800c4111a11840e0b40c550350f0f15490784004000c42c10500711100e0200d1203034040d26406900c1d03c0042640c01c9040900c0e0f00600081102102c00365565400b0300911508881c1c4d422100620b00042101c1c60640c2c001070802c8403641160349146030009000f005080050087d10000c01d00c1c0c0d52180c0e1035009849000d01405080b41c18014407214071088902004240c0c010604980e00c090081c510b403800b030740ca049400c154002c190050b107114a20000740b282e1a188010001140a00050341507522940100203040d2074441110702e5006480c000c0c8040081315a89003a04542881d800b55110003040c801a1004c110941c4800e910a070803641c080c0a01840400034841c40c0e20071180c400424a04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 956583570 1250 956582320 956582381
    0x1c06050c0903060a092d140c0d0b090a081201090f02252402040305060603120a26040b0109051305060c0a17070c291522 53
    0x414400799819072011020030620b003841c2d840400c034175000302d901c1e052407070030321002600e010400c20907020f4050001d40f032101070101c40000050750560080103821b140d00c080c400144040c03c40d840c050b08902002010405170042042102c00720390388a01c0e481d0b1600d0a0000048003160240b20340180c46041c1000012070340445e20845a0070360421186081010062644079858244141c003101c200c03116114502e0120303841070120351450500c10016941d90304501d4100d080000140000c1d019038404d80d01000404000019607607003040a25103589140b14508607040c1203040803d050b20029407503000d00c0203016500401605036440d036002800305e074413a1a082e400c2996034a00280107a0810070200310818140c00040406150380d20380f40c41450900307803200300581002d85513030001c80c960b8040c000820a010300c0300c801113100740105426943c0c03542c1d0241010741d80140208401004044002c1e0299a802030300c3c00f50030180454401050000402ca000401030030001c040003440090a000d00d0700403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 956584820 1250 956583570 956583577
    0x5040302150f0f01061d03010603080a230f1c05190b06030403120203070908190c061b080f0f13050906040e0309040c0302091302040e06040603020d030810051c06050c 73
    0x41c0403c4052283e1030110308480c100c182c065400704010002c0700e481c00560303090144102540c00f44460701d0395009588405803001000c00c024a48400201c0c4203802c1550102060f0703107801f5001c4a6450f07550b80d2050241d200843c00f440301d40343d040d184c0018442902e00401245217072500c003800030014405a4003c01c0001d0000311801400a420521900e54510351034010f0340d001000d81c107101000c9c603100d600d01c6061504c0020854076510440d044542802151325104000384854108030045c159185804001c1115202028224120004140500c004808100c45914101e0107010ba00c0f50000b4100302070010a0344501441526000042103c3c1d2920340300d100c0000844400071441c0948000500c0094040600d802c1e05059013030040d40c10507254803080703501e0301d002041700503a070341d05110088078100b00190116004034540041800141c0301d00303041d09400313034160070000c3c0503a0f200d2a40401040e0340b50015500060580740740904001c000c5400f801d940d01c1000184015a9072107c0390f100b0b0b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 956586070 1250 956584820 956584831
    0x1b050705150c0316031107050a1208190e160b27030a14120307210c0503041e1e11030f06190f020a0e040f05072307050105040302150f 59
    0xa04002192502e4000b210404d6045490309000c207540c0740040103070000d6002440c0944a6400009800d01040102d00481040ca00a41007200e80e90910b0081100743c07440c0744107200d00030b80e96010440c2c06a441080081e1751034081c462010211600ca1407121aa034000c040c58000898056a01034100c07a510f001c40c80301882c0140042102408507140c012020700900801c06003400f40800b5011b0300520720005512500d140d4070385000c1e191030042440d40c010038000f400c591a500d003425810300a9031042c01c4070703041600f2100c903002d50012951610400c4c1a2200c0c0180844000f095200756003004500d100141402410010820100b1001341901c0f0401c0f490310803150f4000f5800200542c045075a002042042c4100004041d01c40c0c01240c800c984c441c05598020514800da091540d15050041078480e0243c18004d1116003080c2001600c03181a6a181500700010440080080000c06084d107411581240082c0801d040034180079480d6070307061301c2c800030181c0075100003901c10403034400340c0d4083d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 956587320 1250 956586070 956586091
    0x10903081f0302090702070602060c190f030b031b030114090709111b011407231c11040314060c09090c12040b090d111b01031b05070515 60
    0x180d6070200a207400900c681607800c0748140144000c009621111412031103001543c005210681c200340c80a898100c000f88450340c0b0386020000751500c241804d02d864000007848c100800d8501d036a03042500502014580c583e00752045403509a540355a00b0700450003404103030300800c03000c002070703640400000c0d045680031780725440414108000440c0e40d2014410f80008100c05007042e015050543e00c03110f41e814403003150703910388040d4030480034604910741d0091f91074100f5542c02d2403c1d100d940592541c021184003c12008211104820b110380000301c0e0079100c196041101e024004442c2d5519000760100f607070201407101d4030700700e002c40010b81507000708460542c0a08141291040102c00c1c44010041d0220a2040c003d404048202003074480c02144141d503401054540f0191052904414009103001c000f83c0740001c0d072280b20080b032904030402d00200881700300d000b61401130703002d0704810740f56410101c052418500d0055125000d030061610641c1640d03094100402d41c0c4840900545480310350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 956588570 1250 956587320 956587337
    0xc0b06042d241403012a08011d0708040c08010e150601021f0b130c0e010e0a0f2606090706091d070302070c05060c0a03111c0c03020106050a060908010e010903 70
    0x10380501e03003c0d00240050010a03840324510031034514402054032059030174640c0420f002550303004440320380544452051449888214559026a900060100814850f0305404a401d000400020300041c0035480c000781301c880c1d01c426070551303130341907908070703155004401c2002c2052903201240030050303502000100d030313104000f030b109800082c00580300041c1e01031280c1c14900c690300c0441c06103002d98501500c504e5000031841c4005002400941c480d1403142583c01d4050210301440c40c0044151342c030a03d4084c01d0002503100301e00056504107040b5202c0d1040e80204a1000030010300c40080d90b803190703600b0710390741e03500c018031400b41c0c140382c01480c0a1011240042c00b0b0612a41c054151075011b80c0d101c04400d80c1d00c0e000b2810f2030380105075401c00c580201c1403202c10315030040083da0361207030310707600500f040ba654135104042402079401c800104001502d441c0103142c404d40103000907000017800c0f07441e01642c1720320152100c6158401c0300d0700d41d42000311200c0704c5041071090120094044e01d8101c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 956589820 1250 956588570 956588579
    0x602071d180109050a11010210140109090302010e0118170304030f0302030c070c060206071404031106090a09051e071706060f040306061202090907060c0b06042d24 72
    0x1034000d099220301d00d640d03031001442c011070320401044e1100d0b8081c241c0c482c0022011000242001007a241d200d00303250030100050794803d020007205044a0400d03000003105196490304170b01400030020581e0040d0b0070040500d0412100d0003542ca41075100351404418010b254000f440b4a0104640c09000302d9041300030061407500940003564001002d005041c6001c6c070721350701d18414070703610f41080780160b1003501003090168002c2c59080034110100304442c20145140d56408541c02c0b0220428051400414452496190080700d20050072551a00384401d2516001140c1d110710305407204c004003602d5070041007856000300030b410b13441c8a20270207440c1c40c0e07542d00c414400705612081c8102d248200400000010641e0341c410030300682102d00b4410100c1d14540100010010060803090668114090801100c1e0b00300101018150f40118000b070196a07480001d402451301c1c100110100c960f021100405100080a60b070b0203010321001007084420000c0040c251803a194003541403802c0801c0c0a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 956591070 1250 956589820 956589841
    0x6260a08160309032a090e0a120306050d030c05060c07020f01080408040812040311060a050706050c0403020607050d0207090b030d08190213030309061b12021203100602071d 76
    0x141c10354064245020040e40c0d0f0707680e038408080c1d0500e01803080d1090009100c640c99801c008440100a608028003415901001241d100d0502c08001409001c03202869407503140250841002468002c1a21150324070500f400342c20150050411103c501910000811440003c02551003154020701030b101761003800c000540b11500050811b4031402c4d81440001208141017002e074982c00b200c3e411854489207103141c028400e05204100d030b48503640c00d010100c0c0e003aa00800380c9030030300c0e00500d010407103071910f85282c031491242d40c00c0690000c0b00041c02c801030000008000c940860a503088030b0040b40e48030031010031200010341d060350641103080c0c18461144101503268101290800e03a03d05000210380f0380d4101c3e40a9851a2007410234100c04105141d0090100802060706092610144803460f0700d5070840702802c1e90003081d07040045240c4100c54420800103008102003d46240d59045c102c800b41e00100880c405c20005210b50382c000300d80166104048000441801105009a2030350708111 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 956592320 1250 956591070 956591107
    0xf1e06031503080715051029030601050d090f030905120609030427050411010807020c0a05130b0306010303030222031104021e0f030709080607020c01030c1206260a08 73
    0x340e48200c2c8041100700707605414450355021f4a079602d0300310b41145ca428518088080c010004d540b007002c040c1422003002e000041120390000007440c00303c0c2e580008e07481072030050a252801400c400144180c0c3c02c10560043e892805450045418016810858a0700ea960340800c451039911500244020080101d45001600070300440c803e000d003406134041051000c03580216401e591441840141c003949580008090f60404841d2026000824503c1b000c204100002d105c1c05006011001e244800c498003544a0036a02000505440055130369040050107500815015080482d9105106611101c540f60102c1144e6100e84050420038584003048020740007181e07015001e001e603d07400382c81c03405114000c1c1380705d001c000c8910b174603410300f002d004108031416009110154030041c24010a242c00041e5094840c009190108010081c814106c650207242c00c550b01c21581420400303d41c80702c82c03040041291011030000880b8802c403002e03041d524400c02c078000d04219800c00c0300b280c41c0114903113034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 956593570 1250 956592320 956592323
    0x151207090c140313060b09040c0311151303020a0f350d0302070507060311070f08040807030501140a060b031306060e0406050a1d07060e0a0f1e060315030807 69
    0x2e640402d0150086800a0344100c0f20122454031003103c0070100119445200c0412000b95003e0a40e443d165030380c60500106404050070014840d10840030654450b1654400e000030b900e482626241d04641c9421a64441e0000300e00c18002000082041c02c80c01c2c1c122012207010020f80040503001040141a071005049030918081c043d050003551080704006502009070a0795005956003003e04040e8141030b07098000320b04043c01c00d0a0500e64420340416105910340101c20485a00b83c03500e04a291031280354806c0065000e00080003041c0441903100c0f910200f950901e0114a41d0381c5189001215560b025040358500184042500d010a1001c006800740c850080054900d403034140048031120215001c49060f62602c0c10810340c082c50740558a80542c01090f00e04003004545e1809403218002d020b0401003000c0e10034010200d503180001c202c000e05d460030040500503120000c402c0500403004444206410301000052014031921a160a4440c1d0100c0c4401a6042d60b44294065001d00380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 956594820 1250 956593570 956593577
    0x2190e0406090e07030308160c060b030a0606060504030c170303070c0503040e042a0b030705090103090f06200306060a0309020409140f0c1c0605060310020f03151207090c 75
    0x10049a0050148140c0716043c0c10031004021483c0f86107001008000002c1c000781400b516a8400f4817000c2d0404c502110f00d80e40130401051540e0681c3c04a4681740310068050b0000d0700303000000071200c1e040780040050340c9c051078200612984800b072941003071581c0302d017035006a0b20800014085610075007a00c0e0380d161056044e00d140580d207020f080c01e03088003a6000d8444500748135201c883e200c1d558001d40c111308618a00d890a813450540d9001082c04018140c106105000800c190310b41c1c400c1d844240c0e9254846101d40c14010305051a2004200d405040504c4180c0340c607144002c6040c5200341e82c404c03c801450272b8600492000300b1000b8107100700040b030b089500c840f4428000745c0049103030020042a80c0c02402540804400e591400788441c1d08540602c405103900915120450090f0001c40d8100c1c1c0d001c10203803100000300b8604443c540943d0300403840410240713404400a8005c60103a100700350000c200e2203a00040240d1448029050012a400550204031864190700040003e40d842d04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 956596070 1250 956594820 956594831
    0x111070305070906050f010c1a090c0310241a0a1e030b040c0e0a050f0f1503041a0606070b071206030308090d09080624040c0e100302190e04 62
    0x1a2400d1030900b40d600100143c9448010034001d606041079001c0c2242000d2820043d1a01d20ba2642c078083d80c510050003103102c41200c0010103902040141d941c6a010140c01c55012614000448000308038801c00c1d5000b02b42202d11503207002150340105000c0c1c0e4035069200300c0844000f1451001503211122a1040c8444000ba50341c840e11001c1426040942c030361030100e000c000d044200000c0710548401c28042c4055058000081d0310341c0ca455005030b40c0c0c1550160340c4011800c0000d44417040b48080c03039600400a094400f012202a800741d40210b00c103d0f491485403905240049081c102101c03101e0b0080001d00003140401c4d40780c0d243e02d8010803603007492901410300107111400c0d200c054000341c020480020030701050b90000c04c41895800c43c645001d1102e82e0500c06800c0d00c03007501800f44080303820b0090884c019401d0320f0042c7e50307020b08001c104120000040402400c0f2148170090039103d540c12444840c03d441c020300031160590030100c1503c1c03681c0d040c0072050315444440c2c02003035080350b61030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 956597320 1250 956596070 956596073
    0x20a0603020c2d07080d0f11010b192c073e120304080403020607050309040f0501031203090302280c03060e1912120b0a0605030105130204031101110703 67
    0x2e9a0f107207030090807044020180ea0b039125500f4941185944400d0b83d503485404644111a480705016124100a00e0114031446040000728050040110013680c860200b000a0443e0521070200d80115035500c0302c4c110004464880700400c1c0000800502c208513100000596024855003040410b0300115005607071118806180580381403a80c240300201381300e0146100d0300d0700f40c10000091103250150100e4030b185800ea4900c84607000354840240283d0003c9002e00421106009032384201a002c3c2041020300300302003500001d05400e10041e030702c42d00f10342880861944607024002c034154043c0c00400707030443d88042441011003829031039002400120714a0300082c2038030300d20300c0085001d10008203004520305901d504069407070581c003200d0300002411313000080d0000408503240740035003042c10104211b805440050801c440d01035621105a10300440d0980d04030000d98181d03003058a06080052800c03404100724072030b500001c0c101180310700356104258895030b011440000c00800f40c0d0b00041e5203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 956598570 1250 956597320 956597353
    0x1008041a04080d0b0312070b0c16080a030b060a0c020f0102070e090706020c06070f06050711010e1005100806041101111c14210402040219200307020a0603020c 70
    0xd581c2102c294030700080901e0b4101d450300941c03032542000c90140c0300086c0281e001d82c681c2e221b1608001c0540c4034160004034600164400da03801002e180c502003084000c40e18119525070300681c6030401083c504083c0110504214003900c001d074140b519000b1645140360200800c0800090382c45045100e0101c010641c05050003000d03006d450040300070700c582c50500402a0030020903158581c040d68052204001040c629031070f01d26411340200c1c000465454254084038040c5054406084940c20100c110f0b10101d80099407104000c040301040200307440308009016900d0340382c42070b62410b03403003600403401060513041560f00201050501340b8030340070490300b00b41c10031448030300410050201e42692000d00e900002e01c042900e407108200d0380f030041e444580b00e500c0c1d40f000e40032680c21a880c0c0c0006045440b15411201c80e130340700b0361a5580102440710001d02401c0000003c00244550704855002124004181d994580e0b000b0080c8c000c45080c200c0c224000c0d0000c215a181520400c28001d640b040c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 956599820 1250 956598570 956598623
    0x110318040b19150203070506070f090f06110601090e0d08090309120708010b010c0803040b150405090313090905031c060306020409090209341101020c060402011805100804 75
    0x10611040b000c0a442e10b880660005510340c000015500100207610000e4804100207910507030340e003070080300160f00e118100c4044000e50007030402120003901c0401d0b50784d041103150130710881b844209c3c0c416a03201d540590644084400603030f4140e02007005510014042c1074055409841241124141400754000440e00b0481141b4070303040750050307103081c41802c20030301801310259420308040e10010141d0303079425010303c4002c1021303010803140e80200e418080b51503462140003034000d20910950074217100450b16030f4840c0f520040d10401010380050019102e008002203660071002640c03c0c510606902030104c20505c40e070801440d512400840060300500c0a0320181c5440746001a50403254418840a8a000f0702012031050800e0585100e0013511114080b0340728075070708202c0001710003c0c400c1d5000248030000a1155002041e16007006000180241c4200e000740d944410318107810340b880700e5440250040540100610b928010854003036a21140c000344a086050716800e01c0180b02d288000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 956601070 1250 956599820 956599849
    0xd0308130506150f03070f060f142206080c0405061602030d180e0108150c0c16050a2304020a20160b0301150e06071a06010809070608040f14060103080903010c110318040b 75
    0x10094bc401c845064048582070010380f100c0d00301001c41d410306842e80c08090240c0d2090f203107d1600024255820304100070a5148035a019049a0151081140240041a005d040000d0b07401141c0e400280c500c0140355407034102c0d01921f01500e400100e104507400407440060454610708800c00c001105044104036000a408038a80303131900140c00c0804001e88203805a1220095403421724201c1d481145001d4490741c050302c22200181c0c2d56400d82801e80c1c8000760490103444d00c41401c84840800f0802191a420100000c0c4205a9150321884a80b1003804207024030b41003006070300300c0c02e28a24000c1790700b2001d0b400300503d224205403096895010a01040c20041d002d2545502881800d5810400c941e42184040010b480d5041c28003100a01d5020300a2002d00005400c40040050200216141c0021018003003078411540e124101110151b100f0031840e40258030780000390741c42510031400d540e204450400030710702e4840781d9558840d10f83c5110000b140d015650300300600d85a5134403145a01c040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 956602320 1250 956601070 956601097
    0x807060f0c030204050310090c05190812030c070f081204080909090309280b0f190c031d03120a030902010306080703020d0308130506150f03070f060f14 67
    0x141100005019125035400d110140343c01400140038658011421a00343d000d09240094107590908252003109506d6000c180c0080e800ea6220040e1680340c40590103595802c01100e03120554644602c40b68442220300107070245050100300001030380c210200081c5402140c40500b011f01150041d015014141c44c00c6507000c400289107055410142e0a03541c4c0920300f0702c0a0740c01c02c80c3c21030200e0200d1000c14103410ba8554020a642e00d0a40b00d0b20f40d030701c06170070321000480d11103803134401c4000154401c41aa100c80003203400ba40d4034982c4288002040140d050355000b03076030883d102044441080d81d000f1103505000d001d0040c400c42c510348000d01100000c540d808140d40132640009030440e4410b401607503081d04400810303c007584800b000403400070f515140500c1d490f0f44030001c1000248140c02e00074414000d45041c440070002c4600b401c1c0d80d004007154017643c101151010555102042c0c070800030440c60300082046001c1c0030780100710f508100c1b0700b000c1004400e54456900203910180c2d070904603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 956603570 1250 956602320 956602331
    0x111906030c020f0607050c010603080c0f0624060f211501020724110a081c2003180601081507050c030f0a03060302060d0504050d0c0b0c0a030603080706 67
    0xa90390501032501e000400b0700150a0b05004002d0a80d21020000c2c42142400b10000b96002d00342400d40c00306004507040340c26030392244044044640c43c2c2c8451003805841c0c0c443d107004079440e121580a50700440d180c1554000c055000381c0244011500040d080340031485041c085a1400810203042d10540080181d080b815450200043c1e00d440401d06c02c4141103502408042c45080d11410f81e04003510364000460a0741c0518000403075014207601c00a407254020031007000e0402c64a82c1c080c02c803449103005003000c81c03840301000c0d80807070b9400c00781d02d40309a44880e0800d544901c420300039074016503181c01150101203144103c9142c0034007030f030080100380e201e00c81044110820300d0b01503811040b44e20386246082460101c0d16a2800740c10301c14007101c100011040540741c000d600130030043d41d018007115190340d03405030344500600d0100e4040d2241d000e005006910030303101c1d00c15031020a90000c10072034540c5170010494003641164001d401850750b82c06c4088041000c040140c840396200706004501c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 956604820 1250 956603570 956603579
    0x5040c030c0803090604091a06070615061d042a0503090609061303110715030507021501051507020d081c1401060512091c120e0d05070f1119 62
    0x10100c42a4011800d60f0030921600080b580c3d800300304c42c221004060003180201c0c01c2d030100c540519158110951002c4000745010412001d134000000c4c54004502d11031144c3c0c0c0c0c0c0c42041e40c1b13810300401a1041c040720301c01c80e1a5140340640c421300704e001501100c0036003030a00c0e01d40b04e60ba484029451102140010080040c0b02200f0003000c0d6000c0c10102c081d04260622081da03841c98420144020144410822508410002005058018081d1900201101110420180003801c0c01d075000001401490190300301e442c14004114101c0310b0181c000c81c0003181c0300d4900c49094000444c201d903c140c0e807900340404100300300c0103840506ca01414820803182039021001c00c41b581c038224140081c06442c01002031301d070804143c0c0c1908255030a604034694600e100355040455a207004203007604000f18208141d0352203880450b411090200402141c402a81103a988100120050002500c204070390381c00943e0034030119003500d2060f140d40c0205015000080c8008808501c1c00d8245403541c0002c11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 956606070 1250 956604820 956604833
    0x62607181a0d270b22120215010608061002010209030a030f110a02091602010b09041101091d010b070302030403051005040b180c041d150411150706180605040c03 71
    0x140d04404844140c1d4400650000760343c0062a89101410361010381d000a00c031030b07100388008a10618420691107400c2010f241245c1c4440c2c2c0070201400510511581710a0040c410740020f059945989568205540da43c0401c00310080c4e0f0416201195020300503038100e07440c100221403460b8402d444107200760744031201c000d1403404190803004080e40714200040141e1a420550364200350741030001c01c0e11103126072040e400340240041d413a40005040c030401c0b0070320104c14024034801d5000d0343c03002e10107070755003c107420f8020b119101c0245620301c01004004250050005003070062103401503d040c1070381d94480c82c0c1070122440c8030041081d01c0f00100420071484981040e0300044580340e03404a403000c94040780c0d4030b5070481c0300315000f0b5607520300b4510700c00281050030100c24000c0302103e10340e9001070749040c0450000d0341e00302c2e4049600c0e00e0301069840c14a03048140c0d40c41f03a4081c40e04054041e200c9402400c1c013030a030200c41aa000002d6004111130b030149900ca01e0040103041c03009461440c003074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 956607320 1250 956606070 956606081
    0xb150319110f0a080c0f010c0812040c150201050a0b0402040f05090402030a150f0b0a0305100e011d0a0506070c0b0f0423150c0f16150c09062607181a0d 67
    0x741d041100c1e8840103230014441c001a690240d242d18051800756650307141c542080f0001d81c020300d00310104001002c1000764150040c41c0718085d0000c00344840360400f410b11041c1c3c003c0b8002c180e007401880e242400141002030100358800d00040c1214101c900d20340310f00300724080030003486590030b4940d00040c0030496940110b0807041c0003590400500c03442d540740e0a803140d41d284400c0c0081c640300d01000d180c05400750403080f1900415188000d444000034581643c4040600d4101c07500e000d00c000280380390f4007501080710029000070103000f590381d40c130301085464800203001f2507441c00c50000c540c0351401c0501c20f42c40400b48040041c00104031480101d21900c0d401407003030081c68020004c41520a0700c40064560841000d420007614046500c1c0119507000f100c412a00118600f10b0b0310400c1903841040d25017100c180e510340d1010b020f80c2148080880c86060100c81c007204604000c0b580c0c840c4642100300009620310012501280ca5451483c049115000b03261301140c40494000345800b02403003503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 956608570 1250 956607320 956607349
    0xf060904180c0b1c090c08010c0203070b090d09031506150c150b13021b060c130602070308072904030f0e0618040e1204030b150319110f0a080c 63
    0x403182400c0c050300c5030081361007440c40000340d02ca4032002c0c10400c00c11815486009014004002c0c0440884458002d5032504214010355601e11801c5c0460311100340881ea50300c8008a965444440358110746481070036584641705880c015540d8400061024a880080144603004d035590800002c010308080e60210030340d07145281340070b250034450000c13980ca00d12480525040d503400980c0b1030020050b0244501601261032109000701d00c00c1211400055006103043e80076005880f000c203444180490b51707000c50307000042481d00c0401c8484003194550b10516205800300400a01c0410700d103840206502c01030710101c3c0401c04444800312125009029010215026942c45040480840301040d800709020b45850040b980e8418108a080043c171004052800c25a01e083e52503660345081c0802040884510120071254a9a60000c1c83c0119907410b47c074000d00d02031000048075462700102c44002c00034480d44410a0b401020407034840103001c0c001003d411b009040e02041100c14041e4280c0782603107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 956609820 1250 956608570 956608589
    0x3070f1803021201110d0e0f070f0e040809100c020a05030c010206010909050c060a09050a09021206150c161406070201050a050d020405150706110c07050f060904180c 73
    0x1450200030803030080020440360111960016042d0303107240c42e070041c00b10341414003140d1000910005048032031b0300800712031100b080460707050101b02c0444a844442c10301a45c88201030351402005508003c440c100d030002e000c0d0720704170302e004d0041d40002c0c403010b0056011400710307503585100800d42c07520600c001d00901065010f0085220900c00007500d0701014046c61800d1543c43c0800c0e014480100113007544124050041551600b50410162050805101c1c4520411141c0300c00310344031240380292210604c240c07011020540350b810411a00c4807100324406034006050203846246001003207800010364202c100c6c007603030504107072003003c1e01a442e01c0c01a004600800c0b060005036030040403a20340d00c2c0e0614026403110255401c07c406031041d5488240d02c0105140c00f104c0602c3c84000614003903220304800c0160000090161801d4010242c0106071500444010001810700750039048003580010059403400303900d10005011074800301044504022045020070420414403086409002c0452 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 956611070 1250 956609820 956609837
    0xc090618010324030f0501020702030106030308010f060519050c0c1c060e032b090b1e090705031c020a150606171003300e040b0406120204050711060c03070f 69
    0x11004001e402c3c06201c0200b20142e551070003000c2c400f0a506448490b54014001d124441e40d030304004180072428010040c0d000800200002d6803806502140e444405078140c1c2003101f01001c000307a490783c00c084803240260290b50030001d00356840d042041505044204030210807011400c1c1402200c2100c0143e0009600800c8040c0c141400031043c0f000e00c800742501102c6414403404c409000e00040340000308814040d6040c4940118007842c41a0180b04104d1890410754403014201c1d9110303042d110b040e4140d007020b02550038100d502010185240390710300441c0d160209544d0780100203a6103012880081c1d0340c5400a208460748440c1d140740082e201c0710b4a12040c00c01c01c4880614045038407000740304411658940e008020f04050610740105021071003a80910780e40d00c081c1c501c24250122a1165252428140302c503d4148030312010344080005400e005581e550a0000a050181c07502041c84103c100c9206500e4007040954030800388000103d840303040140d4090b2810303400c485900d05200008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 956612320 1250 956611070 956611121
    0x1206150902030a0b0f091302060412230c0d020103052206020703301a0303070f060608120f2d0c06010906050609010804062702100918050c0906180103 66
    0x580c650030003040c50000c7c01d28205480050020301c200c3c0e126140100031071001070140b00b84203049415200b04805244498144e05007520f45800c1c02041803540718014400c40c0b000765120341d000e181c0c040d00c0880307581e20704030481003205e4941465030230845016400081807400c06501200d02503c4500e010a50b1040400c220620180c2c41c00c24103144041681d900c06d08480c600c00003030200d015070300c007030103495071075040c1c0c24503000c4c41c1195081600c46900302500002c4a12000449401d856400c1c1d0486080c02100310502d00541e00c050100b004401e080914892080400c080100009041c4c09060b5554000b41e002d80d0b0500350140d00c00740009203490003c00c890b8842e442103800000317091070481c00c0b80d900c514000004018485610714000d030507407056401d070b185c25541e2008183c0229000380710b641d414082196445a02d0041610300d02409420740b80103604d45e040203422070101022141401c1c1007c3c081103442d0070615803661001c0701980e00400558140c0b2a844c175880c803281040ca44050300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 956613570 1250 956612320 956612329
    0x8070b0c1e07060c17040605030a1431020a0602030705060a02032811180102010608030f0412141204150201060305030901050d0e0115061101060608011206150902030a0b0f 75
    0x20b20414092010807031380706003040300c081d400f0350040d0310902c42c6a48958070703000000d100d03420840318280024600008142d94840c40150300744183e9001035141e050069031321448040180d800c540181d0b42400c505034500682e0340e40356100c09040b0f42da000719201c0c00075040141ca03111024100301289031041050150807007070300c2100c10042c480d002001035940000d00180000b01070301ca108100984011a488000321003400c00d4000c041c1d0300f6402405000e40b190741303042d16441610982c9003090001c0104114a004c205c5003109068010416500d41d01e0f01c003400d981c00c220341d00c10481c200401c009814805100712103406212034403144020403032070307003140e580603a42d1107004011030602001045944c00701d01f06421400800104000a03c00560305603102c3c00c01e21a580200c90100d48002c8089000c410144030301c800700d41840c1d0301e459007a40781c400007a66884c2030050648010f5100c1c00d01c000b5110303a004a6000500c43e003c0300582d40e1804079116011500d4510b0340c2c40c031803030410000c81003950300c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 956614820 1250 956613570 956613583
    0x50919120503070e0405070e131415061902010c080f042303090a1202010f080c040b0915130602070f0807141206010803040612060321030608070b0c1e 66
    0xd160400c25aa601c0e604016181c400c07030744002c154410b0400f41002949584640030446088058481c1074485001e055860b09580341401684545000e000000300700d40d00240410090072000380c446071508452030041124400c6041107240540e460f8410544c1d600e500100b0325070b000e600d260b484020f9061030354652113408480001a14650f600b4440f00000f244240b08807a6050b0005080c04121a5121440490408a01c50070707400f180300c0510f040b40680c003600c2d83c00e00c14100188100d103400d0070884101d001c0d0700712520030758200084030040703200c14044000800e00140205040a4035503d0400024a00b45280e080004c01d107405980c20898a48006030b000b0503100500050740d4051003a00205030300c1000340703004050511403a00002510100800200f003079070031030b1b034403c00c0d07a038a26655801030303c4092000506c1e003402801070391451052036a0032003504000b8076010608958441c6114a4072000e03800c0104203000c00211101501c0b4200100b000b00404c050030344511410459109880c2c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 956616070 1250 956614820 956614853
    0x5010c020d02190915152001020913020d0e0f03090d050f0a0c06020c1801090b040b0306011710140f1f1202010f0804080412020a080a06050919 63
    0x2501c2444a90455a0b483c04032107104696429404801da504c410744400740100110168070310007010004200b100c01d8080f01c122540f03050321040040800001c645000c1007540404040310b540c00e000300da409a480340b000031140880383c0409600c03603c1100141c03007210041c5070400c416910002d401000350f24040103541e0805012660074030540d16909002d4100024090007501c1c90090030300d11030800443d00008015100305900321100340c0302400c00c3c8030170030090841e0b504802c0d00c0d40c0300401500c1c0340703074100c2066070501902c04942c00c0440f20100303250640c2a00303e25065080041244a10034042148080f01d4070351490610200d64500c100003812078000d8000c1c0340340568000020820210300c0c0e100d0100205645070f81840030364900400f200d0a00900e412030014031040c01d5801950f115017601c0703020b203400c102da081c40d1510348640b10314181c00307074201260820845480021174600a01c405203003140144400310f82480d22012490401d082c1200c1d00158001400a0902090401316080e0010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 956617320 1250 956616070 956616079
    0x60915030501051e0102030708030906101706010312020c1816050708030f130803011d010b0c07140d05010204080706140a0905010807030b090405100f1e230a1e050105010c02 76
    0x131215004030700398804c510001c0d00580000060003e91180050b440d4810a51041e2504030341d0745a680800c1c4684030250011141d61040c1d006001196400c00000c00c401114011240d5601c061000b0403c140c41000a4004044020707040215100c989042e4441e91360003403a02c90700d00303d815513070b48481d400040c21000740ca80d40d140000d81090810407084000ca41c00c1180c06840e9a901d02544a600d078902064145c1c055a031340c0000350302d61466040d81d407180302c1d03c0301412103103082c240001c02d03100c440c1c0c1d130040c0c0c0010300c1d0390f100c0086442840144090001000642800703801d0100140c104219641c01c88030a40d0b0421205800580c00303118030042d101c00740780c0b030100740d02d422030b0440260180000080e4080f100c10180001c211000500364012541944280b1800c940c850800c82100c140d54072012040028600f050700b00b62150780402203002840780b0b29814041a54011a09844100c455640c0b159951082c0105d1003100f00113080d030f91920036001c0c4030640c10072000030200a081d0500a004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 956618570 1250 956617320 956617369
    0x236150a0b07080a0e091006093312090b01231012271b060f0509060d050115110a200a09020a030b01030506041527050106091503050105 60
    0x381c42020b07211805e0300010022085401e0000100800012620401020464041c0f0018444031117145000700108200080040c90031281c0b81d18910200064031941001005141071218810302c3c850061454015490701c2d00c42e604109203010210303102e4100322095040d008102800e5034a881c011143c2410034074002040041c90000c01c13000d4100c8010303200761101481003c2000f940254074907640302e4010034612022522012080c82425014084c08000139201c000241500340201d0007495150380c003170100c80c9407014105441003241c41c282c0110040c4020030b41600c0342203500a01c50300a0200b040301500d17600038660703904210124801c9407041200340d8940310614680d031b50515040107107030301c1c2019941c444000100500a1200c034142e02c0c042031030000400c109040c18403818244200400b19510081c2c02d10400d058130b0701100c514154611508511040708030b51a0007994000d12882c3c865214080c00c001c40b5104034080b00f0b40000405160100400c0107a44022401816501034408442c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 956619820 1250 956618570 956618587
    0x190b0c090d120c021e130b03060604020a020f0f010c11161203020a060e07090e061909151a130c080106050c030c16050405010b03070203070236150a0b0708 68
    0x142d200500700f000c0d40c400f6040303a0070121074019601808000348203c520817840490081c44800305c8004959554069200b0310000e00e06082a9004080d840031a00480e0303407480a15443c5c80c81d040408d81c40103030f10b944880c07004028582080c40341c003910f5440409040503c01c0a41e00c0c6000e4134072480355031082c082d44040c000c02d240c006d0045c61800340e0802428030118048840d2155144c00c1032085880e80c51408402c003035a003901040081c0036500c008140807040071400328510140c03610303c00c15660041071035001c0c2d00340d050500c20504054000041502d071050010f04000e14042003080e06a802030034841100c60345503205500c00e044d10114209152245810045c035841c50158254941481c85695202d045603000c800d074100880700b0031a410b12440c1c2e264400074811f03010540c0c807040941d0091080100520700a040c40c40408000d49140c041414078060082d010950b184100d01c40301e000106000803080b5116a0000b80c1105a665070310740ba1824922140078407860700d0242010340007055070354 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 956621070 1250 956619820 956619827
    0x180b04030315081c0e030f070905100b0c060a23041202070f090b100306030803130609020a09050601020708060105010c1b050409081b120f0d0e190b0c090d12 69
    0x2e01411400044454840000b9800c002110f04101c070782c80404c20344d00e01c14140c2d240001c2c3d0031b0340111030000034041c81c81c0383c000303a603000c0c1c038029040680c245400480484e00004a07000391a0340d01e41c140060059062455141d07044410380071422851540031a0710b82078520802003c1a00a640000325036178030380001d0f90403030030060950410754081c65400303400602410150410340d403080e003ca407141c035a821035180580845040d440008d1540d00c081c400604805404a0012071044c05410007089540b029400212000d200e42c1040352801d0790f40090002c035580c10803600e0013504200008010b954108400a0488160100003e0051a1200e1400081d9400078819801010054400c2c00040c2242c5014103640c0c000700002001c44403104150380400b5000121030782014107a060013464080c2e4490181d20325032065001c0d45200d52035140c60214114100200c0d030082d052034004034100e00851501c2c180d04400940303185400e003c00c1c804203600b642d84c10280c80b102039028000113a02c1c141c1034400d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 956622320 1250 956621070 956621111
    0x6050c01090209010609142407050c030a0303060e0609090613050f0f070e0c180607081c020904230c160f030f17040f110a0f080d03180b040303 63
    0x1c3d00044040e000080302c0307420140c0700040d80e0761b051660100101c1c0704203000e0810000d000c040003c00c1d2589000c0d0b20344541000403e4810300441c140d580d2408800046403a010002004800081c0d4440040224106ca2004590408800c8656681c2810078000041c0c0e50200607180c0c580768a5030b0102202080790401c010404d40e50001c081e01c0c0b152007007403c0e00b9100d0841c1d2044004011451000803050700c602c80889126006e400c0c00865100346500a02440d504403001c1100c2c1c0803030030403199a0102d100c802c07080c0780d00d5a48001595aa1401c401c0c00141ea412a0f540035400003091001d0300245445074100d03070301c15a001159a121142580310300740b48200345202800340c10b5a036840200b4190b02040a210240c0c1c9910303012404030030611881e6440c2c8088801500700114114100700040000b0b83c0d50898940007005c5079070303030754640c4142e081000e9241c0c481c202c150b01180c161083d07a9010700484500810200ca002004181c0351142c445800740108020101940d51400d150f85445180c00da = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 956623570 1250 956622320 956622323
    0x70510050c060a0f060807080c01080601020712080a0903140616090b09040b03010603080a050c010506010c110d030905031b030705030a0c03170d05182e0203090a02060715050c070c06050c0109 84
    0x7c40d4007581d03582450507244c401c0e40d1451400202c0410010f540d035400092140122444007603a203101c0d0b52103481c2da00403904648860001c1000048000001ca140c81200090303040d1100b000d0300031400c04409400700d03400d00c00340d0a424008241010400e04000d0810340700040f0f410b54000c01c641c0700076400680100020341008007645004600103942c04d52103800b5043e00c90664000f0003ca03241c07000107440030001c0b031200501c1c0444484645942c0d04010480103034461107420f0800070f440d00d80c2c000a0074035411145079103262401c5040c0c50110324042118500030031007030700504210000380d00d41c0b40e03e03181d0901000d000381c80d00582d885155540c42007114031004c00e10701e0410a50a100c41004a140e000700100741480c41003500601c145034003154602d00c0482581e0700c01c18424000c1140320080d42004001070342a004003000680503889000007441c120b4800e680c1c02d0320704400c00da40d100840c0c0001d4000521100c05224020000311920b07000401d40345075040c60790300c07282036508403030161510800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 956624820 1250 956623570 956623573
    0x5070f140702150d0e03040e060f1201062d0f1203050915090f0f010509010e01030e0a05030a090602070b07020d1b090b0a050108090330010602070510050c060a0f0608 73
    0x103400300d03d842c100016048200ea084014800c1c45180c0c1035069803801280161802c0000d0b04011070024035000000482d56500a0501000c0a031402c030381ca400c44107986c3c01400c9450984003c0c03545603106100c074401c0110030a0300601858101148054000740500445850745454a0301009140c000c000b80e6100c0c00005000107040e408012205406421103000f0038003030f4a11070404401c5251900c21210003110603900d00b41080120001115800c0c1c00451160505565852200314050309200110840d070140b80190b07901c4419681c02001080c496000c442190403d241c10300154002030210344a00342c048460480400c4c050a010700b0404441c604603040d400c414400203101c062507006056090422154000e16a603502d005492808003161452502c0d0000c001c10381040d04040007512003405241491101104005d40c0c600c8940020781040000d680002e8041001e490308517540d00c46550a03140190030010501c841c56a076000240084614546400d00078102000f41c0c0d02050080c5405030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 956626070 1250 956624820 956624839
    0x1312031106151509010c030e0411070b04140d020c04020a20070614130314031e04091506230c0304060504030501050c160f0305121e0601020105070f140702 68
    0xb02e40d00c1444600b81c00e040e014002550035011800b060005076002001e040e100e1040c1443e5564007160322186419031203600030394a00d101080b0320030b1030020713102880c829150804541010b06118425a040c1486807580c2d61244e0043e95109a000c5000b03102104243d03005038581840d4442603415450070295480368001d0458900c8a1090001c1c1c0c400c11a2111b40782d1303203203070100a801d81115104032941d098403441d0078101007002803140844000500842c00680c2e08143d03031000c2d48000070340800c1c0f010b40151740c04030f0140314106c2c0500c15000e044107003105080ca40781c0361060140071054404201c0101060404100d01844010030417150091a0681640ea40c0c58075240081c0468010340000c1d01c4541c604800280b130060440c0440e03074045024010110320b00a1651601400d10852108800b005800d214642c68103a49507260360103240f14000c0510807544400c0d800038002e80080000e0304584c102018041810f800001c030140b004da403441d0052459031810381e16040391041c4d40c0003d401403d600c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 956627320 1250 956626070 956626081
    0x10c02040c0503060a0e1b130902030403090f050a060e1e09091605030106050d02060a0306050924100504060c02150703020d080c07020609010c03210b03121312031106 73
    0x240158131a14040716844800ca45440a0b80540202112150032003030015074454401c3e0f0403a00505810700c0809583c401d01d540320000b000aa0b041a10210701184d04040700788990524035114401401c0d00351400d5000c6407420f003006201c2c3e400102e4031070080c00c05920481200001070208600d0101c05040c0450504215244684c0c0d250f0744d900c641450280ca4102144910b4180503030007c84a0080111490788110780030082e076544011850403c1c0741c2d5a10001556440c2d40326001e1007001d650f01c41c5485110001c01940365089080105481582d5a462807900c0a13084400e42c2c05481032803030040c03040d030074603c0415000d91411050b070030807580109146040540c0058208001e010541d50b645041d21045803941c400c0c000d05038001c2d44410b0501c1041165481400001c0342d1034001d01c0c00d169000c414004c03007107507040101c0c0d840e6080d80e02c0b11050768240c00c04200c0c3d00c9400c034001c3c22040c80d161168003068015400d50080596590070f04109500385132150301900a4821020b085d61002c1c01c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 956628570 1250 956627320 956627327
    0x60f09090309040b0103110a050c10050405010c030606030902150d061d070e01080c1c090f05070e10030c0909030c020303030702010c1704050309131b0507021309020a030f02010c02040c 81
    0x1d0b400701d119504013000030360036511900613002c4440024491a0400c11300250035a550382004081c46464491604280726007103080c05000e01982c0540000203400402500c010269205600460180350401d2030410040e240c030340054500714a00b10589441c0e064041c00903001d001d6640c8604a0f0035552000d4051512443c4103d50243c0c401c0d8450429400100005507940d00007200e4081000c00c061040390721400883c03e40302c5d48004402800203140c0116501c444c000034519406981680c00000103010b0700440e5000d041d0403d1189403d0188140f9559801c01160440e000d003040130741c0c450385010301309405002ca180b000d550050650341c4925040000900170203002c010381000400400007030910000500d4090f026a0708500510324280c1e6140074051880104200a02c003599100b150001168408040c40b80c3e07280d441da0342c25503d680034010030208003001301d45403110380d142108000040c0c1d10340102c00101c0358403840c15070106c091400143c0b0901d028500c0607400a040158841c8116030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 956629820 1250 956628570 956628577
    0x3141503191a010603050613090c03151a0102010209101b0609150b061603180e180106080f3a0e040e0a02011b020d1515090e0601030b060f090903 64
    0x108140902c0980c1c0d81d038904030141d910568011790051100d00f8000c800c00403580000f00c0440c0925042102d5543c0e07079981e160070681c50103511207615030390340c9641ca01a288843c1c2040901c400d200a40c20131146c2d00001c1c1410b202c4051000c10701c008450b000007882c0001c0b1f014801d843d00110b0400c8515424104141d620030103e140c034100340d1804548604a150003800e440c0d11000c0740303000203051650b96605540d8440e5045c1018450001800e0029460202d0000e591042d0381c48007490610700c0f0048200b0307007507502e035800120080d0055005c00c180190002640b0120461880c102c40d07a01c0d00900d11703402e10894500409190440c1d007413000035404c0d049403c0217009482545c081000943c9019042e4a8640c5408024005880003a41008103407207441205150360000301140124904c40d52000c007242400b500301003905440b207810225800945034a0401009202c005103d150f41d2807a40701c1d11400140130081202c1c80d480e020640d42c0d10342115460703003540b0243c105903141c03c0803c4855030360b40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 956631070 1250 956629820 956629853
    0x5060c0706110403211706090711060c13061e0f0923011b150203090c040207120905030304080303010b1305040527010e060f0402270709060314150319 66
    0x404003080c1c40d003502e00c100341100d42441b07603d01404c06a01d85104000f00b07043e0252503541040520b018001d2445003e010f500d010b14016009255030342c03130810004060f08021f520180a000c00c608002c8001045491306025104007403828084003181110103841d4100340390001c6001b0891240002501c038030100c100203100400740c9509649200e0b80b0b014170701c0402000300007032196240c541c0c100917140ea42c1c0c018507008050142682d0b50b541030038011030100d0f044000152a030b01442441c1c100030540005403040035210a4010f540f4180c20986025628803040c0310302c4406020015210103589605040d220181c48020800d001500345a0340c1d030a00980f0144001092490308020b502940c40144140d01c240101c0c1c1c0702801e03a95440581c0601305020082090741c10bc0303858400c050300000d54281031083d05001d1a2600000e0074880070040402545402150915180030484400c02c841161001d502140d201d0340c045100d1604004241406c1010b038140e0b54110501018100b00302c0500c42180c040b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 956632320 1250 956631070 956631113
    0x201200a080c0403080a0f0e18040213020a1b020a05040905010c080a020405010c03080a0905030c1b0906010813030201060305030406091406070f0b0c1e0903010507090305060c0706110403 82
    0x5450b00d4007510310510591000800c062410840c0204543c061a0400d40140050412103050041c1d0b80100750103402c9038001010010001e0108011880e048078003002010f0705800031410201c00384809025645401d0031488081c030403941c04001c42d5110003184002e440d0161051000728072602d01540600811008500810b1580c0f002482562507442540c00f00c0b80305a40b515603124851701e0584114502a18660f440d54039000036101040703040000b05810b400110040c28001e18204820340d05000300c40074188540391440522400e80c0c0d009400346c1e0071000c040c8003065250642e140c242d0040c0481d070b10040c1680404500040d5454000d09440221051002d1500394500380c00b0420005200e00389004080c0165420004046034201d903006078080c00c4640040e24214000c10343e2160700190310724030b50540a000540c0c44180c02c8c00e000d43d90b009580c03030500c02c040906644e102601c4120041904013841000328079034040c4032154024840b240e2100007000d550302c1d101d04107140410201140e00021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 956633570 1250 956632320 956632337
    0x1050921030d0204140108160f0e0d1202100b030607030b0f180915160e120715090e070e090703240e180601030f24140c09130b010201200a 61
    0xa03501447e80244540180542d800c41140640025038001e050000c0910070003900c800c0c0300c03051740c9a0000c1c207140c00e0f00a8603841000d415129009103070070814404400c02a0415206101540380016000e8010000341404240505400b004c80c40010316980c5250340410a880340320142c074031503961140200f03152001d4401096070001e155040c0351040c0c90148240048002038080c00b882442d8680c0c401100611a00600038056407540ca0018140c12000c0c0ba81d100003100341c031041e0064846001409480345441c1e1764901040064440700c0c003028414042d02c0d0550004124a1080d80724980e87c0200c071414142c00080003041070b43e0044c4c18010060b501c644d00c00415403802c0c9000011000c014850002c00e01603003507568144001100d41c2c3c00300c419440086507120310f00421025090540d2200c080002c02014005801c069443c02800001c00c00c2400c012660301034039000d010114148000f94041140d600810040b4018208032000006400583c000c00c2603032103020300206540012540d40038135 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 956634820 1250 956633570 956633609
    0x1b0d05011503022107090503030315011806020a0b0a020903070b0d0b0f210a0b0c0901030b12100b120f10061a041502070e010605040614070201050921030d0204 70
    0x1280304e92882142ca024005010702d6016601c03694842d8409514544482000d41e1080800d02d15042075170800c40340d242040b0074001a5a00400c0784815100c03501940b40701303901d4440040c0d1543ca40020240c0300c40a0400007400e61003850701207075400d48000d0119146c840c6e5404440304140c01002140000904000c1519240c3c9080882080d507042c00400c03003041c01c100e500e9404041440c040c101e500c035000b01e4440d8400311324082c0e0200e2042030b05d540565507820309140014100c81280f843c02d48501801240e480a600c0001921440c00c14014000142410031000140300c500074503d11407024030928072140b18415010410381190400b43c901807003100c1c3c807142c003c5030440c1c8cc0d869420084d003040c0003c001c0303011000d4180c0000455070060303910440d1140311070700c6d280382c00740c2080002ca480003408006036a80061303150180030010880905059455000a0562054044840c41220300100540c80f094403c206c5080d45407094048960303d410a07800c0c08040c3d00941315078851580710004502 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 956636070 1250 956634820 956634827
    0x10608120405060301060c0f020a090b090703060b030601030c0e15120f01030b0a090807020d12020f070807030201141903052d0a05090c06040306090b100311091b0d050115 75
    0x24103070344000b403c0c181140e0a024003143d490281800680c5e00e80860030001e00541c4960b07040c0d00250448900100d04002100e050140000015000600f0186405030400c6581c14000680360844424600032a6102c86018110b41c81c0c131602c02115400205000c49442c2900000000c0952442002c040d0409649050031400a14824031010f45005000400100f044072940e0000c50001e01c80c004240c184842d64000c04c80703845d00c0b01002c480342c40311900d07660b08841d010002145103070490030044c5034860410900702d1b02c03007103107100080c140044d40d81000d040f89211400d40314440d41070034030512074a45034a0001c010b0320302a181c0c0b2070320001d01c00310b4100c4003080a4000c40703588441d1000000700e455090110006080c014214200b60045a0080c5080c0d1303a084020320056000700000f003502c0d1132900b0441e40114020b0400403030860b4071007017000001c0114100e18080a400c03a0840d115a0f5a01200c4040c140450f0305050000d038005810400511141e2100c5e0581d6021001500390052211096 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 956637320 1250 956636070 956636077
    0x2401051207030303050402120f0c0f120c0f01021e0109020a05100215100f06110f010b030a0f03051e12060a05060d0902040e010c020a1a070c11031e01060812 69
    0x18269401c441d10a00100e40240c0003150007510192400d031a0030060002a800c01d071b100c400d410600d400c620700780007892030030480034960940110b4000010904000314103036903c80c030400c007e004201c03c03081002168002e0191080a48050340c1000b040c40b209190240204407012040703102d0800c0e508082600d040103c01c50903441c980d0703001008010300c9540c10041c10721009000c40c12208d100c440214041d00710202c02002000340741c441940b480030a101c807078200802e40e601c0440341e03032418502d00010786c1c0000780b180a554000380400324284c6541011140e03072003482d1100500756a1818000c0f241d5003008005c02003020f0301401e440e403e484120800035041c84500c5116440601403080483c000a1a070000d4a00761000304006404c000c1c0d01e2909080d101818450f1002d0703004050711030b0900be900f0515a031500c17000290240e40340741c041c602901d086252880a0400140d00c9400d04042e101007000403051005c0020312184d091500c071615010b00414000c1e00054050080c4003d103100302c00055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 956638570 1250 956637320 956637349
    0x909071e03021905090411040b04060305010b12010b07060b04090305071202071815030f03050c07090e03120a24080705010206010326040b040803090a060f02061f08240105 75
    0x904869040483d01210241c1203002c0e001c1d401a1356200103070343d10782e4000052008100d4500c03142c0d12246000c60203001c44d28142d100510b484000c20607a4a0b042c200c015040c10f440d2407a030340907215402c90408600070010005e240c0c0d00240341c40d44107400d064002025151191040b1071700708401008101c00c0b81c494842e442400011280b20842c1b0301c000c6080d400041013520340c0000203564560765101d105a140742da0a042c0e000ca00000380000030150309000c188044c4c0003110090000c1c88081c40e4050740c0b80300d082d0705004607611800c00304030303154016081242c44007450004d008451142c514400100042d6200d414102d00c15200300060310350022a103103040b00c0d00b0089074022440740b02605814160101c81e1301142036410000410030020a801910140215030020354803000c0c5030081c8144000c982d0030036001c0c00110401c10030466800240282d100012400f01c2d00d401441105048100740306411503516401040048032203050034840310a00717401c030f0358130424042e41d958040c0841500603804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 956639820 1250 956638570 956638597
    0x7150f0806100c05030d02030601030b0603011206090c03080c1513050606040507180b0703080609010308033c0609100608071107030f0b04020f0f0a0e09030909071e0302 74
    0x2205454502074054401c82c0310300305551203400c0350351000e00399880004030200380f603404014402c40e035901d403082226040d8262a81403a55060608071000c482e96441e0040c000c6444a001500f00544a040180207548c4425101d84403a800140356849130111104203055100031000203616048103065895541e1300300c0090909510b4080c2400302819000340a20244a0b10300d40a0300c102c60721030a40e4004050340c040040d102c18651900610b8510042d1100b0b2003180b0401c01070020600c240f04403504050440c10541c92240c03d205200d00c1034142d8100d404004c200c8510014091391500c40d035900c05c8000315031807082ca41c0c50303580c4206055021f014080000b419400019400c0d8040e946042c03040454204540c002c554035030391400d204408540c00c540b04482001072104509040010603060101181c1c40417600383c4510204041500074030030605c0d10f1070b4140c040359034900180200c0c0c101d15000381c50417007949003201c0c010300420801e046207840c0d003041800060010b4801c0c8259404072f082c105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 956641070 1250 956639820 956639837
    0xc0f04090e0312090a15020a1b030c02030d11120712050331050607020f1002090a03200a0816060c020310060e06031618020f04120507150f 61
    0x4480600401040000141d00c0c401008140440d42120121030f00c58060030006201c0f504480c03030000594180d528441c9022030051020418154018040d03d042071040719154030040c601d402c00300c030039428000f8083e40502400c0b101d0303800d0035884190100501c0410003222800031059000d290a40309203600504910482646c50303c40c2d5115100950700700406c02e0b00140d80084d0381d1681c0c2a0003c0c243ea42c46150401740140e0020000140000c55001c050340c0081c021848900c61801d0703c6510003020681c9460340022030615560fa0700541901a54101600d61590800054070104084041d004144912007030348000542a400040b410500c20159600d80d404524000081e202e00c1240c0340101e82c180182d0350740d034488010610500c0d005002070703a411081c0d07043c80400d160800d291802c0a2241d144c55101c2840300410190103114440010369006940c0c00066440403417600447d082400021400610041130200c0028181e09540039641061080b0b0726402040d100041d140c8402d80c04581c000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 956642320 1250 956641070 956641079
    0x9060e011d0105031b0d1a0405101701061a0d060b03012103140307120b010509010c11010e0d1b0f080c01030504050f03071a10081515060301030b0601080c0f04 70
    0x140090341d004005103070200c1170704c000003008941c1c0d90421286c50307020603540c1000320341030b05900c0c0c2a8000c0c0c0000303030360800060800d1036000c10180320a000c0e24041050940d07215040580c2580124010a00101000800c40c00e48400c264294003c90403201c055007800341c003040f20030034582202e0413070780488400d1401c0f0f0051010351824942c1688150b007889004480d080c1d40c104400010b40c4200001e9a80c007110b801c000b02c40a0468200101960400c0010700c08101c003031340c2100240c0e00550300800301084207480000102c80d21110400b24039044024182e20104000501030109440c4080c4e40c05031100d00d0311210060a082c00a102e42202d9a11040c15000c186d402a8044c6070801d00410071754103044c00078141c0c2c40c030b1a80154401c0700c60107040f050246a00e03800096183d081503001d000301080030b182903441e0703644510034542e4101544060f00071403040d070342c05107041c40b5120002e40655140d60f52410401c20201084409501159072000080d10350119001200c0000d21103940c0b0a0030310342003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 956643570 1250 956642320 956642327
    0x406060b03190c14030a0f1116060b030f120a0909231314031c0c0e0913060f0518070602100b060f040906080d02030a21091209060e011d01 61
    0x1003151250034804018480c13450a88103000562050103140008038020031040083c80c200d6a2558070711500110900103402c5200344503120008441e082072001c200148250002030902c10030a0042205200d1104c0c48144684000041c21718400c50361202c0780c215507200304417001d960500a40e08081da0540410700c0c2c0305251101ca003604000c43d40d000600c02d000d2980c0d040c000b109070164001e0203500103d008903100f00a42c0c0d0380c81c03603110b690314188194200e007400134200c4030013072850340d100b281c0001c005010000c0c0d80b0505014240c100b00284400700c6440c2141000f09016505041c0e40710003802e020039007860000e9038200311003050b8001c1a11818031b980e00c000400700040d01960025040001d0414407403848054030162081d0180001e80619010f4981d1600c50340e60a100e06540091004590581d04100c28841c01d201240600c4540b44106a00c0d40041c140c12100401044108610b201c0d040c3d44141d040080d200c0c2030305d81540c50b085400040d9401010305007244040a42d19001440a512 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 956644820 1250 956643570 956643581
    0x3040f06020909041b060302090a1202031002030c130b2d0405180a1416030b04110a091401031104140a050d1208060f10200d080406060b0319 62
    0x50503006060020200c00111030701810f075015140c0c5d03581101506042c090101c6440003c10103820118901007811012a40e0110740348035040d421001c4141c00c0c010354500780304219040078500c808660300d141c04401c03c0000d030400442d800c52502080e0011811940b483c0c200d800c034410045c44084082e03c1c90212307680324090003480b4201a5814800010151504103842d510f003803210340b200200349413007581081110308010b25a0081d00c0340f40240140000e4060520602c9025461701080c101948004038024045d0b10801442c1c60800050601040303501141002c02e89442d400b06803000042e14004509552103c6002903200904100410450002554003094104064016401c5a0b079401c002001095050010784030b10b41016172421240307a02c8001e10340c3c84a801c60b10b010030b8100b4070011880c089617101d009000c0c410400402c11200c070407072100e07020940d41c040455400c00e440032001482c3e03040075503080b40c106080c80404112040c1c0d21003903038464002e16030302d10440c40c0d8600540340a4032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 956646070 1250 956644820 956644823
    0xb040b030f091e01230720011103010e0907060f090509041403120a060603090b0103030e0a031211120405091b0408030f0301140a1404020f040f0303021606030e0303040f 74
    0x8102200c0000902112203031124851201000194680c50b0001507200d00c0000799002e0300002d1945d04000b08681c110040d681885010720071000c107210a800d03018011301c4001c503c02e01c007903404000002c1448c41b14850070320408212064510140c0c0c0c5140c113407018455000354002103180f4920510982c20445040c5512a004102d80340010044d500e01c113043d5480800317000d281030fa4003403c1142101840c040c440080195250810031230040c1c0c1c89040610301c040c0001002c00c2151110048155202c14452010350b400c820800c03155001800042c1500c40c0c0013803404054003c006202072401d03110b0046d9003c031980030b003568265a8841a141403820381e0105010316980c41400041443d003020405030440d55080c41c6402c1c1d0300c3d4101410007140fa026802114403c418018017408118010003042060301c41c15900940c0707071580c00307070100c12500454000010817030509400209041c2d0010300c512044003110f82100115440b206d007201587e01c2c026016011f40e001700003081c0040d202c05409604907 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 956647320 1250 956646070 956646073
    0x110906060301050607021f050c0601080c13020906221401051603050a021507081801090c050103110c0f0606011e0203030c071e210e0d110303040515040f0b040b030f09 73
    0x1440d4086000340c0c442103441f54a000120041004d00e200c220400034140941aa80002c2800111510010320801c1c402819000c2e9260045411031841c0c80e42000d84001810b5481c0d03003603500040002c0000b40000d207100e45a003035076049001e080745500820032203500024140d00c2da6442c3c041034074169450341c0441c00c17a100f184524a0500307840c0c0401c0461901581e559541c11680d410501d50007d80d1107581da40c0c400310750f450007124800185003807000310704880c2c5c00c0c00c0102c2c220702c40a49c001114091440c1100d02809080411034003001e010480c18462030090303c41840b49840c00c80480088440e008215025a2040002c503d14440c240b014004051040c29000801595400310b02c4544c100d440c006c503001c80085a89105076020078904040000da24a880c40c02c2c207112000161400103034110241045d4828002c0c000d185c2c9080c0222400744c44050555a442c13200100b180710b081c0e0261041390a0706001440125400b90140111412034600549242c150b45034244054141d26028200d602103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 956648570 1250 956647320 956647339
    0x2060f0c0a08030c04050109090e0d030e0f0f0114150105160f021305070e0306060a062f030705070503011401090b12070b07030810050603010323060a0911090606030105060702 77
    0xc0b0800d004512541d01d000b200da80b40d518200c00074105001a801c008205070404200410003400040c8800c0c02841500d80810904880ca01e000e041c4a000c2c00c000ea800e000e14042070008070300540110881a00441041c004c0da0b03501f12101a100d4408030032680054001c021169840f50180e1102c08641e010b07444400f418101540020100403540d9056a4401d403608100001140c0100d02d060105c4016400f0b010180b03810b100158000c005030003040c00380054206064000111000303803d50840d046041d030501542c21492095507074005400480b030a126411000c201c90a06020f1640701c0400c031600c4005603420540c078003024002023908603420440f86038002c80110420400c100007405000358042d80c40c1101d0600030702c450700090910018189144040190b611890100c88c11240c210350703003442e503217102006400c4203a0408820281c501c030b2042449040a1140c0c465005d103807041c00095111480c4000f803189050b030490300207901580510042100b41498401070401600c02010b0099 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 956649820 1250 956648570 956648573
    0xe0f010b0a051c060324060323101a1c0302120a03020706050a06050a0b0c0a080c190c06080f0f04030e040b0a0b0903010b090f0406090c03020306250c02060f0c0a 71
    0xc58a0645c82910755444140783d08501c50700810070b04000850560082c4410360441d12600c40c400c0c50b103005000310003480c25124200050500100d03041070071228040c803012324404480d58080d880480c1440c41103c103e01d0402000c071a04d50782203070169154000c0c203403280c030b0528a100c941c0c103c0701041040c95003c200170710004445104d00b6120300290740001590a050406001594829401ca61408201000320f0381881d0000980c03800030700e51144c190303940d500c10b01b5046802c4c20b4a840d500e51a40354213036950006c0007100c4a495056a0711035441d82c0d80b40d0f0b42c100e40082c0510040d0b90220012010750040780209200b000c0c001f89800c8058404152010003102080c0b080385160300c080c850120200320300905150030301503010900b208a41f450300e903041160544143c014050300041142d50745000310b2041003050110180110380040950790146400003100c0107550f40d0741c0034181d07881006d0400c651040c0c0241000c858240e0040c009906122080c000c1c003035182e204c0c202005561103003d107030305c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 956651070 1250 956649820 956649877
    0xa0b01090b030a0615020d020606100c020a030c03020f010503131202012306041503120804060f0504230d0f121506023009040b12060a02040e0f010b0a05 67
    0x10b008881c00c0d0b0380001c600303190000481d11048005032404c215000320700c8070744030f248e80020b015402240803249424640c00b921410744050a00b60b1000750403c0300c1883c00428840c0040000003100d00a844202070301c500e5034011101803204840c0c440d01c0b0112551480c0106803500740204075101c140c0000618404100b450400c9408030340c1450181103622000c20905003080c0c041d8441a40300c1d000c0140030181199075180350f10307042c5a220001c00640000190a112407174100001c04900e04204001d14286418035007107544420b00c00c440317004803980e08003200820004d400c102100d1681d640d030504944d240b20407510030030034a411515840d141c041d95018110f54840d20001003000760010041c0840b42444100c50080404488269010b980e11103441d0700c1c1e4040072a005c2c40c800b1600003a00d00300031000922070300800c100b56901c070b10074542080300d0003000d0381c014000e803814400400601c2d42c4150252991140900401d0810304003800141c2030b0705e004001801da00c071240481c01310110744820062 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 956652320 1250 956651070 956651077
    0x1090207152408010b0102070b120105060a020109080423030a03051b0312132108070f0323190218010309260403030f030219050a0207090203010801020c1c080a0b01090b 74
    0x10243c84e507451000c5000c0d581c040001000500390000654200301c4482002c00c41d1000c1440380901441d4001400c2c06003900c02e62088200503880355840d03403641d49417808000318158000c190b0340440318004010800e4035000070300365965949599032614100012909950880038003801a03401c0c0301c00e0040e80c1084060708402c900c1411070b203405082e04001d9080580039070400b501344444c3ea05e00740e2104d64001c0d0b407000c11240d000303446045c010525140740c9411001041c04900c2400603d0058014500c00c082c4030300e0b0319010390008584540d00d00841c0c22550104d105140d0580d040d03080e0603414114650094100c2808036001d0500110185861550580168020341180c1000080040c0a004254222607441814042e41c94110308202200400003603200c01200d4007014404085400d00d0034620130170225024142d1004259285d52392040914040e4000f5026181c81c1d00030710314101c4100c042602105800305075640ca44d00c2c0e50701d9096095008046642209042002004c0007080420400c0000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 956653570 1250 956652320 956652329
    0xe060f0606270f030f0303150901030c0b090a0e16020f0c060714120a0203070c140306040f0c0801090c03050c040b0d06110d0c0816020d02070b091207030b040b010902071524 76
    0x342d5070328545826402d036800712320611244502d03103000040c40843c0750302c1d0360b03002503694141d14241d03112541800250407041a900c005050041c40007000301d0600030104008040c100e540850302c2d450391494803c1c5d220244003003007e400410a100c8030b03002c02c0d41c0400041100400c44191384590b01281e80c1c8036103962104180c4400b6074400241e11f41000760b816000401006866103c580048103d40080e4a6910180000c0c3c806045a58240144a03480b000307407009118100081004031003515000d4108540f0344016a024001c0d000b4080076030405001d00400603a00400c05d440d02992640ca0308000c10030204251200d940c1407000b6200145e062141030840000c2d40c5505e9000c1c5081c078a07050300076001c40300030811504014100300c1e2140c3c00240400a80c2c421044003921481c1500104d20543c0c52040190311034804c105000003400f1240d2003413070080740103060302800d42c2c0e242c0d111301040e0301c158400100f4070104d04a0040444280343c3c06945210100c0383d03401018020933003984103080c9150803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 956654676 1106 956653570 956653573
    0x901060b0d0b18181209030c13020c01020a0c060b0a0311060c12040b07030215280b090907060909090b010909020a0305010e060f0606270f030f 63
    0x21801030445411210f20310f000e560481c1d41d942240c107008054081e6102812103440c00b10100d07059072001a004184850010341409074410201810344d03100c9901380700c2403000090038001000c100c80b49596901c0c844c82507041000840d03001c242694410405a4001c1002070310b0800500e0703091000b1a2001e48615640c2c0c035132414025841114083d244002801041c1c09a02d907002c1d0602c9030003582100c01c125110344880042031019100c1e80d411300500820b0100c9002d441c810b0410030050b0b04408141d00c05048045100300303205848418191b023109a0510029030300c518060000e141188040c8890380c0c507600c980c603424106018401e282500d072114001903460302c46140c070046521000811200d01d0138144691100015030b0a506048441004a1702c079140400548041010b00c040c1050101c2110300c0700014a60a1111541c0201040d509041640d138103000f2030501005100 = true := by decide +kernel

theorem cover : BRFrame.Cov 956474820 956654676 := by
  have h0 := BRFrame.cov_init 956474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 956474820 ≤ n) (h2 : n < 956654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
