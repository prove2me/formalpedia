-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1959
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:18:09.483377+00:00
-- url     : https://prove2.me/submissions/ad842131-7046-49a9-91d5-613b196d4813

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 352158273 ≤ n < 352338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 352159523 1250 352158273 352158277
    0x30302060a0204080c0f2e1b12080928020f0409030207090b0a1703220e1504090204091a070c0807080a09050d0c14010e101d04060b 58
    0x110054494580451900e220500940c0c050b2612600200300340070782581002031180031850455001150110040740b140b1181304400c0645070380c9041084015001c607401060244031180020340f5030302036440c05000074680c4018030301c10700f090b10b850b560589030508075604100b00468020384040340c041c189042a00080302e8080c0c0c0c18021030309240d001d241c3c0801d11040d1154000000c005800c0842c050080e0007555020221a410160025444540b02c1c2c845040a003071200d8408015800400c1e91520354410210406a58600d455041e004034601540f0a0b00341401400707030701000d0803207041603850303844950003250800e0700200107201c41c810908202072401d0f001c11600e032000360500000740940c0c0c01203100d0140d071a880040780746000c000c0d4460300c3c1c0503041038110800f042440000000c55075100034101d10842d0068042d0b45106140c940e64081b07c1c11600300744c50520490808600540d83e900d00e00b000907513581d09107800450328910090b00e02441d1400c620ba805860103102003001413003800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 352160773 1250 352159523 352159529
    0x317010305060108060a020702130903110d080603190c0b0903150705030405010b01021c0804050c04090302030d05090705060919050301061401080603010203040c031205070f03080708150312090a031a01 88
    0x4c1a11078680314100100103a03c1164006504143c01031101c212090281d030001d215035001340382040a040a64007401e042c401ca511f140d03c0000c00d00401e0081d03034607060020b001c851402c44002084645942e4603000a1201481040b040201c0400ca00910352401d0140100d403210810348090a450b100001801640054900795503a41c42c02c0700620a0354000143c00301481441130444010441e0245c00711950b440040013203400d03005040c064002a19580a10381e030180c840d8018548a40580c1000d40480d40c00500c001c41650007202e00300526107424048668141040c0d034110030094002c0c003410341e45180d42d0f00c4550150301c3d0420004248840300144d10b10710f2801d90700c0d10b2035038035107004141c00c0c0d000589014256035410041000018406400c0450002c11402d02c41e041c00499100c18a450740684020340108901804108601c0e50081c652540f10000d818100c00e00c0034400d005c00d0b1f079014001c1a242c6106000a01015155244400a8002c43d48101013004800c8a407098a0b60076200384 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 352162023 1250 352160773 352160789
    0x41d0a0f1a070c030e0907230c010c02031209010b1f0c05060126030f0315030a061401090501050603090c010f090323010b22051e10080705010e0a1203170103050601 72
    0x80840045182440006c1e0003800503588440c030054a83d403c10312101010644522080710410030108a500c0030f00481030400c02540207140c403034042a2507014900c01c004d2582205924003200e00364039a0712450032110f00240c000038808200d04214080c0da16800d080d0010300701c0d204a40001880800041122400e00355942e1900c201031011040035590f03001c0c00d5140318882c03000b400040c8919074118250001c030b110040407201ea09495450344c3d01242c401e00c104482c0d5103040001400302035260b01a250042c07800b9500107255142080100341c03202049040d8604001201041e48480f038454098030000e10381060342c4810000d0416007451a0712482c000c48401c1d5402c14000a18920348183d00021001d0342d01801c004807154001e505001b40001043d400700708004564040304030210929192040e90405004126541800081880d0803019440315042044400c3c80904985503c0544000c50390170503044180e440c500e25064900c401840c1c803000702c8844980002041c4400000d000d03048030002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 352163273 1250 352162023 352162037
    0x5090a0903110a03080c0702030304150908160531020a020102190212121b0706090b011505041e08030309060a11070b04030518040218041d0a0f1a070c03 67
    0x401c0b588034009494043c000c40c600c1c1000a05520705c0714020004148000e00341ea146c25110a40321101c000d1042c2907400003035256000384018002000300110345142c59034120702052411000480e40310f4691588141100c2104044510302810110b43c00010010031065407114140c4000a000f034101c14049002c481c0d1046000e5107240c0007040106140040725046440c08420b200400d0200c000a0940c1301c905d80d1076904462110752010107048103501c80e0307001180c0b4409606140d110618180c0004829010b605070440c21141c101c400ca03030484030010b280d600c41c08102d08011039498400ea100c0030050000004012a000010404601c11200700508000d00103d0054480071030007950750084c02c00300c0b840c0c0400c0100c0d029a0250070f900724140e54441e004214803001c241a030300840e1007500c00f01780c0e04445903060316141c014600184000d000c0705291140000c40305d0303030301c042401700646441c0382e000b5118244807400307401400781c800005401e4030301e00303011100521703091f20702100b50001804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 352164523 1250 352163273 352163297
    0xa0c090f0f02030f011203090305071203021b13180b040305070b011401140c0f070303020706030c0c02030d032f0403060f0203060a30050c092503020a050405090a0903 73
    0x78920a40c2e0083c1e248407410301c502d0382444841100c0c1d0702c010009501b03101b0102c00001c0000c81c104010000f41850541c3c00c0311010840c03030003916040c0b040303e0300d40d0411913407520041c4070f03101e6140040344031040f12808114444030b0103903182260014003016207074003010390800060542240080c500d1901c60785540c480e030fa81e94000400b43c4036009020f0b90002d500702c80b0a902c4407200c00064242e101100043e900d4140c2c81940c1245012900d0b801100940c220070320401c0101e0b0144240c07000c0541d14108185074660f164002501c0380050705a41003407658503800102601d030000b10030500409800c4030b507100c1401d502c1c0c11141c1034001c0d12084844509118109101c00414025603001d180090b10314800c0340e0404441032030306032000c0c05132401d801c8a003030480b03802400c4210030160103005801030551030307000703100340f00c1e6503a001000d2315a2040c21044144480c0c43c50200000d242140d403400503240c00c0524011601c0b0300c5642d204035404403c00041c01841900f59004a914034800e40780c00c3d0180003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 352165773 1250 352164523 352164551
    0x1406040c061407060f0b10021b010908030f13050604030309030c0f0b090d021212090a0b0c030406050d0902101e14120a09050307050f0c04140109090201020a0c090f 72
    0x1d074510040c511100c040c041180010307070641003c2c4c1781440b203c8010407011004008100e08030310340482e4800503440030006a0110340007a0380c5112200c020710b0004915810524003582d07034401d001c000002d01c1000604802c0756036094640001030000104a140d60f2035a03420300030600344087c00280c410558503800000c0308c0840c06030b4001250038000c140c60a00800b0410420004010700080e0780012801d0000e04e54010b041c400144501d05028000361204810400d2102c803040d1900044c100c481d08001100c0c2c410000030540e000c4441c0c9151480e6505c5c44900c1920140803940002034001000040d10030080b43c202d1a10f000809a4030064100401070100865056216078410506084204100c1401e0040503403e44ea100400d4000072620510300e95803107203594030061040d10107070054040d0004104051011190a40040302e0a00c4541ca04518941104a043c4a104002c5a0b034a09c0b0404590082c40022038450304517000c40700c500c2e41c0c0c00d20a409041c00f60490020a0b260010f0048441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 352167023 1250 352165773 352165787
    0x170a0c0c02010509030a12030e0c03032a010b060f040312022b0215090102070309081f0c020c2d04140a0504150903090617150f0d1406040c06 62
    0x15499920314551a080c0d40041d141e9a015468468040c041c0c10350750008204010380e05040d408559800107030004007040480e08040c0c03c5000c0501ca90000c00c82c00e01c509400b0314260819851a0100d801660b102c15102030040c240b0414440c0c1001021403210403031000310300a8400c032070082424107100c00c1000c00807a200c1da0641c4006110450440d00b0b0a4502c5140400d800c0c0902c03140121802c0c1c6528075644030f94044126016102c0b40c0d00010f01c0410164092500c40042428000902e0105000d01284040c05800c1d219010800e03a152200509a403003000030b808400405411681140011071666001e904503865103041451000305080d9242450b2144014010346440711020039220031041c2406004044c00a80d201400f18500000c800014403548805030710030b4882556262421070082d0444001c1031006014989000c20401d00307513a5041d071104418070440c0c1100d0120311417800a03102207400740300605100d50304054209480740c0041c4840c011070060312070b880c419a030341c00c04031242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 352168273 1250 352167023 352167041
    0x14070b0a09140105100e1b0301030c1d0f0103060b06190201060819050307060507030b150a020601090501030218040302160e010503070f06020d0c0503070204050f060a0905220819170a 80
    0x980c5e0210411010348543e6500d50405000842130f04000c500844205490b0401e81056500c90051803040280f50180d020b00d0f210842984e0311721845181c60b070b1450b4401401448094900c0c2d441e400003456079900d500c00c585283c0040c0c8101c020500c2c4e41c04000f0b0003080e03c1c0c003c1d8525445003c045c0488401c840408041161703103c0000e40c64405c071a520900a0b24015001806158594030341e202d80f9600d001408207102d02031652140c0f2115140d000034541601070b80810420b43c646801400940c0b208102c242c03085140e00c064404940f00c0c4e11b400c038a44109403803108051150203601086150603021014100d40c6c088045520081c0c88071600b4441e42000d1041c0c0e00541c1c01303240c0c031445641c090280190164040c3d4140c03802d000ea181c02003020342d20300f04c5150346841024010030055283c1142e0207405807046500c200005d14191071000c101c0d1100360310301d545903503040c5926410030090800302d400c1b008454048450b400300c4d0036800f0701480b080340600084900f402c000100841082d101d12545 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 352169523 1250 352168273 352168291
    0x6072402031302010c020312070b0f070c02060412111302090112021206100c02180604150302090c1c090c0302120a170a02010f0e030c10060807050114070b0a09140105 73
    0x38480c2c4542c010b4400c0507044004980500600808203401d400038005003120350700800714501c0a29201070080480e4074010065014040d15007120f0025855540c192400c0d2010580d040a50300d015080c110403003460900349644c04000203070703100041c98080d00a040348d06001e1701d50118130005c40841d032080c3e00416240340400c010b000000b801c580343c0300d010301015000908028401c10b07069008940c010840c20041e8080200190921450342040e1269000e074040110a80000d903046a00050701034801520601807090b010446c0400400b013a800d40ba00440307081020024400c1d80c2c5840d2220103098881a84928001000d0704647d110101d1a801c035640d002148003041c01000151002503001030408200b15907865a02d00d9100f11184990070180381c41c48000c50b10b41207000189807600d460719400d45441403e1840421070154000341a00584e8000d00b0041c00b400c41c10b402d813100300e004120001d0905014441440501019540b085a54500500f4440412a403500307009098400a40722254 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 352170773 1250 352169523 352169551
    0x60305070f0518280e1c020a0c060503070203130f050f010c050304030803130b0703060f0f030b0c030603120a03060f0905010e060d0203010e011a030d030e0a03120b0607240203 77
    0x404140303084020719403401100f0010780c4140c4000010801c03a111001178100b2988039001003404070002c40f4151403141002c0c4006d00e42d1881d1540d40c201084828412b030b20034800c02001250106000740b003518010710b50184012181c96642c0c00b03ca20080c01c502c201800b5800107502d0600039442004084a01c68201000b10b1400e4a903a48104403984001e00c943d110035106141d030f000080d406040d082c040c6186d0307980890250b08020303140300c100390254001c010030001070728100001000040d1099228040071032260700e81e03a419002c00c0c00c004210601c5200f034080011103600329a096800b0f9001c2e87e050f0b000030640f660720303602200200e40080c0540802c041300c11000892034508030780301400b103a00c09000404d00c00c4c0500016825202c4107910b2100103091551041541d060410030751840f40f003285410f10020301c00542040c7c0b00e080481014041242c007005440040300c90b9003081220705805000c2341c0ea260300900344401c84414a0064840500c0c007244000c0d60304416000340c9014040340086c40d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 352172023 1250 352170773 352170781
    0x403060b0a0609171e030706141012080d0207081902031c0b0a0b04090b040506041506050a05040e010b0702010e09061c060608010c02030c0d020f060721060305070f0518 74
    0x210313201c10426030310000c0c450400d0a000000381ca804800782c0c05080801140c80380e41c6894800709a5145030a41440c010640c020009012804130070762040358202001c00c00201203071700b0117008900c959044034480500018140040104480040400c040c0e60342240041c08071820f002ca8423446504206046004440a154020a1158007503c21014000e0144825540d142c10100282d08140c0c4a401d400307580d4030000c00385042c140515031303105d5003c8070b003040244007070001c3da0aa03c03079600428081040c042503820240b0f00440845004d413950700703c014500c2d031b55604000d405a000d808101c0c005019a00b40c141c85051030b030616400303000b0041c6109625880410200f0391040c0b000350607242d0700c1d107c00340001c10f12820700c1030084c0003d07141d02071b43d6503062000025203070201b08100c4c80110340c070140f410940840301140705074200805d890b04c0701d40002181c4002111511111802071042d10b0400d0001c03c020300020b6080840f100e00442e03a074155600c9041100c03e060b000c8000340840d41000001f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 352173273 1250 352172023 352172039
    0x30b0909062203120c120e070504140105031b0d0b090c010905120709020d060906030b041707050325060e0f060702010c08060d02030a0516090f091e020a08120403060b0a0609 76
    0x4205c0c4101c0c038070300b00301c00401091402003a1091700800840d940c028510520890510b0f020310851f80070100043d10555242401096941d0a0031403406d00300038081114503a9956420390380568150000d21034451030402d0014551500d844008a5011654500d80081c143c208030404905102079034004c3c1900f6840c00030b8981c06503003c00481c141e1940d45120201b10503d00b407283d00084d602490a02c641c078a45440d04020010036440305e2000b01d84144050130028600100711821001c09280918049488603080c0408080a0304010720042c245410300b0040031000601d41021000c450440b4030b1921514800c0e070032600348040800005403a800010f0482c100700c1c2030302e001d60348080d08807488680162243c80c10040d003011000201e022410302003190b100507004540c41c109021008000d0f00d5040d685101c3c011007001c0301c80c01203c0034441800155941e40c0d0083d001042d50a041d82c103001641041da41c00c036070081c0403c4803400d207071600e00d180b0340c10325005d0a002d950321a00c606544608041c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 352174523 1250 352173273 352173281
    0x1140d150c0e030d0302030108011808190c080a0e01030b0103230916060203040614040605030708061809010b03010e070636152319030b090906220312 66
    0x58002444021040e1200c5a00c08200580c601c03201342c0e07001a01d035414010340074251f5039482e82020b036114080b0b01180102e0070300f108880e100c1174040d82c40c0703019416084040e10407000d00b510152520001042200e1100e4000c0e4400ba2501c500f41e0702080313100018001941107481001c44000e610031030074405c0c0007140c0e4a01140780c0000d20103085442c480c4615031003400c5581c00b80c002d40c0068002150801c240354100c21034140c0203904540c0c050500c1d0074110000c0403400010074280400c0803420108403141c503540c0b00c03510318445200444556141c50103100d8003030030040441c54082c2d071800901c030011240100c3c41c03000747c80346547d820380d95418400d411041d0b10b400c0c100307003420320741086992a00030304940841c5004001c098900340c1800d100c05805004600b83c41c00502d00b6200c1e80d030a00444001d03902c00c950403207070300210100d0640c140d50360403002044405001c5d03400030210411b00c6042c101c0095054810001d680f441c0000c850314041e814000d101c904001400304540c080c0d40c407140320450308 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 352175773 1250 352174523 352174541
    0x80406031a0a08010905210a0f030e1222050f0f0303130303020a020108070519030213081e060702030c19020f06210106020712060b180109020301140d15 67
    0x10301d01c101e214261000855820003a440b200440e035640301d4030410441e0030301a942032000e03041ea080d451071b07091404105044c410188564100540034000305d000b135020380d210300b00c500d003003101301e0740b403005040040d52107603204070264021058803002120002210a01c0f400940300054911440b242c002401e114407207040d0491030b90306000034041200c0c90041c010204c2c0080d4025801091040000c0c0009044090081c0c414010450100544000500c2412950807140a1803070f00581c0c3d0201003802250400e15a00030420f03c0c0036041440a158203907405814081070800c082e03e88a407144503042e603a80c27041e1484020300d41c1110903072103595010183e14010550000d025050941a10b600140f41c031703444000055603c41c3e900095440ba000400003140c05407800d800141000d9042c011802d81101350320f68010065a2210301c9295261136041c60300b915410203485018031035844d10000001b0750001d028220b00110103540c85507141c42d01d43c400030301c02e80d001007180d803010b41040752001c01b80c1a0a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 352177023 1250 352175773 352175801
    0x605060f160f030302180f0f0f03070b04080f010f050f0f0a2a0906030608070902180303040f06020c01020105040c0e1b0f0a020c03030405011e030b190e07080408040603 74
    0x30200010940091030210030b64402e40d401a6242c06035800d0181c40e0440da80c4041c015015003a05440307603100c0c60b801403030f4201c089903094a158603400009282043c82c1c0c100020245000c034001901c020001416210014140300030300000300400c81410494804640700741c5100c1040002c03c07080707507000c6052508090f0501e804603507040c5103010164596031950202c83e05612502d80081003507403180b503240c00350505141c1402154584a240343d074034546400741000580d4001000c40b401c02003107902903003808018041d02c4d100d85d07407a4000401905e0178461400580a00c01c1c40701c0c61907106100da6032049074055130b8005994103150728004a0031700100105100e01030ba03001c00036107009080203000110410079102d90350395101c4000078100f589000000c0e01a0340103200502841c1c2c1c02c840c1c00802801e003e00160001020320300101c0262122000389500100c040c0c0c4000200341d040b0000780c050741c10341c070134202c515181c14000719480802154042c0c6000030900c01480034500c0382e0001141d4881c91 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 352178273 1250 352177023 352177057
    0x2070804050909160b0301050f0d0213020a030f09050c0a1508070c15062403021c05060d14010f0c08070909050c130e040b010b0f070308100803030708010503100605060f 74
    0x1405402c8404d403039400a211030351300070004000c24a0403108400c6070180540d500405200c1540c0030403810800c2101d00341c01590045807510100d4425403081031590700300c18007844142e1050a1168841c180c41c000a40141e902c4200451501100d480c00400742101d5950f050f40fa0f55007440469110388040c0342201c080318100d10107000406907001d410301a0850b40300d00c8450703441c103102054070310250158000034980180504801810a03e00da0316018003000c40100e415664800002d8107242a00d000420941320110b120846050541c081d0341c8140b8512170400591403810810365089004482c088009600e8000c01d0108c6416900700507000b9401c08000e50401c1100b041006072604150040800c0b510200100400d100d0320125917801032030843d0109142180c060042041807080d010003038240300c444004140c042d202d00c0d034100300521240d0107580e00e84c1403411004203d0030081c4266442481042444141c0300d00a1042000301d800013400a481c0440030302200c0000e03006456504400018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 352179523 1250 352178273 352178293
    0x2060c0303150a1a030a0209060712080702070e040b0414100f0b0f060403080f13030206210c091e03030c030403030c060f1407080405120a0e011202070804050909 71
    0x4200040c50103800c00310340005002c0c0c40340c018009040081d034049a8075091101d03280190020003821a0b401002c3c000d00503a56070504c00c0801c01d54030560900925003041d035418030300e0700d42e0b100308214041da5a603825203a80556520300720123501002c1e50003616103046840031600041c1800c80c544003841142c01941c1241030700d02c1c11003045034428804900c102d03440f008076807607500d0040c0900c0c40055040b1170060030075045440e03103545401400354045d02c80100040045044810080c0c120055034024103540d95603480c00032010070fa543e0003603440c41201c40d0101086904d42d20302d050300d004103000350014010700080c4841200b4009036034482074040c0002c0021103000c1000f40b00a001441c041d845000403030460749000300440300142581074240303180006104089258144054000f5020710381014a500d81e1b0030680d060210040403c0ca600c5400181400002c1c0c00c60a01644200c0903281ea41425540b480100b0136481011401022180108011710a525140c1c52094110aa840880d0301c0800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 352180773 1250 352179523 352179547
    0xb040609060b0c060a060e0105120c03031b060a0902010206070309020f060a050a02060f0709060c02011205243312010305070f0909051507180e01050108090304080d08040206 76
    0x1e02500300d0320003038000240c03203d00001c040082a4100c0c402403030400081e407916080303588904060003405d00c10700501c2086025100c0401140700e01840090a03a940c032000c0c03107131420011080c908207c1d4a40281000a9088401d070312030040142d40680181440e0303a51503c040b40140040c000803640302004944042154480c03402401c80c211094607150394034000914041d00d007601c014484400e0304030a03070400c40402e0340030000204880190906805c1d400242c80140e07001a0321440c10481c45103040204010644c0c1c408a03802005040d00d40850741807000403c0c48045800c084545200d510b21011207943c001100c42180e5032460041c40c0c0340d040503418420f0f101c814070281d00540e080e50000b641440390040002161005201c005802c120510440c0c0d54242c40d8045a5241c4001c400c2540004103850f016440c04062202201d22108800c2d0b00c41c4a865039030a028091280001c07945000243c506800104682c16102510028000d14101c10012185018018400c0342c1024040c07204450010f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 352182023 1250 352180773 352180781
    0x3020a1203020a0b09070b0d0c02060105030610030b0a0f02070303090b070e010c02210f010b090c19032c0f0601270e0a020d030c0302120f0f090d1202030403030e1504090b040609 78
    0x44c800d0000c80c0001b09c000000b403415030182c01041c4a90484403d03ca88800d1050001c021a54810034800380c40d520310001d04003d0150038604c6071407500008200b02015815400350b0191032107910300326807580700c03d1411506002076408450106150708180e05c0586800c80c0c1c0c4403810a190010510102c044074803c5051081881d0905410ba441c1c004603041481d098111a90204100c600340381000204040380402c148410325031001c0c941c6d500d20481c500c00f0184071302007458009025a640900d002503000d55555106600e40c4900c1c000c43c4008110003d043c0048a40c1440310602000e41c2a00d14801c0d2005290302500d0098910540c40c0d01001602c44542c242911402901d80c80c0c0c654405040103810626182000c26602500300082850903100e04250386000501d001741a489584140c081201c6204100c8007418110a04040340300203a400002007080d24440d03075501c1612840d4106001040f4894100d5107035a6400b07000070b01069426a1010103008002440880d13115580c4031400e00722 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 352183273 1250 352182023 352182037
    0x7050111100c0804170a1d040b06160c0902090d150f0f0608011404031209020d050f0601061202040b030a0207060b090103062306090c031b040f03020a1203020a0b09070b 74
    0x400c8014080000748030321342c111803502821740c80c078044c9000103201d0001d151058070300461940350314048807507046480d0b83d440f607081d0400c0604119590107412496071000049188100c5044100800c0440c0084e524001d8034411800074042c034800b080c1340d5442000701c80c9501921030b4038a94078000c01c0106c486030b000e0220a600c82180028103d8142440c150075552904d0004c0303d8020f0103024040000d601c01082101c0604120001420981c144001540e0140f1000b020b00b01d03100d03c1100c0c469090000c581203048806545500c0352110490080030164040c034410107107103040a200003010f84c07840c1d4004000072407082d070000038594800d80c00507460030400c0e0000d842131a0745507010310410f0001c07051040d0622004100c40660b00d8250006615500000e00c2051030302404400b140100c100300700c60300440c2c0180e400b419100c03615900081d5003070850784802c1c7e109111032840041c00080d0a0a80300ac0143c2681c0503040103200307a141d50ba04004050300d10491445501800904680008041c2c10a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 352184523 1250 352183273 352183277
    0xb040306020f160c05100c0f08130b0d02090901050102060103200a0305010c08090c040b0d11060c07060e01120221070e0a08060a1401060207180207021f14040807050111100c 76
    0x207036051900f48074011b295418080c0034001100400d00100c1c814110b80fa90069105150355540c2e081e00070400f010030300d5a8001e0380080030105050f80c24116a0300075010751401a01c1412140e80d0301c030012661908203210280500a00203400300411840004141400c6806000c4900c0150760303a0700c003403c5400c60042000083e02d100103000c0900c80074400c8108006046509104424000c2c0c005030b420440130348028404000e0301070a01164403844280c66412074041d06035401c2565402c0050b1100c5032040d143e80c006541466a56601c10b840d20990b82d03004c04200b10304e02e0300600f55891031400c00001e0241c0040c401c80c0303143d0b9403c44e6603042c03015020f400307468085e160905100190401341c903a040c080d800c00b80504001405603a500156240c100c078403441501c0e50019100401500920580c803010f50000b0b01c802c03a44268404804801807640c0881c1c1e105100c078a8415140410740c0564059018160440002008150712520300010002d80841c1071715000c1c0a81008901101d004000e4200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 352185773 1250 352184523 352184543
    0x7050712051506120d120b090f1905070e3010050606091f0e060703030b0102160e07050c0106180c0909050403020606120f0f030c0c0a0b040306020f16 66
    0xb8007510001c0200340c21820a403020340204c0e0621011a440d080c000c00074030100030854401c403040c03090542005c80c9017807001e041d007101410a4040030011401c21a850502806010b07411602e00b0a544030b0700384201c01076030740c95882d00104010040c80c004500824a42d0345d041f00083c01d0100b91030100480c001d0a114018500c0c065004c00600c10760340010591440386a06200e40000343d203c0b501094001c03401c4079084d40c3e080e2500345066403080002c41d403180c1c00100120301281016056800410030410076000c980d529a41000741039a0303004580500100081a0300100c2c1070207000700c0c00342c4044106000003007401511890310668150550113254401c0ba280c201c90000c983d00440d980001d801d5482c070510240c80c040d2030195490038042c08660086100014000c3e10703000501050a098225806a03820b2201c00c15006d0364a40103030601714214003440c49007151915140070880300312041207c0442c142851516060001d401c2603482c5948004108031584070754109a8101d0b041d240309104240c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 352187023 1250 352185773 352185793
    0x603070309050d090f0611060106030e030c030f040306290906030c120a0b0105010908190303021207020109140307050613020303071211070e010b030610031116020f06030112080705071205 82
    0xc005c2411a42c0a003061080c00c200e104d2505901144060664185040114000d00a01c5c60b052440c4182d044200d0780e400080390240d103240700e080c000e0044070301480d4244060114a0343e180340202d4800c150200da640100c513000d0b040d00748100015408080201620301e1090b404003c00d1100c0e403054400c020320b810800c000001c0145001d06940580000c1c83c0408107541081800755039a40b41e1001d4a4840e1000d07940e40042600c6a0111000a0310f03161103a0103904142c40064003800c03042e0000c440d99620707102501c000c0d040c00801c0c0c41c0e2954000c070081a45483e0864842030b0003248440598060108001200104a42013604039140005640381003c503006a4811803c000158020354450400304004001071214201501e402035021140c00c442c81011002c2a40207080040e05858010800b085850031a8801c0d041091068020348404c0101030341c500804c0841c1c8024012180e0300daa110308038401059a04016022540c0326070100c499240c0c49002560502e1900350084565502042c946 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 352188273 1250 352187023 352187039
    0x909110405031e03030406050c04030c0608060a080c0307060e0604080d09150219110406030b100801060b07021014130b1c1401051e130b01020d02030f04050603070309050d09 76
    0x5441c1103510f41d07580d40c40b0305034908003180c1c13a480003030005840c240c2c9400201e0808096042190002d40c0d2080d078045c1d01940d5032002429141c0100c0300180306000005000400040210f8031080e8000020060503185087c03030300650710000240501900000c3c203100104a699040060200c01912601d640008130310b0714000040727641e5500a00710442d0041c092600c0e41d10600d088050200750302c03030504204045d9100105004003039a03440a480e510500701881400040319840205a446c0c000080c00f02a8440500b0040781c403e801000750040c410320800e00d125841500d4410000c0d100003403451030180000004035101d00c094000070030060001403510090021003266165007416100c060180c0d400c00e1440503400e0005109a501174100709500620344542c0200c400b20f4180c008240303178111020702c242d05000781094040640035100b031b0071111442030f0000003540d04000090980c640b81c1400c00381071001c3e076003024001ca400d00d51101e00c0480020400d2210100c000c1e400d0751500d50591911f4070f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 352189523 1250 352188273 352188283
    0x16020a06230421050a0c061d150f0a0516120e030c030a03051803010914150906010324290a12060504021f03050901050f01081b01090911040503 63
    0x10441108070100000c1094000403020b0718890040301001e05100d0a650401d81d0400310208801031041850003004602950000d10036880d10800e2100e00c0c041c2d2080340103000d04802d100140c07a10040c004e106c40544000c0100040407808d410b450100e0809080304005444e444140c0011200c00c540490319203041e40c0e008083c0050000c1c00c0b0020a070050313502021030740b00c0741c0346003001c1d0400400040781c030781c402c08454001d030007048003400070010881039041480000040ca0500c2a05024407820b41c643c0d010300340100c42c0103184400240203540d1840d0352307000381d0303a0007011540c005403251007403040880c00a10519200108010300d0148900804100f00204014060b0180c0301e2000c4420910510404c01c2248041e19805100000d06459500000d42220b0803e1200ba403088d551442400c020340e41500701501444249000740025100d03040485074802c001d004260386648010b4207000d2102202e01003d074080018180000a192034413091001c0d01c6140c00000c20f083d900080801060400f001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 352190773 1250 352189523 352189577
    0xd0c15030e060a020a1707110d020106090b0108011d072c040b060c0a060509010905010e0a061a0f060d32090a032f0a030806120f03040b16020a06 64
    0x3200f14903298074100050900c031b01802c00c6280d2982d6480c0015059401085643c2000c40751500322900058001002800780281d402910042420505e40840b10750286180a05903000814621407020040c180b660100c04010f001c10208800004400d40310b504607000342c8100030346500c045070044800c9050000740c0d0301300846131b401101c04205480503070002046030110164026800b00b0a9107030003a186002d821074800c0070b0110f52038200034103200000010340c50000c622507082402480e1000500c06c418020701880b49401003000340501016103440d80041003001a0200d000542203209500002c40b1405600403001c2c1c00d8410844445420002959a80c00911400101f40480b4550b5004103181340401d0420007035030103840003c0d04d10901c0100310781c008542c4802c49480b0111410020013040084d9081c5000e825210302c16a0307400b1021503221100b040b103400651416107400040758091340f141030400d04070415101c02d980141c0d52010400c004091030b59604103010140301c0d8006c00020f00c14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 352192023 1250 352190773 352190791
    0x19021306081609120c05030609070512030c030306040504021804050609120c070306021303080d05040209150114031f090e010510030c06120603020d0c080d020d05090d0c15030e06 78
    0x3800c1c00b5540c075032281030314082d9464220031140b500c21501c0c098440d1500c60300401c2c1c1c10300070300d410000900c500150038011601c0458528459824000c0c3d103544130f1080944101240c0c000308006000383c1001d4001c150418409001241c0c0341a05041c010000790058070211120342101e411322039a80b41c00c0000c0311290350b04100311850300b8820310f0869521001c6100003042e07107401190040403e00c081352440000d580000c103090303039031510000800007407a0440c0d00303c1c030550460002c0b6802c07003415a2101006081030311140c031a0014610980c0098200420002035481150b02e4011903040c200000c400404c40d203000821425542000d0f1420740b0402000783c1a0103420030000c202288003100000c04031011070400b00800c070402c9060002500d401c0e0400380d0004120f007018400c1044242c1d440080b1945c200940314480f43c0d0b42004c036110a4407580f040002030041c00311a886140c46107aa4600031701c9150310500c1650b5400d809030b41c28a0b02002d14020030f03510704403100c1c42d074018000654011102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 352193273 1250 352192023 352192051
    0x8040308090313150c1401090201031a09070305062209060f050c0a080c27011107050a0504050a0f0903090806010f0312120f0f060503070b0906030106081902130608 72
    0x10f00e001101142c0510800064440310408a54458025141803402d00e8001c4034000780d000c40c03420b00901a0615181c100c0c0003915002d12880078400c071850011103d40010008240d80d1101003007140509405005254084448407804030542e030340b5200707501441415040410780407081c2c1400303003c541d1181c2e0451413031420701c801c01c001c90340c90340205d41c95000241080702a9844882c1e20050134060300801a18000b0030400f02e5085603207000c00208140e900b6078420b08184009514103407120283d12a280d00444075072030601040c5826041254050b0383c1c00300000da00b421507203441056521107501600801d4011000307011040c014005075024026103401042e205103959038583d40007000c03400881c00c21103652602060440309400c4100b0200e1490f60510550301c1e040440340050105108151091080c441c0c00140001032000f0380d815081c0041065003168a0b004060740e800c0030040000ca4002000407a80003c030005102501c03c46e07040b02040024281403e6001d4812080605644219205 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 352194523 1250 352193273 352193287
    0xa17010f050603241c120201060b0306040f02070218090f0c0102030d0c0c022809060308070206070206040906080a020a0b090a1401090b040e0a200301060c170a080403080903 76
    0x180c2c0c41165002009100700c2080c1c01d0b9222180200400344864241d84031000c90385140c151306194010520361402074001c100061000a016400c03942907200300c4a030501e003400007440d43e240c035038401c084442001c0d8015151201a5000491202c02010b4500d00060f1311802e00810390b0080298100c042c5e8154010b1826440d4000080c0d540c3c0500382051440584030026100400d21400c0f072150000e030301a08000003074400c01c1107003880141d810b0b640441042d03034580010341368000d8000c40c01120b8011640034501030440c4c0a000443e8403800341070384c0140b0204030010706513410f4072404000f049190050310f4041010f2042200810195000640c0311000348900003240c1e590040d00000c903610010303807001c5620803a0060f0f603070403110743c44024111004030340044c0021000c03145900c20342c007400040101d40c100000681b504c02642d191803500c01418030051003d14001c0c0703c2c484e0403a0249043c20070429080803614210740c4000f500c1d4000408080c00d0000b013580144640b5042000c0d40040c40c10300d40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 352195773 1250 352194523 352194529
    0xc071206200f030c040b0724090b0406090813150e04060b0d05041509050a0204050106050703050d110f0a030b0a1403190218041406070c030e040c11030a17010f05 71
    0x141c9110040802e07000000c6018a440641103400510645590a0310b80d640b030309001d4840c1449440080000d80205034600850810748146050140d000c2d004105580b00d03501c0e990018804150200c62510003003040c2d00b11040115982402001018080c15036400c0d00c0c0d00040080c080030ba081030181d401c3c52814070401d03182c40c0548804500c44080041ca5540c0d0b81400c0c4840a00c3d5a24620224500407190f001d0060110768985028000c0e1003e2003183d070703600700440d4580b095100144c000751040c4815051030105800103107038440101081400c189841044003516071024a0030808a40d5500481d5558203044c2e4407070009154426080e0f110340341034000300c0d40743c00208000b031518550a6003142c04540d40c01124102c02c880314a106081490302d45000c0f800c0503186240c2c0070462180b6030005d03540e24450300744010704560585c3c0720b216248041c0c0502c4003400ca0b10280c3d009200c0c449100c000d08400c100043c0c41800c2d4150380d8a0710700907038101c009a09810680015006003803145041c08942c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 352197023 1250 352195773 352195777
    0xe0106051c02010e100507020411070210120603050610090b040c090b070203330a051005211605040c030b06041505130602060403080c03060a050f0103020c07120620 72
    0x440c1d1500308001607255880121140c104c007000956000c180300017007a100c00d9110010f811414800d440c20130400c1c5000f074955100303000d4030a00075030280c014000c094109205500482c109014800c001c284c0b82c2d100e0356014105002120003202c524403404042161900b2409000d05454050f00c00300a003806650b002001a8014060390410500000c1e011003151010001e8501d50a50703041200d0b0040221204502c0400e07020304e02c44030071035180c0f02241d62135480303100740f0307002c0c001001900031414a0207007070002ca1101e501504001041c400b074a0000c501045c001da81400b0304400c030303101090b82082c0400c01101d01a140900c1014503016060f400d030b4881e001110300f40c81d400b040c0206100320341b1004135007030f01c60b2445508030100c0f451000240c1d0f5800052041c0168131a0701c5654881c2d40d002c4424000340003c85034140d010350825001c00031818444908011000185800351a100000d0074262034003180341e10444001034402040014041c007440740c245c044500380c040251080031154252018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 352198273 1250 352197023 352197049
    0x30a050f040f080307091703040f0e2404060b0705010c1b0c210210020309031e1c03020d0204060c1208040b1f0905090a03080c041a160b01180e010605 66
    0x190f800000400e0740c00d80540c1450300101811080ea00141d12500c1ca100d40701c1d08075100d0342d1644002c0c0d51011607003012084800d44500e4003142c001125161451003520100c0000d044107400543e10100828a0b802e110000d01e0301c580541c0010400c0f03139201d10028001030f040742d1181c6a09440c0c0803e0fa0021304039006090440340405c0d80310201c80c0c070703400e19002080140c0d6002035110703a205804203c5190080b001c1c10510204405541000800101101a081501c0d010400302e412100c1224a0440343c0350114141078030520f001030901e9048c40e40380b0200e0380700703400c5000882d41c00400c21b42000000086c070198007096284c903030090b00780b540e6030186121001d01520206942d01d020000c100e4003a002e41340003058100750a12050134200c0711035442d000404402d9000884500c0000c142c412030208440484500c494103c4002c0b2503040405400e4008030040c140700c000c14100710b0041070300c1c11203803400b921035103c241002451136802001201c41aa0a000d00d80e41050003c1103a9507a00364072240d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 352199523 1250 352198273 352198283
    0x181d060115050d111323010e0105030a0902120a02030127020111160b0301050f04110409110909010f0e09011812020a050d0f0e01090b041205070312020102030a050f040f 74
    0x160304000c1c25401c094120b4544856515601098044031141d60460304c00484c1c02025501d0311b11451071350b080440980f280c108034003064103070030401e51275442140155070054003400300240b50199980024285d0b411034841890650243c6203200540ca003c3c0324582a2200c42c03610020024400400009081c03494500641800900740b0481c20155042c0012114408071501542c20240c84480800182d0401c1c0503060080004407001c13201030800348a250080f08200403460306044c80c012080f0060006038183c080714086c18401c6c490300b616903400941c0a4100c007803c3c28400e500b012001c000c034140040002d03103140e04000740402c0b00410101c0907109a9048001c0c09030b40f480c44101a8503201e00c1000040952041e032001c0131202d03a200c21b010030a04140d60345c80c00e110000d14011194001c1e14001c0705460b40040104101298141141800300d80c4a030003a11031059a070349a10030011610f444941c007503500001001520f62962250b10341c040c2c2422607580080c10180c40e82d8550680000340181 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 352200773 1250 352199523 352199527
    0x9140c0f0c031c0b01050a020a0605090f0a060f0c050301030f0807140a0f0b33030717010b010e10052715040314030a050a0e0a181d06011505 62
    0xc108803051048550500800c070840b59a4010b40c4100308504060160b20002c00d40b80000511042d0310440803560484900e6004044070981c50311204001d11020b08250070610610032890342c4440d090110782081d07070051000003050003941420304143d074002e190040801800300b00600c00182c00211030000300303800c03041d469254889442c1203154210004110b2400388281c8515008000030041400c0c140ca101e007140348002e40303601c000b540b0140c9101880c0b40c10318080c50f10541d85500038071f5004801803c014102c42c0c0e1581c1e1819403000182c00c0760202c54099448141e0b40b042541c10443c4000a880103485c082c004809001c8010120b000d08507100420320305220100030081c000b600c128004003002000b8801d9030302065100181035003d0710007200c6240b20f5154003004900c0100c20b07980e6440c0c49883e00c600d04941d41008540c0c00d040c040701d07070354071580e445070115104980070010741840e004041300050800fa85075683c1d00d481c03000301c8038000643c44803005010305011031100302c2e407140c50380c03c22507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 352202023 1250 352200773 352200787
    0x4081b0d060b03030d1a1327080702181006050403030903030e040b030601060c11040c0806151306200a02030c060d0209040e03190305010e06060309010b09160909140c 73
    0x24194420740d108a0001401c04500301034004a030f0a01b180040421551013084615030807580060b00d4012501051000c42031040307521407100349800d125041c4c45005003505d00461079000594400c2c0d50301c000c04010a103842040500e0000030007c0014080500744207003411714550300141414080c3c000102000361600c44026103440300c1d0080c140000004040d0b4000d5a11500010701d44052400180c81e281c03541c0100103050b090600ca5805c5c081b803280d07120801d65540782d00340440c0d241141ca4159070180d00700300c0c409220410030101800340c589551017150164070a03501d046e1001d1600d440c1d211980180801100581e000502540c0c8030300b0503194142c0b28003081000754001d0056043c002e4005027408581440000003100800701b04454500d84a01000d110304120201c440034026400c082c6040340101c0c5440c41c004d4055907005224800104000c0c002401064072502c0a5130f0401e032010018501d050301541200c9450040c0150140403c01e013014040c04020040d0040d01c0c400c0301000001c6c0ea2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 352203273 1250 352202023 352202029
    0x70f17031c0c17040c060c03110601090b0a1d010501030e0703061e05090607020c0f1c03121d030304022701030f02031b060a2708010204081b0d060b 65
    0x80e0744444251903110402403400c030441c00203020b404100b440050820280d215450515084480c0545d0300300e1148540c46041001c1512a000400e00540c18060340b607482e4500c2210800c5194060b210040c0d002c0303500c410b00d9080c421004d005410080b0f94012342e59413a800700c41c480c00702604580003440c008ca26454412100360070a507060b00060062410281c080201c2c2d003030414410900c2d030260004100c41d80d180e45145403200b2068038204016007000a0f0b00c0303168a020395030200c014070001d101d10103102011010f05491174107140124041542c0c0b07102108400707020301c51a450301912103095045090405046605c070312000703000a11654441c00021401841c0b4420700c81d500015072840d514658480c105851840b441c01c100724400e104000751845003001d4040040c0d16503001400c15400c1c5085000c0c1030360307500141c0c50400301b04403000749081205500300d2026001424020001641c8900308484d00e801c0039100c011002c411005204102c0c01511181d4071280300ba0380188000071004028800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 352204523 1250 352203273 352203277
    0x3120c0711210a060203010f0603060807060e0411041502060612210c0303190b030309130902031002031303030e0c0117040602190e03100b01140d02071a0117070f1703 73
    0x4041210702c1410000300400001e40e000754103940e014408c412003150341d00760480c1611041c0c002c164031130704a40d000b00500d9026620b07484026400400c0412040314078010000c1e15003055003c24514503401c0c00c3c02401d01d0f01401103a4002d035003502d0500d80c00d40e041d40360361360b10001280e001029404030071505403150032140585001e140a0801e5a580e03040200e003c89809210300350825100d40740110003091490008220b88602d41d0142080031517900d0302c40e1103001000d92400a980500800c03041203a000c00500c011441411071040d01d0b045000c4a00300101110b185820501c41c98cc070100c00410140e07000b00f030301041681d4034240080c1c1581c507460403001030f0203204c00404699000c0c03001081116045418062440019012101008145650382c0c047d10750114045021030640a60400c80b20800c100801c890b00c040ba1025103404120b5840301640383c91f51801000d02440c403001481424100401046e070b5150b001e000f001450700b0460070b54a00c0d1100d1003444600d02c0f8144c000d00445c501802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 352205773 1250 352204523 352204579
    0x141603111b0f06010906080706261f180f20030717070f170609010312020a020303070609060b01020d0e0d020a0e0702010516180902070303110301030503120c0711 71
    0x3d8507141c0d6034910030030340500000d000b4804a400f46034804245c4c1881404e01c2c068801c1280045c0ea0b0110802019640e140c10203090403100000c2c03450441e0750155220001402000c40400303040507240800525011101c1c0e45c1c0c03103081d9080c28664545044100861800b1720203502c4440c0035900c0e16900801d56030140c03460714a0100c2000c038002c01c1841c40d0015081d021410f0180c03942060503403050032890420004440455106030428010f10106210307232005021038109004031580c91515800003440e503000850301712041a10f600b000400c10605004100c0e201e00207000811040c030900001600d80003c018800740620f80016185065507580d0001500034100c1c903190750420b04200c5002070280008648031800469003a41c00307444544075043c00600d07619030007074552416050a80c40406544465000e07000c042d00c66800450f45001c242c0150300841c0b0880080d40c1e02c02ca20728122240c0a0000e0072200354000030320110b4045158596407403405e020450f0300b500300141040071019402c1e0404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 352207023 1250 352205773 352205803
    0x9040605060612010e01150c0201020a1103120c030c0f07080622060f0902040515060715110c0a0510060f09051008010c0f080f04170c030d141603111b 66
    0x1000001e254801030010360690b0100d20b0210b0031f04102c66020b13150380c0c10301d49009005a01c250f62280114004103218656010018151440700030981c01b00c2d02c141d0031034040f41c0d199410010b00c100c1e00d020100000152b6400e000080d040c602e1a2030b034001d8440344020840d290308002c082c95080706418020311050340c10f900200c100a00030f80c50008800500450340c0403405186020041001d000c00d080001c40942c100428030b03441c10844c0e94802682c0001561086082078490b5602001c007195040a003080455420080c448a5040d0601e203282111410000d45d800d07180000500001c98801d000b03800761400150081842d46410241e00c14485456100c2d2a4039440d04054900155125001d000798480070f94a1503a1902c4041c468038000c0002d550040c40e240c10ac0c3c0d00e54a8a05030030020380842da001c803059904000148401c07205554054805056a40449081142809000c100c450744124549410030a42c031050700c160210b481034100780c042102c541c80107421101d80412400090349501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 352208273 1250 352207023 352207057
    0x10c080f090c03030f030103231b010207051e0a0e0f0403030e03091302180402182e05040608070513090e0109020409050102131706070e3c01020c090406050606 70
    0x217184105420a0001701c070722019000d0880340010f40e50a03084c01401c00a0064035080d65003848100c0448100200c99056004a440001e0140c0e54042e417001d801e9052070100f0000e10b0032404019004240e07806c5030308460002c1d01408a00c4009003030f0944c3c046d5042c01c000441114010b10945540524071f01035030b0000b80081ca42d42c02c00e4451f000751100301c582c10310483d1481013600401050340582001ca8000c600d01860607542454086040810240c0104c045424030070075400d03050b030501120314210082080040c0420046600040c4540c0c825070a04d840c50a091007541840484441407040d45407560301d907110300604d51001c0d803000480c80e500610400c58201240381007400f0b500210b00a8905003541c6500045452981c00841d50800d40c02c0040c101983e2000815515000d0155265401000c9445078240b507036000a01500354044a06034140e64610880c10b141c144400114828110741116001401c5e9031280400b198200b43d008a0104196550101190483c0660424100803c000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 352209523 1250 352208273 352208287
    0x1b090402070b100510051e1b0a0503120f010b09040e0f0a051b010306050a03080c01140a050a240308281d0f0a1203030e1c11010c080f090c0303 63
    0x124035400f1080790815030340c1101c94607031207006440c1c2d4018900c00c541031b070036440c13200d0700a022440d00070300200c10646000340381403011416240c98049908030866050f4800903a0703a402c2c3d5100a8080e40c00b00d040e00402d00c003507040039800384450094444550040362076146d03151200c507060207070341e848040400031211130742d0060900550f80c1e0105280401c16891454203c44117500c2400390300c0075100c0c007038040345c0b110f45107a03104100c3e07a1012000c0302d0595640d010585800950070300c294000c42880501060f1818900501c0c001c40e025001c01540c006e8071200d000d45103002d050a410126904045000c4e01c503550081e000440e28040e5204d1803d001211003916001e41c1c0001241c10826100d401618104061000344069942d0105030242c1c0a00e1000041201e201c041c071200b450700344249808900320074803012603032408456001400408a100040500317541d40484040010b61091000b8840000e441d4000b40022101501040384503007021300080240f8410025059a6000602100d54520b8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 352210773 1250 352209523 352209541
    0x7050a051606170606030103020d050a06050c04030b090d02120d0e0d0804050628050c120108100e15040303090f140610230910090609060512061b090402070b 69
    0x800307802004080340d01400e8649508002c295128804d500240140c0c1c5143d00f10307002c11845d501042c00c00c8400b40304d0301002c0000100030b80101d5028985910400345c0301c42c2140782c241429030004105078400e50180c8041d060499000480400c0c0340c1017940305c26a00c404850848029040c0e885900c44e6900c01c43d544401020343c09590580b103240100300ba10101c0e1140720210444403501542419442107060683c440081d01da840187c110000706129840c5c0303600c606407241c10708000d0340141071582084144140c4a035030707402780c11240c82c1e540010741a94100c807480352400322005071024080581d59070584080242c035004001e03285800c409007080f2052004852070382c40c0012034100e4001ea039030301c8002400800c0c0039800c80903404041d110b203280b035480500707200d00504006d0032400e5a02c40610005501480303481003001408000601050031030410f0b05010104d09210420801580030f501080202c04960341c00220901d452000c1e165243c0c0450000f8000c3e0240300c0b400b400040b444820302105a0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 352212023 1250 352210773 352210813
    0xd20151c0203100f140307080703050705300a03020601150507060c0c08070f12080c0315012102070b1e130503090907110706140405090603010f110a0e0609060a0507050a05 75
    0x417008404980082d91940d8410341c5549041c88001c01e1603104c00020722061600700c140c107003030798a0020700c00c99441580310002614461b042c010407aa4000c101d04c13105241d03050100a01404040d40004040030849500a10350310880401034200da0f61400012200ea200300891589213401c6103805450f0041d07401e00c110f940000034030440704442032140c0c10f2841401b46005a01c01c0014115003415503aa4403081c3d000002c051110038104424062120420174a0040408101220b4100162203400a10b8a581813a1000d45404a1000f0708045114085035800c00c50754403400d09900301c64245128941185103019280841d54044220010443c5480d030050105d02203046500c22901040d40c0c2c1d4909031030085a25071508078004080009002d5030038070048640d000800034000040714440d0148400841c3c00755031411407160400900d000c000c07580f2010310076510000b240d000c0e01d03010a041c001200b511071003140c8402c0c85000308421040c01818480074000700c0c0c1040c280c882194a000301c0000310 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 352213273 1250 352212023 352212059
    0x3010c1101051501140c0109230106090e0a150f09061a010309020a140102030f03041407060f080609040609020a030b0106020f03090f0f0d20151c0203100f 68
    0x9610b05800961000084001c9455149041e10754000303482120710b80e0f01c110350140c1c80300005917485040600000da8000d0b8440c1c1444000c2041c2c01c1100b4682001a00b0754020390b0111010703030304041c841d10210402040203407825511804074112584d600d80d440d009400038100d540701144c039182c4110180304480d00010005883c40c40303403411111550006400302c5d502800080c0d00401500070502c0541d0328018a00080c103014011241005000000903845500031901104d01909000c000e4085180812403500035000340c0c1040031120807680340042000c00c00602c030b1803041c15000045401e001080e0703c460342d541e402414070b14620351213081090910400b881450300620961610170100d210101c15241028401040d48201c94245001c02688a0200802a40c08007044800c08006422400040e041d40d4500001001415022081040d0070380552081d001200d01000424044510304111541d10340b29801d00503145c1d1901944040081c58542000076005207500010801124408600c012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 352214523 1250 352213273 352213307
    0x52e060504050f0103080f0403021f022b0e040f0218010206060f1c03170a050103170301031a0405010b0d06090212120a05032211150c0a060b0d0203010c 67
    0x4090380d90090008640c0221495111071445000510000311600d00030030030351800302841d03030409031241c0000c1e00160480341c2081c042a5450442488260140040d426440c0025442442c10412074100201182145a030300d040140e0b40c0702c0c550750750b81d40c7c0c0e02c01f4030003038080e510031500c641ca820795032422607003509072030307805031217600c0001d04a03180c004c0500040b0480030302103004800c02ca5409150241c098070b03044060040c05000c01040440070030015100e6101c03104042142e51550070166150000e50380c0f20180380c0c0003000144040392000e48074082c2000b440701d0b822010360b07803408d20500406040d41615402071040108405211031600010540c41c02100c600d904803030104c14140d940c80c410703038070541c1a100a0203509000340c080d101440c1d100e00c01c1e100c117002c404200c40b00405540c80200c0304690500900182c4046824501102d0021841c13032820704c3d20b420417040340035540c1c0d51210700042c039403510344049003960745503074240c00c030003580c0580203102c01980c1500183c880b4054a0308050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 352215773 1250 352214523 352214531
    0x30304080c07211511180406031a10060302030c121305160e0a0b01020d080a0b0a031515030b15030f060f07020f03040f170a0b2701050121052e 63
    0x2045441c0c8241d031003117841c480070103281020b04072084983c003211490f1154050f680d60000004240104503140c42ca510550b5041550701d002420034649000075000a4101481441000704603152901103582c81c200d0041c40c1025540d0b03414842e40d40c215001c50003031183c05002c02c224040c0f07141000c0700003610105028240d90395144003020046441005849005902c1064445005030141c0d40c215040b6000400101c0c0d88001c5201285c404041540704640074141181d9940c0329035003910820200308907024141c03c0310707451502c43d02d8910101a06d803084200b40a07540824a0394200400300c28440e14070180c414a00d00540c101103204803c039004800360007800d00c8054104408011902a1203a03048003a1001e03042002c0504100d10710064070003503202d0a42c09074007203001425020b00c01c1c520a110250f010021042e407141000c0308000c0e8145581c10036005010501013460450030b034601c0c0d00c42181068015042880c44e040880700303901c041c0489001c4410041009141024249000620600c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 352217023 1250 352215773 352215803
    0x607052a010503090601060806030f012a051218010213080c09010f06020319030204033c0b011509050a0608010503060f060607030e011e03020c070e0603030304080c0721 74
    0x2d00c540c44122210340c007582100d0018400385026140090b0898405412158070481c0c12500508461103400c2c40703054002d0000b0501c68280a20451040ea9030301440d1aa0500840406840b4814ac002d0040c00d8020821115a05580c1c0d09505443c03450010704050807030385985250f610b884034036034801640580b03c0c0000200c0c00340d000c20780c0c00049a54560003540341c45a0303480c110000c0ca000150400c10580c08120000c00b10b4648180e5403485481840082d01220300c0c0c0f10784600c0240c8142a070100711480300908030104000c00c03e841e0449010340c1c104800c2d1514800110f400d401c564000c103500600240c00821920350000103281658030030381c115002038a400600f9802d000084070030b2640030708104400000030748110052800e104040c140451004202004c0c01c91f980e80b91901d400009a0100e1a0220100200318003130003000380075480d50352800c0c0100429201e00c0001c0010389103403400640e018081d90704120039002803506d00035007105030055241e008085402500c050f00c0d1441001980c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 352218273 1250 352217023 352217027
    0xd031a1c050706051215030a0204110a0306090b03031602040605060703020a0611031308090103060b16050c04020301081e070f0905153c06041706101a0304020607052a01 74
    0x4031780c2c4042d44180c01101750b40d0000c0d601311141c01e034100240c143c0221101c040041c1c4840c01801c1d01d0300c1111916035101c0e00b2982d0f00408859003984415241d500b0000c1a4042d928048216050075010401800302e0303600b04c1c00071801138401c9601c840d030032510006070300c024540d02040005807103106050070700034014141d041398030354003065681d00c111841c4964810006071401b0010003034a24107050104001351765104891854010044c4908a01d0a0003886003c0280070302c0804004c401c00c503011030840d410120110355445071040000200d1700304103007101036901c1c01c0058000900c003805082d141d25031140003000c0588419104000e04032200c00d100442403514030075080000c105502401a048001280307c904440340040032121510103010a40460300d4450017400942880000c3c401c41c83c5140c02801d203808002000c0c80144412044180702600515080c81c0c85c594164260329203a0303e540c00000c0e040c0c869013a0080842c0b04212501c60b51440c1015581c54440028100c2d40104c0c81000c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 352219523 1250 352218273 352218277
    0x406020709140c0702040905060108161e050628020c011b150c030b0a030c0807080303070c03030b04020409150512010c1b1a010806010f14030d031a1c05070605 70
    0x1410031480ba1001c001490100020041c0c03c000b40028404140d40d403ca8813160b0030801c0030381010f083e941040d82034587c0c000380a801703400142001d4100c580d560072500b0341c5c50720030412401072920818001883d81d01c5280040340f0700d080312000c038158102001507828069507a90441c1012404581260803950b0002c0007660b0079060960400c9005c1d6108104240c80f40040c8150541300c41416079030003409002d5210b80010201a40c4502a02c1c0355060906140501c0d04155920411003075004000700720309103510503074510401e6070500f4049162144040001e020f40181e401c0000b0184c901849074040d25413051010040780c07010b4580066803241940014282e81d6540086004544403901c10400448050000c001c8140140d00300400000e200ca000444024203038040784141c2d000d40010b100f0711503c15a080024134886a08286a544040c080381d100c041103c1b40d84140340da507032508525280f01040303c0101c654010904c00842900d042082c003500c403014000d49081c4a640b0300401c0c0b41c0c0c01502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 352220773 1250 352219523 352219541
    0x90c1306060221030f0711011418010221060102031b0d0f0801050d03050d1808070302060106021603060203100e1e0f0105010c140c130f1425180603020406020709 71
    0x10b081d450350b9285c00d0640e0920b200641420100002c01e021504014828801c2200c200c2042c21004a14200103007140d0700030f05441503076803071644100000c920309141d0189010f010b001c41a03002120b0381d10080103030700390f00404010702203043e1010200c61160300041107500581245890b46a180c04000d9021154a90240962038000481404907000b090080000e044848001e00005c1484032040807040040b000c88a001c5a500c0b102050304803c1507014842e15000d40114401040346412500b40010240424440600303810b5000020416200e00d640006028120040d072240d110700302124103101c410501c0423105000c60303840c40402e45800d88403c4881c1203410582d160140014240c4038140d08400c00a4812214899008450200e03140d0f00080396406a010700d0000b40a1410308504090351100450082c5500c50182002042018455111512000c18040201080645405590295074010303946001c05118070005001a410b0300100156001e603400d4030700740da0b940c1d04468142da056803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 352222023 1250 352220773 352220833
    0x1c06141602060c091509061812031306120b040c0207090f050c071e0c06080f0903120a02030703060302030307060507030c14070f170c0705030708160e090c13060602 72
    0x2203429824034016800e090820a0410246e00d010700c48000218540e00a00301c81045c0200c8c9403041e6140e16003100306141100171034020b1441c1103040917003011203507514015a1705001d540481c02040b06899070044400c904d01a108025400042c0c002039566165485000320b00e50400e40d680500d8200343c0541805030380c001d040e03641001156030311114070440c406c5c0031104030b9030080d0340c1c00003141844451030020111503c401e445414131200c0d40002e00c000a14404050748204003113440c0c8802207044175400190600010f8498a0301a421000740106500207545880f001c20810b0a12181d07502c5180200c0b065101084003030502c00054990390f2400c491058800c00501c448808a2812500c0c40d1030301d8400d00d41c00450114043d50569035401540d110115503126000900c4541010040100540142070041a1131180b0704510340741018507006d02c101480e2071502040e0070341c00c100082e0b070350b031900240300307198054090381e140c401004544505c10040c403e48080b840d0700740c1c00380720000c8440c800c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 352223273 1250 352222023 352222027
    0x22107170112080c0d030203060a0905010b09130b040207050c18060a0e0c040f230a0b0904090f020d0305070308060f01050a030518160f0e151c06141602060c 69
    0xc15416041c0002c003450550307007544104007462403080c05020b900e000085980780182c60341030800a12000000d6604094031141c40e100041c0001e00024099441c0c109080b143c2c01403a681e03400039103015103400090300d17400c580042604820442c021800b204182d00c1a59500783c80024070320390140912080e00d20b107402c0320010809002e10140020010ba02291700c2101c03d242c10358402a480308100180e000211004000c00e030081d22206580c0139034440b0344100da02c14801400c2000b00b2034148109008181310b02d0380e0740c03024004c0080300d0450700301c00c03034000f44084180c41d1903003409049540710b1082140081c42e140001011403806ca00d00542440d01030352943e0404100d00000d0703004143c0540b520119010031606447c1007141045607442c80e1b0b010782c0215450901c1c1613000d1800030f805410250030207a4200400402031080b0044204004040b07032421110003120440c034100381b14031000079000c641000c076019964010a4019401010801c08440d030300003110f2000ca89442d010b40f4244070b01e00b02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 352224523 1250 352223273 352223279
    0x70b030114040b030705210307051b030f070e0a0b1225080106081002090f090a020d0f0203010b090d170d1a01050702090f061816110a0f03030c030207060221071701 72
    0x945407e40c00c58040d6071088030300e484100c0c1c80d018035103400c80b02052188050700f000341040381014004140c00c1030422004003285810304000900c220002490701c00d0350703980e400680c0c0f0b1584d1181c04080c180d48000083d41c0701c146010b400e0501c0d400c5010042c0c080500f0740f140010701700314140701d0b03541114042800742100c0071910302c59102940c0105407059108480c07074804001651074000782401115072810047e134800352070380035000390ba03440342d98096014418401040b401c2c02410880c1c2130620704603100e03040c030021032515410041d929445604500c0000c9181a104501c4d07034403d5002c140c0c20600780f001500c20b540115112711502400a4100350003c02103466006a8943c060308031200070314409480010b50001c141046044844c0b0650105c1c41f80c5403440aa045003403410b00d41030a0016240560301921201c40502c1c00d03000040c2096960b00858842c01e00c20f40c140d0780f4883c3e12000a6680d41074018518019503100e4003d41030102800010400302405142c01100b640149009180e19071300e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 352225773 1250 352224523 352224559
    0xe04140a11010c080408030d0905070909020a090f020f03070c05010b060403020f0d0602040503030703020304031b0501020d081f061d040b0a030803130f0b0121080d0c02070b030114040b030705 84
    0x2603036003004c9809580a000c042018413007440503100036440000006964211410010714044407a4443d14002d881c0109000c007503151040c644064030742d90a404120b2410442c1e0000003403048500b2100018400700a01c608680d004003c641030070b001c2c100074000b0310301c40002c0284610642c40000c1d4000c000c4650f00c089030034518001101235025150060078513640d5004030b415617211150403801a08001005d01c20841c0e40300c030510348109400300041c1200e0500700013079990628883e4101c2840450000582c110302e11100a81d901d03481c600c04400c0c0c2030b5403504007400b000c4a82d181450700d0341c880d60501c4800c2c10540711b80c0404190041000030a5451500c40340c03443c0d8006460089100c0c47c80440c0740c082400106600c561500c22060074480b50b1400740ca4074820030111010001003060403d030707000030620b03000682d890740005010000d1003180e203040907482c103201d41d488075190800c007000026000c4140c200c1c103c403403e02601c0034401c07062044100350b1501000d0245903401409144007510fa04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 352227023 1250 352225773 352225787
    0x9070f05190f0b1309021608160c1d071404050f04090b130218072309090702010b010e0f060a0c031404180b0d1703190203010e04140a1101 61
    0x40320816501d25548403009000030b61801c0e08000f40000700003405900452102c1460b100030030800004500b000005e01d07490540e03d5080c5006040c1c5100403d4160055a0391038111090603481201494601e98600f035840c00d01e4102e03902d1a080c1043c010014890714050322200c0c80c40c6031641c44007441c00d42400b08010032080808000d5030010796501122000500360510303580a0031000200c0312248249204020509250b4440d8a82da00c1482d401d001001d60001d0f81c104448044801d002440302e0742c1920410140180c5184503405810b102c03e1001550301035100c01030aa8007a40c801041020110511082c1129000c2458020b0070410a40700703014418403483c502540b0038500b400ca030080c070f4500c0340042e40143c4c06c054105012450020a00c0b0003c3c400c0c8480c006050322082203100036174882a03078600e00d0700310200074424000000748242460810b9440500c580745c004540f656100d09500726501c0c0c04843c100d405030346d04104500400000526080383c2540000c080b003c01c080301d40111440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 352228273 1250 352227023 352227049
    0x5060f010c050d0503280209040e0a0c0e070c02032d072d0f0f080c01141e09030a21020307150906020d02030108030d05010b09061803030c060103051509070f05 70
    0x440c0d00ca164801c51401d06040d07000c8103080c201b10158031026040f041204075140404c121910303501c1003d40c1c07030001e92070488240882d0389050b510401580c03070b018241c07014081c09074002c1d418055240c005e902280080c030307019120304d1002120040a044202c100760380310b003680141481030355107540d103200c4010914202e800300107076418442003c96584109175081d8040d50000d404032206c903481804400b0b001c200e2594070000901c5c1440d985a460704040303a00c0d100b811108001d102c51100b00c2d0f10075950603030481c1c080c11700141c21142808401e041ca0750a5000480d04585101c030000d1541401c68800801d64051035004a0481441e0103004e841e0402040440421a40642c0912003809005440d10180d802440da0f20051070b0b075154041ca00c88102d50781608811281e100600000e072481d110710040d1406c40c5007410403c1207414407034001074035601916410842c40c3c4515000070040240100d0b020b03078607070b20b20b100c1c680e40c0f03031541001c09441ea00c072401003541c1040300200030071281c03520090000071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 352229523 1250 352228273 352228291
    0xc15120b04090803010f1716030f0c030206030a020d0518031204051903050a0e120309060a09082b05030105010c0f030302070c26060603071e081005060f010c050d0503 73
    0x3158440b80c3d43c80385182c00981c0101e007016040700d01084414003007610020741d403520700003a04411940f041c00c00f19815080c000030781800c00700c00c058010020040800340146400400c0d5940724a081e501030b04c0070b540507410049039141400085441c009821a02c00d40615440340a142000451940c001c4d54260040003540c840c400d486180c00c0c0003040310458002e140c040c1d0354280d5a503120610162002c00c3d07a03000c3c5405000c58481010f903868000c8103030b070b010500c222110399503110464000c484802c001d80000145000340720842c10010032966441c07601c0100100442c408145110042d10607000911815010a000005d2000040d002d0203144150301e100703050040c03c0c03c0e080d407580d00444a450300404a000c1d00384003000550130400e1944090115810010f00e81450011f001c6911404248108503109178900081040c01d845503015001074075521045603c50039080d01030101428043d2aa039000d00021500c0541951184104101c00b03600700005140c640c0101ea8110780b268001019090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 352230773 1250 352229523 352229531
    0x3040605100b030a0b181311060d1401050f09040c06050f220503060a02040b181210020720010c0f030509101107060201021315030f0c0c0c15120b04 65
    0x41814120b400b07140140400e1342e0008407106601c0c244604ca48000d8518201c01c1c00d807004000107403141a481c03245140c0d1180c01104041002404245e03680035500340e03040a41e0401c0e450020205005035114122902150790060740d1402c80140051500152005810401c03140014881103000d07070001c1925a54000c41c43e03107004c402905070304c0701480c2404001e00c007905461040181d80b904019603500210740707003411440c0c1450101540a50701c01e851850912403414019042141d581c0c0407030032004001c200960b11280d1515a00701c0096000780b070100c03903030703059241240b08000313103211482000401a16032001444582e1280c240302156504200d00704441000b000d00580c0741c10301d02061014054039040140d8051025140c203100040c1c10000131a031050140e0700b0b04240c0401040100d850707001070b00d40c4000c04904100c02400c0b003824003c6049080c901d00310385165010100f071201034041c8132506c041588400e85181d0b01c505400c0300c00c00084050000d100003032850750121240480041c4001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 352232023 1250 352230773 352230779
    0x9131106070206040b03070e0303031512030c030304081b03120402040f0912020c0102060901090308040308040c0308191e14090d05060a022104020a0303050f122809080304060510 78
    0x43d206030b1180c1c00207803422201006000c034030364210075004080c0301d04402640c103514008184111050540030401d100700b10841540c80616018802c84211301c41c18803e684e600e1809040c40f803039581c05074454501a148480e603c58200b18007005039191840c40095000f101d46540e000c201c05403945002e4602a5035490390044005a210b4503004c60751112034015107aa060904006810710b80c00034024411641400a0500001c1d807221020303500a6040c02c154400f9180c90502d00042001508010015000005e22164641c035895850402603165501e034042004224100c95030a00245840c102007030040300103e03902c0d80c002c0064000c40d070001e00701c460310074503d880b450726100741600c800d0340307180c1d00046080044010800140d511641103840d01c0710390415501043c518941031001408100001c0740d0301b034100f007480d401c842c020361503030602d0822400c2000490b41e85144580700421107408a4101048142c011b004111070940c220b01c50a04541e40c1e0740701c000c05403c00810b00c04021281c0f40000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 352233273 1250 352232023 352232029
    0x120712020d0c080a0b0a0e040215160b01031101021b1c05010513030801050a0602070e0403050705060f0108011512060c0c0203160503010c0314040f020a0f031a0105091311060702 78
    0x2e1040c500c070650b906000d038140304815004484000c0c00c3c2c1806030049110900a2210340e6680d15001a0305881a02c2d041c90b5503a0411441c1c014420b0150700898840305035401c3c81518807070207061340d0107680d0500c0d80044450059946000c01c480300e00e034040858060f080d0383e20b40840f082e107032200d074411046107000c1a41e0f203190844038200d6488402c2030540080009060340162064050304c002e540c607840040c10450041d58900441c41641e24040c064400142090300c80d9099a0f1059442003c4a0090900c0207601e580030009024071a0950b103014180e4040c0e4204403c40b800322280d064500c0c0062206032600c50140545c0f60b01e040922035080e800c46c005031005c0000c044860741c0200020a2642030030101030a4440e0036860004040c02c01045c030316000c1c86506240d800c03503402000c0ea45034198a20200d1601c0644e070b448034413180a05c003000002c0c0f0409043e40b4016035000011920141c2c0c0b500c1c1046440ba40c241d44448003080c2038054407000545503600803810200050803103007410110b40c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 352234523 1250 352233273 352233281
    0x160c0519031706030a02031510170d0f02190308060a030c06020601140108010302100503060a0b030109020c0105130c0e070201060b0307030209100c150218031c14120712020d 76
    0x20840c0001c8816000c0c8103600ba0240240d0780058084001d17018041603900041d541d040254002c800007031940d00420b6065521990680c01008071070103905a0500c80d1a426441d45040350003400411030410800c0c0ac410710214041040e10031206000360100065142154100e20052203290001d819003008404960001404001441c01d940207216660402022007952001598568140b0a60381c005100507910b141030345c1c0c80e02802e8500952a9980c4a002480141c1254004040d2800001c0041070355000c0d9002080140302200083c01325407103008880080c440d40e4003020b003060700303059424401c0c10700e5500401e400c030182d88004280702da201d00d9030b100550300588092010a40c000340000c2d950170030110b00d99408020f03050403803030007a01c4e0322014240081d1400e240c1030a9030000d0b010045080319a0310940d4000c024045030888404c3d03c0341c00300221080c0300c000c00030810007045100ca039138041040b6400449441005001919812015501d5440c004004400a0b40900c08448141445d00c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 352235773 1250 352234523 352234573
    0x307030b0103141008120f040603020a0309020d081308160303080c120f07140a1d010302070506011e050a031104020703030b0d03080106080106090f1406040f12030e09160c05 76
    0x221000c0d01c0c900480306140152281011b40c02880500050000d00500d400751801c407042c40c10056900c980c440e20890090010040c020760201188042c54144aa41405010008890044881c0003604c90141950f0303640c00006c190a0301c01108005d10010b07105a4113a508955134244044c240014501000d9010808440590000404404102405a00c504100032801c1d0409441d8a400b001342c00041140a5a406a012080c044140b049c0a039101e07504581b0640c2c0c125081c0ca40550b141c00c03080c005411128801800700800030004a0300c2d14004613620b0440342e2000b4140161001901800081d4004013410f5061580c2c401d040c1206807035482c80a0f035003038401c1d9110621581840c0c2d000c3c08111060704031504024215070309004041c0b20310403032016503044415000b45c0504203000203402c0e100d684c0054500c41d8a14400091400c4450340c00030800b8402c2d01c5040c50a20303460180851070104a408d0246882c82408a0100d580141007105019010700203603480200002000d0340c010400d21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 352237023 1250 352235773 352235791
    0x20d02070c081b040c02060601322a0a060f2a0f0e0d0204090c0f1d0106020c0904060b03390d020d0818030109030c0b06090c0307030b010314 62
    0x251240b40f00001610320680000c42114100000c210310303800256600d100503c0a414441c0484a1084066007402a086041c0108004ca0441180030b2034007182030700400d0300000050a500420444c0c1e8031000004181103890000a0102c05e4145d150100544181082074009075070b2a142991810864505502c5607004840349035a00c41010100030510529031440100308940e4085000003542d410014031100381e01254042008030300c1c1d044c40054044e107a44802460601d0304170001e0b20b030502c4034034801041c3c00c010801c150340e03a84207803c0c0d03151810880000e6126503400e00003000200198840c41000d2000f030f003110041c0421488840c2c0200840f18a0b111042e42141ea003c0b8010721521000100402034811810000c1664040781c1d54192070f000003405020086100d40d980c010203002c030004031ba0001e00911440c1c2850402401040d040c1c80d040e50040c10102c0000c0050400f010b00c030b8092501c08400304e1440e43c650304124028400101c0c1a4101500d860100389560703442920b95009490032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 352238273 1250 352237023 352237033
    0xa0303050105090906010b09010e0f0406060819111e1603090807081504020607030216090515090601120e010609050f07020d170103020d03090b0c060901050615030406020d02070c08 79
    0x400c00308042d0f400f0081108140340d10840041c4009a45e000c103030b842c2a17000307003400f1502143d900005482c042000c150250480d141c404000303181c5078000700700d9000e840c50139000024414031034000c0c41503851103182280c2514007000782d0004103050f410108500b808075502641418000c14480300f09130071200080d00010a44041807050500601481c0e00500c02c0500400410011064405000c4001000030b03104a2002c078400080c9030003400202c00c14005191521085602c660b1090018002500d0030105003450003280403141c10000c00b01402510146c440d0184201c000030400080e208840c555042e5548460000a28425901605005800144036500c1c54a0301c01c2c4c009107841000c407802000c0118105c1c1020340712582c80d031500e0640740c06550001008001d42010f40702039229a04c02900c1c108005800030001c00f0119089001d824040d0080c0282c0c1c1f1060100118102d03900c1074011020000c0000c14000b03900c0d64010825101c44580c00340c201900d54032002c102c1e4200b43d001001ca5040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 352239523 1250 352238273 352238279
    0x606080f01290d0f05031c0e010c030b06090d0c08100b0f0d0305041502030f0304050109120504060f110a08040f030614010b040e0402010216060e120106030305030601140c0a03030501 80
    0x902000103041d10315038090b0205900801002a100a502c2030002c0c1c0703401d120302130034000d01c030007401200c45100440400c042c0610300310400400a2011900920040d40b07820000a0101d100c1e00802e401c9150090840c0d050510550801011002c0114200c0d03041c240106c00080c1c0c110140a03480011108800004100303c50300300f440200310054030500d204401c90b43d0700c200001c1e0040107a50584e80800440c128440c00d082041c0e00d1845144041240f5102c044100b02c10810b054012440441c0b00d0b8001c6541860520300030750f039601880c094a40800c00d58852402d00c141708a0300d10344002c1c035410403204503a5454031000500d500603005000c8000d10b0040c00d1003413000d02c0c06484000f0f500d844030242e1545c90314001860b540224020440d28804031804901968401c0040c1c0c1c03907003681703403481c50001c599802c800f80001010814150083c1407080540c1c0c40c22006200303020480350551242442c680e00e0a0044a04800501018117200f606004108280e0010001c0720b00e100d11a031400209941 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 352240773 1250 352239523 352239551
    0x11280e031209090a1401290315040e0109030e10020703140f1e150402060d060905070e0102030f03011703070611180301090f0312060801050c090103050f1302010503040606080f01 78
    0xc0c00404d600c010500346902c07504081043d03400a411503001a205680d10320f92258243d0141813250340d820344141021003441440500003e5540007401d04580400c00d64840d48107440c07d032400c800c00a004140a584c60b0803503410300c0448641150038a10540f209192269640111418080300707500566100e8140018909402c00000111603810100061401000421315030b464103004504030b0f014852201140842d1105002d5444c20b04006800303000080c0c56064032401070000301c801c3d40000d90503403180702142d400031089500f4000d846580741c0c503587c01c150304e960648203100e00c215000e1100f041040d01240d440d102b54599030000e0700e041ea030f8401c0d4600b0000c001c0c1640d0310301c55220340d1404a0311030018484501c040c88070390780350a0606031070705024401001840598000070542d4201010440d8200d0914024000504240c80c200b01d243ca644140012300c83c030813076621441c1c4040303098407000f66005201540c0d025106260100e00d4684848006040c1543c0540d50f06c0584e44540100060351 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 352242023 1250 352240773 352240789
    0x1403030405011d06061905041d0d23070c0e0a02040f060f051905040b181804050307170708160506061203160203010b09010f0911280e031209 62
    0xc2c5007900485030f8010080c070058990030090321492107000000c1d004403030140c070758440d039005240082c410060300103505051801540d1028580380e05014182c0c81a6001d4040e040c0c181825981c0e0006441d290301034400034000d0707401564266060004031600040202500000b644529213081e005601c69103420250081109950481001c1c0300b1608050803072547c0c050203480040f406800920800f003150384e0241c1d042e01c12500440c0d46660009043c100e40a40d40704c5210f1079070015260103030303009055403d503810500c0582c2c00800d181c000f00141c03800f144c401c0707401e100c2624400011510340601a680c4400326804080e80d41030100e40001071805104003886020b501c004262440010341e0104860261603210700ca005000c07049a01a1000c00d545003584440311689028003545120b507100d000c2c0c4082c5840381e00c00e4000a504283c1c08000100e07600b4182c685c1580b403480c101e107990002030b412104844650616108000c42c044160304255410030002c0c0301200d80d8103006079101900014001a1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 352243273 1250 352242023 352242041
    0x303040c030b09030f030c220605070506010504111e1c0605090610050a030e0a050303010b090a06030603021807030e0a230a0c0608041416050406140a0501050f07140303040501 77
    0x240c1c0003801442080d05c0c1c0902201d6000c4e00c0d4100a550f40c800012550503c0e421600c0c03820004081c543c0c0c0419503030340050050802c58000e4085503456079a80c41000140c541803110f0221005081c410704444210301d0007441e1100740080306e12030401c0c50400c50710101080908114642d42c0d140d82c010445400c1101080703800030390030740d11754194803070003800a8079a01c00d000c2c56038200341c1d49a40782d02d0602002d018182c0681d500030f041c2d998959444903100c03907580100c0e11445c499204044001180d90080c854081201c0d800351500050148009a41d00641c400074822020716440303240310348140380c0074051030040620503a1510707030069160950090b0b481816000504a03440260240049448100400111280b91a08a07119a0346c0d01c0c4c001c1d583c5a101118985510820307082440050000c1040b209032102039500300303d016a07501c48070380190300000a194000c600c40009000035440b40005210189161400a1600c40300d075450040782d4044081510183d0004800d02c42013160a00502c010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 352244523 1250 352243273 352243291
    0xf090e040f1e14060708010e0108120306120a060c02190b0109020a020309090403023003130201020c0a08070515030f01090b0d020901060c0506010e070203220302030303040c030b 78
    0x150310309aa900c81c140414008058000301481e405044129018003200544560000e480040c0d21a00500765669500941c4c0140c04681810000719400301a400824100d0b0181001000750180400001c101580041d00a40d08220b49606d602c10071501088000d0340184500d03000640c1000c003000080c100007a0020f0340000d90881ca482d440800d00c0221194103554480000603076a0030340c0241607145125142041d500040305400700014140c011500350140f50042e4800050709600800c40f08288007180c491075002041840851800c2c07030005450712503d48113004070342c0ca031048c030000103500c1c0c5441d5004a4450b401503205105c0c0381843c15003854590040011503055051000a41c42001414020301d0142a51080032030003940d20400d0090900760040c0c00c480140d615140010030201c4100f01c2690305108d090000108810122845482501e803503001c2c40c100100c4800d0120603012040c501e018140c20380a021001d603074280005c60281e40300d1544e11030100c0c518904440700c80310040c46810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 352245773 1250 352244523 352244549
    0x20c060412031805120a0b0a0c17090c030105010801060602100c050909130f0b090c010905030c0f0301060308030c091008090a151407120f0e10021308010504030f09 72
    0x40c80e070441403415a065807508200d0751610910f149500c00d441154001940028900036509228102089141180c2c1c0907070120056681d85003040c40640f00322504140010b2518007524000b0290f410405070482d0020b02030f02c00c046403550000742510420380000b03080380d40d0703030004201c0680c0401c1020715101d02c158060041c0c0740400b4000d0640d001d034840c82d6005442c560700051032145034141e2140e5903a030202e0345045202035401c2040520004850101007131088401001c96503000d002c51400300d1703400078010506404114240070150054000ca603416640300c000c0800010346e800040d6204e00710084015484100e44810440301c401e13034010060030700c4040760a1040c80e4402003400c210184e003000e803540c11006d02c26500001841c54055803c40c1d071540c2c40500c201c5903071081c100c180e0141101410b004150f2540d145200b2100640750340c909030f0748480350b0407c00701c800c1e4025081c80b2040300420300e070850390340222a0a544c412242140000c000c0a182a03200e50000d1003034015080700d0314a14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 352247023 1250 352245773 352245779
    0x1060501080103021305060d061112060d0f140c21120406120504030c0f03030f1a030606040e0a0506010e010e0c03090a2013230f040b0405160b0a020c0604 68
    0xb5150110071701c1301c0300c0c86074482e000610315494007504590102d41c00030040103403952030714141050f500094075a01902100390081002450311802e00354415800042e105d0400d5101d54405110903082d419480d158010b0041800440d030792039803c0212140208140350604411095407410102c5480701c442e03402c4d505101c10b01400b40d0181100143e002c00e039800007510741310742c02c0c16200d040107064014407250303000d1080d2080507416003200d06161100d032010320040e405000849004148101c010350154080c40026800c2d01d49600082000032070306040d201035803021f46a050500c5d0b000d0304412070b44020b6000401002d010f1050305980a1030410a46007142800c1031010380b03a41c03d0500c0034000040050020f0280c5603a01c00c0410354040040184140c0001d0901c0040035141030104000c1c1d5500000c400d03142c4440d82c10708144911601d0b06081c0c0260340f5a030303860807c0000130307106503030350300c51076810a2068465815540c060590740c0080790b200c07010300f4002450410030503140c6001d100c084c0410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 352248273 1250 352247023 352247029
    0x1060305091c02070302040c0509010f0f0f05090d0209070206150a061b0606080d0306030203120705030405130920030115031101050715151802091309020301020918090106050108010302 81
    0x28082e2008855141c0d214008034240484c80c10080c0e4002030341c42441c1a40c007c04680d0414000d041500c401e03240d0307003e24a02c2c9082520040505d50041000c00c4054024100d00c500c81c200416003d48014090802200103030003041c241d0741d04039152000343e405607043c00820115090300e60b240c10000c403044040c0300d040440080c07400152024a5044040b00a8130104005c40c81d0400710140590b8170448081403141ca000a000e40020301c000e90103030140402d800002180b00045655091300308008515281c078120510402c3c0003400c101189483d502c0034003c0000f1102d220f805c0c1000e60101500702c140c0058001c04d400c50341440340e040307001c40740c003842000000c01d458141550701009003800c03508c60b0020b051a1703d4817410408840c039210302c0d00b40798540da0000c80f030300903060742e01c00a06103001c103200d11564400c9205040400350310580e044000b000c0840b03a908403150a500c0500003504000400b00803d00101104c1c189d00b1012030b90004102c840d402c24410100105401d1908101c02d51458001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 352249523 1250 352248273 352248283
    0xd020d09081233040902030f1b1807050a0c0602070b0f090615041505030601030f1a0c030103021e13140709030807110301090c030b040b07030b0f0405190e070e0106030509 75
    0x35440140509400c0c0703066544c562002070b046801a0a50b2603128112282c1e584030350362042e241c00002c800002040761030074a07011204a0540c50741050609032164201542c1680040110a08004c08412900006102030000d071042c40c0c4500701c0c1d49a50f0401100e4488002c10062246805610120030032401504946c98503da0b03c10540340018170700d156611000160403181c001d50f4261040b03200020030000c48021a0100902800c44070100151000140c888150241c3d1131a038800014001030015290018010881d010b20125030b24070403100c580820141c1c5020406808419520884801d10390000f1030b45030f90140607454070240041c1550b84030806801004400307820b150b19140c50072810b8070254000d0307400c15003110019098568031700c2c02451080c801c0704c0480d90225000c0103e00c00c240030307000f20101440d00401030458031040301e06020007894014200b04421828950004c845442c91042c074800c01a42d8016041d090b00780701c0341c00650007040e03100b841010f14000070454150b80200d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 352250773 1250 352249523 352249591
    0x70515061e212e060501090611150c030618010b0406030207060b030a150b09100909050c0a08150f040327090f0905010b09070906050d020d090812 64
    0x18002c0d072492a25420204542466403001c8664401c051021120418554001c0012400540440c6210104400308400d40d4180d00c215408202c07134903024000301d40a40441c42c120712525044a410f0b1140c0d1158001c07000b4152003075000301d04004203012441c14810103160b400c3c0300107030640c0e10301d500d4001907810b940704620400d81003540c046658800c0128a400441d0003000040c21540381160230b0500d410b10300308109142411628120b4011140e05210400303c2c41096070744000d0b040c0c1813400d03081074090507422408440070b0190900c0015175644a080c80c0c0c0180c0140002800c1383c0f81900216081ca0314080d1181c2547d4210408120020b07900c803d140052a084c0068407291541c2c8000c4510007007000c0d0048a40d05051940810840c01203600040c207840c0140300901c070511500e410b2084100c3e0648903071001401c00c0c0f0041c0061802440108003100741c0c003400500d80307420405803104417138003048226202d0100081c044d01015013003100d1604161400c01c0c0c18006241500c0445041d06060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 352252023 1250 352250773 352250779
    0x1060f0b070c030c0303090518071202180a060206070f021506010507020a0b0f1c0902130b1210051b04080304120303180f0501060b0a0c0f0512070515061e 68
    0x12032808001c000040b0038000c6502c04012449191a4500070b41b000302d16014541c042c040500001d81020b00b04041c19004c2c0003d45c4884079140c0589040340042cad400900102c01d42010742c001d07080103854503421500100040c3d8064a142c0c1040312000b0001c400c0741f6584811903015022007000d410b4010200c41c0c1110090034074941e58603940c0701241070f4461a901a00c13120303001040d90601466070300e001749952142c3c283e55a01ca0490b00790902c048880c0c041b001780d000703800064040503d48141e4090812884010300203842e1040207a1410724180c404540d000c007054541c01442425011044104190744003d40b20720b00b09400e101c0f800d40d69001300d00c5a050600b1598007814280741c040d07802100520815282c40301300600c3d605090b08048444003084440f90310308100040d00f0b440e030100b0790342d0243e0a99078420302040d443e19216815010600203590038000c081016001490b900001d0034071078464405440c2c81d0034540394185611100a041306c0c007034070503180f0360603010000050512890b0022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 352253273 1250 352252023 352252027
    0x10209031203100e0c07030201060e0103050c0d02060c0d020a060609060509041506180212070504060e09090312070804170412080c0a020a14030c060c0a120507060c08070206070201060f0b 82
    0x10340d003c40c06540c5035900c015106049001030012801c0100010b0015a00070703002849566640c4145035a20f00003440003501640180144040d1858034503003810515000610150600700d4440c002824894403004450150744940020b01c208007442c0a108002c000a58080048516210108103003510080000344041c1881514594281a90340f0000140003805441486040c10f014110025440304058155000007103001800c554400d004507420340b20785a4030603060001a00502c86810300c06890150316007c00d100300310030b11803078410b030f244110b01d140d668030785e14140340c2891007944004003120030102c0c208202c144881c4444c804151450755100d681c407540d82ca403062910b800d00782c0c1124020361020314180001906004e02d080e503542c03000d00310180c0d524690620104a044c0c13140015128071034002d0000c9002184500c105005c01c6401410b05600c2c02c82c5070380e00c403001c50300100380e4107002c82c03901d40074000e007030780c1c10030241ea40405180002c2080b1070904032000d9803020b2521034407850040c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 352254523 1250 352253273 352253281
    0x2130504060f261501030b07030e010501150f020c06280305010305031207020f0609162306071b030c032a0e070917060114060a0c080d092012010209031203 68
    0x10410070113405080340441c000c86942c480c505039a450300141e550100103030620300e281c0c191007010710425040f2403043e0407140c40340401c00e42c161410074072904504150701840c0741d440700540b1680000d103a41036071303124a20001c00c94070040f1001341b001c50000e01d040528100060002440020854228007203402d42c0c0c2c11103554000f0102e180c03182c4402407021714016203041c0109000000b810740003400c00b502007060080e80f100042d0f506a045880901009850240c186480b42080e00c0103003000c500400014000c240c00418401c403034889035104413000300d081c4900b002840002908807000303062041d1034000700000800305c8180b041741e500860150040b07402c0400c9560b1b011300001c00080000c0d21606900c041140c07285501c55509105091041d5060701074802e103441c2c81e0003103842850241c0c03100e42550440740c50f840a02e402154001e10748603a03a03041072021828201910005140026080222061040500801654006081c209030b8010b10207200259404600b41c803500c060841c041d82c4135a1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 352255773 1250 352254523 352254599
    0x207170c06010302061b01021629010e1b0c15010902040e061207170606090907030201021f0b04090503070507090204050d150b0d0302072103080612010605030102130504060f 76
    0x70038540001b90315840052082d811340119000302e1000d60042000082645880f00030094000a00c0201608000307820014000c0b2501d1110003500b210507040c8810004959014401c01a800300c0440800c591103c500906081c049204060240c00c0b103000a40c00e207450100c0043d81650050320301489911070034040344c0381c428208a281c004001810032303410780c3c44005a04580b5004242c0d000313801030661100150221138001403c03000ca91341030f802000398180609800781c951100c0341d52805c02c20348441e40f60110b80e032070740a1b6102007401035002d5550ba10051502071314090440e840700c449140188401c01280e80d815109040e410303000081104041405a11070000b015049961584508880c600300203065000950f1010307544826007a1039000400f0041c151240201040180018610300024007241000d014134200400e414001140c52510b5100290036070f00080f4800c2040d100029082140d841d042c040d40d0020a410300c0c080d08004e040002c00140e80d003155481388114100010241141e030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 352257023 1250 352255773 352255807
    0xe19120f0c0f061e06170f030f030405010e0a03050406170910090206130806010e150f2e0e04060512060609040206071e060506040209030717070314010207170c0601030206 75
    0x18013010003039007011111030f01c180300a003018040e010b0090200e01d03607055017100c00207000c1451840c0c0b0000354180b10030041c2c1d4030305a81c0014400c2b0f60075506c40301301c45840c503000c101758510310740301c0e4841c1512942488001403581108114400e5129544d100380004890003044210442d40d0300c180206042903e0300100d9020300c68401a403036405584040000c243c107001c9106410384608202c2c2d00d050380c0302c50512101c1300c0000c00d88290b02c80004100c4491926010f0007070080c0d2010100544804000803181d0180320440c0410040891000f0060386460b240038030803100a13008c22200300c5a0800c0090a02e55102c000a1a9034003036544540800d0035961450140c80241d2340c8850414a2110742404a140768445400b046511904010110741030b8a454025118054009802001c0441c035029440400241c0c2100d24076460050050100c04111245071121805103d20005aa1505149820703111000500001b805d40038050186a40715403010940701d0441c0d0301150401c0c0c94000c40e40300c480b140c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 352258273 1250 352257023 352257041
    0x4061a010f180f0f0504060501081b03070c050f0a03030608150a0f060312021005010b040806060d170705160b0304050304140102030412061410051809010e19120f0c0f06 74
    0x42c3e4081c07140003e10b8510b81c0300c103100b910000e681c24443d60780e440b401900c04403020ba0f8a200c40c0e030001c82c0b580c2561104000519480000e0385828404a040d540701c04e4100500d100c3d4090840e0000307001c10050580502803200100b41e1480142040000c900d650310307084c2c0f00078010915a9460b8103440f4400340d41c50b0010b8000d1908691010101301c1f000a000c0d681e800e83c0e031600c2e20001e00b804000511100241e06031021074003180060710056603404104200c516a6044c2211022030285091820b007480d2030141901c240309600801d100030044411032910303c030070761240300c0401080082100013140032064030200c40342031406007100901800180c0c1140529001010361b01d0454620a05100b2150000c07210380002c240342102a8590300c1d8005181a000c0c0074481d008140c03441d1210501c00705420681e40f042428000042c00200c0050550800f04000303407812030301c07110504000601008801d00e51909006041101485440050107000d04101000150401305090042010300016070002c03a05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 352259523 1250 352258273 352258289
    0x30c060d11031e070c0c0e072a020306130c06200105150f0a2304020403060c0f1b0309030b130506070f110109050a0609020d050f0604061a010f18 64
    0x1d0b850540d610680090070f10311144154140d40c804280d040340520941c070140c0703402c00d000c00801030400e041c582c01c0b0940900464100403c0440707440c0c10768850514045400348004400e0310f2440d45004061500f01d024100c00350210300c030000700340041d50904080b000c031513450030003003445654044c0603200c10414003100390040d4200020404603078186143e00e04071440c12100c0d249482d040740c0a1180c032114a015420340e4a03510440c03a154010042265a1440c200034005031400345c5070354078101610120400c0b0004034003283d86001200e40c00081140407000580384000d0200402e0320001c0c00120244006800402d940d00418900d4481d00109001c05800104840e801d04003403000500341400114a1000140d900c6529125060103001305249070350420000e0042d60100d4451800500c03904404907480003950240000086c0d0a0014515000680b0040d00942c9402e051180c182d400048040010f994070946005240c2e030440f80d403000c200303000d20706101c0b0304580316040008107407150001c83c3d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 352260773 1250 352259523 352259527
    0x9050a0f170f10050a1b0206070e03070803070b0109060519091a030a0b012111040e2401061e1205040503041e081002043b0a0905011a030c060d11 64
    0x3040f080d407900b01900032618600c0800c050b20b02e0324042c0c0c1a804000110000581018020405140c411040c51524040050549501660710112540386030305c00e42045038006c4030000100000301944c4200001404156001c820022401c50142217442c010b003d8001040e5031001110b403507090158408210001c0a400c0b60841c000394144a100f078038092007540c07020280e8108a010402c2d445000210050707000d0b01d4444901250000c00000d08044400c03890340b8894404812828400525402e440030501000400c40c0d50505100901c0d1a40300e890340c185800d64105943c0c00241e100b8558100c1040034613001600340c80d41d2400d5411480303594040c0100e504004002c0004590300d005180c21240214120f1711000e030b16031040c100b81c0c0203510420110082d016410340d03e0203203621b008042ca0401b0580d003d4020600e41003501102401c5e01d41c52070080d903414040342040008d03c15590400c1000c1a444203030100f00b0000303030380e80c0c0e580a403190040e24003060040210117240c1241c10b1104110012913 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 352262023 1250 352260773 352260793
    0xa0611041716061e03090f0206030106090e061e010e180c31061101090c150224060409020a0b0c0a0317040f020103051905040302070609050a0f170f 65
    0x103a64051100d0005694441d1207400646907004d244a110b10b42d00f01000941c2074902e24074141d0041c14104d4045d50207503d8184040016912003000314040c2c1580e2306e903040742c42c1c24289444001030340140a035001f01005200c4160704205004400300e8a8001d291640030542c03c6000718001d502140d00c0f921064100200340502d90744800003070a000200d65030134804641d2411840380d4214030400360700480a455200900902e40301d16400105d0100f50000810a180c841d0384401d414402503001411420038540440c0c0510340c1409912545894001c0c1c801d05401e21444103c142e00c00504901e1140780d40349404011511000c07210002845000507050322081c1311a00103466072444030f0100c0004000e8480d10329924498241c1500468002410799034140040d40151b0040c14003400140340048036200742d00120189000701d41c8601e109901600601d45810310150080b050754120038803a41c032136034045c0b01a030410b240041c01c0380c5840915495000000303140f40d040c002d001c990450140940c003484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 352263273 1250 352262023 352262069
    0xe09030d06030803010513110d0b1804060c0f031a130e010510170d0507020906120d020705040c0302090d061109090a050f0f0402060327031605070e04050a061104 71
    0x618102e501c2943c20f583d181150780c1042003266a001e580000f200024002c40140317400c0c0342c3c080902b0300c0020341002c034024044440d030320341e0b4901250102c45843c0c4a42d1007031802d81d4800b82090b42021030f800d09010002501101240a150b111100b07801032080c5110071600f4040d50b007042401041c9500208100d013040c00c2c0711400c4003140e009000004511885030310015800180f60703108082c0b10b0395828109150382d401c01c07042c43d00140069074032201d180404030705031406107c400e402000c640c0003011903500d08828401560811201041403520500882c110b6884007031021840302d601110015038460300400e4080b0b540900305a554000800c601080b46040c401d40c09a80182d9800e511602c2e2a81c0342c14803030540681c1250025084041840440c0300303d0954010040040f003e01c0c80c200c2c840454940310351454220b030b812084000000e680e81000e100e0140401c1c0c002d441c01018941103032030b043e21605e42d02c44895a009050329070360010312750341041c1282510054075022400c03820407807500d500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 352264523 1250 352263273 352263277
    0x3160906140a030506061b21041d1506040e070f0302030610110102070b0f04030e0603010501090b0c0c0603090a0b1f060f0314071106060f1e010c0807080301080d02030705070e09030d060308 83
    0x550701c41100307500401c0500d2410300b007550221645102b00c041c9a0407404400400f80b423001c0c06480c0741a00d8840d10380003c3e82c0703000107040900b000a50411591030440e4009010320018100c0d481414170420034410580c4a02140710001c50160602100c04007070716022a009101e00f00018200d4601c20041c00042d0300e05124850166000f80c0c1c5807421008035008000f014407013072240c01d021a01103601004140d803042d01400340600954191481000030501042d15035000f1101116580c00124500c0700708031b404210150420049100310803000345002d51503a0302a1140241400e116802e0b08041c13180e0310035081841003076800c236001c0025080406024101c81c5140008680303134081c00000400c1418005203801e01000020108844141811040c02d1068551200903041200710448035021032106001012424410b00c540c41d0383c2c0d890800c11600700384031448200b0864004100c02e1010600c00100320095900f03404401d044ca40f942e003030341459403091001c5a2101801d05000109029007000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 352265773 1250 352264523 352264543
    0x100c0b0f040314180d020609130204050406080604111207081b1002011404020f010309020301050c030f0906070c1e02030618070b0405011b020a050603160906140a030506061b 76
    0x94448001c11104034241c454000e40c0c02c1c042c0f0000c09400c40044c1490610284541c050000d0301d014036100702c00020840c5215601014065550001020400750034039204200c010100f060180400342080d0740c9007405140b07603610552160f01c040300b0f0210500c006100040041c529401140c0d400400c10024580c000c040c0d42e00c0780d120701c05041542e1540341c010301560b0403072030364007110b1203c1e55520360811500d03082d803041c00c0781099540c650b00360040c1c41c240b10b164024000d40800300c1c0c1307070300c1c1805280b40441030007000301c1c5640e04180140103800d0f420203c403000c82036120401450702041074a10342d202d1000c2c800301079070501c1120140001041d02510741c850702d50141c42540c40840e2202001010780c440c034803449000072410782c0192411920340030a900840e1000f0505909640e4600004044d0340055402c0b40c45450701c0c040d024040d6411030b400030010b2840f400e0240c00c2c41200e001c0140240181000c1d403003030603107840c00500280e0703801c001c4070312242580f5842001c0d10929008a03030f49515080e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 352267023 1250 352265773 352265777
    0x9090b0f130c0f0309030f110f07090227030a06050a0209100e01020106060f020a230a05030a0e0d0c090f0905060702070e0c1306050d0204030501061d07031109100c0b0f0403 76
    0x1940d108040c82c86070054211580c4c051f22100c14075a9100c004551400740c00030b03402024065642d0a1014903424000e1100511040001603201c0c000c20a40400301030b40d8078441c5041c2d60390340c3c81c00031098070049440c0b042c4a40018000500b5a036800896010784901c90813070350b22a4030960704921300c0e90444882944d80c1c070280c7c002c200c0c650701c5d464291294201400c9110250340242d030035800084052210003145408040920900c40040c460300f803401913401000c960316003010801041c45540241d1300e810301e0408a030460f500e0460754542074004000c5008042182d525041c54014104068106060702d0741d10400300c801c986410040251100c1150060068101811011601800602c02a201140f00c0042c18203109441c044050b40d4690000403d0321060342c0a001c0000424400c1c401d0786e004010021107004550b0329400c603102201070007007040c0141071400305c40340220038521066455a22060f0342007003142c030200c881a240162071a02c01041c080c030110800207021500035403e4040e074442d07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 352268273 1250 352267023 352267037
    0xb1003050f0a0e1207020105070b040c0515090108150621061804050606040903021f1506021c030b0109090e0709180b0604110d020c0c01140a09090b0f130c 68
    0x269641da010744442e50080359460344200b8a80136441e0104008005591050605a00d4121240c1d66480b0741841158161082d11100c0c0c8100518109116164400d0041e912694540400c440000c0d200c19409001da0280b0845d0200880981e10340d6002c032840da404d6044034120a6403a00341130a007490003220140c1c010a808801a500300c90b02900743e5000340c1d4840c01410150340d400e01480700421003000b0039011171040140c20702d445403070f0450445851544200205411584804006041c10a80d11400456010f0801800e42045c0034076416442c030b01d02d00d400b241541030780e0012258003c0c0c80c1c0019460710b00d002030b45071551500003103001c125030031301c0c10078414030312031241441d8500c4642001609540190002501a141540c400c4228601c11002c59041001c2c1c004544100c2e0000e5141c40c0e410746c055510b0940d25a0090044403003486460f1840c0c0c50001600703001000d00d00b05121f0040781c20386032506200d10380d4070034511030020807010f4824111100c9e2010000082c01051030104082054 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 352269523 1250 352268273 352268281
    0x190c0605093d110a020f030106032324040f15112713022a03030703150513020d091e0c050a050f0d1502130e060402030709180b1003050f 60
    0x11491600000b210300042d00c4c000402e6000c0c0b20030000d000030015419544d440003c8000390a030144105620b007a64030047d8001d00760800d652600c2080c1c130303003041262010705c0c0081d00ea10001c0c4035903074820307801b0602940800a0f0b01d002a000b051a40152405604105619444100d94805002004111800c607580c50400c80185103802000200700c640209810410029080f241d8004081042c44000e1154030f107201c151481c0841e042e1000304180340c0c3c1000040c0b103803072941402030103044900340001007601450603000a09412072800800c00c100d801240400c0c0040540d400284c6058020641300340b150480d4540c1621160301420440354000103020208150038080d00c0b04080d204050103c01d09400301004105444012510440d07002200707900009114401d800a0260f0b81850f410401049060040f940304000005107103900841c070520400c032090342d11070404004c4402c00b0122001880c03502c404c4102a100800781c1ca9008550312800c4c10032654950300641c41075001146040082d15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 352270773 1250 352269523 352269527
    0x90b090f071e03140709061206050a14240a0306051803030606070f0f021203090a14060301060e0105040803030c1206010f08041709040617190c0605093d 67
    0x100b24642000a203000300c051002407040c511400c81c0b042e85104036400e05075145800c0c015a58244c020100d90100101c0d200304200042c001d0039082030304140d0500080c48031094102361000d0003880d02c0c8000c0d042d0307600240d180e5109c0c140d61841d504090600f40b412501d03810050064507094408603c03095050301c551144500c0441030b64092080244443d14219080d100c81143c0740f0780c070f0419910203442c0c0003c400142d880f81103080320040003c1c0503544420980c0204071300e54102d6440084000d0180100030042c0c0e0b104000c030b07415a0b01c076080804250004c0c4c40103d961340169001000184400024010b0710140d0101404403000300302940e600030381c0c4d48801190300c60104910000410042c0c00820005803114400103400721541d64081e080c524074000140546a040d8080f5030900500d00d5011014171003444082c9043d4901c10148241100706e0340c54101c0403455228000801c40013183c8000b072540c0b0585a42d507220341c0d400080d040140580e42c0e42c0348101441440100c2682c680f411810124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 352272023 1250 352270773 352270799
    0x8070305030a21021c0b0315160e10030605030c060a05030415181b090b06040b0304170304060b0109240806040b2d09010e06010f0201090b090f07 64
    0x20351280286041000340d01040d03c10300c01950201001015800920310443c50510113011240e40001c04d00144101c1003030894100c444400455020b600710003410030a0044c2c181059030003000705040000c0503021400c0c11548d8131480d031106a40321701c2941506148aa058202c4016140110301b81e980f1200d41100f0800144204180b03074000c6601440020046070b00d0b89000f018500010360049407811040325030004100c51000c04550440814810122880500080d080170b0003083c2e008103c8040e404000440c0c50045210740c10901b0790000001c0c041256060314550038180c030501c03050320303420b0610345030003d800c100c4895400104c080c10300050b9119584407003210740101000121554541c2101101c0c0c042004000540103515030700458019207604d50361424100107000a10565201c50a02105200120070f40c24460607440c4018030150072204152030300040300342000c46038081c0d144401c1c1e003d017001460207401220020108180e061010620382103142144003070360310003611307441400108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 352273273 1250 352272023 352272029
    0x80624060301030b060d030c170c16030f080a0210090605070f030b0105032a030f0108190302030a0305041514071b051e0a06020d06050a050306040f03141c14010807 72
    0x3081d1200108051707043c0200d50409484c000e140641c1204239988646020340c0b44944c0300111011700260741904404180062088845081e0710340c5440780c6552111196030030440d1020b00310f4840040c0d81c002040c02085588000074002c0000e22010031642880e80080030100d41312000300b200980c40480062007413080003080d5805031100c904544601300382c0b101e0700042c3e1a10001604401d03140425500440c0302852103940c400351103100395030404081c1405d1035504140c0d840041300f080600fa0010341c0110945000c5041c0d880c0020700d076955070030811045802100b002c84c0603490315420080f10026480351510070002612004140140840c01c014030501307000c40a0100d40202d82c0010382c2c0341740590050240007a180484213140a03030b0702e1b441c1c01c80e40140c950031141c40d42c43400d00700202e0400c03c43c058005c28048018001510b41626051840305805800904210801080e090f003114100b05540602c00140c800c601480c411028090090440c1c034404030b0566800b40000400030000a506025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 352274523 1250 352273273 352273283
    0x50406020a0806190e0703020c030c030a090e0f0406020a0903080c010903030b06070506130206091206040b130302060f22030215090f030a0503250e240702130608062406030103 77
    0x40c4c51901504514428014100c0402c040c2c080099154401c403c0002e810000c0c4004c000c1c540d120400f03203001d02007000950004680f003c04c0c204000765082d00c0c805503503005c3d0704841c000d60b0314400600115082c00060300002c01c2508007103402003800c0015482240764078800c1d142000220b950408010190040180041080d030082000910050844007141c01315480600080d007028065170005441da000da00c0080c489034000c2c8208000d01400280554000075000030302c14070a403954034000c0d01c580000306000002100c001c04200fa81c080504003c01a42c550720394001c3c0001e80e80345c000d4541e41011500c0840301403c2c00425200540440c024200003c840700840ca048041c0205544a40004049a5404800700314910220320f44035910036074407a00d80c2e5500d900c0394010342001802d0602e280b02038041007008450541023030703d900840c2c816a404860034040d001c00d070381004c0098100b0307412407070880c001c00062211244007508a04010503201c02c58002c0304c1c04010910495000900c00a09 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 352275773 1250 352274523 352274569
    0xf050609010c050309060f0705010605041503060c140a02010f050c041409071103041706090706092d120c090c051b03090a0b031603110f03090f01050406020a0806 71
    0x1503203601840305a01098411400d4904000350f06000441d15004102003c004880008030401041001e00c02e050142400b16420441e200200d003010a110304a404001d00044e619844540380e0b9001e540c0e0000c00b40141043e15503150000030000340600001070101c2038440c2008081307600c4110318801d40c0c040e903030b031803021003541e89001d0f0401c940300c103024100c0401d003d0359845c01500900c0520050000c6c1c03641b0b43c0c1c20400000072442c5586440401404500c5070303040f140b010b2107040d9012030b00100303c5810b40d1f402550b0b09403041c04000100d218500c0189040141e100009401045a00c005071aa000750703100c100b04c613a81c2000009498050300170000180007005042ca0140310351a0b40415500510300722824004540c0214406c03940c1c61f01328060011000c4100f0010666540c002c2e00b0a40e101d24090080101380d80340c900b140e020f8848400c83c40780e008000541003402c1007001c80c4580c3c03041d40080c80b140c201410080700941c0400d00d03010000301c2050025005040041400550b8100415880 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 352277023 1250 352275773 352275787
    0xc40080705030a060b0a0308070503030610030e060a0e010e030712080c04030803070f120911040b0402040506030112140d080703060b190c262a0a0f030905060f070b010f0506 76
    0x82d0040100e0305e0801d81c4040d000c000403021070034020240020348c0c4110011542d0307080071010814058007450f0008209030404511908025001c00e001d074000072a000082025503078181001d02402e01c2c042d03200014030001c0307401c07002d0044012204071010301c07136121110304da200d80c0ca98070070030b2049000242151400b04082150a031243d03001070080141c03803410018440300341c030042c001c1e079501c080c2c1031310f4180142050000c2407410b8442c2d12000745003101c04504e403034a040c0210350140014810042148440b18800081c000c941c0340c0d04501002c1d010945124400d99600507000c002e051b01c03a10b0001740303000c402041506220084030420081e8a10400d04580001000c84558089020031601c0303000c0d0751013148440c0c0c140d50283c00e00c4444d001c001070b11840c0d5911400c1d151a07100014ac070b01c0c400a0703003080550800210764000075980181060100344034608003034440803115480b40381c2069000850200d4643c004c6c01400910307124003030f007011590361805041c2138403100f400380690064080020f1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 352278273 1250 352277023 352277033
    0x15030408160c0e0106020c0306010501090807030312020717030406050a0902010c080a021f0b1309030503040308100509010b090f030a0201020309061804061d1e0c40080705030a 77
    0x4a951a00c90715248040c0b50310b0300a150f54118003079010074003607406402c004406140610165015103000e2074000c9080e443d0025056480d003503480302406014032029048801942e6130111032400350801c6018003481803800c0064040d60040310152074031440d2001144509541d8001c1c0c000f403c0d0142c1d2032614081aa4603084000d0344615031440a500c68203104281210340c2c02a9000d8400383c00400003100001041841003000c01000d1950559151006c0300700000e401c40c082e01d400941528102507150f44505940280c5410b0b600065400b8200000000b8a42010030007042821800d444840d04001c00409165a50152410003409030700207100300c00150400300d020744030048034201018101401e100101b07045880c1074228080b107a1040046c030340c00d03011001540340c1000c41c00401105085032081c117040c0c0e1050281000c09800e400045100d013110328a030101c0b0942c28120800000d00c504100c02c4403080c1c0020b12aa820200d0b120400512010081810070407101c0280c09414086915912 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 352279523 1250 352278273 352278307
    0x510020c1b01030209030a0606060f050403080a0c0f0501021201032001090e100e130302010c050f03150a0825060f02030706050907180906050a0c020d0f0210020d0b15030408 76
    0xc01d504065080c02122a242c0d1704101842075103005440000d400750928000410b056040d1000005101007000308000007078185088403029134071441d0100e10801c0720b1510001e146044c00700680190f00200320a45504218502c45040324441c5000624102008612000c41c1d03200c1d02c04140804c401d140200003200130300080c0c03640102c8000c05445010340b40c05202100030300c00c2d5021010184000a40804c15409120f0841d201241d070800d6403c18850012440a500c00100030981040c3e51008030005900c0c1c034050f0f100500607801c161001070800c100320403480031607900e501c0c00040700007100040080c0525000d0210030a2a07000d0341c90314034180c6503100034040181c0461014422520001000d000d00304041003400703100704002c40c050b0241d003421019940058030381e203505c40c80c011400c030549400041c2c4002110070341c02c1c1903e240c0d004240580c02c180b03204d5560540c1d9400040d0720107400c51a548038070107007401100c60711310110895509810501040320003d000300b5081150590750440124 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 352280773 1250 352279523 352279573
    0xb0a0b24033105010b10181e030606060809010b0910120c030c061e0314010302010c0302010f02190314010302151c0f050405010e0f100f02090a0e01030510020c 70
    0xa10070707442c0014030500c0030086826030360a4950b41d5546448a54510b4016062000382c0400d103400001e000d00c442c902c48420318940304030116100300400d040103608641201000035500444100841c644d85e810280100e00129034480083d40390602d003040ba407400c00c0c07880d03000d889a145540c902d2800d00d180300001c2c2649241c01ea0b44d002a444002000445034150710000e0b0140381e60b400c00c2030043d8281c40614044d044e0703164041c181801c04944c08580c0301014036044a809103040300401143e800c09900501040724180c02807400050800407442c0c4420700441000b05966080080210100c00000c0e8000c1c00c0c0002544849030003560740703500b03006402401410108484e00824024220602c004403090380e1140d1010985540800c81071042c02e100d250543c038201e10103806115801040340c3c1d1034031114414042c00d15a10001c07120b0454142e816100c10200c0030307010440690301c40c0741c0c0c0180b1381002d00c1700b02c0e13041c8642ea2a41d040345584e03000f40c85550303401c0c1c4000c15103100e01400c141c511500a41d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 352282023 1250 352280773 352280821
    0x80f0a030209040c0e01080a1a01030504032601150503090703170d18140c0d0303180f150c0504030804060302031e10091a01020a021c0b0a0b2403 64
    0x20100244659591103450344ca01c2003078441e040411401c07000505a458020301c40e10840d840e0014007d01003007030901c0703513600d2282481c001170b0554452a0039624051840394491480307181030000c6080031542c4000700c5c180c07a600b0b001400303000080c401c01c0303d0505c0203c075541155000383c00100300040240f1072300c004c1d46499401c282d003440d405c213460f2022114003031400280700070417507001814015040051102d1000d4080502050b146080105604140d14400203041558511901c0f520420301501c0310680d642c0180f00c41c900307102900700726080c61494850003411501e4607524070f0300240150102c408584c0c1c000325003410301e45403150940080d00014980c06000400b210005001d004c07400341c0350b1044401030340d039910b8581407400003012030b09100990000341018030140d08142c1c3c0c001850105465044580340c0c035010581415480074030702440000c01d03d2010600344030107810b07140c20081c070100060b1081340200311820070703c9918092048007480c092008002142c3d0b8850200b59100d00c1d41c6030a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 352283273 1250 352282023 352282027
    0x2011d070302031e2103160e01051c060512011d07030f080c03190f0809070f051203040510021b0a050a060807020a150c090902040503120307110321090109080f0a0302 73
    0x1003400014407241c1c050138500e449000420030003140c0e0b1214203c52100a40e203003941e02301d10706400103091440350341d45c81908001251146907802000303406c035402500b00944541c0d001c2280d90500c901a107401c8250515000051450340c10030319000a4560840f500009101c0d00c4004946521070382d03a2000891000074002045050689948903030682d01c040d1040e0b0717541d0140c9920103002006010040c10260071500002e6040240242d11040c41c0d0a9405c2103c05d5940e01c0c81d44440e4a00d18441c560000d82c110072036446405000e0b4000c01c413490b03070101c5440c0321112240110108000400719000300d55028582c1700080c0801c034030030075400d42d004005004650340003840c0d031503034046940c02c000701e96215912945800219a40048c1d41d06c01440c3c0020194201070030540043e8440c41142c492000541e40800003588551240e0080c08800c00c062050307980d1b980030110070b10844a8084603c1b480a0904c101180c40700005100c0d00303032002d802c6056241403006070400f00d942130f801141d1407010183c003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 352284523 1250 352283273 352283293
    0x636060615200c01120c1101060905090d11061501030902210d08160536011d100e0f0405010e0a06050d0305030402270702011d070302031e 61
    0xc003442203500102030b6168214a40e401c84030304142501d186000c41529004103052201c03a90f00140031007040e501c94500450a048041d074100c601c0d06100350040c0366503003040d900060205080e400356008144a40548241e5201501c00342d032000b028815214956100c80005070240c2c401c16101c450500b014900030881e49195000252074140c80725298006102c00c60000d2080300c4d0400c244e0303e01c003000b4104210145442c0b1000b40c000f2450b880310300103004c800210350042c1c2040303141511103403031410351500b038a81001d8800e18100031460400c50210303c901003040124501212a000d44203401082e15020002c2160f0454100710f00c0b44d691a00f0840c0000300002c159128001c142c041c00b41c02d00d00d0074546ca441c07a039240076030b501a4003641c06582180c6990000c607601804032130388a6016580f4180e900c04410b00010381041c2041a03881041c05001407100d0b965040d00090f1100120508503149009011201c6441354000d2000a40c1603025100d5007440d01d0b0f14460a08400c80d01e0f10035640b0340c400d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 352285773 1250 352284523 352284539
    0x70b1e090603071206060201090803061207050a0b0409050703020315040e010204080102070f0b0f010e0a0506031006090c021b0f010e03010f0e060712110d05090705120a06360606 78
    0x200b9181540030034002c07007084500e0741d031314132490005190742d20003800000d60940f5a42c22a1001600060103840c40090a901c440c20420000c030090001030008031006e0b903242c402611940090003010b02c118206404544070f24403074000e07203020701d204081d481003c200650802005241012603458075540a000000d1181005c2c4050030340345000384910308000350340c1c0c0390107010803200038405100005c80800500c81508060320040d40300c0520407001800b41ca80700e00117860b19080103804002035081c60004070310394007940c0000351402d500fa0226100704a092070a01922182e11040301e07044040b071440800c040d803061051485030764014000103140d00d01d070030342101a280036100c203000d01d900241c03c1c0940c0350b6210380304200c03002d08041c04016105261800341038521440820981543e00c03500401c20282d424082c0c40028000181026a410071124040f9203900206d04203540c06031800300e0b241807855800c11074910041010154000410300c802c2c00070b8550403446815903450750b858101241e860 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 352287023 1250 352285773 352285777
    0x2390901090b04060b0a0806010c050a0804060518040603050c04090f06020d0615050703020304030f08091306060906020c030d030c2006010302090a0b0a1502031309020a11070b1e0906 80
    0x1c9441c0364007151660036242408280c1c0c055038440101100c0030000e400700254000d2141c2d4200d1800d03e00140c02c400d50f803c085251600515010b0111040060b00040c5190000002c0c4000100e40c110402c00904101c01c0104640700c501c0094919003162848a002e4581070303024504241c407600341c428100301180c48a074101c0e040650040c4250340d503040d05108510b070103824003400342ca46190052820b000c2340c2c0c00039124015484000d0190300c0240580e0200410403080d80c0c103034000036211205518003040381d64083e040e0b5100e114041000740d080450f103030b4404980c0e04480b04c07000e0000c0241603008001100204081001c030001c1083c130060703101042c0313503208884041540c04002862617504500400650040180030700200324039000c0040f00c0b5480d150000022603454407040103c0421030101a0700b1407150800802821761401008518552941e028203031400d0030b40d80c1c0d94a5070803c0c2000684d00c500a00805890754400d001e4019503001c0314681070103001180211600f400b0b4158041a000c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 352288273 1250 352287023 352287029
    0xf1802221e180f0209131a0f01061107150c0c0909031812060b150403030305010e0a050c0f0a0e09070305060405090102090a05090a0b03060405030d0c02390901 70
    0x110401c595000418207050051503181c01200b002414074120719070700c0341e20104081d00700030300814010307000840041d004040c900501c0e402c134501000d031000540c01a0f44181003169050070300010305002144542c07140c1c0303a01d041c0364884002490520300701010402c0c001d0f0030f90aa1030401542454810006044400420041680d01c0300418428580d180141c075000b1445c5509102c09003600c0304204000c05400741400301078212100003122034041b004140440d40c5020005c1078800000b80010815070305901090481d0035a4501c060142c030b52404000c140c52095071070b032045003020700c0001c28a4140c00000c040c0b040183c20f082c1418000710010600d007850864091022a6036002006620300b01402615844081e44008500e44903001000032903004050041074050000748001505480c003603441014076013002402c48805141c07924011382d40394000c04a80c2807136418107140307507541d40c0002605002c0484c00c10b00c4007000c480050040054091200403800e1036940c10848068076100c0d4030488d406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 352289523 1250 352288273 352288301
    0x21c080a050c0f0303070c08130506031611030f0922050412020d0f021213050a0e09150906041401090b070315050906090112080417060403030f180222 66
    0x1900350200e0b45505103846590051401d400400412100c158420030a080c45540301058a440345084201140828800e801040d0041000002d10400050741e0307840c0007a40186503109440301601944030754403401001c6078070301c86003014454501e81c0d00d4401d081020398007221b401000e00c8103082044a06481c0f080c0e9098500303c00c3c80c01c0402c0030980c10320070412400e01e141021044c922403600b009580b0b81c0e001e564080711400108050f02800350b00002600105802401c1c2130b446500c03002c250300c800000340c400c3d00151044003601c3c40c0f4010300c00c0354644104494030103480d803a81c45449240850004c0401005255600e004c078a00198610b450305004010710703075000901a0402028454246032034000c0c9106990060810516548001c0c10ba0f040d00c008102c0c0354410000361034160010300480d0001c50160490004c007200d00000001c07820302c618003d6409020104034003030141c040719003c40c1c1c9103072000b20031640f80c009410506a1700002d00d5039441c01414140310000b62604607800d055405034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 352290773 1250 352289523 352289527
    0x302090402130212101203020601270e010b0102011401180519020c070f06050f0f0705030903030d0c030b04062418120c0e060108070e01020c040c05030402101407021c080a05 76
    0x110b4821600005c0d016001150002e44550080c1e06c001e9582c0c0c00510800c0da08141c900c080311910301d040d45d48000280110304090001440901040d8060140040d80c140190b1a2140c10311826400007802d50403183c9460b480350610081820500c00b07000700404142d0001c8010781c1e1118031f1b01541c401001a44044800f500065003091410781c0505110340c0b0040c10401c00340004d25040d90303200203e032515040c0c400c410340d0b94002464242c2c00c42c0940c214541d414000400c088840164070381100e90760600ca80c1d03003004481281c604110807103000d80108040c0100d0703c0c05201103150002c01288903201d013800c1650034140f200452441e8401d158001d1f0403500070188160703080000c01c01d4150040c204c02030b0740c1d810030f10f40240003c10604c0010110380401c815481c3c20082a4000e0001c1681448041c000380080d01701d02002802c02c2d4010741c1c0490282c81c00d1070380400070030b2080100000a82030558403615000d5240c08200469880041d55291015a511079174005070100d80148242d28040d2500344d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 352292023 1250 352290773 352290781
    0x61407080403380c0a1d0409200307150e0a090509030705010b0d0201020c01080a0905030301260c0108070c14010e0a0c060903050709020a0e03060a0f240302090402130212 75
    0x10303020105040181c0e290f05904803c1c80719040b08001510010100fa1814903101d184c1407070850107400d88944465005171401d00800c05000b18120b0310700d0704e41c510648042e4191034020074155107000034805e24002080808202100030b1040e402d900e1450f1000741001101900c860348070f805c8034410b6480440c41c0e40300191034010801c0070b01a0700e10860781121b6079a40302c1c0b11a00080c0d1241b030004140b50400507410700140f0f02040030b0388400b0000c2e40290232240c803983c5032210007030303c46c81001c418184907280f0a03100103010400107890901c00010b030f4506901d034a404200365400d540d40c030340459010b06204103c13440341109104002c9010200c1006200303940b00c0b0305100c030b030101454016408100b2404814808114002856000c5460b603200050b6560481380040303400002241082c2c0c0d043c0524401e00c901380d443c980020007000b8411303004002510000071403401006107040261070301d8414260400141c49d1980da2641e04c14000750080d101c1403001d01c81d140032a80b22903c901036440d0320304240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 352293273 1250 352292023 352292093
    0x3270f0f07080c010e030604020907050c060106020714060a090b1e030907060311031509150319020102060a18150612150b010504030302060a091b2904061407080403 72
    0x442041500703085c143c1010721902c020070b444000c01030000e4000e0001c8000b2076031103482002101c1c071403600751007900c80360350f1160402034480e2014401c1080680b621280c039011441d181080301c2585003903480301c000a5140c88002c0300103400c201007800c08a50611202e041142600000790f01c1100e04401418085041442c06012a82e1304005200c00e81c1d42481009005081c2095051503140100c441e41800d980314500741c041600c41120f01c81c2c00d4040d101e142e240c0c40751000e0503c024103200f40c00741e480740d94600c900707030003207920350303c00c034481d4002682030382e030108098083d41002c50039500c4000c18441d4a40c9c406c2c1900041c0000200c6641c100c01d21800b01001e0207120300085c1c90303024a0528981403840d00d0082d40c0301402b52a004845503200b01c05820480400100600c6030746d804c807000c22032942d0b8000d11000c922a50703560544c00300d4018250128a00b90b20895003501c031240c94643c03c400c02c505280d503094018038803c82d1040d01c1004007002180c954210b881c9000003c40000011210903505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 352294523 1250 352293273 352293283
    0x1f090204031b1706131502040603020318030c0a0b0c19050c010c03020702090601030e071505070201090906120f061404150c1418040225051203270f0f0708 68
    0x100c0d01040c0d01c9004401419020070f0342500940507055117030208986060072090459a07030344401d0034501c0000c1c0044c18603059005103204202645140c00360300010340b1000c1e182c4c0314140c01c1e144a500402c80c0f03000047c07800000c1a80014042ca60b1f2400d10444ca050385441c000c6040c505000301c0d5020a601060100900232420528030510b003d41c1403070160741c04260941d0018101905240d02d404412000d0001049144024401154951020010303440003505580c070201040e40029420b42c000701d001718076800350300304940034004000180c01c083c2d00c41a04140c02140e0485103607447c1e1702c500205c0301c001c501c042e00403409000040c0c132a19001c0e2200707044615683d4210280040341c86a180038500305420340f418200441105c044203000b101c000b030000e1160144140c07901d5111403060184951220b10503d01030f00c5903084500320301071024006030318041290b080400c4104004042c41c586900072407414404c4d802011603c954681d00c00b00d07070070a800c03085082c2007a4846042004524000c0003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 352295773 1250 352294523 352294529
    0x31011121513090c091a030a06020405180c0a080403110106030305030a0507210e07050d06061406121914040b0702071a0403020f010c08030103050c0a05010302121f090204031b 77
    0x8100803100c480d43c0e800110b5101817044004a030b540341d1a9080c003e068a5103480c850a008060b9200c900321031400030000e42080c05024003031005071640d00507907065900d1041c02802038130b411a080805104044a40e500c004204804010000c2d942005900090180303001452103a261079850b1b20380f2003544412903400916020400c000b1601b411600c3c0c54a02d0059207490000b4004182c200300c1907007207482c3c00e0311684800d400000c0b03001c290050003400d5201c0c000760b844071b540007140c610a2000b003264a00604000c00100d184100110785096034202300d2042214810501040c50710445600582d04041154252149101d91003040500c95040c45600c02a1422200f15254910880300f040098090742c00024000c0c4210303078040449038002c80341c45050950000e04a5660760f12440e01c5030b21007407040c0b80c860086e07041c03600100d031070b40c000d0003a00e00702d800307171941c1e80550b503500115410348600150141d100711081c100041240541e5000810245000e0a598020f1241418240c0c0315032410b64 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 352297023 1250 352295773 352295809
    0x1113080604031d0d11012307060606170114040f111809010f1a0f031e01060201020f12070c050129060403230316060c02060708060310111215 62
    0x30440b007880340e0714040c01d404c00e0344c1c000403c21513611940f001a103c851801003d0301205040c4882c0c3d0040c001e0280c010300d82d581c070034142400416510311003960604401c688103010081c40d440144071660204800703030360245004101003803042d01c03000790748101d4008090305100880300003000d001d09240210561401c3c40140c42c03200c090340c5090031444a11841d40140c4c0160340c1c40f40b590300f26086048041c1d031040400350101c1584e030300b00b1000f66800e41944410116400750b48100008aa60041c0f090715100e000c0d0100032883d14005e44400c0c000c6050050900060100b081c0c4009d000c2a0244200d030f54600d18001c1900340141d015400409060107050011311909c001c100610024510120180c54011801c200c020142e9011202d13900310301640d24140f4030a602d107030054060203466000011401ca1b250255410750311003080454141070f088800039015401031a00345c0004090b40e0281c00900c2c0c020640c90b0402d60b0740042e001003000150703940d003403200d00b031800c644082c5031560090003040307484 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 352298273 1250 352297023 352297067
    0x1170a02090f01033f0215010f0f09020405061c090501141e1308070c0b0f0a030e060727030209010815010b1c1109040e0105070f0903020a09111308060403 68
    0x10030794145984006507444d21044204800c0d50300c490007005142603406250b40d46010641c1c441641d09d42c0750000b4030449803079481c0c2e0240082e01c084140f08803404d0b114060b00e081d1509020301005403c450326580c0850900e0790300c100c5100400c4085c0b0403c40080b180c408071a0a0782410300551650490701c01070006589400c01c1841120421000041c0c00140d010112a4aa54481c1000d0b100c0007866400140a0300f00010003400c4119a00014005501281ca040224044d411401682d40c401160b0b032402281c0c42280c80404030003040903620346900302da42413800700d5817242e000c07526038902070340400d0041d408880910300d074212209283d030151051040641c2840408042120310041100120f0790550381ca000034a00203819008a521b1040e010f0018041c403840764012500a1004503142000995a5603d03441068440c40d103010071240c009010740316203400d10881800400f50415080e807280010000b1007810140e24070310f81c0003085d9181c0605218a06810041d1000b507201c0b168500407508 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 352299523 1250 352298273 352298333
    0x30c031a030c090c090901090b1903030c03030f0b030f0a0c09020a1409130507020307021e0a140303040909030507050d030b150d0e1006030c0801090b01170a02090f0103 74
    0x11110342d498000c03a148103030390b100c49200d80b50b588103045081d078020504600202c4c03a401c00360846012010241d4178074141c01e0068401039603490b1540002400901540e4030880400d100c1c2d0080c25001c0c600c01d10000b0281d040a00282c0323801400c442501a07070b0000070b90101032004881d245401408014800c0d8031303000400030b0041141d0803030003c1030a404408260b5000c80e0722242141c1c100300764401020020390400240c040e41e00e03000030320200d1180d0741d10155401030070310070701d0289203084024148075446400e0007404482010007100a980500c030601c00022095a2805400784150080d102c16985541e541000d0b4200744456004800385401d00c03125814075210030a1421003901c3c1d242c58030343c0361203880e03094034042d1141c034071901c12034403030f41e4164890720001d48c2c850310440b8030a50310312001e1503030341554a082c0d500114024065101c510010480b1140203001c503034a01282c90709543c244011903000070f202c3c84003070754180420088807005008100201a040100d02d15102d060030305292 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 352300773 1250 352299523 352299529
    0x101d0304050d030c06020f04080d0306030b150312031312020703020303090904020d0c08071508090a060509072408060d050a1e080d0f150f050105070c090c030c031a 72
    0x4218440c09010b182d885114009042c49a007140c074002c0d901ca00c040d0b640300030f10103110485400a0054156038041d41803080020b0340a0300c110b9040300e60020040d04685c1d6120360f01c2154100400c8580e40501030440750940d181d1054008505c0b403900ca004589c1c4101080c02c1140080e1103401e44041594804001071000d0380e4000140c6c1d9000364100c903442100d588910119a0945030810005c04640c0500030108039003602160003000d940d0f40d202c0c10343ca11000b80508a0f40c2c04800d5811141039080703642d100001c502a40c100580c081140c40407502e4456440502d500403c802c400345090000c0c6014418800b15030083c54603422203811148010708008507182e483d283c3e12210780c02880f10003645101c00410740102407902c0c10310741040d451511524400c6140024000406008980390b24200850403aa180f03100c0903415100c2a2008030503590804005488540c0000d200303683e0340303240601c00149506180180099034401d0341e404a50072062010160030347d807003500480e0180c0583c24810b80d9a803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 352302023 1250 352300773 352300777
    0x7050a0303241e170715090503010509070302270606030a0b1306060305010b07120815130e06131a13080c0c0f150d02220305150f06090403080702100608101d03 70
    0x50702c603006c2e04812850000261690f01720750340280d405500340740c01c00110600206003213040302d00907501c0303030802e03080100201070040304a8121020003451101041c85803d0681c05554416200480050844258000039000c00390f0f007403032000f800b901c500f000e02c180c1d031b858042c203070042080700f182508240c42d590715620051000c0e011101000b45200000e0300c0c10550001e1654103030400b80000407042650300c00300707024007111a41038602c1c2c031038076001c103c450003480c20234542c1907005900c0d52252060f14548403541c1101618542d0b9003640c20720704e18007250304a401060300404210040010103840300c2400a961311a100d610320940706072819103c201c5454040f41c50000e200c44005039501c51404040400f060768102c41442d11980b1040441046000200c0400e82c49600750f146265946060083d10b005404558032504840c070000030800007030040242e83d40040c03460040d10184542003052000700d0340658410052603100701e241003148822482003002c21190340710240a001c1da01d40701c8640e64 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 352303273 1250 352302023 352302029
    0xf020f1207030618090c080f15040809040f0e06150108010501200a05150c130b16061e140f1315020406020102030610020307050a0303241e1707 63
    0x25040e000505014482d90101014003002c42d40d000000c01951080c0c0e0041540a1080700d04200d0300740007207a407203000100194128140c41c010400c002d12404100340089014008480e103800a00c541300302e0765240e010314141c13142810380000d10100822052403070508090030040c2c249248807801c081036640a004941540d4003801d01e0b25690514103520b1091241202d0840c44900840295900700728001c40c00c02e481d08524400c0f41d0303e035255034444003010321401d85180d042c04034420f4100708013400703d806003005101380954452004a9034941d01c040d90030340c04190804120702d08001c0c44404003441045e10000f159045600e443c83d002412100b05000074104d014540b8003c04420104400b05141d541201316420089d502c40c1e03550300e0301a000c0c0d041a18070901c81d0010100c104903d80c40003054501e5603802100400300913400d80c505070014240d1121174400b201403c007111850403104042407009160302a8010010303105010705d4900d04445801040d40ca12210b400c240040800003140015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 352304523 1250 352303273 352303297
    0x3020703120e120c0307021f120b0604080f1c0e0d110d050a0c080d08040b0703050403020309030d050904050105030c0d030e04021603080601120b011407020a09020f0403060f020f 78
    0xc101101d100052400c028001100c000759800180e8040340c0c0004409046c20034402e5442021a40203941d680301d045007002c0c0c42c00700160941849294a6840ba000700c0e1038444082d00b0145130076200c0b2445401c1c5240594031b0070096100000341c007840d1f020340e00383c4451030350a0314250840d040d101d0005031282500400281490001c0000c004240d6962010050034a80c010115111040c072443c004000310840d00c5420010300a02c47e40d201e01c94001c4035070f07520480c1e00184054003035039003c0d015401468060401e508500c41440340034042e4504001003103202c540d035102c1d541c40340d00c03c2003040250380d4141c202601940000389511841c0e1900550103404561508041100a40d0800445c00900801c41400581c800c8061454103041e0031442807030081400780d80f03070189400a0350f0007200b03503400c43c031150780090401d030030144110708030320003901201e4401410f0301d20f003a41e0b0340c2000003640c02c0351081c0380d1500000179081007088440d1081440c6202862015414800d41c072403203083c103000d541c8803919 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 352305773 1250 352304523 352304531
    0x207050609010e190807080f1912090305030301090e070f08030403030f030e030301090618060806070c0507090606030e07080601030506010b030a0b0a0b03060406080c0306072006041a01060302070312 87
    0x1a243d983c4e40b560014a80f107055020b044140d42d03078406581c4800078840d02a4901846443d90200200032604d408591085129034402d0b00007541e444084c080300c10555403c000c0c25a40c0440010300c1800150300070230b880c14001c600041c84d01d060500741055a8805070000028003820008420040155821070390541030403c1300030300188050300948001743c1601f82c9404000000b052170315090780040140c0e040d0072000b01c000312400c1103510444a16010381c00f80c40d4088800a103840b445006c1c40a24244120142c81145030b903030031000240c46494110750003185d2201e503c2031f881e080402403030b001481000300074882d5514544996803604410b01840d0907040d80000003c01d0300c9a6504211a5110050070b640740c3c040c0c0e00c0c41e0f80003280d001640d10601c5581014030014001d18000b405844074403004000d0130050b12400f0055541c40d940304014050882070014031000f0400c1489840e2140740500035616009890181812059105811502c01d01d4814480b41c00400d60044203d4a08110035400003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 352307023 1250 352305773 352305797
    0x6050607170a120c0f091211090714031518040c090902040b09090d090f03020603180f0706080105010f1b17090d030e0f03150f04230d020607020705060901 68
    0x42c0c420f180c038100115903504129201040300e80c842d201c03030180b0160350390b110070960b212006610020900ba801405a00304249141c1d0f5a140c01130165800c070401e030070808280d0200341c41d8402c03240c00440764000c0c60320080c0201d038501d06054040001c2d41d90340481558161415070795141051200340500c4c0e480a68654900045485aa20900781070800400c01e150038986564a940d481e200035441c8030000703a02d0100054036003500c100d1002580d034004c04650940e59810765080315200c0c40a9035090512860300903024400050081c000901404e0381c520342190f04010014004805d000a11340803c06c001f4078108500c682c001c4400c0220358005450015240841c900681500a2907101903001820f40c01d11010140c204410311b00000080c1c8202c460081004101925150f2200098500da1454400111112031000510398090b2040702a2080180044044d407890710200b10300b4500e5500480d000c0b80a240c04009203a40a4542d10040001ca42400042085800b5148031641404406442d078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 352308273 1250 352307023 352307027
    0x10f050907091a0d0204080c0a05040c020c090402040207020901030804140904030c0f020a08010606210b0105031b040806040803180f07060c031b0609120f0903200306150406050607170a 81
    0x13144401c021003000d40d200c3d61a40d0070561105003000c94284602e43c000130008850030302c0c0c01400c00c1c840c800d0f0083c204440400f0103000e610300c40208102c0e40950300308010401699501751043c003960180140f00d88560400d20140c18400c001c524413803080304a1400c11000941c8858a0305000394406402c2c4505101c91022070b5440d041c0d80c1280c0c4140d402d0010114165600105a8041d10301c0403c94070300c50b20466410000b142d204c0f5040c5070010740700304000352001c0d0504c42001ca00d080c4807080c4500d0942d071035108a0612006a034200c640080000620411042d0f4281158404c80300d40040e10261010b884102c0d0380d02d406209100030f1080100d030100038540500f0044c036171121500350701d5003245042d1500c1ea000382803020084541d980220f040400d424031400035110030107082e031901e58140b0704540b1542c140310507108002c1050070701400392141e147c07000d010700c0b40502124020804510401002c00c4280c5000d50072050240c41c06121503804580d04e5800e8069449070031030055965040a641 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 352309523 1250 352308273 352308277
    0x190218010e1c1b0b040305030a030b031203040515092a0402070515040512120c071514060a062303150306040b19020c0a11012006010f050907091a 64
    0x110319400d40341c42080780309120018020f000c14480701200c814850f9151200103030b040c040c40c08003074084c0e4000d018101c00c12703009a10604442100030112500c01c2d5400d40c1e014003a0f030048500f15000d4204c1401103103c44003010155412105400103010b550204111030b15049403080189202011041c3c40202c044c0c07680c0d81101c88558214007914080040540c08080020090314200d03001e2160b65228501e101140d400c0d20600c003003c2d1039040c080c0d00c8072000c88805400003cac040d51880103541164144008034800c550840841d2038200c84d0718944130040196901703007540801c0c18030410b0011095400c058914400c0d64082e000000780d101d0700c5220440059030000d0038000e4041c4101d00c00d000501440e00d040500c500c0000540c1d0380710700005003a0ba0141d004180b030400031030f449840f0440000d0780c05452880842010b02d070000c032807142c0c0a081c14195081c0028199140c0001e00180400c0c003224101c0d2029020950f150303106400d0102c40281450700728032400481c64800c0400240c03035012401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 352310773 1250 352309523 352309549
    0xc18070c0813060908060606031006080618070f0905040612020d1b080604060501060c030917151602011811090406020c1204080c18070318020409050303190218010e 72
    0x102c146911a110030029103079408501a4a14911030310000a603546000400c581c8134054070002049428a4020156030385030700035100940c400409001e452100301d0f00740450744681c6d40e0380d9a03260641000780300580b031100c1c1c0e508264061801d2110500c14501181e00d041819079041d9813004480004d0705143c410101c0c800700c1000040c2c1c250700001541c000002e042c90080d40121010416a41c4c1c4400c2601c0e1918007510050200e03034000c00402ca4640140c00b114030780e00442080d56424503004800028060089501d892150800301f2220074a83d4240325105042c16141e148c40103007502900d4005010092000040c4900a9500050204449501034800d900545030031180a104440c030744846642150003003e44502c00c402550442d440c00c01740d0800000013145a005a80e10703510b40c02c5016200c243e60805140c640d0009420058540f4410040c2141c00740000d1600ea082c142080101466100c030102001b50043c002015500f00405c00c1c286c11000c00d08118400d00440c50105a090f603042c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 352312023 1250 352310773 352310797
    0x3090f0306020310170d0507080c01140106030e0c03120f160b0a0e0a020d06020901030e10020a11030705150604090b0901060303020609160905280e0c18070c08 70
    0x2080000800c401500a9400382c0f01c0381000f04143c0d134407190185281c2580c1241400d80303500c04029284102d000390014003440d4001e5581ea0b00d0102401011425100180060001c1681d030400406c03005605100e2080940d100501030544d007410140000d07a29190350300c1000301c80354001a10000800a4400c40e0804d014a4140c52062002410013200380c442c02c83d072600314a802c210700310541c4a400308003104107c1e4020403400200d14280c4421009412400400c1c0c140350340c0e40f104400401c400c000b420700511340b0b5000075031f540a0340c11000300040c1c01415032103070641c418400100041c030082440078507110341850304081c0e42c0da0500000c0140003403c0700a80001d24030300c28040701c4801034000c54103880c025004c81e40d85403200580d02d40c4d6850403030070100c0413030003c28041c45200a26008150028600b41200c0300700420b840201c3c0081c01e212010500d89640c03013100700110304050001c650061011140d0b1051f0240301041d541d03a20800510356001c000404200c0010400b0200944400c1343d440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 352313273 1250 352312023 352312049
    0x31110051b0109021804032316061a030703020310050c0d0c020a030f08070e09041502030f0f01060906050304150e032b060803070b07021c2d090506070309 68
    0x1c1000714001c1042c02801e0f07008003940b0841350784282d42c405519004030380c1030b95a040d01800c03140340314103216800300c079201d90040100110560121403003c400c40b4980902c1000440e03421003910300496981c070215150180e000140100091390303001c510303c7e04445600c14040303069a60181040e001741309150540c1100e500d80311500401a0b4005030002c3e40d2840313912b039080128608a419649103030215040c40c0010b18605085409041440d03900d90090b00caa86c41030f00c4681c20407910000da80080342c01b10343e000500c03810400e10814407c80b41c1d0041c0348500b041d2817140e081c0b100090162200800261072240811802102d09159030700c07240005a408003901c3d2620031114082d50850010240400c004803010a0324088a015100351411a600300d00158501001940c50700b850741d0006010310154011480104036504061605200744400b42e600c100304040100c000400140400d2050b0880009101103142404e8011200e44241c0380b00316007194451074285401c40b030005483e0040050400d01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 352314523 1250 352313273 352313317
    0x4050106151110060b042c0103030e150306010c0204021617030109060602071d061512221203240b091f0f14090402131502010603111005 60
    0x804450b40100c00390000c16034254008003c004402d41d00c0340d003e015450002044100000b003c000407075088034056801450416503502d2080090391000da2003540805c0d518486540d03c4e10300340e81e20f4600032145d08607013400c1d41403920008000895800000f402264000703000a48203000b004080300441d4403039210b00e805409041c4002c03880d0420f1080524070341c00c0c80c801049807800840d5280030b5600215012034454002e00c0054103401000d8811900103003100625003803107444400030711020849200c0ca10721402c00d0310544e50002c2c0d4050100c2c900320160462000051960b401c0000140c040d4900490200e0b800034101403d0416002440b001c01e4150000040c08480a4003504846004840f401c0000703040380508411502c65810b01030000716002c2100030814003c052402501a1800050f82824130f04c0c1c01203000ca03441424403c1d0070b0006918100006201d00c4103107034003204544028082240703541c1d00d07003603881d9141c140203100d407469032140401e03240f1130343c151600450344008003052804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 352315773 1250 352314523 352314527
    0xc0f150c020606040605010c020607060e03130f0b120619080f0a060c0804080706020f071410050c190507050c0a061e090609051306090f150e090607080405010615 71
    0x412038080c000940100000641540b03403900c103402c2103078410f841300142811180d0070045180c2c0484d404641a55607249142080c400c10005401d01e4000800c5901c5100d0808550f09556085544019510301003000350704034401402c22015040081591000d61905011303c1d940c1e10456540c02403001d43c401c0300c0700b101034000c000990030101801b0f1903040140b002c04190459154400300d03005484610204114000070340140e00600d07462020301c080a0034035940c1c0c2e460710020342c0540400601d40d070041c9094024060140305081d0049560303040949450643c500d00d00403007030303003003a44014008007003849010b221050007000d407044c5000344440444c5032689005402d1200000704800d1081010401007001030292510500b82c8d0701d592150301800d490030003084904a03005010281c080d0300c0c0e00d00002c00c009107001d500071404045c600072552030000c0a602c4401d1110740d00c01c003005804181809000e210208504e038020066103440d0310281d0300c03800c05901428041d030007428183e10003464580c50355 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 352317023 1250 352315773 352315781
    0x3050f1b090a0312031401081504031803050a03050301080c031b010c020f04090b04030207120b16020307060501032001090f0b090a0f06020303150405040203060c0d11040e0115080c030103030c0f15 86
    0xc041441c1b44400d590304c0e41c001541c0d808602445424542402010801290003014991800c0e1f800343c50232110300d91070b56070f46428001d0500003107000c00d00100040c08254024401001308143c160b0040003201c000550040b0b0b08080309603051f05100040021405540b2074074020566442d02900030f004102c8035180103005038070121420b40050041d00c90105150819251000c052134101200340e146841d0740d84100304500e10721403640b05510040006900107145c500031580214026190781e83e0032590280d20912001445035101d04020324201c00740010700400442e0401d44203a559120b40b640b949101260070b880150f008091503c8a00c0e20002e1a554004019403184411850090b12030304060b00781b00a0350f0003500d000b5030680021000a103045c03c0c5d18050440d01c01204004039a13148540b04081507030b84650458800c1c61703c410014040d080500c0030050f20002a031400161a02c0c0c90102c0030b0a5000601004080049120203041440a8500d0a2440a4000c85840d10084403450250014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 352318273 1250 352317023 352317041
    0x20f0702090c040e1b0408100f0510050d06020d0b03070f14011d0904080d0906140106020d021209010314070206040209160e0603061315030303050f1b090a031203 71
    0x18084000000c000c1c4242c203003540c3c11039210481065a40d220500d0401c0085206440d010004038140000601001300b080400c8940b021a04001856403840740c0c241709480340146484101440d02108101a46910f004041d9aa410010058983c0c4809080c1d00107482c80600c11541481074060100d69429800709a030100c03400f0325000e0f80401d083c100150381008046840c80d001070119000f9442078100710503940d40c018410001d40345082c81c1e8035000f204803030280d88140c61056032111800b01910000200c540501114001481410b407503d0b0020b586414654900052200c0814800c4090f4000d8204d02407401e0b0100341c2c1c0e8041d00d0101402941d80200f21001d81c4180d07401808142442c0741c0c00e900600018403981c8070056603040d6400d0118a500203400b043c0c22610080c01b0303942d51409803103420702600c40207171000d10312403842c18010300b80d0314007400c85120305401c0f0050121a00740c0c80440e000d00100000070ba500c0300c078610001014000e42d5440a095008102002c03034140b58564001000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 352319523 1250 352318273 352318279
    0x5090405060a24350d080906090c0d0f020a0306020901020d0e0303090418050a051509060f060114130e070f050c0601050d08070821150315090c0301020f0702 69
    0x4803000020075405043c00c0701480071110f030402c200a01820704602d041e1016402c54440d141c1c0301854042142104001680900c45640c00100a0000c0980e0054400360400e0001c402440d19042c4000401d8440c1d08002129110751800c08601c1e040140706d0b021903408980042c02448042d40d09d0402d6400b035440300c0c4907940140503020160406600403c4485641032002e40194102045036051000070807109541e1002d1901d080740f0b100000c4c01c2008030800d0107201d01d014180c0b01100c0340b8102400c4101412018590f0008010001782841d82407460703034052000d1030626240c800c00441c2014a100701c045c0c5221120700100041510660b5400d564000d20b2180e680802102241d103089031240201c0c2d000d1001da400000041180c5d252030700480424600801d026803410420f69a03501c0e40c0c0d840003441d012400c8420082004020f09480c805600000c0f9010341504403c54400203926070450504156050180c1f102262881c5c0c0c041000108204001c1d0085580c0c0c10125003040d119040040100c0c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 352320773 1250 352319523 352319531
    0x2010b150a1d010c020312070606050909030909250f0e01030c0e040207060b1201050601030b0609010c06050709150e030f070501020703060b0d24050114010509040b030705090405060a 80
    0x8086003000c0403640e440c980c0340c1d51804940010303905400e407415000780660402c0004000180960b034140b19203507a85001d0200c0c5a5501d0b002c2c503100060303503001d13400761740f2a480c180d08010310420044201c4800340c1084a103a030721681e8141d40c400041006000a21540780307c0c0104045039074000500410ba100540c450000c1540744100441c180c40803100d02c5800074000100003411800c1039006010307020310404000c112802e140d004900324230004032010140760344030410f00001d03580510a0304030282c0140da98a25168144001800c00d40c661340e001040d2540d01c2000945007840b80402101800101d00602c0d074580f004440245100c01100f03002d44a8050104c83e4541290000791040843c2d0040e00034005651542d122480203150712004c050f0070140c480d001000107068041210008010100b003180c2d4030f5002c04803a411203205810130180440140d280250903031300072050b6410001c2c21140403400c4484040800c2c101555a80002c4c1c00410704010321003008000300d1190711490800c20104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 352322023 1250 352320773 352320799
    0x130b0d020703020601081f2c03030f0702120702091003170403150e0a030809073f0804170307020619111b0108090f1608120403020a090b120a0302010b 66
    0x58840c0e00790340140c104900060003040b40d00c0c1c2503070031205880f140c034610b620038040440c54261500380352310813644039508000304006440015080d0b840c1c1004052000700803512020950740704c1e510440318081e1155441100085000a00c10070a9000c0c590002c00315500e80790702c0024044d160407902084a00b00b00e8010f02c079060030304902c100540710500c04001d091000b442d4409460f0a00080c0070020075005054001c98040c800d005a042050044060b12407401241002c1ea901e103d01481100c3e0307203d4210140c0e101048a480c10341e001d80b0301c030026802c10055070f031602c1d40c0340d40f05284000703412110100c0c500c2d1b659140300c000c014407108582c071190155143d2903e001c1d2120b0600056007540705c9025281e81280d4402c1c44950750102188045074030740603100c0002d924003100b05c241d00501c41466075040c061118240980303007210580e0040e26052074210b40c0000d010200901600c1d0941c0d40d01c81d000011540c3d40e0301054010711402d4203546103a030a0f810002c0c043c1c591038a00700d0091403281555 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 352323273 1250 352322023 352322039
    0x92101021c0902030d03020c030c06010e100617070f0201060e1906051009090507090504090b071805011b050102040510180501050906030f1b1201090e030a02030d02130b0d020703020601 81
    0xa0402e0720340c010003406100e081300000b82c000f9044288901c0140c84144030307541903d0010000d2901800c02201c0b005590b00d081c081915201406070842001c0005040e141d01881c00707c013013542e03003100b11030800500c1c018002c5022801070220390b21040300280300030300340a00042d5101489061134443d90313041c0034035074540d41407110300308030710300884005111910100000000c80e48602e400c01014905040036650781c000203016640c840704103641880009050049058105c0120034603e000488230840f0b0a28000c00070b0a900100780d40c4400e0401042d074010308026084d411200940001449424020381d1784100814441504000c940b03040341d00d010105256024409840350342a004010342d1841e40c0b1080005114900a0041300c0e1361844e00765075080c3c0c0d00e40200640424188070702003850541c90145050141c44020745448007036001080440340055002c006c40e560398036060340260303451500b0748050b224602d0a40c8000705001000c1007044481d0362a400418070725009608403226646c846c050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 352324523 1250 352323273 352323281
    0x9060c07020d0303021c020f0a081005011b051608030d0b060412030c021f0e0414010501051605030405101d0f061c14040c1706040c0b092101021c 64
    0x1000e588000042d1211000038403030b80080c8640c03010314000c40b000388541d81c3e00c1000d0b600100a0300c0703800304022800b0140960700200b050791105840d10402016464040080c1c0203c9030750200c10310131000d030803510303050060400a80c001c2601e00b02034217246d10b0b5600c0145e034580e08018100c100c034038201280c0d82020b01d8001c09660660381890217550f41243d032a078087d84e00505960080b03800216010541600c1450008116407408164a0f202d1401404400304000c503002442c1000900c00c4441c0188902d0f40d110080c1c07101d50380d840c0c02c1b403554904103040c010715500840d4030032a0f2141d521043d4285c40b6034010170505250070008175503c00c00034140b0401c0000514808040e8002c1018070201700410086588501c501d056000e00148a00c0140249600118220340030303290014101010130019514820509884070800082d05440c1044d5807100d00c0045c081c031600444d0500410451040e03510f9201101c0103000d001e003141548440d00c44940d000c0d41041e42c0c2e4242402d10340c0f401e81d01c50720403805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 352325773 1250 352324523 352324537
    0x106051327050a060507030c0e03070803090d140604050705090a021603050a05131d100806070c0314030702060403080105030c0a03020d0606030f0b060f0f010203090d02010e13020309060c 82
    0x78080c0022000d80307455a6005040d07901a6554482c00b0910400300d9000d1007041e01500582e500441c00510498000d0180d900c11a0100d00a42c44690200450b000110941c0c0b1080b07800c50765034003442d4040c180101001c05480302e0540a00075402484100480014480103c50003911004c1d11983d400b206003049018002d101110000402140d1740001d10442c002c0c10030405905040342014000700c0c16680c108000c0d00304485940e41511070703410344585030486ca85c1c880c07511440c2c1200c65003001d40d42d544641c806007140d0300340007580d111881007500905006c2000d50510103440e03101d14141000940d5200161429004159540d00100d501e0401180311083c160000d800d4545080c0f0b03550a02c6808041d0700c9003500c00d941d4508000c400280c4810100080360702500ca800024101001000031102c2d00003a00c40c402c040c5007040f89100c3c4d8000c403d0350035924003181c140e86000402d00040e01c4074502c540d45a41c2c001c4251a581c510f0030310a43c05180140884402c5030f155698680e8400242d01c6040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 352327023 1250 352325773 352325801
    0xf0105190303170402011e0e030c0405041707020301090209160906020601152a05030a110303011d06040f0f021e0408060f070315030b09100506100c02030109080c01060513 75
    0x11580b07043d40fa49004a034001d1310602d8a04041d4018072500b03440701d462011003400260302501c1061103031404010070032100c0000c0780c00b00701e54109a9116280d90a441000351007071740703001c501038055603030030340c804601c80350003034909911480c002c10f03d070018a002c40c145a010698036540421110710000b11203041c1c40700801c20301c5109441c10026900044400b030140a2020a8251a40c002da00c0f501c000000781e03ca070000f10b03125800c004014203034805504d800c4032140d01c2840108240c0617000285600001804c94240003502d558021401404c410160810000e09011800c6144040c0d0b60081c07210b450313251240031039222010071b005a24031640c4079490440d40241e0100d2450084c0030110741d000903550078006402d41d2250360405861f00c2c154005e484040b0500200b02e60f00b0300900c0840c44c17010320020104201d16003040000c000c048107800d140704100441d410f01003191425032201060030307001320b2259110000580302d070340038113883d000c0d40c0d004041c00340c41a18080550f000d00c0915402407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 352328273 1250 352327023 352327037
    0x70614070e060c03040f06020d1e091202042315040605150306010c05070902042105072c0408041a030921160b01080118020109030b060a08060f0105190303 68
    0x201003003000b581c10241c01c60250380030401c400100410116090b80c01460513401901c3c1c104402039002e041d10320b449a61003038070200d1b4922410381603403280b0340001341c90000510b199401000d001140042601d40400c00c0340c229900004010381d01045402440740842d9680b085405204c0014401620404c1c8969500f001649103000145001c10010b181d210034103240514200705151945031402d1140c2d80050907441c1e00280501c0510b0806030304090004c41e0342c0101c205400159519503407071070280b003584240071024a0382c0600340301030204698804400b100c9080d032414a0300303005280f43c3c058482c074250034410346031701c0b11030440010a9a101c2d40c101d1020f4003040c6a20b60045039501445104804ca04030100400c500f00c1440f1181882d8a5000d040c03142010360400b5001400c41d8201c40011140740070380d20940c0010313030b400310510701903e0b440240c1e012181c9a035030100e4000324658004140c3d1780564802c103d541c4240c0c0d6802d41c1215400c4403600c04c1c0c3c80e40055400500c1c0003034040940004d4507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 352329523 1250 352328273 352328297
    0x1119151d010207030b1504142401033c020d06090b090705031902090d06020a09050111250306060602030a020c0109050d030c02030c030f07030507090203100e072307061407 75
    0x14441b00395001601900104200c11407080d640da01d01e600319000702d6914201d0003540e400b500210341c07003e8001828282085400510800440d001c20920450180c1041c458101100c8030701020301c04102c0181c0207070540d1100c410a0b40390014051034050030032482d1918444c400d0510b06840c1d0107004169944a0351315546519070941c0300040060300141d1300399000c21450600d511880b000f200128001c490058841c2010b43d40285150900e600247c10001c803000440c04400c0d010404000c60101d401d041071f80014040521980341c942684098012880c011000480766004001000440c016900355a560344a1708015140c4084a000c0c1540010a80807900c001034005d103c1c0c0801503000a0072100030f4600000002d1a00134182102280c50f0010b510400410030208110006040088001d60462510725050303070704043d0314455004010703d064003107802240a20080412114400400000b070760b41c8141d0051242d1004100300ca80d80d1070701800d08070000340c82d88003078016080d540e030b05150900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 352330773 1250 352329523 352329541
    0x1005010507020126040b06090f0903090105070c030506070c0507170a06050712050114010f0203030f161803030503060f0105070c050405062707030c09031119151d010207030b 76
    0x84a950401d0f06094601580c1161081480f60314407586c13007592050300500d4881c003405000300000e03044c0c48103020900140315207c04040117840e44171b542071038032503241c40c11410b0001045a60f130384081c0c800e015003824042034540c04514524501c1c080e030100c40a082e40e981d00519411002114014160003551420000038156000140c1064440c603041c00966400114503007140c0302a801804a54044500840d9558028003000b10090311030010314194034129450f801d0070b800082650704c060480c018040c0a0a0081e810504004040c0c08512500e83d201d01e13014080e42e2051364410b100da02c4621040c04c40350320601c120748a0b41d60022203402010b1030941404042c01340905401e6021a50030511308000b424515a40969581c41100c02024280700300003404407800c80c2c800c142004a40d105c1400803c99000000c4815402914000346028640090340e602d11425002013400300c100400350203006620028900424961070043c0d00000c88081c01682d480e40288030003132002c001d007800a08801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 352332023 1250 352330773 352330787
    0x3050307050906030a1a010f090b03040c1203032304240e010c020a20060406270e0601110105090c060f04050d081209010209060313050a06051302040510050105070201 73
    0x3030480d003000d6040c039070340b14001001c40c4c104441050100741d60318003213000140c40740400030394445e00b824420713600602c00764010102c0600f8040d0145045002020404004e80c0f080030000820001014a07141d0601b0301d0018090100110140070b0711110740150312200494500c0740d4040c603440209414107010190b100c0121160740004000d40c190346500c0304103100428001c1d000301e100c0e642e029080c1c8030444d10b0a45c489420480300c03a203d81040c0c01c00c1108988540007100d05603a600c2c1060400d0050084400c41012404c0013003188032400304000041012100c6001406808240c0307485a901c803a01c0301303480c01c031001202d0200896000c20340002003400c24100503c0351082e005225481c194551b4007159405e00354030b0341200c4044001800088005000a10941050700f000082d450702e074120000900392300010304141e6020095082d2031040203000c1001d0f890b80c550011080c00f032890304c04285461281e150030160f004074200400540700500d40c404007816078005840380da090141540044400c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 352333273 1250 352332023 352332031
    0x403050d0f05310f0620031c020d0f0203010e0f090712020109080d051902010b06030f072705040c03050f010303050a2706031d1011040506120906090f0703030503 71
    0x4a442100c22038101e00c5030301e00340c001401c0c21134900c080062404800070050050030408600d010440c1a001444a00100485c1c840c00c1c800c0c10001c03001c510301ca840d44000d1045102c40310701240303484100d02e00803006801460495514020f4440d40d07030303500d00030b80700a00421101d2700801d40040409000c0c0b02800d5041c0a00a8010301d403042205031500180c2d0f00d041c01c031869000110b04085100071074500c403034040c07414080f4288000d1000034902808a1038602020b4409101d8094810020b1012131046450f0100f030b01224410b545003180d9071b218a000c18503603020f020b00503401d1420300580c0d503000b40542801103403050103800320345e8a1340e1805c403291b4001c00e04000c10040030507a854022000180000700c8022544d09240c2e000749000f501074100d441d01020b00f282c110f01d0040c8100810000b0800c042c4c1c4100e110400b0401e0f03c7da2070390100f214840c503005640c2c400e0f0085908017030302d421f007101c2c907100319040c0701151403a8403854400e075a2406528403281c40c90380700407000e00010744103038040d50700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 352334523 1250 352333273 352333327
    0x7080f0c0f0d11041e0b07110103510306090f0507080105060306010e0c0d0903050d06090501050a081929090a02030d0302180d020607170403050d0f05 66
    0x5182c0c003211148151040070007809009403000c98180540c40c0482d00340f020a00100c1d150914aa107050020304185c0189403006d00624001c0e4000c090590183d000340b506580084000201c007218445001d540c285040703a18040d40198002500200620200d40c503521003114500c001744510f1a41d460004d00300003d03007200c0c10220b020202000507410000b04000d041c0b450004100391404005142c50318505070302040c000e01c000d01c24010020000070459085850541005c64030b030305103040070368152144120801c041131801c4000910b1030a1540112305841c0d040781e100301a1551580d061381c2e508140c000040101c42e100300510001543c2380f9002443e191342519900300407680d40c24a14aa51048511818540003d8486021480c06014400070846582804c600301003501440d9203079584513154450280c0c0e41c0e60554000d65648d2003d40e14115031100002014801d0a2072080b0283c1181c4400c40742486a150f52469680c020740c01c6d4500c000c2c0c5599842e04041164a5400444004200c80c440c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 352335773 1250 352334523 352334527
    0x40c02100504110a0305060406050f04080306190f09021312020f01120f0911011b0c050f1809070f0f050907120209030703030e0102210405010507081909030b07080f0c0f 74
    0x50136192100c12030b000b107000c0c0b0054a035038a0942010300075140000c15030b000c403c00c03000c100301c0003d01d51800e80350410401d8032110700600b90f4042c46100c84015800024519451040005010590703030014400c0004d0f142100d01083e60341d03c444003000300c04000096000520411003600e5501c0b8000d080b808600c0802c0c0030965071007120810b42202c58042080d10f0240d0419200c40003543c105c100c00c48070111707055040304028034507151044000524003d5901c81d0314002d9102c2a207683d50701d101042441600d0150003a401d08a0700355680341c040b807151500003000c03003500080381ca5025409100325400074282a5090303542c0c0000f02e814503240c03032694402ea0b07400c0c0305009a0b520100424405188030352241c13100801c045001903c0c00c3d0124168a460140b2842c0840300800b42d030064400f15002801c1140c2c0351805450300c18024007600480007104840c0755121040254030030104c1c0d0440b40075840c0540f42e03850b851411036076480101d9810406001b4030307000c036550050031001040c800d00d100c04218 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 352337023 1250 352335773 352335803
    0x30307061e020a020a060c170601030e0a05031801020c1002030d051b130e0604021e131e03030314060607020f04020d15080f06190504051912080105040c02100504 71
    0x5002c81c1c125500020041e4022080102008418030a140d609802d504200c070640d010000410980072000300101c1c1016140c9802c403c01d0482048410000ba034000103898403103400c03031503040d454081d09070814018410282e88040c1c50074040b505500e02c005540c007442c54041e60343d9401005c0e006c06005c10152510a04082c000c40304290098511104812800000d0b145000d02c00110000080d215a100d244100008090140f14041081101c090668502e0b200c0380062114103100186900c01f2050b510340386074084500c1015603c45044e40e100362010000003c5440007010340c080b0403034009411441c00c008403000b61030101d1500f114700704024800761a00440e00b8068003520b00843d02c8214610b5644810304c071440080c003000c2d0880d807105000f0030b0b6030b14101410060344090448a003254668070350216042c42018004444404400d04011030306038001d1600c031415240ca4408400007551050010420345840d000b030204002c4d0707aa0080c185103207580c00c00030081101070000c45498071495440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 352338129 1106 352337023 352337081
    0x3080a030b041506030f0212091f02090f0f13020a030204060e030105040201051b0a060903110607111f020412032c0d12170411030f030301030203030706 67
    0x70841a6450486600038412908c1d0341040c90010340810011440000d221a001c041d0942c0340458a2600d000c030310304034096081100e500a0700320710300407400e1425011580140d8002000b0000890740780740c609080340c0c020111000800c0d004142040b409401031a400c003140c0d8260002d10907840c180d40020102e2041e140000303a2400704094004070000c08102504200f9070100d41084151034500f00a07000c5281d03446000c0c400d01c030390340001d000f841c46281c2034218000c000d0000c210310104090b1580807604400002c00090380d0900c40010b2480c0412310f2207814034000d0f142c81e0840c0002c0e5080800b01c41203181e032404450354034504200151a01d00710680e03003542081001080300c00d80c0800301d4010703210000c1c3d110200ca5803001d20060052040c40c10f500031004400701d030400040040142e4070f13400700340310282d4560030512006001c106150004154160320040c02e218104e01c800c03603 = true := by decide +kernel

theorem cover : BRFrame.Cov 352158273 352338129 := by
  have h0 := BRFrame.cov_init 352158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 352158273 ≤ n) (h2 : n < 352338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
