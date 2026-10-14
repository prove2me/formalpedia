-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1673
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:10:04.924725+00:00
-- url     : https://prove2.me/submissions/a25007aa-3d96-4800-8037-25964bd9e0d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 300719424 ≤ n < 300899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 300720674 1250 300719424 300719449
    0xd02093d1b0c050102060f04120c020a0302060403060b0108090703200102010b0901182301090c0c0812010509060306160305090f07150215090d2a060912020d12050c0405 74
    0x184040c1c0b1005101c9540d04100c0141e224091400d08080703800c3c035888200340d484044050a0401074014030f50b50a6455070140000110b44c0908000c3c2e0365652414007a000b1700301416254001035095020401d010703c00a002000d8a400140712118011001c6039245603928520728541555282c00c501511641d40200080c02803000384458085520300a40c0d2004441d03d0303120143e42104031404080e801481800d01c00d054801868002a21161001c000c0e50040f1000e031000f4281b81000a40c40e11480150400e90304851003650322101988454003011781390350301110107064200018030300426040c46a000582c00c407a04a00351118000001751540c140490340d08110307510125028048609a410403d1034100c200000c022030a5090041d200c5459400306401482000f034103c4c10900c05130311860140c02d22402c1c44164191b512541d203000c0d400741c810040180d4002e02d0340d401044030240003050501111400d66030302a00d008086850400624000d050014145018080410307a030711070300e4524a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 300721924 1250 300720674 300720683
    0x402090d050d120f0204030b0f130507080a0302070b0903150a0b1816020105070f032004120b0a0b210a02120a05010513020a060302090111030d02093d1b 67
    0x1050324443c204050f64803102c982c00340148104000c2010418426003590080000e910441403602c50404c00c1d264140c2240d03010f80180180880010960800205241540d00c40c0c0c00b524043c0340e40350750f503a490307000d4403881e244c245d04085401e0b00c80d00c1c1c010b041c15501a208850000344481e4542c00729604003850014100d24040350001c3c003c054641410b0500c3c0e400700c1d8030090145180005004140c000200c603008241600c620700c0c500e40000f40d4030715070290756a600c50507866a90300c003405503043da00a5000c0d0380d20782e152400b05568004070301400d036007000301078043d0b2242d52074450001e400c840165000e44017402011010b07001a40d4801d5040301d41c0661300c00801300302503541041403c6030405080d412650400340056801a00d8000092003114414207006884040d05030040c0c4010407920403a4041340400141d12902c14110342c06015402c40c162400801a19800c10f141918001d01d09405c4008480500305003602050b00095203041c01103152400c401c0c1c5010946811140d010742c000c85 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 300723174 1250 300721924 300721937
    0x709050a0b0f0405011a07062403030f1103090f04020408010c08060a080715030e010905060103060e010f0902031b0a0306140a0509191101020a0f1b0f0b090402090d050d 74
    0x101c42c6818840e04891800480d01008103500d0030b14020701640300e6982c41584454081200c3c0144212503000501400f00b00071001c1845143c0e81c00e8944c17107e1b182c041100410b11140e4081d0702d152055910391060301c140d07030083d468566047c0410003090803d032041c0341e000341c080201054102003800b4030b0f00d40c203040b034130713071065030700300081080445e01d80d90308a149503600054042110301d0410110072410406410f000544603408202e09014000040018102d0f1044000010130007486031302401c01031000c803008004500ea440c8002090750b40880010390b0660104090380c14000141103c6002d80720003d01600d03016a1380da80f848182e80d1506003580041d41704c0002c0203c2a0b1450007a43e601203250350141002c022044035600380c2414020001e00400104640c00310580d008114003200d180e0840b1403405011f40518000c00d911001e040415901206d80000140c0500c80c0740b06403040e01d4051080138100f20500b82440f000350070100388180e0100b440741c03107000883c8060200e80e60001300b998544 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 300724424 1250 300723174 300723191
    0xa020c1002040311060a02070608040c1203080907060e0a0e0703140403090f0b0a050d090525050a14010804121404060305060f150702130e070e1608010b09010806030709050a 76
    0x1646011400202a8007a000400c0f60008055008c01c020b030540b411410310403035540301d60810b843d02c800a07420200d03010078210400c84c2456000a9081e10410204c8120390340b03d52510b604564035110b00b0302894000c03a4070381080c080050b008241681c40f89a6150024900e500d000c4407101c88901610b050b000305551754818055418002a50000b821500b40d10034544800a840245288100c01404852076601c409140400c002400f1400300356540000001490100306550480b8042e1441841e1240f4200000083d003054424015a9800d00584811995a485880b00c66170300122249800400040990003d8118100c2c030103440940020f560000e041c0c42c1c8942880340d0070380d050040c0c900c54601c42c001d40c035540411900f06d508070760341514413030110200c41803e0b10292000e0101440c00740100c2d140440d00b00140750540340705030100403ea401c04040410140c40c0c04e038082c001c0c0c0c05000310401014105500a0114075002200503007102c3d00550394506c440c04892046d030780218101d8131607844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 300725674 1250 300724424 300724433
    0x7060512090309011d0103090c060e030c030a0b0f04050c03060f07030507030519020a050d0908131202010509010309051006180c050f0315130c080a1a0a05090a020c10020403 76
    0x900d940505140c0042d85400300b0507001804440000840c0c0c0450b1851070441107071640329820810400d41c0c0000101d00c442c4d02c404001c0c0c61100c6900c0043d0280c4140e106506c400d160002d2010b09450704107456144646411541c802d02d100c00402c1598103205850302040c2c607440400c030141c030500c480b55a1980d2400c1200004040d1080904194109810801030007100504d400c2e40480000b0501001030380d4a0300d081099880c7c1c0074410703144841c035161000d1030041c8486100202102c2c881c4070580390302b141d111112094070800f00f61001c3c0c0050380c00d00c00310741d440d402607002c01c01d4140681c08a0314a4960044031005859050f089000780c101c400317039414090138203401202c2501b0700c0c608105080c004c0c080c0c4a65490f00000b0074180d205100701808604035181d40000340c00020592006000d154580b1074050900d9100307440312043c451414001182e0b540720b0810034072007000c00810209030a0301e08010850b003d40003070041c9810642c20070119500301c13000c104404100c142c0d000e016855030b10f907081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 300726924 1250 300725674 300725707
    0xb0a020d0314042f1203180604030c0b1602091501030506010c051c0c0503040b040e060d1e0203010b040c0915090b030115020a0609062a0e0609040e070605 68
    0x12105050b81e01c0d4052000141c61042403039245210000d000382130002074400e9080100c80a0022a004510225040302e142c0d400b00050007408a200501d00e043d200c51000e004051040744400340240890341414800c1a290343c00402e081e00c904070084018694980000c0c241140035100818805082c544540c800d58040c0521603010b4400d003000c601e0801940c50b110344070640100740041c80b4510700d6051081c5400b548005c1c190340d40110440341c03166200c81808010f5800303401085070b4202e803880020b00e41e1030700c181000019980500e2030803921402d01442001c5852040040f41d06540354640c58030292524420910700707441c81da50b02101c40e0300d82000d10610107660070050080201c8000103120901200c1c089a0448102c9041c0c056540c0a91004a003003079031150005000c981443c150b481800031942200142c0c0e0190442d91250032a030350200713040003040340301500103e91220920603a900c0e0003006000c0c0fa650282000c43d000d1a45029281000c6264100001042d404030b004503140c0103000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 300728174 1250 300726924 300726941
    0x4180b010f121401060803040b0403031106070c06050604060513090b01050f03030304140309030706050406030c110d0c110901060206091216080309011d010506032e0203060303040b0a020d03 83
    0x444041078505000c400c815510b07000d0005001026621900a2080001d43c00360000b0302c11082030740c0d00c40d81c0307411114170990b009101c04d500140074401c403102d5113040850f07103034080c18181c1c032070070900480c41d910341d0090140200340a501666852001400d9100d521000b01d610041c45400124a811454440309041060700a14012548041d01098940b40002140e40098010303120007140318100020524600c16400e0803a0107003d00180000c00c00e8120020b4021b640281e1000d2200348e80205040b5a50718030f0b0b604081e1b1941c8000b4072010150700a648103d140307401503400085104130840813401007003080c4c0c0a080180d00800400001c0202407110030680c000c2c54040910f0041d40000090070900c501c20060f11104001010400c084d00035408100310031036840d81c0c0844600c110380d03068002c1004a813954042e00407041d202c2c0c109620014401d00b841944819808030205503038801c402500014052034041c8020400030884540080140081041d40e81c014005006c500e03000030284c80080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 300729424 1250 300728174 300728189
    0x90c041a030d052502130f020304030305010e0906040611040b070503031005221109100c02030f03070302030d150b040305061b09060702040e1e030d05070f0f030f0b04180b01 76
    0xb800000c0003084c3d01d107442d005044582020703403a6400d441c00001e5140302044006042c041c0303400707a404520780c540d4000e54415406178804000c180c0e40e811045204007011500d4040c1e940082001900141040d0700a1403941c09694a190601d40c984004840991112030180c4596101004100702d0780001100c2e100034003030a607203407040380340c24448920f003003031007041c10b1089580c0351002c003910081306c0002d0311204070b001000e00c0140e074080e907409410030743c80070410f0b80280a01b60302c2035072503c400011218040d80c0741d4020361501d41c6160003400207080c3e070b00d40880d21429811001480c02e150b100a4805940154050841c42c01e020301c0b12550744000038203002c40e8000c03e01c144c148036607411040c2ca82c042c1d0160b4003c101504070074401e90400841110011032a0346010180182c01d00020181602102800c4104a180c40d90350041d6204214010b001d400035042140d002c82c81c81c401e42200c0c0c000000d0341804261654840c00280030b54031120260f400402d542c500640500c0349400f005c0d801040c1a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 300730674 1250 300729424 300729427
    0x10e0912040608090a0c03060e0606150d0b0d0f050d020105071b0b06040f0218010e0a080a0201180308030a05042a12050a050102031527040605090c041a030d05 70
    0x50035001a0280101d02c00d1100f404008000034205180c24881102038560090f030482078292207203041d500500070220350034514810000001c4150a02000c022810740402c10211b0400715806402409002c0d101c1542e0f2f0029840031070301c0001746120b26269103040c41140a8000320071030010082c02c5440052441c2c00300804402c1c0e160641c4510340400880760b40001c00d044003540c0320b00106001e44031002003c0b80e8644000b0b00000d00d40000d50f02c3e6860094260f81d10307080c034042002000340794125806170895540200f00c0b2080150b01680c0a83c1d8040113200c50301200300d60700c0e2202c100a42003203520355402c1da110700802c4100811000c10064071510300d00c0280f05220882490310300f041c40c0380621650755500014100610a042040b020084e900c00c0c0255a245440407005c100020748404050084400305142501c0c0500c0840484a08200c101c90b044180d4481c1c8924003d0000500100650300680b2030101c081d440754007078000d42c0925082c490070407034030f0407003498a040f03480228401080380 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 300731924 1250 300730674 300730693
    0x50d020114211522020910050d0f020f03070c1a10240f050a0e030303010312140f1c290a0812090d0804050604060e03060c160210030b1008010e09 64
    0x750139909505041c03420b04007103000c408800c0c2d800001c0c403420345400d602c140351000711200c07182c4c01001040310180d122014404180048500d030242d006110000d111982e0600c00558020300c9503842d02c1250707014811214100342200c444103811031060326514504603903000140611000c00e10403507080d0010100a4980428a510081150400110410400c0b0001072098030741c43c458007400d80070000050540c3e0740d80d6500d240960300e404d55400118041895961058030081c03641081d9540d010460350494509140203910b615580c036800d1590502503540c0008400c07000d0b010800480e161400700c5e02081010900082150106081c0e01c0621030343d00400314111500125010f41d1a540c10948040304245030900d130131718003405190803054122a011a001406c1540540350010000c0e00783c0640350b10751954101e01c1e02500ca055560031300500740c1c403c0300e0018200311008240c042104d15000408080311000590a100c03200d0b21280000d48000040c0014800c40d039110740c000c0d000c1c0d0020104002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 300733174 1250 300731924 300731929
    0x3040c080601141804030909020f040905011a16170a05070b0a0209030c09040623100b040608070c0609051e06010906080c060f0904181103060c04050d0201142115 71
    0x10f00f03c0c940c0d00040003031038010604140c00780301f455010b001414420764885441441075600da40151103501c40722420140001a6000700a01d0102c003002207001051601540c0041c120f00640240003c88146907500360814240c0040380140c078020090382e81c1c2d00e65820329400c02031551400941120790036441040705621541e4002107019461806541c500181e503518140140107000c8c0c0c0015056400941c0700121120341c0c00742c0300d1481070303000d0400d41c284540c46110103060750007640211404076a1580110355206d00984203c01d2030f078810f00000c2403107009a540c0604020b1078450f40b025103060710a002e40d004000303110890240c106071b0000c015803450041070b1603840840e20b54450140100150903c2c00e141d044044401028000d0400d025002c0805000c2428074120002a283d844c00340384107501e545000f046030b5018103508008141070906010811064600044040741400b4104c12400d00c100110f80142c81a0660409003000c4d506c081b00074400b031070200030005c4c11901c1c01003194907003a9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 300734424 1250 300733174 300733189
    0x191b050307090e010b0a060206100e07050412061b21050c09060307020f010e03041d09060a0e0102210414030f072315010f0f060e1507020603040c08060114 68
    0x1c4240b21000702c0e41c0669a2040750040611000190308039900e0760010456580019501d80280d0b21104080030183d60303040796032110381042d270b4400300140c010001044424164003010312011301a0500141540c5a00702c040480c41d0700d405103401054603915803480701d64082c00141400d01e8008018091031800302c01d09446485081c50181c82030030003201244030a403080080b07c080c1c089610003003000501e1900c07025900d40080c401c803115a072000c40c2c941010712800c3c005600440b2020014052a1a100f205101401491000784490341d42070000c1c0c11a00c03c00400380c440d02c07410703550299190529052030722510b40f00607411701e80caa001b0450358040708500c0040b02c4180c1d40200b4000d2000b1036048441645225180845949208108080c129450480100380c102c401010002e240c1581d1205058061300b894480c1d80089403408107501500e08001c3c05525414160340380640c070b01307070f4a540000caa03504103880580c1c02c103103d00c82c1401889010442d580c050182c00b0700b02c82690703131042c00049a8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 300735674 1250 300734424 300734429
    0xa0f0501020a12050f280e100c06020c1605030d0e030604110402040e0109021201140d080304060216051f021315020a080a0e150c0703080f0c191b050307 67
    0x60058002e103c648a0000c2d101155600c2006565551034445000c544800800c2a40c00c4030720780280f69407006004d0320f043c140124001d800340c07031000d65900b8143e4842d6100441544c00701d03001c10121b0a1140103029801c903140151162004090500301810315001180501005003c91499842159600010a0b56103e6809404030904100c0940810040c0c000ea0b440541200c10305030000c03480130059001341650140d2000702a59076a61501c1001d22500d20183e001c3d04043c0e13040c48880070804180041d85d006006c1d020140c5406c00036980301c0d2002c0d80503074040d00c40d40c01410350b0079600c4010b08248409200700440641c14140d41030480c581c2c1070900e1040c8907040c43c41290094045000344010003610340c1046402e600e03200c03124405020400c102c03d025108824010b960481040008203580b983c0d15120004d100d06402c40e65403429661114242850300002400b1050340e00500308015140c1140c00f24200c042804186002c04010f4040c40f8580e24110400c0d0090020740c8000409004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 300736924 1250 300735674 300735683
    0x40825140d030212070602090423010501200f06060901080f0303010b250803060a0b07080f0318060103050120210c072109171902060f0d0b0a0f0501020a 67
    0x794106840c040e8640010b05903d881c00140c0880d003001030180ba5400303801030f6070042d9401e0119842c080e0300b0b84a000d074003498010b40400741600500a95104009455241040303c01742d030a180c81c49108146003003206000384075158400320810400e0304007580d1035030041840c4402000300200b00342650303859000c14010201c0316480440c3e03d040706090040c0d07070b0036a10032882803a424115681401c07600d552088441c0c0f409465000c0000410241c00c40845201c660041d010030304000c148001c0001c40d6001912801d400303582c030985580000d405105e000e00862142000081c10036580080b800e45440c00d201024086000780901c0a4075200060842c8030485070124030700e45540c9000003040303280104000a00059414183d94a00d540d10101445101030140c840040c89a0b03156281900348882c0708159500d1b41240110000120700e4400614000b44010801400c051001c4014400740c1c02841d05c00c0d000c1915442d0640d11801c02c404400c0142c446c0100c0c0c00d0404d4144000030303640704400b00c070041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 300738174 1250 300736924 300736939
    0x60e04140318060913021911071d0411030d030e070509070f080c0f0c030909060301060f0b13031203021b0d021e010b06070f120504051f021204082514 66
    0x2060b0740c4a140345400c0c140820380440d00c62207c040c022182c5900c40040d90003142c3c2c01018290480c80008224040b654401d010044100c00c6c2c0004190700f000141040710000901c000260341682d050011020a07101a079000924103140800945071044643c2309a000d56004d9091001960303010072441503c106c1820003400716119a0441021882242003c00290801061080a002000c0014031103450200c5014220ba1110010075080310303810320610220000045082051440c41c0028190310300e0709660490919a03aa22400005100300300340310000781c1c0c0042c50407002000c608500300c44100b220014207a000403001d010350b0701e00d62407210100c04004008214140e40094110001050300501b2140d00c4407030074030344001011403640341100c241c401324921959040c07051050310111000207104000d80e2200040c51040166044c43c10011070284550000502d0060390060004042030310081c0500c02c2940075501e2640c01300b416140f0880485c80c01002001c900c06200048200103c6104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 300739424 1250 300738174 300738187
    0x1701031e050a0b270f060403180905070302040305160302030c120a020d060203010e0702011b08040609062c060903041e150e04050703021306030203060a050301060e0414031806 77
    0x514100d480300b03000345032204840410944010818600032000d400351000f01d200d015403011191101d40c2840d100b8040d41c46400000e0101c0e1241c0d100e04000d0000d81d01e00010350340c5607a04001681e02c00c948817000309800090410800c1400c104a80d00c48071070b499900001b03820340d800070341c8980e11044540d100d04001282c080f10010240130b1600103e900500c0c54042068500c0c0040203500240711f03c040380e0603441c0000720054010b00402c00d031900040707140148504601001c1d580040040c0c0103842c025601e0541800081e5548140f05104805041c2103c9220060b1100d58103804208010703c02ca42181040c4500c100380001030b01c2c01e48140020301868244000c41c0d500801000354040304030860b0710341c003160806411510213140300c042a40c0a20080d6100c800903410b0380300c1c410215030300030b01c0340384100f082903c0380c4d0107075030013240c018038580c40705039100000303800c1d0f52a82c1c200809041040e0300340b0080000e1032414942a0341d20750051410014400c8606104060b0004194000c04000a42d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 300740674 1250 300739424 300739433
    0xf010210021b03070b06100906080703050a060801020c0f012016030c0f06020a020105010605030124090506040617010509090615040b090a09020307080f0304060327050d1701031e 78
    0x25480d0b08111501220b442e11454101402c55500c152002d0f03000b2024209503800c03c901c1403440300160b420a4803100517588480204030300070030006143c1c8011941d00c240100f48200f0030300050640e002581c0040c080ca802c010742c1142104c60224210580303a0720034550000c074000101c00d881500c11238010035204c0c0d541c0c5007001e0301c1e1103500745001841e8140f0001000200000340d401742100c2a00d82c2c3c020400c13a0388030070301680e1905c0203004842e03103105252009540755820f030300d66a81e2a5800d28103200c0903650741c0d003c00d8160304503800a1022800c1010b0b008840140000601d005080232142132180381805010680c4400d0050100a042e410400802c0300b07503251030b0405900c0340c2d030103031000b100d03071822040b40002440385a4003244a40209200000c003e0310004818081c090102d000c2c0d40f40c145003907403c1d00200b5807c2160f00190b401076808130309103100802030344004d6000d2405018283e0111500900101604008107611059500140301140304940c06014211034906180d1351381106040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 300741924 1250 300740674 300740707
    0xa060207020d06050408040905062d0102121603031503020f120a0c170105060d02130b0a0308070b0708071404090222060504060e03010203010302240d020309010c0e0f01021002 77
    0xb000d081e4a04040c2400104042440140201c60045004200503103a02013044a800705d20000701e08150000c2d80e41181040e2040c10354101074805004648104545554203007140d0030544c1584402c1500b454401d00313054250050303000911a10100c08a91801e42c0c0c00203a2a202c180328450240c0304018001440e4002048000b02090300200e00d81e25155507240080c1c0c03002c04204034038401c0e50929010458900302910808461a0300400d102d401102d241c3c40b4200400c02c0040246d0700001c02c80c8004081840240249540c0d40a5010844103107443c1c08040d0513100042c05450412500024001c0402c1c0b26000765400d481180c100582d88607a48007031700c406070840c40a96410126001c900103089038009005204642068403080c4144243c80704041c200d0200b40b10107500103030f5880d44940b4102c911202101803411840d191410310356441100c0c0200d030012540030a13269503801c40d2001807a0410b42c0340140c1c0608551200030f045503480000d48030b4003420345800300d5540100c0c0903000580b1014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 300743174 1250 300741924 300741949
    0x18040507091b1e17060a05060309011401050904052a030d0305010306150503070509060319030e150712030b04021603091706061e0117070e0301110c0a06020702 70
    0x4014030001100341c9a0a11003504050000080707803e42011882c5036200c000d580128601540340d510a40b443e1031049803143c03600520260b840700c14a440070416603208c80c00342d07005030b411400000c0c05420040b01c1d680103206c1a0030103803141b05110b0803c0700041001441500143c1c2002d8120718541401401c030105082404240b0351502410650381d01d520b915521140c1240c2c0150360602103c1e4414007810520380c1e4a000d02d0ba003540160906001e2428445061030b0451405000c41c1d10241c00703041d4800322244046001c0b000900200d00e5a82d4a18001019011a1303250007207891a007111540d691195403280c0021100741520350741043c10f10398450703055400726803983d018541d1075103903854000c14225076030080e1001c1d0b480c82c3c0c5001d000304100240e603134462400503000403400710040ea80c02441c104014012070402c0104180240e40408000170b00d4080e66680c0c584a212000420415080d150603943d86002c85000344403504044000203060100c40380c00502c011f94a20240c00410015100e18 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 300744424 1250 300743174 300743189
    0x403030e07031703100501030b010e01050906072f01180501031e0608160b0405150310030204110405031b0108070e120f03090a0605030103020105031b0c0f0c0f0108040218040507 78
    0x2c03d030b80741840030034000551185440880c0002c03001c0d2101c0040d01160040f44d40c00d40055218864400c4c60b50141c1c00078545004000c0c80181403205a84e9246400c064121110540000e54a10b00c01f06018000854101480900f0505035888101944002e0241207202e511f04160f21884500f20000310b44c4896880110241e070240305d01d545a1501903511118512080c4169226010001e440301c0341070155010384000506846031500c148180c1d14054102070000000285000e500000603a55886031411403d08804070985070751078481010708001c6407114402001d001008008142d0b0707444982942c3c006024148045641880004a103100c0c800c400c00c0c413000d01c02c1642a00304404c0001c0036020002086900201c8541c079401c08540c0f5000a01c4000e0208c0c109201041032905901c0c1d012810507500f402d005c0c24410500c04441c076214468811042d00d4102d88444c20305800d0150000901481c00e003003d06060030141d01150144c0c640c030348e880e003402d011100407a0400c40c00707000290051055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 300745674 1250 300744424 300744443
    0x40837031b03080601020c180a0c0918200c0a060c03020c07090902090c0a080a0b010e10030614100903121b1203050106080c03130201090f0e04060f090b0403030e0703 73
    0x500d0003411410307013610303114054410703459420413601d00404986a900200300b845109505c0c0c40964201030f0103580220000d0021954011610b0380c00c030500c82d02240100080454440c1c1c0e110014550b010f01009140c14210301008115140400090443c3c4a1917100c800010822200401240280502840c80c565401844800204103125400072408180212410b491f0750320340d4480302040e445045014400b24900c5c80c00100d034500c60303611000b030038603041c100744400e002ca01c800580d824211104020200f0f644010038003101b0071000d00e1059084041e1341400910031702000141c80941c0380c0c40006c14264040c915542c4003881140d0700503046541003100d1045a05034500b140a012000c0c201e500024030785000001c80314444d0a005000e403c4000d580c601d10f480721020f8001c0185140d000340d05100c1c2d08203000503040342100918005000700c52402c09142070503e0a403094403d0602c07420300c02e41c1004064004501d480110540041c0d160500054070000007246504002e407560000c0c118030103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 300746924 1250 300745674 300745727
    0x40506040810060503010c08070c150915151d06120307050a0b070503060901030212011b021b03030a0801052b0b0402131b0507030306050603090304083703 68
    0x1000038005101648105041c03201a884d401803508840c84800d200c0c0004da06100403403072050042841f81305d0381d40a0748041100048600e41c58050300e04170721003200c0c0051000500004a900380c8140010703020b80d120480340403481c09440c0b87d078107503407094402c0e820228000802c00b59964504c0350303000e201900c81643c2d2030b680a403c01d5900c030f100b00202500d001446200007900c1c14800c43c02c032440707080020b142d25a1642190240069004103e5484d40d1540da140080e4090020b0884401c4221a0a50041c50030141d0081c07009070980744243e400d03019500a100d0014030503002440d843c103403101600d21045c0d40c0101c1c0480300c683c071507500820641404190b401e0051060a05210b44070f58000d9030015a03000a04002c1003c494828036403024a48158004841c7c0703d120f200100084d60007841d006c2003c0361a0400030781c15a0090b5131030462984009002c00000606120340c0c0303010752060304450703c242c0c1c010442d40e2641c040a41d900030300c0f50122907550201805030302d01842004504c2030000d0b1000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 300748174 1250 300746924 300746939
    0x91806060e0403020622060504020d0606080d020c03011505010809031209070512061e07030b0910090c080106140d09290903041a09040902032407030905031c0204050604 74
    0x70300039030381503006001d02d60002d900e90101c6580e151600c1d0300300d911030180142030740340c4031300501c400380c01268082001c106450208185020350f07009000c1c0c0c2c1014090541100d2400303447d18900c0c1e00300c58083d90401c0b030030380342404010004c44100c68003801d143e0300303503a2a42025419442034248030f001d000c0004082c13191003040000d40f0b0094a9040d101051125088070ba8107076101c404641910462060001401c061a035411403150808410704020440c9410000011101441151900d1b030040b102c1d001001b80402d00d0040d00354018007428400c0c43c0d94140000100f4a14007104280c0180c40005103a60309043c203603202d44916604851080c01c1e003040a80d40708203442c8007070103001c94810744002080c0c5040d0080104c408581c00b034840744d4007001f200041801325801204071039900c169528507040140e1014400e0070300120308031201d803c54461000038070340c0024015081c0c0080504d00582c80001640001c1102e14801481103001003c03d050100240a48184d806c0320350032510103d0002400c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 300749424 1250 300748174 300748199
    0x20a180218060412030e04060b0a03090b0a1b0f05040b030a0b1203090a06111023090613020918010c230702010915090801110301030308070c05030409180606 69
    0x5000001c003101069804100700712190090b0300071142610710010307884000a00400303a08021400c0600086949039540890200a40001e60404080b80d203641c3e582e401c2041404900713512900d409010440090b001e0750b040e2010783c84007020000c1c08424514001000d0284058030b008100402d5150380e28a080e6001d240580b00c04070b880f034012280581a003004a102200707407070034500040c06450a03146096011075540000c01e0340705807940203110000401040a021b03020300c8044405904c050101350000300b290310f000080000c046900114140003040c048644002100c41e0110b035120b045403258070019503c8041100359103401c0d841c0c154410300c19074004802e40b00c0380242c45018140001456001d21340703071203021030090014120400030312601210002e031040203c11490103d020a89510000e42100c5544512904214020004008055210140d0341d4400740501d8005d02c150170070350b80c2c0343e81c82c0aa0f000340d1404035200e9a5580222039145a02c2ca4990b0700140180021551003069980d403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 300750674 1250 300749424 300749437
    0x141b030403030e03031e06090c09041a100c021201060f060305040317090f0f031206010f110703080304021002010b03060a0c0c150c0e060c071203090b2b1401030f020a1802 75
    0x6d4020800900e0f00c0c9060042544100e240b9800c0310300c0c0000c044200001001c01200d51070910380346d1010010a03440b050503c40c176420094580403401d060a00410443c0700c0071503441641c0c2da041003000d202e040398a030f40100c121807480c100824251100d01d019188041030503e07090304111500200003049500044400070b00c0f90200507a0403040503198465268442c01404220004000340495071a520903c95500726407407600d440000d40740b284030b16130709041c015481502d1002c004018402581741107048070380f5001c3e40e40001c111800103100400c0e165031004088c82003c42d0f8030320030403240d89d00455884480503803080f0046c500c12001c580f0503009100ca04070003c0003034a03c071540e88240c00d25004880324500148001d100d4246452444910400c50440450421a400c2c900040c1054804090601020003c3e90304084407001040681c2814100001e50400b50501c04c002c5120040d10364041d06494011800080c06500e900106d461400581c0c0640406d41040081000c10f80031980a40380 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 300751924 1250 300750674 300750721
    0x3010e01060e072f030712050a020c010306060c06090203030d020d0f0c030e0a12020312010303021b0301060b2a0d08011401080103080d0c03090602040f09141b030403030e0303 77
    0xe0640310f84030210340a410313035800ea040002c10310a4001d0007016400399206260b40300004c613458491a5590543c45844c407030304003030110720080b030700b244280d4041c000705c00009402e00c1c04200da0351814500400c05171084c6c2000e01021760358103118040d5102813045070305c0070b00314100c10343d40e903481d075800000244414131041c2c400600d4076414003070b02c1e4800d0154010f080143c8001b003000c801e554641d2034003510000c1c54182548802c01280f48105014943c50340290700130f40103010303031034103014410307048118503d0600e10036407401e6000c0c054002d80d074083c0c8044508021002080a8400005450607080c02071442450b20540da9040d030001c1e40305451134180c480a000810029100100545030b543d028000100000790521800550441c198400303403104406240c081103000d029214901264015000360140d100b190109010250060040903644403400700c41100910f4105418051404100c0c0800340c034500c000b020409052194000120300307895001130741d075030382404140e040100304060030945 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 300753174 1250 300751924 300751949
    0x50a020613030227070807050c0a11130b01021209010e06030a0510060c0b06040c0c020d030f02010606090f0e19020d02030a0b01110607112406040e19080f0903010e0106 74
    0x401d1070780b0005083c04d5203440da2400f9501c0e516044e8003610714040080c680e0f002c00c6007d101a8131400d03810041645801d00807000390400081200500100f4001c91000082d000c0c00d08075560038a0b40d0010f4101030b03c40c17901d0b0030f40c1c1d2100304010040b60120b10521500750f01c0700380403060123040d400582c00701c0d00502422105600e040d0b503441069408503541c400141c0071104c0c44000a000741016040047c0c43c403418503007148528481c0d400911ba40325414410b0b000552116280001300740c091103030074080c041c40c0c10314221446ca4203801c0070303a001c820f000d5680d160000401003681d14241921918036901046000d648a20403502420300039081250f0144645080241824003540612500202c01c03290201034100c591741c2060a071100400304103106418403a140415080107074480c1c2009000035191500a00350810a0801040e1a500740c1c440f9403503042070044050440001c011b000400e135004d405103484003014400300b041809401e11480d059424034640f802c80300313810762052007990003441e9100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 300754424 1250 300753174 300753199
    0x8010b0301180807021e040207060504030810032103020418020d0b09060f10090902070b04051612060f06030602120402190b0d0b0f03072301170601030504050a0206130302 75
    0x20b5220003010320280c078040e03080145001600300119103801c0740340c201004140906c41d80002c1412a800150161040c5503180e0900c020154000d0390f0b240c000c4141d0b24090043c3e0f0a50301d5840c180380380341c61240e00005503100500d031b2243c000c1c0c0548006041064041404000308080f0001030b51080c41840015882d203d9190000c0c5001d03151140240e1001c3e010980e401c0095050205a043c0c0d040d20f80107005044100280e01348160008146051041c2d00c0340406042c9440c0440c54003a5961031590f105106081c14071041481c11f4400000c0f5801210201d142d00000541100034003203a0009040c6c10300000c1c000e2480304e84000740e28000c80c401d82c2c450301700f451501e0913010009000c1c0900214070340100200c1603e44540c2d007020350007000080013601031104200001c1d1410012b548800141e00310200035001e00110781e80d03074840e040002e00341010003031007100d804299094000c003524141a550404a0700784074007000880f1b00c1540c05014190364403480c40c014124908584001c91240f907a45156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 300755674 1250 300754424 300754451
    0xc010608070e01030f020102012403060f05071b0f0209010608340507022101050103050f0a050a030311120c19020f0c101701090207061b020c0f031608010b0301 70
    0x881c040b60004000c508040c0d08660b150001100d00c148142e04541d2103004400da000f407140d900500d022400458488060310394640311054450091a210742103150074200300020740c028035426400441c000519540300c226141c405404068000080d40040c0468000300781d8035000401036004d103107507900802d6184104110910201c4110360358481802c106034480c52214010070103018291b10040c0034916007550107400c03207860741c0c0142c0c90004582d1038100402c14440e09110500c81448000d026280c480c01d00e4488a03503c0c00412402010982d13100400b4007403401c1c1c1c00c140d40b1092500403180c20b140c10404e818000d40d0304609900d01d0030200030740140c07a915000040360f48206252002801290542c4810005581c6166480c1c100707021a0719804206d685002241c20b0203410805001601c4400c2030900d02c044510025a034032400c840903050458003500003680c035001001c2151030a0340c0400b410302117410203080342510001c5a50a030004a0100d0303040d0020141000d003600208855070780c0061 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 300756924 1250 300755674 300755683
    0x40b0a0305060f030c130204170102120702120313030c150e0706020c1509030316050d02010501090905061503240402150a0504090504020402043c0f140f0a06050c010608 74
    0x1254136034011180c01c405800d0241140313000c0c0d10480001130626a4440c69001144600413005525950002c0d03001e01c0c1558084c03a240e000103242c8002c5c80c41c5041341c0b0304c241252002a1001c030fa0004403e1408040510945441e0480c503032000c48041034034002c404480c0a0074000700d2603551030140343c6010507c03510019a12109143c018502400c10341c01114250031513001c21121a014082004001c40c1070480d400c2d0031001c18850b1008203400003000e00001d08448068010b0562582014820404140000b4000342c000e1280106c921410b41814006403410040151070568489c070480c078520340d0841082c55911880c0245c99886c1441a5800c003055030788220b8221001140c000d00061280c131406510544c0d0140c4003a000504d42030310340e002114401a5001c4440454a002003192151907500c2c02e1181c544560000f01c0729450700702240d0b1401c840c1d290090b0304401c02d20211050305941c4003000d007412590040c0002041d140c071080002c140754030044004c030342982064400184600000b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 300758174 1250 300756924 300756949
    0x1812030e06060f010f110106151e02010b060a080709051f0206010b2d0408070b032406090d0c1a0417030a0e091305011a0f04110a0507051002040b0a030506 68
    0x81d90b911030f80c0500d000641d86e200c0e0360f2501c441035650311900840c80c407114000895090011f03480e031408031840741d40503039a40c6071808440c3c0110390524250040d541c441c0800d842c0f100c02c06050a400a41e103142c400c071010601c1d90300c5281e01c0310440d000ca1820303044e1050503002da2111503003030b00d002c3d030b8a80400b082c041c442d95012074525220103480c0d04c9103a2800e0f002c40312000301e642100d8a0142c0d5444081c1c82c08880d908a1080a5000414400d440c0e0420780c8814056030604900384005120303100080306806843c0a03140544240241201005101c803003d201a10341e160400c4c80c40060840c40c91020342050180604420707134903048460000002083d0307090b499565540701c0086000f241030001c1c540f40500070000c00d4482c00c41840001c1c02c20f02400e007a8202540c0c1c905091929a420821640c100003a005c0c0034604e030420007c4001e14440894201c901281000c994804035890302c1d601e00131400f01c402d100c1501c007007000303c2d840302200c00400074410750b558203101d03d4862000300a501c901e40f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 300759424 1250 300758174 300758177
    0x1060f0f08150607240203010e01080c1e0301150807050913151a040e01200408060f1b040f051e0607060f0204150c0506090705010906031812030e06060f01 68
    0x50186982c1d1402d01c00804406115076035107a2440407040702c0d1100000b0856200b5501c1d0340101c010700c04680d0507041d860040910200500c0d0540e401400f01d06258040b0f100c1e070b000c243c00320583c101581c9094000b00c0b07049a40200450400d40d0b10400075484100318000d1a1140d60b890011071400701d02d60010208403908405a001840e000c0703000d09005005c0520054810140d0300501d14442d0740703620070161091094000829031118141200d040c030752001090480204040c0424010290b001506541c0809000164502c94031160072022070280c0d60007107140b60840000d4081003443e8041418021a0302c2038a091044501091661003c0c81e9031010041e00101c0610500001c03503125000b800e0126202c140c014503043c0c40300045c5074100b420540d22008107a030154040d041100c1040140e50143d003440141c510b0b14241400204401c05034404c6404140d00ca07420b0b650f1001d0400780300130206a0000d000420343c141070310050301270310071160300039254040c0c000090228100090610043c0505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 300760674 1250 300759424 300759451
    0x91506020a03021902130216061d031602030a0203010504121101060b030604090f050d200715050a11030301170c040504080a11190615060c020607030804140601060f0f08 74
    0xc3c08000c9441444e0014207136408404204c00070300d070603040c0c4010039151900d880082c0c03d481e51820001c0075189160114071003040641c5504040311404000c2e114ada02d20b01d9074142a035519800000c0c0341c424000006175241d403034002400100304c01c01103030601600303650311004414101500140e0803502180310f48000004100001007941c81d02c4e91103508900d02c0303011030541110007a00c549252001b10724204010851169281d0300c8101e2040c043c41890700e18500402c10700b0b04000280e00c1411614429505000e40420050307007050180004000509680084944941e99030400d4001030000f4a0280014011911009024103250103501c2c41a40c118201d0f501e000740700c440072104000c3d91155040c1c1d6000e28448852010101050b05035554080e40c0085850300c414200070300e0304e04c0c96078040d90034845030100001c0142c40300030503108182d03014182214555258201a21200310f54415100c0300e00a800000c00e40541111800d012440d15565010308410039800984540c44217a4404221b4500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 300761924 1250 300760674 300760693
    0x5192307090506010c0f0c0504110304020f0f03030c03071113021201051014071505010806040b011509050d120f02010608030f07050a0203030f030a0b0a0b030412031104091506020a0302 81
    0x500390026600b0001c1031506070740301d1700580c84039058000201000c513070300055420100300380d01d0305014400340010340142007469070400b40d0002c0c800000109400703025208100c107000c9155000c1c010f88500d28003000c02e580d920082403030500412100703200c2c000c1c407900c070386041d003801d0100c14420790782d004241c0118403449908000c1003000414008808004011700e80042000401d20b20000d40b0b89288940c0b00440565039110300d07501078a40581000c1000c1c2d0120003000045100260813034110f9254280c07407404a0040003084900c510590806500710484500c80340c20040e0f040e050011400c0b042c0c2e90b0b904120040d07081242a50854801e40301103a1051000f100341c140d080004100c0715100398100d400b001c590303601203410341c3c000c031483c0c02403240c0220810250f41003e00804911201c1110400140c0341004620411400041c101804150030410080001402540442843c14514040c952111366a2948002402c5901003840442a07000e0380010503a0001814920040d41500504803030750 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 300763174 1250 300761924 300761939
    0x309010c2405010503071203080c160f05030c060f162007080304030501150b040303110a02030f0a05160302010e09092118010c020906150705192307 65
    0x1410109031510301035801611081801289400c01c6006406804903240d8949000c03d070070207803564060503c5482ca115181d000a501c2060709078844014008030740c50340541038074a1071800c500710000300340c40792241c840010300200202400d00d0485034030448500e0f03a44d0081030100c01c40181c40340c0c600061021410411240100a00c44400010303014264841d00a0007480d840c03c20a070b4804090f5400c006424400e09c4000e0160300d15440e100d4000341215460401a03949600c600d12000d4100400f04854a40c48a801e00120601540080c02c030380c0f4001c0c80704c195944405802204894921400c0c4050106900c012032100483e034050f120109461b40c00380501010a4000f00503e40314091030440b80500d030b107d016510580407804400948808100d01c50035641600c41104a0500016444000c010395511490907400201900c0b4400c98000004040c1d000d8014800e000f0214001c03860908001250780f070510844601840c0c22946a00100324201043c4d18400c032104a0364110410521090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 300764424 1250 300763174 300763187
    0x607030e10020a0309020301020301030c03020a0801020414060c0c030d03050a180f0f021c03020a0c0803090f13020d020f07020301060f061d0f1206150301021c0e1609090203060109050603030901 85
    0x40503030502080381750b09580000d0032a07009800840d01c49401d0714003801542098010140508050720085292600b0207181c0f035002044001e0309031145d48009445d82402d00d00384010000b805028007100c019154420000d0040c02089403180422072925112165451583c0c03a00400141c024031440d2004980b80c4521a00071400c07841641c004407145080c0c00704845684c21060b0450181d40905119221450804a80c0e0020380c0702840a500c18031400382d40360340e40c5040308100f0400300c95500e801000002040064002c1c9841c030140d040c030100d128408032111a009129886c8201c0c02044181e44450310030002880034002c140000710f041e145440a000030309071811110070000d0030700402000d0900010f02d446108003020405070041c20070b12011450840c84660b4030300c0120001d40c00c01c01d1803403460b4080407038408052941504d900c041d0b1400e010a11490110b2020042c20050050311046650302800003084124028810b22000003040c602c0e0384100e0740180301c01005185001040030045588 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 300765674 1250 300764424 300764437
    0x18060315050601051306170f0609062404090203100e09120f1e090109080d3005010605070c08060f0103080912010c0c11091b0a032003090607030e1002 66
    0x140300082041c002e0f0170612040c0e0704000d044a030344907020051b4101d40c05407564000b4005402c596221000d00c68555181240981d1007901510420141c2c400c4c171039540401ca1400c0001060301070001804207400069800440c0b0540089190303c40e0150740e0040d0440503002119170b18030a4110f204c0540542110700c0041c6507185c4004d18003401c0018030400c55503d00465803081c5036440000a00c50f64650f04440320400600c450000b404200d051941d004d440124051105488041c110f800c41814001c0c55200040705241c3c18020005517850b04406006a0b00580090b1001c026a06000400040008449105800d0040c180080f0f03461961840916008165410340c08850f68441c56400a401d115080c414110741d030f0390002c1c951040c00d0a003a000300651a450081080400b00900055400011419046c2580c0543e94410000c90210000d02c0d4521141e200620707100050090442404080d5001e801c442040c0c07040350310f41e1881503044400c510f043d0300e2036030000100451900b00b503902a240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 300766924 1250 300765674 300765677
    0x30a0f02010207020a09090201031503030504060f0203041a0309120301180c0c1b05041107170a140409050406060b03070f050f0403020a0b0d110a02100b13090b0118060315050601 78
    0x1081c0c3c5030741c0080c14184481c4c110104071a03880c0101e1040d5a0306004240700d0716801d00086041e1030564400408070322503405040305108a8206c203c0c0c64502c200101c8000308100404200100c0c841050b5030381c59481519005958400d210304603d04041c0d40086034102c0d02c4008181c00c401ca040c66800c0d0107050441c20503403e00007480d00311b0012030420140c0102035624503044141c9142003c003000304030f400d070702642c540c8028107211690000354204120483c4903440000c3c2e9448103010742d0101c070350300f5148208401718907020800003031421060300568022407003840305203d0a0344480900499010848403030300002da41c00c1d005924280524014600f40034007040151400761640c010030090a1180d006200b5140000b0b03c13680407589072300c07070b000140d80310700c0e0514034005200070001c1d6a888210411701400f0380c0c94076001907a0303a901c1c10b0742d008404e4068060204007400e042644100078240b1074001840542d2125003000d0000340700744000d9035030000701e5005010080b0700a00041800604850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 300768174 1250 300766924 300766927
    0x1110a0e0913140c12070b07061a060f03100501110d120e01020a0203040f05030106062a0209091b030c06120c07020d05070306060923150901080c0109050909030a0f020102 75
    0xc50002824104a40343c0038008120742c2c44a60700340b10081d8441c642d409040d0308041030500841500c8000c03525442e401c84c0c000b089100317500c41e8a901907a19461266071010740054950318808510b0091032040d49c0c0c0c050402c00c0181d40b0070044d2580036113001d008540380c202c0000000482d0040714a031140d05490000000e00d00c100350040303030890380300e15150005a030020074200407010905c6602805403009600078005a49080304c060b10385032582c0c01070452403410502d5002009031109003540441e800030300b500b406040500c40c1c2034441d520b001188540a4030070031200001d0800082010707001c6d01c040c03d41850f00981c2c00d0840c0810740041c10004a0703683c1003040a001d0794911046012a9024801a081c01f92441c500740089800a50090021600b81043ca001183e0ad00f2001d03c2c04401c2103812082582d1004501d0360030070ba0112020307a00400075030000c10302880025801c14000800c0c1c03285403015854004004a400b0100c1d20421260b1040217106103452080340d9042445500d4000503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 300769424 1250 300768174 300768211
    0x5101401050f1e040c050d0e01020a0e13110f071b03080313020d0f0c1d070203040510120501140103060b0702030304120f050609010b2706040507050403020d0605010302010201110a0e09 81
    0x2a0071750700348a108100180012501080c01d0030b02e031096072000319600c0021803818591940292141d40c60b486018810600803d407001c015030550405480009600905699902d01070324062103500705003010303500048598003030000d074011000103100356904000402c0c00c6996103030071407851034001c42d000c07a00104494810350015500c0c00c94941801e00c036640800d20541401c035040c9448105410031003c03507441c0c1041c0f015043e008021201580d50a40b2100140c0c003c82e5015240e0032070a94401d070342e007461b0200000f0040c81c1032401ea10300103402d0381c0510085545000c81da006003e94000a54550400c00c0100840b4a511030b1302c1c0d04051050a4001300c03e1115100c0701d090104c110ba00410a0f51518070b03034021031420020411002002d00c5802103036030080c0c0d411a440000080001c3d00a80e40e56000c20800350048040e240116801040e280000c0c80500c1c0440c00f42000b840202d0240d820300281a002010041c15940340158030340c0c83c1c42c83c01c01c1c6d01d03007001000070015000e07552592014490 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 300770674 1250 300769424 300769429
    0x240c23130302061209061b040317040b070c090c03091a0703060515030403181203030b010210020f040515030f0c0702010311070501090b0c031621060305101401050f1e 73
    0x2e005608000f00e55400d1a00e0680c100c01e00b0b0850050980140c87c8a95004001c42d803429420b07182a250032120190b62203805240783c0c1641d01c990f4105186696002c1410030420804010080039a2a0301a0a00030aa6080020b505846800c07030010508202500c9407001d00800d400c2c0d59a1100749441c012a59030b40d54000b007049285502800081800b0000401c024140c000e09907400041c1d0442510782d566103014160010000d40d400000d08240d152075001145030302c200b100c1c5074a450000700455913080010b041511f5030344036108860182c4074461104141d0b42d00403040d41d104840211080340940c0c0c4901081c4c3d01c81c0c1c41150101d05041d613800446500c4081d540c050072403d44160000540d02c20b040c144204041002001e08500c204204100540011a26000d25140590342802060740380c1601c0564460f007003d42c4120801841c01c500001031010000700e070540104001c0c1c0c1000141f1880d91403596a0300c0c00d000e1180c0013600e1044032101810000a4900040c203407404441c92100c00780d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 300771924 1250 300770674 300770677
    0x15230901030b0405070621020304050a02060406050414100c020d050a0b040c0e0a090c12031e0f14090d0f0305190305070e0102070806041103030403240c2313030206 72
    0x355003003a502003c1200308041088079802401c03450801913103800203404c2c3e4025680c09014010102500400440d04015080109a40003980200621346954650b90010525000381c420300100b41c7c1d00034040c0c40a400d01501c41800c5a88a03030301c150082075a82c00b8003210b0020584111014402e00c4078030130215001000f007138000c80c8281006c2007014505070b03040f10082c00c05025076814506d01541000000d28103000442291034200b034081d0044c0503400e05413001000c2c400d01d13100140901c90403007407035039000c0220203400500743c80c3d5881c2c0031080d0101c038a440c0521050309170485429040e01e804203c601000018080c440d00d4810710b09607001034116a48038400c2c00781004245c0742c00601a8250308801241c00304d010130310042c84014980000e055440b0009417019007100d00411118695480602c01c580107103411600f42122010103c00c4583e00200d0003a1410b00c140c170b010b1030000c0352481050607030129410302c54410001c2c50f014441440c075511210b0452281c2101d4100040182c4a400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 300773174 1250 300771924 300771929
    0x170408070b07020108090613290a0f11120103170f070507080c0d0f0b130803010e100905010e06040f0204080f06010504050114061803011d0c100315230901 68
    0x1070102e403150031901c000342c441c4101401c070701041d4224408201c0740d51704640c0002049900030035100301c0c8490031502e181c41e54150f5030030040800b0300a01080070341451500301c4110310031010810806101298401c80c014001c01545402d41c270341d80c0c8010004113400001c2161954000140c42d80760901c452180c9440ba8001d00003120950045c00d0108030100b001e1048100404080e5002e5000d110681c2c1e0f4503d5141300b0840040215000c40089841d10894404400b00070b540410690740c2c13561614900203140c030007101c000351286410328000c50088101c0c0074683c100c0e5216035841030349450307401c10040600a030300000c1c00959400d000000d907508081118203198041c50f00500025414002404151481600304188002c04906030940546500c1c04a401440c00001802e908070f41d14000240034020301c2080790742080c0e0407118207520080100340e40000c1501240c100f41400180d402c00e4040d54886405007000c0d00c0914400c02c0b9514071007250b00b10060341e011450604008180c00031b00ca086003078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 300774424 1250 300773174 300773189
    0x31e1e0106021c05030c041e0e01030f05011107020a12031101020406110f0106050d23010c08061804170f0f040807030c1e031103010914010e0c040e070317040807 71
    0x1ca000000200f6001a8998000782c60124650f1070720759800340f41803007644106450301c20704c150745125802d1004c1801010b46441c0040c05d505503034a09140c0100d03020080107075229440c00c0114000608139101b2500e003968064071344d868441c98980c804100b4442d00713000740e00380324146900725021903080c0f00038006005c150712441100ca4421008a1512030b030f42d0005111a0f14280040c441c40e552580c40040342ca87c01034014004200b80b0010103080005444614850742c02e0494001d8001d401c0a2030034800c07502602e000c10060b0440c05411040c0c207007643d0182140040114051402d01903070024203140c038141f11458602481c0c940c41400991040d4407843c9144c00201040c0204510400e44600503d542c020000d01c2da1074005584880c1012440000c01c0c4110035103800c10030b500e080d00f081200e0381d0132941615210380201e030010301805c650701941c0210300031181500800d240612a5143c089000b400614040d8111740d5880c4103458890a0041d000f0382c180f10004125808001000161400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 300775674 1250 300774424 300774433
    0x2106070f08040b04050c090702101401031505130804090b1003140708150d0c0501090503150705071406100905132105120702030c0d080903031603020d0f090507060302031e1e010602 79
    0xa03403090302c1101e003000c1880708422f82c4200108007140e44140341280b40034130f10310300150790b8661001c2101d499120f900d000740684004200015030b00546d51000e20a01c4045c0d0380341e2541748001c0307801c4080303400f00c0304055044108100400d429a100d88178450348000d9015078031560801a4000900740e0031070302070884a05d10110f4083c4420b5030301108105c001c1c0800d400810311009407004104041c1c00c001e01080820001255040500050b02898200c0e246040d0940b60b40741172003180d000400e6010301036448018200b0380490100300b445090045020342010b41c0d0f200c1c0d0320210a5280440c8810310400082090a0200011100c10054030a0003071040e0340040d65910a02c003642803c1c008549108010700100d0002c0118003400407084030b0340294103402c005c3e041041e10384103800a000c0c41070701e201c0940c500700c0b100c810072400f45e005645060084040750002c03a03071164100d059100c00c0311130309441c100111074110207404816906801241d08909014441c4101407079484441d402d07406040160300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 300776924 1250 300775674 300775693
    0x5060103021516060b011229030c0307050603060402040306050c0c010e010b0d030f12052806080c0904050c03010c051c0603020901051e2106070f08040b04050c090702 73
    0x60118030060007940e0140c00b0350400101906042c3c0348002d0030005040386031100303010903543c2c2c858083c2d9411241e492104000c202d05e03441000d902c03c0031840e0700c041c0c40034410300300105529001843e80f119200041c01000194201000c3c001c054101400054120b0b4080c0004000a0000e003e03803485003031380a200e180c44030102244c490955a9965024156901d80312210200d5104c51400a4100c1c1d003509001561075401c480072125500301d40e44038410319207088184008100140c00c0c6000c0754018403580310942140d441c0703031070481c0c6d010b2040e204254010310210503281040034410750b1090007001a10340702c1076100042403e4540000701c0400181001400400920302c040300076034082d400003010880b8030300310343c085003080c8010701a451051516071244d01241011a010315451440680700d034400140c03549505100311584000c4040c28007400e800a0140340c41080c0c440351241c1c1c560360351031135a1995100c2c2c0300d442801401c10340b014000c410010240340c95181303400340221081c1e1300412185c407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 300778174 1250 300776924 300776929
    0xf050d1b17040503090d05030c250512030307080702190b190b0901051228050607110712060209100809010e0309010c02040216022106150112090206040906030506010302 74
    0x540758055256589900040c440861000001e564442005030ba0600802c501d500704a403440c000c110b15414544074500043d0200007552440e504183d24101c81c4991560b1540d081180580c51002110741990040c03000508051040d14650380050300b42c01610108662018140049020a2800d4801c04410300030b00c149000c80e01c0b08801400e0fa8400304011200d40a00003608203503041c441c140c4203588a034045201c2d80410300a10400c085c510803a0100c818110261960303000080c1410b0303502e07000e000c001514650080440c08030307074005072001e4075170701d410000303009109000207006840d6158240480051510b07003540c442c8040c20551600c1015141c40e8884c0ba003520101890074141d0b4005004501a07039030800565070103264125405a202d41003158403403404224143c01039440001135003484900344a800000300c42c42d102c01c1c10b0311a0ba503a00c81804080d4070348803c2c0140003401061a05180c074100ea802280b4642c0b0080005107416501c0003c0c60a50b1900e40094036243c12145c010130031807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 300779424 1250 300778174 300778187
    0x110105070201050720060a0e010f030e0613110a180b0103091a04030915030209041b0212030406111605010e01060617090c090a021305030a03050421060516080601090b0a0f050d1b 78
    0x4ac00103240612180c8803d03000f440d16020b029180c0f400c1c40001100c620300b006408034010340b442c20090078811400e40d031903902c0c154401d0362280c41d130801403a01c4a1b03e58554424041e10404940101c3c507051011000d41c55505050001003064080001c02d000c00308001031200720700c140d85141542c0150719260301204000131280c03105d05001515580401c0100e5040d00440c08060500b80588210b031240da5504081b4080e1600090000d0841000100c6440b00c2500e4941080041d00407170080182421901ca440d08848450041001003000041ca15882020909034154000e020750250340300380e460f00012032003940040d10600085500400d01035120b0b02602c02a2008000c204c0060043c6a110340300602140715038084c10020070511900c0100060098120000c0680d100c0c008100c90320b88100c800081042111100000030401e1000c500d00e9071140b0602801e035840386440034500421540151007080c00344000400b0310005203c00541030780346109911000e01400d119035101d00903080010600c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 300780674 1250 300779424 300779447
    0x607120b03100b0f030a030e0d030315031a010b030c030c031806011502010e070f0b0c071503051602030702010807081b070605090c031606080402040b1903110105070201050720060a0e01 81
    0x46d611150505010950000b01036009042c1625075108041d1941002c80151003c0c0e460403100100c81e04001003040740114080940000078501c3c055070741d884054503841c130300c025a0700100c503010a002103099904e000c0700079904140482d4500c444d00050310300d0103003880801d80c00503444083d412135420fa09502801469125007542c1c01505100c0e0801c3c00c80303041c0c1080e50040c000b261401042600f2074440404c154030160080b0711051120360400e000081c00780c40119109812040030f40300180c41140004283c5080760b46c16103d00c012907643c1881119110001031040e410030840c5096600d101407810700500419001da0008a01e5240485600b4078100781c0c5440b00e07010303500c9040810b21b002600920302d003d440300362805120645039400010007412030b11001aa10100047c0c6203c0c1c0d1008618801084078401c11455100e60070000c01500c50340a0404d000c0e02142c010070580700040c00c2d41d180e001c19010014594401409510041042500401005800715440c44040c21040d81c206400c1c0c0007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 300781924 1250 300780674 300780679
    0x1050f070f0504051c060e030c03070510090809040506150c0a0204050906070203120a060f06021608031c050406090501090b0108010b0307060906080613020a020307020405010f03050607120b03100b0f 87
    0x50f1900c0d040100d002e02d0710b15200e20380d4802050409200304560741c1c0000454080351821aa2121071240030786803240d0003000201c0d0301c0d105a00b4024450700c060b01601c030030710b0740102d155814031140c0000c4c400907000042105600c1b03c0d80e840088510400f10001c3c2c90003d06c0b4000034280f4151510521048a4000d040c0e01f140381d11820400c4145c960000c12102e200031711001442c100d850b4003100602402c0c598010000340c0c000c0ca20045445135000600781c0000f600142e911304120307994280180c4034441c1c010341c06a5900b0700410300f001114a034001c81e070454403410f00061801800c0c0c0381d450031625003040c00c940c101480801040055400d01400c008824220046d011251a00c24003404003410f52080c44184030081000600e55510f0b111080010321070b40c0d03001d555500c6170101c02522a40700c840100d00c290301d08000400e19282c03000c40101629480001000c141e12440d20507201e801d40b032241d030449240c440c50b20080d00e46050050481d400d4000d5400300d061000c0c0000c100e0746000e803121150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 300783174 1250 300781924 300781927
    0x130209130612140c0a060521070f26070302071505250c0203070605030a0f0509030a031e090f0b0c07050604031404080102131e06090b0d060801050f070f05 68
    0x880c0a00700b1000092103540041290100c40c0301d0800581040000030071103074000d2101d2000070b180f13504a0000c0c0311600803004900e50700c1e0600242030481c03131026601c0400281c541c441602505001d00400c41500c02c006a01183ca261350400c603c000d0441180da110020350003150310010441c00c11404080049942d905000514010305c03280c140000910b59548440c605140c030325402e43c017405590800a402600361088280c640501910591041d10408146d038540440c40d0102d8a40e44551030041da110800b55103060340a481c200e000d00055070300074560786001e1040610251451284c0d5230800c3c81f0340914001580725050030940e02000401032102d03c101004034400040c0d001c80d01580c800d50604200300c6003a18010400864000c50308864455031001882090454418050b00211922124081202025040708180c5405940714101c045501c85c0d030107001044000e8040c001100715418002941c5070395126607030079200c09544000420b40000e040c401789a900c450b040e0751100850078640d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 300784424 1250 300783174 300783179
    0x1080109120f020a02010e06070602070b15031605060a0306180902040605010801030f1b1206021b0a08030f0910020a030e011a060d050603010e010e070f060206040b071d1302091306 79
    0x107034580e000c0000086c104265090b5550483c0e4580090b142c1d55500300c041151a1403192030101c844120607581800440e0907043c900460f803800045002400c1e005055018080b03160000b44820758103c000c13040141500c42001040d0108400400710200c90f13110390108200c0d4542c0140001c491450b00702a04004401e0018008500100d000e28041d603408010014121803081a855141da0a9009201042c2410801c1e02c14050142c018094030910450840310040700c1d442e1245d5201605c100003003510300144002500088069243c81e40041540d0503243c460001c0a226422a40003669100100b41d840c0c00d92000b58909200310800710100d1507010380202c0d0001c001604a000c2d9210018200303840740c00285003500d0a40045030620f018600a00c4001c03412a40c940e100d441e03078011400403070008000004c01a2000811500444d00700c0411145501d4080c011904100744850300303030b4000d008035480500303901c903800601d51140c2d8803c0e006850b4201041044442c910b1404000c80513410181b09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 300785674 1250 300784424 300784427
    0xf0c1a03040f021503190608030702090f04061b031d0106030c120c030b0a0b030d050a0f0c03020a0507030302060a0e160b090111010606030504060b030d0e090703020408010501080109120f 82
    0x46070341282d00420614035485162000071030103513492400000300c40c808400d0101a010102c00c0c00f041020318031040c89480d07207031001c0b01e5030b031701404602a5000a185000c104040d012441064105024450209414400c0c00300b0400e61064030b140301c00007030341c2e84c103200074072107039860300000310064200c000c0c40090324503150b00c0545d51040c042c0b00406500600d01404002111170311800030740d4065510b050618022158a0040036250380f002e01900802260780d02c0c02c1d03c13903400c507030701103090347c440c40780c04980720070100d0307996001d20300443c150321902030100c0c040b5104001440082d4803940c010500c03803034408810390540710740040b41c107072030f511605c2c1e665144000c070207036403059a10310b01c0445c4e145e060b13050049403d0030b2400c07806a02c9518103030300840e40543c160480340c40b0710302038402444030600f08001d16959409a12402000841600c032191141c42c01480c00381e001611890058202900c0344000c40c21204283e01c082c613141e54034510b480070482e00808201e181701e05414400aa044810310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 300786924 1250 300785674 300785677
    0x12090b0a050a140903040e0c1312020604050915120c1e011e0206061801050904060507030e0115080c010206010b04150203070807050d03060504020c03091306030f0f0c1a 74
    0x305090007521100090941203581c0e001001c1c035041c2c0401c102c0706080800349561607501c140185240c2c80c6030f400014004615050896040b81c81c1d8402510361b4030324002c1903c00400d0040300c200d81c440c0f4200070002d038940e95889800e005ea8128210f00074412107501c01c004140064141e610040d401050070443d0715034442c80213081c5500500e0039020703c107034800b00407a4131050034003120340c030084200ca00599607540051241d10030101135490341e08480c038004504200300424450a540040c003000080c00180c01500b02c80d800c00e81c0e0b0305011441c002500303d8503082d41e06101840401800e500c408224540c01007165203a181400c0c00a0030380c95042550094003885503024100d03074181c0003030a20010038400c03c201c070115600a110640c0f204100c0c030f010307900d40c40b2a40720340c00024100000890985024422a010951400e00540c6002d060000b80300c203412509040840250b52001c1c000041402c041c00c0c2c004007880b13a0010142d01410b4a008140801140c001d00910f400742d41ca00030f100800d100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 300788174 1250 300786924 300786931
    0x90b0307050a1a0903070e090d0801060516062c15010504050408030601080c070f080c012405011b020405070c03080c03091e2d012004090209030f031912090b 69
    0x4222136911040c03a0042403a040940d07010064500c00b0608203e40200c01103065119000d042d0780c2e4100303e03640d0300e0044401d03001d151842040b541d090f00400000455551140c00500440c03c6141c001170440d03445151880c004504007207580e00f004451b075180b0880500501d0151004440410041c1440e468808080c08001c1142d03050201e07440201e5040545042a624015400041d401e00c2040b03501c3d00a0712908680701c4468650308041100c40718500500d032103000c0504411540c081d944c40c2c6401100d541c0c00300503e0f09220008080c4190142e150342c041d042c46180d00fa150000d13038620500d4021b00c2c450008101c091286014400d000e284140824031508425441604000e104046c030f05031030900b51407071015036550324100c5181e00504441001c02e04150792207002005880c11441044014060501d80c410720340400b0001403100c0880c6a000e4410020094102c40c00006207143c02ca207140d102c0200300155100c400480d9130541d80c803065180042c10000d00502c0044a26964007007480c8020303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 300789424 1250 300788174 300788219
    0x30904060e0c0714030706020d0b10050304020904060b2806090b0309061302130903110606220c09120510050c0c0a380f010b0a0503160e0604090b0307050a 68
    0x40c0c404c4540b038000c000362049282c010794115650a008404c01d1300034085020340600405451500014041c001c0e41640e12a0341c0107005030046a9807940c0c0c040040c1114003003941e03c010f018201c0044007600040030110365181c4c1307140b41310450a041015010200641c0b02d11a0490108104002c3c20800b060031508548035803200705c4c008500d40300180001481c2520304001d0741c40c28000e001417681c405c1c80303802807000311402c1d07410383e8445400b84028422504030030340500400c07039042654003406500100c0c401e40d0034038211845a80f60705800391030030445a800c1d180ca9028910b0403543c00c03818480c143d0001c0040000b10720744107076620070b60f803608030343c0c0700180400c09441c4500c200da88242001c040c1120000316050050f02036590488c50381241a94010496840400042181a115001ca460085031f0791585404c5a8403100600d0034032100b081c1c80c008100e00810f6100c200d813100805070015105201c40482d4070394040090614118155103c0ca1241e895002c00700010000802c0e10110200c20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 300790674 1250 300789424 300789443
    0x80102130e0604021b010213080607051b0304030b01081c050712050304030c021908060f040201020601120f20040e011103130c030209130219060801050409150608030904060e0c07 78
    0x9402c0010024040c3c0661000e0030408010280701d400010b40c024107200944949100c901e54840b401d403655464220754860200e1010415005401c0a05580c44d90814984003107074641900c81e0740340e0541403030030f030310440d0325902031218a0302440407039000800c18006840d0040c10541280c94036804040c1c0c0507508028080000040360902d446455490b2000d170700a400f16051103c000e04203502d6045900c2550340c40e00445010404840380001c090b40141d405a0080c150340e42080c5151103800d05c11041110640d044807480f2001410700c5030103c242c0d0525001038200c0140000c10301c01640c04200994030b0607458600f9542050f1250410740740c0200111070740c00c032140814540300b40c20525075040139600c03600d070408021403402095440c40b074040c402d88805050b42c1415105003112030301e500031203001c64021001030040b8201648030100d6030340210035a440d4054148006030031a0581c2e00581500d03000090007111500b06070103004000c200d13482ca000040d180c103255610540c014041d00610b100c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 300791924 1250 300790674 300790681
    0xd02281a130606230d170906190e010f020f1005090102090d050123011d070c02180405010c090812090a0806180606010801080a0303151214010501080102130e 69
    0xc2801c19982481d40280c0410000ea1611050742001d070180c003251422034046400c00202d82080b003d40d4050513480100100e0001c1c0e00907200900703030051001260004024031106012541070118902032081e0b0b034540524021004000402c503403000400a415540164480c2012040010710011103841084001600f13441e030f6445980a031090fa295668410b180c50349120074400194000442c0300000d000e4001d0045030f04400781c4281070240b046110310385101402110500e64460f003d03502c141e1a00d0701040fa81940d03400154104400c0f1103000c0418068003c110811000744543c546600300343c10607040c61441e041c101c07651194091190a8003140c0890b800081e41c90f004a07080140c10541d054031500e14000300d10f850b84407100d10b02400144500c0002c10590350003145a0390591340c440b8054006070105890940281071b0500c2a00c49111032201c00140314805007480c100e000340302c1d000d25502c4813080c0103800c0c2940e206030003076829648100070300c40200b03410400b0181214142e10712080341c0e54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 300793174 1250 300791924 300791941
    0x141206150703021c0207050a0b091e1003200d0941031312061a0a05010c020f04050c090301060f0b0a0f020c03030711030d02010618020c0f0d02281a 65
    0x1041940030a4100c2c042e25002700b52072035098090050050251207403550020800420b4440345041600c803600203051060400840340f017a080784110020510405a4002540c0c2c202402d40e8000c2c6030280c00d8a90380c0c8018002c000643c0c1c5002103102407400454106d4003c00c81da442103801080001484290710502145c00200500682c0c0c0d00070070382d0185246542c0e0312104054182000c1d08111030652901c1d050506009440f140102003030304c00741c40c0d07180c00344c289030041d5615041d050717050ba4031076010401c60b501c0380c0d6a406181e115501140e006911206079405141c25602160000c50004000190500c0403400c04819141107911034a071080a8000b500c4080c0c0c1001c030f0098409406020008904050210119214010450a40c200d407003151031020201c1c2280ea003402652040380b1511910300710b2182c5038010f02031040c0000d080d02d42c1400c54000782c82c43d004650890f080580c0020020601c03c0000c0c4480c41030b11440c40d014902244500c0d500c0390b12071000e82002c081002040c070302156211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 300794424 1250 300793174 300793183
    0x9020a05270106080402010810031205030a0e070305011d0f060a051909030804120e010e01120e0313080d090303050f072d06060503191101141206150703021c02 70
    0x58038034070802249961210b000602c18101100d0690200e40c5060106200c1c91001c1071510071250440703518100320203180c0d801c0380c0f25407003d4803840c41242c482541060412003408448011407041000040e4008648015003010b007079404c0c0125039400c211084191070710040b0721143d00c0501801c00040c40da81d41c1c03845685011851048804181c50b00c41041d0405030810341c00c0b0f0180e40500c100b4181d0001052080f640e09000071b18081c0002c03445018101194009c1141c4035980403e000085801d081c2d55020a1441c0c2000d5500c04031811291341c03c1240d00e0b402e000d088000700c0e451a04144880c1161400341851090129003011440b00151540c00d1060408890307800003180500d2691250003021002c502014081044e6119480c240d8009400d01c3d000484644624102d0707040c40a05444c0d840d101600244070040d1414801924202002419a5801414a104560801c03106824071000740f2949100c0460300c103003024401c00c80e07d800310790000346601c841914800c7d1010f400e60600002c0b030a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 300795674 1250 300794424 300794479
    0x109021c09020d050303090a1106090f0d03050c01020a030f0b0301020705120309070f0b090130021806041509090b0d02120c060a09050102010e0a03080705030c09030a060b030c010309020a05 83
    0x4500003c0148040081f012034180f4034203018800c0030880d50542400c124541c4211361195901c01c611054208803418500d40448138203000e030030700c541040301d0031144a080ea80b12600000000c0d580300034120585680c0c0c8112900c001f0194001c5040c000f807aa9026a00c4046242d0104210f0780400010030560b8100301c64009420701d200d600711815a10915000f0541201d00300a01180d0b02c40c0440d0b400c4010a01110703603613003507e01d48196100c0da40800c04020341c00200351802c2d4043c4240ca107000768803481c00030002000c40014441030f000f01031000900241040e04051040307070900740350051941c0c0c0c0c40524116180c0480e407113806038001c0311040b450444070500264200c140401c00c0b20100d80c004220104030350084e0020310000040912041d15000c00b07400041c0810814004544814410006564090750b0314074841d140114500002e0700d003070880c0700120b03001030b1200d5110529043c14082c46200320000c0c00c0900070780c4071940c006550441c0031301a050250040c200c0844050200380480c0700d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 300796924 1250 300795674 300795683
    0x170a02211f030b0403030b0312030112050f0604030e010906020c0603070e0616080318060103050307060b03070b0d02040f06031b030b040929060603100317070b09150109021c09020d 79
    0x1500c40d0b0307929081d09940400ca4003500400e240c40c00e007402c9400c1c00700e44490030a40c1900442c2c81c1d07a0070164000300c100d0b422481601d491040d490040405201000301d01c2c01a400780d254181803145203000100a0320907900985c0031500100500001d98a440003580d40068550901d00444e565500204200380540c003440503607001c040803203406001c0c0c91801940250070b0500c40310a002c00f080c81c01c0f50f07243c03070078400184554010841d06e40411515840300c0807420340181a1640d80d0350b20b17980805150080f60785040c00d40ea000804000b28220b05039400018445814244450b04d00c00d5684070444400c42c4001007415150100d40080e035031a03900502d8500c1c3c0c8561381502c0b0b204404e8240010a0300c1200560340310210902203061450140b050340d21604621120011143c1560f58046100a1101c200d4512000501c0385030b001a0050485600c00e400725802810340403a0341007445180e60060b403209110741d1040280e0f0022400b20002c07400100030107400401c0c400000e00c003003420030700c5980c0080c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 300798174 1250 300796924 300796981
    0x3040f06050a2a1b03031710030f030206090c0a0806070810152601050d060c1704030210050f1306050c0403020a0308031b160b0a0905010606170a0221 66
    0x1080c1c10f160010381d020306402900c01c031001c2568104500c002d541140406008103842491041c8044480c401c0e482e4422501c4e00d00c1c2441c15500c0d51950000c0031041e50840243e0012010448100d104100507010540e00305e4101c54403d2803c0689070319040b000d07015008020030b10700090044820b40310440000c0238000d03a1150542e03848507001704496a401c081d00c8031040740e10784401c0b50743d981c1c03022503042e00d40081c90710a1581955607014000c02c003620409052241c0c0b100b40c2d80d041c0700c40bc0b01c40d03846513020360050039080020030134840480d01c00610030303005484800244007116100c40c03d42109164008000102034036410010320141c061944001c1d4811031142d0301104100c00c0c80013450161003160001038200400d581101c030309006112080c5414042d40500074045004a80c0d5241c2259050000281040003901c40a0030b45185800100100d14a40d0001012012000300f8581c486c00306601141481030407640e6000152040c0740b200104164580807030313004644a400700400d103a0b80d40c18031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 300799424 1250 300798174 300798227
    0x50d0207031a01060816090b0d091a0c0306040b0d050d05040602060f0103050a08030a021b010209010e01050c0d0804031106040308011a0910050a110709050114010203040f06050a 78
    0x2903541125001c00c07a0350204402045100c800252103483c160ba04503250a40b2580d28000f6510080d040343c550842007161980d000194a00140c00420038407201100201d03103180181840e09010b50003002c103190741020103040001300103085060720340041040f00d011a51203814400190401205e41d00030340785009003115a00665048002402200d0315a002d07142150344070311138078942400034400640213800c2a0545400103100750004d6078840204d41f001410080d901d072048440c80d45050101c0b85682d0700180001c600c0da08507e000300381c0a02443c0162404031540030260b1078040f4031003540c1c01d1100050210301054020002c07090b42000120883e035140c98281401084c1c15000c0c0302d40064070314449100c61200c1d103c8011544480800b80800306804500901128180c1c031829001e010049015008602038105010f40704c010201e078031700491154144100492038a1120501c203041d944104010400300e07032011010300880d20141040368503100541d006a901091411480d645640b114820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 300800674 1250 300799424 300799427
    0x24120b192007050c010c0c120303020d09050c0112020414150c0f03040302190303230c1504020f040209090403050f211015050d0b0301060312020a20100e0409050d 71
    0xc1d00000d0f0090f0225103400d0f503580e00556803c4042240a406c4a144501c00d1100401a04040d42d00a00c40d240040c949a44a12030700122814221304540e00c0c1c21180c00b14007650791281c02000b502a17203150031441c2506d842800307544200101109806090700d9001000103503c81e406450001d491003007a54032070300e840d45401c0c1d101c0c2d10a000c101e02c00c5081400e510f004a8000080700c0a40b645a1251031000b45070702c007000b03400000c03100500880c00d001c002c4050542c0c01407010f03004018128000e40c080742002d20400c498503040c01030f40d5004d0303481481000c42d10f42d0340035410364000b609820169540d01c5034a0350483c07903114080384801d02e10600c1d16a4942c2c041e044a155114441c0d0150350000c0644602d0340b2843e030b0701c0b4041d00394000782082c0000000480642d00100320a074005000043c05036403030356520226901c0540400c00340e04001c440c8814062040b503212002d480300ba940c024078992880006e40b0744081c03120300f10104603a482048285455550000c804603410004039003490311030400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 300801924 1250 300800674 300800677
    0x100611030f161b0e0c2a01060810050903040314151801180c1e080a080307200d030b0f040501030c091409070e071224120b1920 56
    0x115154807004803941d00c0901c0404041c0e0940d4804d0045540540720303404400140d410a0124090249509480c803100e04842007800004034801000440c601d89040303d0386040c1050700a00b81801ca04020401549070008070880707066962208a0000d510740e4200a00e107416284e000b20549411685d0601941907514109030200340c0034600240000b401d981038010043e120120010240155900c0901c00364000180f00d05025803d0010703e81d035030360360744c080e1762400a0b0f00b6810307201f030000002444902d40d03202c8017100d18201800c00c4100000d100c0140980c2d108543c00c0300b081059611480240c0c03641d02c0100018002c1070050003444075503128204001610341d24840e140030586414151190041d6400d02e4a1080c580800503207051841d117440c0480400e4020306200c02c010f984400c40303444c40d80d01d01c03694024545000e90602040106031521480b040550416014600c0500720400003811010b0302503482501241c40c8046000717512a02800303894030b4a464210f4010700c0c3c05115800781000c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 300803174 1250 300801924 300801967
    0x30f07030210060909020d1101020309090a02040302030c0a06050d050709170106060801061409060f0c070303080402190b090f0a050a030f02090f04020913051501080a1703100611030f 80
    0x2c0402001e581c55501608176036000c403000b03400104288414001c201c07401e48181030101e0600507240380c8999240003908010341211841c4205501081c14810342c1001c104214980c0019035000001c01e00703144018210f070140c0b100075521503071501d0018807d10b10a10003207004001c00004500c03518825298640600014042c0340c002640ca0300000030100e106400520508034154a1245010301c08400c0c070481d0750000300fa0070b10101d410000d9142008082229000941c0650382c0c51046083c50302c10018804400c01d500c040d07240b5a40f00521942c9425021a55409421240700c4d4080c410600803038110020341c0d00603580440501000814070a5009013812418801c4800d01e5080c0d4412919450555064038060b40114001c0c001540d0b40d8600758480c0b90580c0610201e070f2038001d0070303402c1e01d00310a402d030032403000c2d070308401980070810095030300e10512003040c180a141186031582141d2910b0603a4403940b82003080c001d858a5240c2d070140f0403075800c0e000b03580216a454410140c0d0015281280 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 300804424 1250 300803174 300803203
    0x90312080718120206090a120f03020d020c06032706011509050303130605031906262e021c02070309080606060304060f0e1c0e1504090905030f070302 66
    0x9089108201002d00c42182075400c180d160280100c1d99800b07114843d04111465900705d981564003041e0040c40e07880080c0d44a02ca0b04060400e2515807030000d003892684c3e41e680042d544400115401e6a5410080e2540202c542000041040450080c401015090502901103000d00c500100700c0b0b0030f080349034180c07541550f29180f40f03180da100c041c5a900d1080f1030480c80003802c8000c0901c0340303512400055030051400d0301c0707015085e25041d5500040390000c1d4000154103810f0712840001000c1c98003450320b500300703441c058980221060003031242d40381b51680407082d038060300c0e160340301909070f550694542c01000301080110754580001c0030000c1d40108019000309140d407400103941c03800060300c1d51054030040c0c1241c0c01c5446555480c009403910001401c500f1752903031140b1100b0401001481804c070038401c89883c880881202c003515004003408414002c540c002c41201d00c05124400711802c0b54000d00000546100d681803860842c01140604808403c0004510301419400501c41d01100b581 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 300805674 1250 300804424 300804437
    0x10e0409060507030b09103305030604050604090f0204052d0603060c03311e14030a08150307080601030302030301050316060e040b1201020d050907090920010903120807 74
    0x4042151001040782c0c07160b11003207c2c4406004c0507444d01415050500c00058484421024044943c080061038400b01d000550200800490785014024142c000f803007074804214460007600c5010742030741c103150301038001d80e00e0700d01141d802540041c0c00ca042d580242c00b020000c00c1a1401010f2480040e06c1ea10b20078442c142c08511400f8212040720b002d01031589022205040d22588241d404044042d10348035031131803903145401b140204001a481070180d091914807800146890800244040600081030744140701040c9181e4001d040303550800c9c1d4441c29500850b10790300002e860030100d40c0090725a401b03004000010580c00101a50690b0011810b8822025010107114050b4007244607140004603481d00e01d01c3c550601d9403008094400141c4074248454461b42c0340d0b42660712005100e400c1c00d81c6c4000704010000305100e46005026410707018460026a84c54045405040c02d13001c10036030843d517400c0101a0300a2150200566000c102d40c40d4083d103c8a016004460485140d00401c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 300806924 1250 300805674 300805691
    0x17010e0c01020607030c0c140105100f0f0303120e0102070302070e0c19050c12041202011106040f02060d0f0f1a01080601090b0d0f0608012a120b010e040906050703 72
    0xc5500205400107a0041c00503655010080300504009280c40c803e0280c1e540c0c1c00c502141e082e031294102c0070102d600101d0a420f20300c45024110965038404100411904003d00980c40c21029081c2101e8051405005d15400c1e030491800510300000d098443d98400102c0b1001c041d00420603004942c68000100c1c1d0325a90b98103035418510409040e001c0303d00f4036101ca198071a00801c094600240702400700c54100280300c600000d10340c02a0480e40816012920440031980d1000c001e240d0300b50407101424003400c2994541820007005c240c0284201804501c026402100c1d5003c2d001c202c0000009000010a42c200800100110f0081c10783d83d058280040403194090786c82d45000d503106942e02c0d03021614040d4506003a40214181c01c0c05292214180602c0c1190350080030050104640002400f00103990784104144021904610b1101c008006080568012481200d03445191034046280000800126907244022540650007454240d000c000c4c8240703684084d01c46c2070030707407002c1002c5070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 300808174 1250 300806924 300806951
    0xb090d021b030c3f0c090c0702090108010e07060504030803070f0c0602030a051b030601080c0d02090301091202071d061c0203160906060302040b0910020a0807210507050a02190f1701 80
    0x940241d41000c0300e501c60907003000c49040030b1044990211f0404801810144140c2c000361202c1800c0c1d02040303450391220740505424030180441c200515407400c1140c0782034915500d0a545010007003014091040c440d08010425001d014060100c950040c000c550b28600210100c008000c2500d0602c141c0c00c004281c04041102c2d5012a8083c140c140c5680d030701681c89200381c1045030700c0241c1e9519001c2e028007105000f52824024690118450580740d20002d041810091400205034041d620600711440c90764180c589824020750006000d94204280324520803002c0107003a00c0c08002501881080000c081000074142c45a0503607120380c4050280c141c6e1168200e0580c000c5010784d850461080050000c20f160010042103814490b00642c1c809103120b03180e0020725000054243c41c880076071002c242c1ca420454040e80840c00050034028140400350303c925a886c1300c4002c000f0f0158100e2442d00300000d24500d18440145134055030503502d00c0e1a404103150355841026a107415600f030409048003038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 300809424 1250 300808174 300808279
    0xf032b030b060703020c0f04150803030912040e0408030c0f040b1b070f0b0702030703060516170c04060c0501060b03010602010b01021b0d2d080301030b090d021b030c 73
    0x1360141e00401d0b02d000086c3c200720a10030028002070740036540e110719500072608842044c0043c1135110140d070322450203850883c24901c00310071080c4801804c0101b4030850b002d01c4000d075045504030801c0ba03182c0d541c588000120380300e486600c3c0e040b407101040005842c04207500910070200d5126500c295650400031855a4003914040c401050707143e00f100f071221010500180002600040c1140c08982c0d990716000c080711400d5900c4c00e01c80050380708401906410004c21020309640c01511034441c641031a440c01d07940100e002d0f5004006000e03a011081c48000d40100340500903030029036a880d43e40d07000103070003440f0f07036088a405030241c12010a806c5d540071021058108014114051420881c1d079845610a02c2000307494880c4c06000020a000001c6070b1100d220340c0c8588542d03030f601c0d4190f0404480c007010040c00700034583e010f221700301201c650100e07403000c400c860001c0c1c804034441c1c0500080e040c0788444210070b8000080c040c119003d4050400000180f413980c000310100c01e000d800441d1000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 300810674 1250 300809424 300809437
    0x4020d0504032303150301140106090e0c0c0c040f0e01050f090d0201060b0702040207050f030d0603110306070c0b07031805010906060b030c090607030c0f0b0702010b0409050c0f032b030b06 83
    0x403035030500c00120178440125020b4490701008000103601d11503943c100900d80d4086c0c00c018001040381c20244100014a500560018481c1070042d0519103c0441d59036100c0c84d10401c5401203880300b400403000c0a46030800c3c03000810500007440345143c03248901c5002c60044030b86920600c1601c05040c0080c5c0180704400a84464007052460300a6035001c0c44041d50040070100c3c0c1c0b910030110920881d22050002d03140e0b145c80c010001c81c2c0903185084ca00791104401213454440c0e0002014022800d40011040002d80c4d803240205c20541d45040003500200740141c80c03006407660a980041c2000010340c410850f40380b144100704092521251036810b0360004960354440e01c1c00801905003145007807000b905075144070780f808907480300e400e40d81c0451012004000322049611801804070741c0360207005005a400c030686040082e911140c50701540d4032a09103109019075540308060f5240c1d00c00f03002c2c0200c0d00c0802c42d41e41a071030040b000c2c08007401c0c0c000b40e00c10300001e18000300c0404a140c450229881c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 300811924 1250 300810674 300810737
    0x506010e0a142701091a060315040e0705130b03010e010e070303081b040b120109112a0307121103040302090106080a09020411070501051003020d1203020904020d050403 74
    0xc9442da071403e0251284051060b07100d014216040381000c1810b10000c00c2c041c02100c040800d84a0b40ba0f00030026480304a400e03907110304414810895022a0b070351410034440405c40300490900340d0320030a00c5c1004c000e5040306400801c0b005c80343d40042400d4014000202c4160000c00c454042e032200d003822210700c2d0b004402c694100c81420404240b140c0c1403150045420b0b188a00c01c0900900e0345451588281e0100a040401180c40d5000041d162031003401840c50500034890300d400c529264103288143c1d110140ca10545801500142d0507800a01c02c032480c076201107940d01c0750142030120712040c00d1240782d8009401c00c1c140114804011003520101d0b94040c2c42134610364240702054406080080a0150080d511010390015a0b80c0340100360b05c5070048440c940c0d0b920170314240310b402c0d03501c002c08a10b00c080704104100300607207940c4002d450980d044141c019401e070032404220f01038425101c800d58810300210b144507680f407050340041c2c0902e1003a1540990800c560641c01030304164800701e00b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 300813174 1250 300811924 300811949
    0x90d020d050c032127120a050d06064d0c0d0c0f05150a080c16050616030902030a061a12010c031508030301050105090406080a05010506010e0a 63
    0x14190250000e032515501d094252410b180300038400b42295045101c4e41c1640440c2002406913442501c0200350f09a2880c5000380d580c03402c2500800d9444103840c2d1403060001000551552480c03140064a003a002c2d541c40a01001e1340e120070080a07100c2049191041e2880c0e81d0700e0510071200c0700b9400152071003014000101e003258050300311840100c640000300c1781c0607000407001d281d6140c039a401c43d01c80c800d040c0980e686042580120307840e01e50741c0003503014854401d4041020072b00361013a51043c011515082d0604d40e501003c1d2201405041c4109444c0807500d20748070100304010521601c1910101c181030010382d000b00084043c0d946440001c1d4064000750303000c402064071a04003100200002c1c86c0c815888600d2070108107041c008051020a596503442e03000c10003a0305000c0e43c0494100583c0143c107250034081d50a0b1644018460281071200001d101001615590000d00007440c4600c1a20118181030504078042c200c1156614002000042201820b00d0003203070301c1065801c07980e01d05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 300814424 1250 300813174 300813193
    0x90a0e070b04091b02150622050403030b10090b0f13060c0308240d050f0a050708010c082403071502030c06070908120904020708130f0e15040c0c08040914090d02 71
    0x380d4a180045d0501d5001651408c075060541140c0314420860240b00f10300041034600350400078101ca000c0d18130144551f003400703030300441c05520100c080300741e0f640310450300d6450802001d450141e00ca030012805400500920010700341e0f40007914810b40c24066101c0b10203994584103884e8451159035850394852120882d0740a503030070318040441810f4412002c07200804828541d0900d000070444080b21164490760301402610400c0c020080340144074109070200e8141801c0d0306159484542110540c1c40d185101c4151a680030401040180342c051080b081c0130703062000c025280ea010200d005034a2042501042a59209202c003408948090700a0710b200c5003242d02800b20f5902140405030b000d0380038810f00307000c03440c3c43e0003c004525491031988101850188030418104d40c0b03600456030842000d00700440382e0000d01040503008822a4005002403d0610a86508080700009880e091021401042500c12640004d41e4100d241c41d8a030b4842d238848041c140c0c1d0b0601350780480010380119003030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 300815674 1250 300814424 300814453
    0xf050609070602150a2004090e07150816020c0a060543050a02090a0212010e06030a140a140102090a090b0f0603060114070b041a070e090a0e070b04091b02 68
    0x42e980301c5c1c0c84040b00090201308006d03501c5d1290010b801c070005140e680d070314000000004203c6580200303014600e014401920300300c040c1080c9401407500110580c45217003000402d20a000c4807403c223500914065101d9281c1100510642101e4800f04000c580000c0005820300308228038203080607144480c0e031410340310b0244c1c3c1640c43c140100440b120310402020704011f1b90b407072502e50301c5035000100c0182c07a100c00780c03014840d644060b4000d110000310482880482e45001c20f403900700a0308083c160085888140e0401e103405c04464011b08000a51401090700075410340090089801c11a11841c0840d1288040030031507224544450b40010103100035811418804003869101805050060741074030144001901503120107402c890514000f0104010080e105554001e070081c00c10b031503e2240f9104402600c00031042060611170040c0c02c0018030102015041004603054400035100f0f0f0740e607100d80090f0950024007032100c200f4100300d00c0b0a007203101c51a0000c0c41070220342c028000c0558030080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 300816924 1250 300815674 300815681
    0xb07081312050903061807150909150503010e0709110a0909200706090318030b04031d04020c060412021c05030606041a030402120319050d02070f050609070602150a 72
    0x1030070060240a10100085580920445110711100646001459420005941007580982003084042050b0003a00c40c0c1c103900a00401c03ea40544000140c030f120030140f03050300234190340d2256505600701000005840c401080d00b404403a404d240078008408054070245540c06260b8415000a8240b40304000003502e03600100c403100b8240e00b60a901c400180d010f0341d02c40d03009150540e00d0503181c6080c074081580c800c440540301e084000c0301c11042c60850360780b144046000340000d17040110042c29860600244000a1802d82e40100115500c481c144002d03a00c80104540c162054112880c818000c01e001203043c030b0302005111680341560034418070958541e0070250200c0d802003010302c404100c0440349005d8ac80100e104540b05912031034503204210810100d0b81f000401c540080c440d4042900d0060720b07640c61741420303090044d03c4207801800d01c1d00900801d403000c0c01c404d103220b1511040c440c0c00b1500b207002e080c0e01000d82e4030306c0b0386070f9509980e1440d4490280c100c1301400000a1201c1440b42d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 300818174 1250 300816924 300816953
    0xc0103020304170c150903031302040b04062102040e0d080103030f12021209060a0e061603020f030c19110604150f0f0606022404030507020a120f0b070813 68
    0x686400b0b4240e41e1814410a4122400744075003544107140d40300b111994000342d2075104140500451231803510352040071240c2c2c01003030001d00440c1c580340d91071411b640e01e800201c00340580c6490800c01003000c401e0814a00000740c03007a0301071031070720b90495060360010481880071940c035140c1b4001c81c0d107159000c449586090f14a40c0800c1203071314900301e01c07a40724001422418903200c00616a4208050340c1403c0240c0500340c212507901c2d0405462181c140807500b95409240071102d0842d2071440c0409801910607514182200e5400204101190544030b01420020b01900c500d4104005000401d5030050450405510503a0000d00081c3c005001c54030f075030000148400c1b001c2244901c01c42d02d84160385072400c0704041151200d8043c8920350741042103260703881520100d803500c50702c18803038114240d0300030748003804002c000980c400664881003030100c01840f43c80d07800d400d0b0151500701880c00c1d0950007421145029201d0100d29020710031056a4018580341d6003a84001c4c449903100c08594503080b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 300819424 1250 300818174 300818183
    0x3161a09240d02030a020d1d070e070513080a11180610030209040f0603020f100e15040302060a03020406080f0f190b030f0c0316060207150e0a091d0304080c0103020304 74
    0x20040074100c560603001031360080350020400340c0c403800400003420a03038000da0407220408007002403035009a2000502c088c00ca640e000200c440c80d03101d0f64403ca906200d140740010307045031650702c0000e050b80000784903503406000342990905c3d01300d6001081300f6060301c4040c44804480b040c000c1032242c5451140c54004500d43e0030300500e804022804501907440c603096402c64250f590004000b9410600e66880c2200b02c12109801c0440e00004003174050045991070b05e0007011500c1440c1c4c410300c2000c08680146400034070154403a100030708018044d51080c05408009444c8202143c400c1e51910100d40c0600941f1841920690300c0e64a09981c0c04858071803242213070f4a907035007054140c509010709840741e9404c0014284403900030082c5845c05540c40310b1001820051002004000d034041016000e41c0c680c0880120a41c101c07074401c480f800002c158079a400340811000048a0550340e01c18604807d80010050101d000600c059450f40901c0c410a1441d4014440c3c038025988a94025136200c1c1c0710307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 300820674 1250 300819424 300819427
    0x6050f0a090e13060506030d020304030f11030a0b0a0c0203040303050d092315060a0302010806090c070c12050c040c0f0c080c0a03030507171006031a03161a0924 71
    0xc2d8942c038010000181d0f91071600f0016003400c08280a000d000c0c00f680040150010940810711080082da41d216610002d07090000383c2040c0000c0011035a4006501c09008007203e540c0011410003902007901942c02e80407c61070305034810344171400030094908517500364032083c0c1071101c09826100070744a030341011039411415035114840d0f07000c6501000039114461000740442c0c80a04203103004010060003203481141c01c80010001030780d009602d568028003d0b10b8000090700d0300e160660080c0510b0340c004211001c00e90012414490720880080b0040c000c404980c3c0d103503400d030144411100032501c1c1c0c000150b2480340c1d00036214015003002107800c0c800d0300210b1400c0b200022040c18465016001c0300000d0302c0342c1c1400303041790b40100380c0706200c0ca100036006a10300f85540c40307901d408528840c440030302d911458500c0082d051401c4031181240e000d42030380c000c0d00401c0a00039911364030b405100004401c00c0311680c0c0360500502511071200c0301920031681031410121034000a100a400c03081c46180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 300821924 1250 300820674 300820679
    0x9010e0c0d060b0307020c061207032307080403080105010519050f0c01020c030d06050a0807030609140d0f0207090e1e0a05100906201602010905060403032001050106050f0a09 77
    0x210707841020300820000e0030144e03c0e03040806000741001401101c181c03040a06000a9100403070000501c1d801078918180001c04002800c0300f0344a1801c8031014802003800102040120303600119180d114a2007951000390981e2a00d005482c075000e0414000d4001042c001188500e82c0144000c0282d400741030303d03203814484400b261070b0a81e07000321aa0b540c540c0000c10220000150342c01120042d084c1111044d5840d070030441129640c0e0b2041c44054441511198124280000d45800a2206541200b038038550b6544d030307801600c210000c2d01d81c00e0044c403d5a000141ca000f107803040d91240c041340270180c011401030904200b960f4000e16070003621400f44e62410b1000500801c11a0003103440c40a01103142e0410341000400c0b03a0b4040e61444801190a41c1700f02c100c103510046582c04400c410810301c80c46114001201c020315183c002ca82c100c6c10000340803041c140c008071004400c0c1c110440f0040507940e00002c490988500303105840100703006000542c042d4100c5409066114964900b01145aa = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 300823174 1250 300821924 300821947
    0xc120203040f0602010f0f0204050907030902060904020a0804033b13050906150102060c0702090411031902190501050906031801020d06060f08070e06090307030803040308091b09010e0c 81
    0x19110343c443c60150395510005202d00c0301d24020011107840c0c04808508003840e003404222404001811101015692051002123648040646051100290085403182143c9002401034242903c054010422519010142c45032030b003a21206203c0d6006111103554102c00d0f2054001d608005c01a4024200e1009000b03600880c032606100c0d103007000040601d414072103510fa5408099842860441d001034040005003401201102c124076419144001642c0c1e0b2030802410704044031a21541c103000d841c0301c00000404102c0503608440c022a06001c5171007180403070030180740c450322500d80412818000781b51a45000c5015560100950f454a039040c0c10410304a801c80c0e002c1140213014554500c0148107442c0c3c8020b424441181c00c0c20000120300b006180900f032000b5402519216400c0062034103181e8406109000c001c652100c2180e40728205480c0180c1080c2003121403000603c180303802e400d000b44001c022460008405411000142d0a1003404c41000710b0040034008290000c111188240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 300824424 1250 300823174 300823199
    0x3110703090608010b0a020d0f020109020d0b190e15100f0e0f0f1314010b04060306050417030106080f0402040e0d022503020a090c03180f02010801150c12020304 71
    0x40d1095680141003030508a01400116040e0803014030007005202021038950001090340d0081c00a007810700c01d10365142e10403400f5240c600320094010900122034000c100705c100c000c60007007a548110105010071154080700700e520100000e6102e41c410048804000d1002c0086500b104121031280e8041d911500741011840d1182d00800c074545001003002240d1031400c40c034580012104c00c00c00e004d810000c01c007042c5840348000290198442c0c0a1594006109500406190f0b2000c0d0003841030580da42000700050004441c150360b040e28000d0b0441021000c101104d06036001616642c15944415040d5441c0f100b000304103c1e003280d41d60401003d801c5003000101002c55003a0300401d0803284c04510014194889044d42c810816080700c00d000580c0d80e80d103070074241c4a4020700043c00c0030f00807900f00c0c0500301110a2504400f80b800151046c0440071100a800034000c0c0c03140ca050f80d0b030368405240000040d04c000000180c0c1d83c3c0000c0d000410380003400c01040d900744100c900341a2100000b0042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 300825674 1250 300824424 300824437
    0x9041803050304031b0f1113061e0909050601090203090304050d050f0d210905010b1f0801080a0c091a060f04080601050d0f15110706061d090c010509010311 69
    0x8100003000f007004056100e1104200c030340e50007031103100c05001590b81303081201c141140181210400690900681c80c3c090b10320030070103c2203900744142c50755a40c0b1141d070241403122282d500c52000c000443e034921580142401d55038014003c0049070300c0d0501c800c0c02504050003c0007076000820000403144d503a0003021200d5400f94002d02046c40c040030758245000740845009050182c840300c80080e0b074200303c2c482d1010035446000841d042d001840c000d03004041c5200d5003a4041619075615070345010920b10070a034014942c45800c042c0e40c84075550703681c1d001c0c03140c00100400c2e80440305001c0c800c179079044a4403440c40740070070081c1d98004200250054000c2a188444810003203001c01004600f04951401070105030341980d2504596100c0c051b6114802c0c0000e0f000e101c1c8605401034203580380d40080c4800c40c02c40b44290b241e41e0f180c0750070405448e45214141c812160642c0f0202d007a0a120b00c0c8a010790038210007041d40308046001502c07a1381011a0150500d80d6420b40421082d0720000140303007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 300826924 1250 300825674 300825677
    0xc09060b03190614010c021305010303020a021809030901120216110f0f062208060405010911100e120a020a0803120c070305071106040b0c010e010e010c0e0609041803 73
    0x2168a0014000c220003a40701d81c1d5900b1060403c2d0b020040301d00d100080303004014003886c04034000d40042c00031501c2c0c80c0031142915400c80c6040c000009066000c12001c40c494030858840300c614141d0784655000110a88405030a40c100700310300a1650700450450070742e44511400541491441511206a40b4040500307560202181441d4034891030b1a103424002094212403004148481c00c010609500800c01d04902100d134408035000441040c90507100101480411a022460545800780c084e01c2d01c802c00722503040c950611598030b458003106511800140740e03a5540c489500c5c40030040c980a070500f035041c02d4000c1012a8000d62a400769180c0917180110055541b00d0b002c2780c1d4a101540e009100e4074101c10306010740e0000a600c07038100d405181d00301c40070710342d191300e40000100184203c0e48000d201860004214403c072006400041450201703600800403c806024154241d0302c3e910300380c3c80061841c1c0e0022070346180020141c2034070800a0000601d84403096600c4004000306030040c1d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 300828174 1250 300826924 300826927
    0x6030614090c04020708030a020d020705060a020d0b010f0507060c09210b010602120f0705030405130e010c11030a1110060e15180402040c031512050f1203130c09060b 73
    0x307200e640800c003002801406881c11841c240864640001c41e01014040308241c51700060340205018054050358182a0400305940071802d1022071940258072440b684480d450500400000541c0900c419070400561034440c0f510785261036684100600480c1550810b200f0607100110f421041000b9100f000141141d80750500c41140c100748002c080140d00038011540005400317241c3d41440d805852448102080c450348aa205e407074094158011034101d1500003a04105a0312a10701c00e4121426509408000f0483c012000f20f0403078020303010760412105a40104150300300c05119000c00700043d040b9009583c0a0820685010f085d100b0960210b00c900901070103102d075440610307042c0b01d00c1007011131340850b000440c8201d203003003410b0082c4044d2041d03a844100002c240d0094000040c042c1a010181e29240e480311700100103404c20510680702d40c4200404448203501c00203120481c0f00b183c2943c641541c5d80c5441d0340d00d8003440c0000458031039000150025100a4900400000c0d1030000e0046 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 300829424 1250 300828174 300828181
    0x3010303030b131104051503010b1603020705220b090103170711060706020319050103031b05030d05090d110303060319020109091104210b010311060f03090d020607020a031b0606030614 81
    0x403e52044400b447c8280d000204010040030740c1141c210340c0710841e01541c03d81ca48050781000d074188046940a6a04074486611685946270005050b803070400407203004104000c891001e015072240c0901008042840401400c210045c06c8406061486c1c80784103901100c098030000308086810135007040392016008003d04c0750b060f614908048046031800300c2008551701d1a1001089003074200001040c02800f84110028000c00384100d0312412070a080900c01303070400c82086030ba2052003070401800980410804603114001000720b80c00703510000c00038945070000890a14582031081ba0480c1409a20b500015460f0554000d6448203085a250031740c40f640313000850404061104100c03401e0f00740c041810000034640c0301301e2078113494001d4101410b03000c07401c0c041003041c82182060b850404003c01040340d80320001801c030340a080c09a00740c50a079200c032942030380e580b400e40340f000700030410b095151000d0035401601c800e8884c1c011600898020307643e407604c40440d00091201d030500340049080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 300830674 1250 300829424 300829429
    0x9050606180c191407150c0302070c0504020c1c030b090705070b070315050d1506060c08120c0f27011d0d021314150409030503010303030b13110405 65
    0x9540454080c4100d09059180020050100340304400507590303101000c20f41c2d08110f42c4514064541d004481c200c0c141ea440306414012406007a48040702019400c1c0f280f030010740351182c000e450030710342c1c0f158803801650304002c20031010390003000003403c2d244900c0f0b1030702d10301c44000c10b8808980c060548002a911034010140504540010403100a00004118101c0001d20701c0c10640d51210461800140e1071800c0c40d2900441f1409520039035108210f00d2120040c491000c41902450f0b006200400400d40d43e1a02035505101460300645903e00601070154850b00c1c51000c80c2c0d000391120b0380140380000b016802d1f215508094150005060742c01002504000c02404040540b8000d081070041a45000c104080410017484094090100010071004648803e100040c200b0041c081c1401041890b41c2c2c00e0720440e00403654401c11514140f417145c69414944601e11000d505551030701e10356130854809501410140314181d1f003001c03001c0000718040240f0312070100d0711401c1c104500e90741c40c5003008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 300831924 1250 300830674 300830689
    0x10e041205090906040513080a1d0405060f01120609150603050901110a031d03040305010b09010605180402030403050c0d110f07051c020102030d05090304031e020d1509020409050606 80
    0xa0a02400308105035950b520f00c0381c850f0788410100e8012031a544d88000c55a0141803441000b000d4400201c3d12000309034106c009616080008103140c011108203d00700001d0301c0c800d4480c01d4100700c0c0c010f48124654440c80311280030444c0d4140c04140240d445440b0812914a40d00c454481d0f1864103003800070305c1c0d25008058006a0b00c2c8004d0000e6010100140818842c00f20a44245980d03080070001e0240b019001c41c0c4a1074000d015a901c950b42c9041003400b81115103403083c404d00d00117002042c3c2d28041d1081d61006040b03401400c003441000310500c40203500c05171041c0c003448001e10008245500812802c6d5095007150368800a00e00d003420174600c1e004100ca41821660000e4030140820707100d0f032100042440d40820940440009400140c1c00c3d0301c580c5109520950500d420441d02100020047c011a807089440f81003c5480d9020034031803980300760703000354011960a4001c011a90224aea018141d800540006003c40c4e01c0e0300003412aa103041c0200c0b0590881010414103151000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 300833174 1250 300831924 300831953
    0x803180a0e07080105060901030b03030708040e0f13260a0e0306310303020c0318010906050304080a03050a020c03070f0b01090506090a020d09021509040e0c010509040209060909010e04 81
    0x1d2040e40a00740744001414800c4140a031900807440440c44441d1a88282c210003c00200901500d548030346d1814030300d80b244e0190040e501440c800f100415603003150340700780303070f1180c48042c29041020500390b84401c0030b6540c0402c1611580003010900b8088a4581c00403c85010b064a55503034000200701414106038008000342440c41600300880c48410000c1c840050b42c80045400911400b518941640203004204010159110100e062030714860b02c80c04807102e00d4003d0300e03010111035440300d003210280300454008200100601c00300d0401402034102d1074206005a2000d82041e0a00c2c0724240355400c0340000346d500c4444440741343d09101142040a000d03140703c54081c42149005000700320803440c041d0034050040c0d40001c4054020240d544040c840c650300030320350756035040084280d0f0301c00d40203007011621407071078000a4800c03010006114201e1a5040e141c8908003111481048025006601455084401040841030a50b64515614040e013440d101c0400a41054104511000b1080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 300834424 1250 300833174 300833189
    0x110306010503070b031f0e09010b09040f030c0f0203010e0d14120619080a030c0213060807060c05010906020f0c0d030207080706020318010c20070e1605040803180a 72
    0xa0061110791008580d02c0d040e115862860359594a0b621a8500d5441e034518100c0200021071001141c452400340101e400f900d01c410003403101c0c00c000010485e420100340e400074048007856180c00b000902524079241845c1c0254440f11301c5801a40103e403e64a80c403220000f650400790740d441000b0307004686580d600c602c065082c0d082c262020300e4940d1080f4081d040a209122181501003407040b4030014101814981007a17807075000c454034010b42044034000e4220f00ca081551071f41c080004242c07003020202c50408001304929443d00200341c030200c107200c0702a1055500d6060100c04200b050004020108085041c1a03980312041d8107103050851005140c003c15004100d2000402d03284000c1d21126178202400507070341c0e19601a02940c90300302820306040e5500703100144051075084800142c40e491006020111604652041034885202d405004810464080810540840500d021000d04603d007440b07032419032290b100e02d14540102da0494002d2a280c4401601ca050290b410401000d68 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 300835674 1250 300834424 300834433
    0x15050a0c180506030103080f070c06020307060b010e0f0918010e070f050312040603020310080d0e040b040b030307060506030304030b1005030d080c0702040b011e2003030714090324041103 82
    0xa000002e07030a13100600c005002d4020208864015114160840301c0096024070010075982d9070b07290182d2a500403205c152005490314490403940d501504103084022002044100c40d030f0004401c0000d18000504001d20340082507030002c075214000d12826940303540b00302c02041c40603c1c008841c1c5404282d500507500a4002c0c42a51980104690a4506540a509000d6201d90b01d002090002026550001c0b00710300c22203220740582030700400403040403401036600b4851001404c081c002903520890800d60154000c018050200e0829809240c111000900b90780c903080c0e403074844000e90b000075110a05142000c00042261f07150400c2503000d1070b880ca041240441c64800c140036018040e007030029000340d8030fa0541c44071350b038402d4503011400c114641044642c3d0f1070499005000345d90f80008080d0003c035030130350368104000000c19284905402d560743d001029400b000c54140d50402507495070584601c0e404ca110ba1703a0240102c00c014282c0c0d21164080b0312c0e060509030032001001900a000340c20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 300836924 1250 300835674 300835679
    0x9020412052506030513081c05151014120705030a05151008130501020c0a02150c0601290414040b1002030d0207030207050406030f050708060118050415050a0c18 71
    0x280706180794121001130800140e56650219000c1c0c07076000f81040108100400a10400340d490340d0200045058010401001113684134507400c21020340d180354441e4020b80f4441000c04481c8145920301c00d103044c4aa40c20305100100d002116043d0054034240b004c184007008006180c2c000d4450143d021603242d041721400e145d140b0100708111039104d40c4004010380b0303600142002c210300b6086600254000000c65951141e55406616004a410100d00c10319604a00900e0b18215806607a1410b5525002c1c06050b4038082d00c030b098202c548111301d020490340308800484e00c0b50402c090002032440c500c01491558201c820070003160507403030782d952040c0301c5090f0601c2e90aa00109480300c038001402d0060740c030445400c00b07a01d084019805507074414145903000c01041441207103242480d2050301202c0d00d89480320105a1200c2e000d006031144002c900c5410030a03801e00f038121399003243c02540600500e00185500c85d05881e011940028440c1c1c41c1e00f41d0f0103103d039104109500918101d03012066150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 300838174 1250 300836924 300836983
    0xf120c020a090b01110f01271203091502030f060406050415060e01020a051f05070f1d01110118020f0307050607022b03030509070b07120f090902041205 67
    0x310b4000c1115040c3d485200f405264080e141224500101c0012944454141e002d00340c00b801031000880380703181341c03240d108440404a206c4096441d902030381040200041d54401c400a00800205448000d4003481048141e202440198000d4213014078404061600c1c1d030178481aa24146d108a0041e0b1a0490961a505400340b01c802555018640a108002901c004074030706003221038094090302038404184500e664000460308840754881040c4090354900c41d050b50f000072003403043c00100b10603880350041e440c444202d2070b45210050606d002040c1d5000c08403405c4074206c45000a1050b151004030003580303094001c40c0000c0e1011030041010038242b001042141c010b5500090007041440f8180d04011261624500900d900c48450254240da41c20000e0140500b276502140d940106000801c000e1284c0b0104c403416900002401c40c00d40c2c82c514115a80350509900b0340410003841004074000000d80006e0008000d1502060040e031540d003001030400a101424940a030400647e02c00c011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 300839424 1250 300838174 300838189
    0x3140c0a05240c0f0c150405030703080a020a0b0702060403021501050a090b0f03030a08070315141201110c0106090e01022505030f131508091c05160f120c02 69
    0xd0102e8507075400d54090303040720501503001d140141c04040c0101d18280c03d0b00340000500304500713007085800d40302c0e60300f10010404403071003140501c6070035411020301840843c2c801d800402801c64284122142260b031a210200444003d0340c2040040c0c0050b8240030a16504001442e205200651000f90f25450305000581d070034083d1242c2d40c03c09845e070f40b0502065442c0604498000006410303a5034030703089988010080f070012a0360380b0110f403418035400c50b410b00c24280c036010f440286d003505d0450300440042103801800300c116051a50349a41c03003007501100c403034041c0032a40803100011a80d10300301061350090f694101f0f00340206070b106003c10060700d0080e03003a02544000b0313881c508811030000c0c00c1150951040140c00c41030070344000f60740e180c070a0311000608101c2d065911040c40c002000801200e00d90020344001c3e1079644030b09504044110994400c00084c0b0381801d000e8500f602ca1001003c5824804905407011241c2000b514180807000080100420482c6000101c002e100d90008101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 300840674 1250 300839424 300839449
    0xf0a0324060509150f030f0717060108010b0d0f090b09100506030c01140408071404050c0a08061020030a020106050303070f0f15090606050a0602010212061504030b0103140c0a05 78
    0x3d4044e1902120102d0f9807804860084000341c500583c1d03441d25200c0d90a030300c502500d10500141201e0146c401807451102242d005440c140c0d00c003282c81c0d02c2e18003400c9450b00a1448030061584d5a40c1c00d000d2629648035160f20743e80300b00c50700505442c141844e1400c005504248651182c2854100011a90003203454414001d013400e01d140c036000c0905101055000c3c5030030103d100d1250440100d084d402c059031600d25910201c50501840d669031001c00c0c80390180b0744950b00400c0c01c030800f0aaa41c604500c05c00002d07201440c11602c0301e4503601080540c8240e0300728180302608009003403d1070990a00030f00f000743c20168000c624082e038075580d5a2018044040c081d14807881480d595040101115414a105010090901204d155420048014441c2b84a986d11640010100107900c9006000359600d180045640c1c0b0007964641090204160490382c1c10005104108070204c0050a100705082c06140944000c0d442c2c0300302e01291502c0c1520601c010351244145190400032941c07070504d02d840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 300841924 1250 300840674 300840679
    0xd0c0506040b07050c0d0302030615040b070609020f031e1c020d121803180807060e1c060903021e03073212180f0306010308030c0f0a0324060509 64
    0x41c1c1d542e0f0f440469003401040c0e800c90090003801c804a020b2a8950051802244101d826a0a0101190031144548124401d4140001c1c00740300050228030941d01c04c0c15a94006400107581c019000f00181c00c0405203400d058402c05480d2191444190802ca88141880081c41c8609050b14803680a036407603001c040c0c0e2800b00003c1c0050403000510035040908188104121207040b00000d2a029010708168034101d050616408400600c0100000d2039008507041505d6072002001c02d80140100c0c000000041c6416101d002c808000080f20741c4034030100300d4000d47c054544103143d402640c40c07141d03040d220001694000d001a5020413604c14150100c0ca4403c443c6c00c4501d40e085074040404180400c15414600034410407406281d541001803000444031007414060001e14010003074541ca000c00c050f609584142d005000160900e8015078010703c1c0894403c0c104210b201601d0407a6004e96103020000307840b210001c42d21010029105130a40080c18842c0c40700b401c1000040250040300d08a52 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 300843174 1250 300841924 300841943
    0x705040e090a0c0e0916140d0201090b04090b0901141c1119150513031403070807060204211505070c051c0e0a080312060f0d0b090d0c050604 62
    0xc40754642000041d00c150b0380040e2040040f82d1312030610a03290011103209280c2d00441102d0040c3c100480680c1042c1c0341e9110b0700d440b404480c61300384060901700d014200d06018441d1408180d032035070800031b0802070a110034003240041403c0c0c1400764094040c2d02103000e01c80700c0e00e0740868503502c040d542c0c400107040c80c0361a02d01001c10f007040c0c01a00d0a1100260700889d0780074400e0741001c003040146050710440c003039410f400038564030304480c0e074800c40401e15840520a007003070000510050580b9031403000c0d8021a400c010306916400460341c0310402c12188d0342d41c001000c1005203901441d801c0c0c510805d4034000081c2036181c940411101d030034a0391545003a580c100184050b17000c1c2c01003000064200b001c07520070340311300c10340100520300d05104140403981412072280e040c6000c00103031041da03100b100514100762a45480848040b80548029408040d02080f020316032244103032a06154081ca45da82040d04003c18a1414010742c0d4106004000082c41f4441c041000081c7c0560025841907480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 300844424 1250 300843174 300843181
    0x11e1b05092d032a19180b0a1401020705061e0c030c0706030902090a092909010b0d1a06040b0d052104050f130906051806060603040b060d0f051002041703030705040e 73
    0x12005c61030b42c0003841c0000358064525801c1c01c0f0341e40026114a02668460710031502c44030030101491141c840c079401070780124428001030800c030001e01028032000800c030f044007240b00380380040c54102d254001203d92004c5070078040c2060400490004080c0d134202000152100c0c0c020030420700b002030507860360320740b43d10249081040c03580902114440800d4060720070900c480d4020f070f030301c0e0083d500109190f003081003084480c030300740b011624269030004241c0003680c0380169a407000000140030b00e922a6642020004603100d280042e00300d41d104d140070b0008000002d455413106554800c080d401c4010902c8240322070744642c1d030054030646040303a0540c0590700035242c0902900341c0d0321006106504081c148640c407440c081407031103407a000d8416164195244d40a114050000702c1d0054112081070012507080d045ca0038501d0352090103821040944d001035140c10b803030000f02c000a01500399000504200c51036100f1021440201510050340c914200008014168021401501802900720010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 300845674 1250 300844424 300844459
    0xb0a140f070f02030f0303070e0405011505070b0a060f120b0702070b18030c0a0b09010f0513090e0a06051f050d02060403080306010504030c0602011e1b05092d032a 72
    0xf400030a17510502241c0e0b03280340808006186291a081c6a801507090130300218016015030940d4400b600e16540e514100861030f04d41c0242028050700d000d150550740c080100d240c2800b041002c024001c1c0e003c0d803181c05500c0307192013030340745000070100700842d08401424009804007400b04c85101d899a800c0360301000020000038105840001e0180d4040070108000403410720031300207014824000d80b80c0c220a40301006082e80d01d0b224100f03060703000000d00881070082130101c1d8800f9400f0301000b0102c6020940e941d884038211803054690340359030642a010500400707109400d40c0003600c802c2d1244403102d00c0c01c2d408602c0c507025138000204400c0c00480040c1203640300d4411358009541018182c4c80c1c0f10354900019000f007000d24801040036481122040b003480c2d030f074021203414107241c00805e440d8480c030000c1110240c100302a80d55101c0d40c061014a4446034081b140210340700168208021700440c001014074111000e8200c4811040d0312210301506250580681711103803003903800c0c0040d0041c0028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 300846924 1250 300845674 300845683
    0xf040e0c1905030313080f340306050702160b16080901051c0b1e0d120302190926030d09060b041820060403020d05030c070b0a140f070f0203 62
    0x34540500c404100302d900d01520f0600042152290015680c08044001c1055140c0c82d0b4010205001c41040105003036896501c0034684c0e480095090180648c1c3d1a0343d109001c0c0ca000351a5031f00140c0c4000380c9001c40b1451194000700030000c0c00c140514014a50061440442a00c040074001c400082140e20003a409201107178402c0c2000c0501c10180c402184211006000221300c0c11300444446054600641ca901091509c01c100200000001410b9588a44a000010807009d04040d0207002e240c01c4404007101c4000528116100c120f00f003030600e0302c1110b505000c00c110010105542044074090300c0e001c800c46041c501802030100d1101030344c0c1490809005141702841d0811b24110000c1c900b440055580c81405114201426404140ea00074041820005080e1a800f0008210400051804031840e03407501348143c040d6820042c06025031410010789900140d43d0002c00100c000c2c41a81c0301c0016604034441069803410001d10000e501068050500007d00c0c502c1c40c180c024080d99000c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 300848174 1250 300846924 300846929
    0x20f0307080703050601030506100b0405090406090b0109020a080a09020a060f0c0f1a130309060507020a0e0408070210081003170d0501090f0e061b0714070608060f040e0c19 76
    0x854802d542d0b03910300035644280900c03051354103028000129aa00c044800500b04892051580c2803e25041600b0404c0809016108560950380c83d0000000030724000301540c0203241281e0011f03200c007080c0c500580010401404041c045103051100c000690380c990740241900d0440c80c0243e00b0b40f8507043d06488040c03012034081c100c0604000f00c030307041040209071a0b540744200410050b19844409000b580340f0504200100414400c080510110b0b00c91000f40c40594001004040c0159542ca408404904161010f8910305800075140083d401c0c620340c5181d0004041c41e048403513192440354448403041c40d000040c4014070070071801007039111240c00d884000080b03020810581d6941c001d03d200030107810800c410360380d08201004019840204038a40b088418010317501d01c450060b141070320154000c00c0c04443c0d2900c010b02c0303170001180800180703000d4540c544494006040c4032040140200040c20020710640c20091a052880e00119140403500c0082d5100024444415540640640280c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 300849424 1250 300848174 300848189
    0x308030405210a021b0a03150e0c22020f0702090a05090f01020406120903110601060207090b0a180b031c020a060609020f030408070201120f14010602030313020f0307 73
    0x1000380000d025000c80c100e0844050101504091101440554a0390040c1400c2c42c0140c1c004120106500509400781400c0050060401e601a5100c0e9a00c03505c408640700484d0080d560741400c9400950100300b100c00901040700c504c0e032901c48140744030041c003000c01802d0000e140c000c5507440640b9006001d13142815402000c50041d07280108a500042004503a04030031032140c544ea9078800c25040c4215030071340b1115580c1204800c2a114084040d0142001c22404c001d0183e20b80700c000c55050150b2400f0701003503406032134681c6c03402d1035001c260342540410921071440d441040007205440c0d481000d03940203042c004517120594000007400c15481c02c6d10010b004c45104250759000d580412401c4d000c0d403181c030b000c1200c3c40c0c13100c0100e002c90040007819000500b0400100d004920070201a100031803051600c0f1042520442001e000d541461142500464546042a0405038031003c1c203800361081748019411850041a10000c021040e20f0183c015045c3c000625400c0d00d080c0032a03400741041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 300850674 1250 300849424 300849427
    0x3030a18050d1a0601031505150d02040303021b01020c1f090e010f030506130209280213210206030a020c010e19030f090b09210a0606060306210b07090308 68
    0x550421140280043e84030703054141002d000145950b02900c9034841c40050142c2d01c03000f942c2010284420b03064008170344406d82006200c2c840e086101400208044d522960141400016015107841c0c0035102c000c1103410764109942035003054030b900c001044401d0a08259518810441c20181c9400700d9580160000c800c80c0d1002281000d07003000620101ca110f4002c8075116a10903e1040081040e404002d60203544080030403030302d00c82c1d1080005104d5190b4012480300c548544004100d9000c010885040c5c2000c000401c40700380c010000785902403106d00f6040c1da242a5a0019009220050041240da54081b44030900b00500350702c2541c0c4240310400700c41c083c805440c10000c100d0b806040c1200021403500d0881c83c107a12071a02101101c041201450401c201e100410143d13103c58400f00a0011511507800c40000d030810910352031502501300062614104580101030302c4d440e401107518a84c2d18410740410301e0301107104031102c9400c180c511449442d1f505040341c0d890740380c0d8000707040c07046c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 300851924 1250 300850674 300850699
    0x71205031603020325050c013b070515070c1806051e1c060c090e07020f100c0903050601090209180402060306090405010e10021201120203030a1805 65
    0x4001004601600441c0409650a000803030700714164031040312940760b240c0512003000381e640101e40c2265890440c0742403c50829450904460031203021544125900107400581c0300d0120503507080703075111840702c5007134003a05081c210348a0f656215403044601800e80c0000100c0ca02e80f0000554154035440480512507503a07903100ca0b221070600c8402201c01900d07080000949207800c0c45a2030701d881c21a000d250b6040c580270708009418885880c0701ca00110b402030102c000515600c610f8080f01550b481c2c0301e40300790505003012000e0b0801056281907601450005034417030400201d41d4485140c040780030803c0f0511550881d40d040c01c1d0ba100904030310070840081480b52103030f0083e102501059400403a0b40d8004006860340240648000e5009082000412205d051004900b5401801240041121888420f00c286800400131000450315070104e0010518600b00040324018080720b070405492030110780010341c9034818000d201040c464420303000003407445a29102001003800801941b00c50a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 300853174 1250 300851924 300851927
    0x409020a020f010c020c0a09050c0d051305010b06090a120230010e0105040201090303180b0a0f1106040203031c0609020301030c0302120a031b0807060e01090b1006080a0b060712 78
    0x541002410046500b050240004c05200180c5010b0301d2000030030030b02c225032501c10014002d1002811805024500b0084498402c50724011280600c000790000ea40480d003034107041d0301b1503040d01310003441146c0c20000c007003480c2c0e41d900c44203003035030742590700002c944500744002042e0b40030943c4058107021660300d040700b4102c8030310514190407070381d04024814540d00b81220303800c03517000b218004c4c0840d00610080c40424803030b18086440d210510a812002c0d51502c00068054104a1740080000ca42c01110550346900291030891018000b00070000703418560b002940700c4c0a2403c09040e00c550244100400c0b07441d54100d00001e10050a045580707503181d04060358440c00500050707002e00380c0981c1c10444110001a2034241795095aa10860003040c42007030340c0d0000d80a00b06480c0d6a0040c4115004520144104981d200c1328400004400e56140340401c1540340080c0504119000d900d402c10040b500842c01682c450805400003c41d05000d6001810034060404040c0c48190524900103035503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 300854424 1250 300853174 300853183
    0x6050c1501030605060306072606031f050a0b04110702040209271033020c09130218011802030a09050f0105071220161406010306050f0702030712050409020a02 70
    0x170001901511419034990748161805407110764100711031420904070000c114000060305402c01001000e0b41c1c0b00c1200409500c0661000d4103011042070354860a100c100c00d00d505c91422101c0c8240c3d41404003072001d9841e00102d008411300070b4040c607000a011440c2e907803004d010340c40d00c40d00c4150071071070001216241840c4190460f078500340c0480c0b245010490303810402500c0802000440c1200c03440301441141c2034010221244c0c0c030258402d8205c400055aaa08600c030310404e0311030741d0311001144c00d0040140185070328200d80070f42d800c0741c80140004060700c007803084040c55144025969490300c0e01880c1c0117009020001d0018040c6d4000082110b0040d0032403400340c0b42c00e50300c0b40b841071603c400500841d20703031030b0344a180c001c0c43c0d85c9a141d2020704240604454a040191511446120b49802440c40c070321007111003141d08030f040103008102c00d03032060940154000c45004914606070780081d42d04c2c4500348015040c90810641018511310170411030f406080010070644d202e040c9201c01950700c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 300855674 1250 300854424 300854431
    0xa050c07050d030b031006051e04060801060803090a0e0106090e061306090207150c0c060911090903070510140c030a0e03180a14010225050a0b0301031505010305030406050c1501030605 81
    0x6d00071022a402c0500d5640249000d591000308200340717070002d000020142e0040046aaa000354030f881c000070700e104081c0725800c004e0964001859035031074000c0c100041108180c0140e007070446034800520129034030980e0241035900441180c0c03c079440e2000020901c83c07500d0184c3d0151402c20b1310102d05c0c041c1c0b980141242600c5030018400350040113000b8420380f0040303502070000420440794140840c14580100c01400d01400710f030b503000b0303120b0b401040000c0380448182c03c0661002403000d04000302000500302d6060000ca04103c090103a5580c00c0c2d02e110043c0501e0b400400110104604848680c440a0040240c2003103e0b0740c3c8403110a840780e000303002c1400910440c1500c0c80010010040750044032410016405000342d04100303040d144201d0056503807810301420982010941c2c0d2501c841c10f01c080c1007000c422984940c55032410720035066000e4203070454541450700400c0080c2c000401e076000e840c000e00309552034410724110503140c0000c01056035039082c1c03d440000148010703035004070301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 300856924 1250 300855674 300855679
    0x40306050a0606020d1409031203011a120106030e01020c070f08070603200a0903050a0b0a050117070e0603030d1b0201050c070804061805130c260a050c07050d030b 72
    0x880e41e1405a030303108803501480b030040581c11202c900080248260f1100e004500240780c040c2c02e00780b85d10041380c50302151408041580100000521451061010003000642d2944900340b0303215021811349078168041c41410b0905885040d81400144290107959100030240c0441b000c0390355070502c4030142c00c100d01c03a00ac1a80101c07070010510500c207004803000a568494001503004603029000d01c030380e01612038074081000100002c40041c0c0188002d000590140850907128185100200c0490b1010380c040c0340d0014129a0600d00140301269101c12a480303403c051080b0303614000400d0461141d40480d2805503e8800c0e40800c04024400d03003052a11641d00812003076490520005c218810303040003414004052004021281c81150710f240020b101d03d10030101e0f1542e80d40442c80071300c0d14103c00000141c48101060200303503c00c9180d000c07811002c442103000c2c48500413481d01100d02601c145d10007134582e0002440c40d41281d04840325258807000311880b00101c000000c000780352200042d407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 300858174 1250 300856924 300856931
    0x1020307120c140301050d020a030206071514070f2109030309050c0907050412020a0e0403020c0415050a1701110f0304050628020306040b12010b09060a0e0c160203070902040306 78
    0x8085a110b0090320490f00350fa403030501c0c60b42e42814100300443d00b40700001c0b688610342e5040800141c441102070b0805501c65a940c04010440c14081802c2d2110f002d07001141d1000082049031840e03002d04043d0a800441c1000700d2000c5400c44160300302d403000381080c000765007425080000c00d0b82c50341c0300d1102907000342c00382c1d9121a09202040707240c0c0c034192000c4002031400e01003402407030b02503170510001f20710003001500202c0d560300e030520001604aa0544c0942c00c141c400c80302604140c001c0b040040c954622503101c00e13040c0300c0080c0c00e8030018040d40c0400b0b032540ae50340c002c0355400d60086401080c3c0da216161114018100d6450741e81c02182d04a0710740c007441010541c01e2200c00003031180e0140c031624030804d1302c095809401c000e420043c032880d401038449400402688a18001d104d109800300c00205440c007503142031003208003018281c80e018400c011400c0011101a0b000541c0043d0124080c0340d0340d05840c03002001d6040c152030082e602d40503e4030001380149943e0300400450b48a640c050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 300859424 1250 300858174 300858191
    0x50d1b0f090b04060c030f1101330312030c030e03070c06020706180302040b031e0705010221120621030901030605031b091009020d06031a040507031704080102030712 73
    0xc2c001c40c01248110800302d1011080840001e01038204080c00c00001d19094500c1c940001c2100c1c00e50700f074440c4407503d40c055a5650244180c420281107490300a00c000790406c0342c6190b60b000c013000030b4207855404041d034442244000c1c1c1d101c2d801c81c008140700602120b85400c540d040c5a0711000350b92080f40090f100740e0b1030016940e0f00030044d1168185181102c110414959002c1c0005401905803590340b6000e00b03a5407040c0c0b00031600c0c3c051701c140b85100c010f200880c1803200191418001d0000040b0444208020b2500c07940340c8402c48511400141d00c4050b80e444c0c410100b002004805507881200240c001910008480003000e0004000242d8003885600c1d50348090584403140440540b2020b400c420b40c400c210f080c81e88902d5000813580204c0301c0d60556600007141243c01c1625542003e5403585010018880350052142030780c4628440a80340303081ca07940e017507691401880010200e0381e900006c510909514425a401040610020355032840d00b800002e1a4440c09000309011901e401c040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 300860674 1250 300859424 300859439
    0x80610050307060c0f03030b060a020d0813080712030209121c0503040b0411060405040609020909060406050306070c030203120106020a02090a020a0e12070305010c0507031706010e01050d1b0f09 85
    0x401084490903101c031112100d13940c0b00c001004007905010703020b042e202c00040d42241c0381c4000405d40800603a01400030501d00d00c50003000b60303501601042d9110000541c441c01318030458200e070304d170691141148080494210090b00070303000d01828168007031844803a289285401151481006081000e01044d42c01c88400c1a200c0e0b010980707000c4c00c08210b0b400024001001841e10100342c1c5001816181011f03a203000140c195803203604183c0c4160380202da000100c1c1045500300390082d604490600801c0e0400001c00d90780c2c50020300d0181003101c101c80b50028140240110340c864002e0410380000c543e1202000f940d40c01012008074004d480c48800611041151301c26145100055a031718000c2d041040c00300249050648600c102d540034405002002a5007445040d180d1030040d2112900c4241d18180a8900110269284c0c1c0194039801004810382c1d00902c04070981c2024206640ca031007001c650300b0300410001c000c214411580320780910009802103e5500b284905585900c0d0282d00c80e02c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 300861924 1250 300860674 300860683
    0x30b100608060405091501080102041409070509010507031403040606050315061e1807020f0706170402100309050a05280506010524041418091e07030503040806100503 73
    0xc00c0d00090a0001040c400e01e410780210380c1006000301101c1d05100c103100d0410710343c0800c0e0f200c2c1ca1aa0340c00101000300a4940c804580c41c24001c9610f0b03401441c00d0500a000f510640d1100d80c1005000185402054061039022a107801c0c0110714503124500362502034020010780c09103034400e1041c04000c200c039015a84034244a040040c0900c50b190052000c0c6920060700c500034541d02178101149100c0b41c0349881d007284e100301d12542c02000c1d10030307009a5550529180350804404c010210401840fa108011000307900140d050b81c5510160b002c0d0b5800301c0041171440300051581c0100140c02c810f00c000007602001d240107220444407070060b40c41010790003800e030690042c1550496801013000389008607881e42415210391707105100344002403074910f99510a4120450541c550025104203061800c540404511035400c2d80145051020065540311a100f4800250701d060514050450320123010150003154040308890b103468450002c1501e072802111a4881d0b0b22070303c1c0700021503180018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 300863174 1250 300861924 300861929
    0x801050316090c02010e060a140f040b01060e1314010603051005130207020105070f0308100e15102001050618010302010906180f08060402090a0204050a180e01050106050301030b10 79
    0x194008001d150202650180401e042c80350155507032204030022289041c000c591054003040d0000407089217402149c914020081d046041c0c5501d03040801002070011221941500c0c80d40c02c0410352145504001440441c5078503c1c5140e99083c440c5410411040b100541c0c184d82c01d540b4240410340c1c92008601514003584200c65200280d9030551805502c10b83c0241811070041c5800744ca4110307c0c3c4c03030301400441c040300200c00241500c8204200c9580780300320480a412040c0c000b074101d08201c00800f08600c0541d20192281d0041e0a440302c00074020720050711094100c25240d5021182d00030700358002c150842d9101d00411001c9650039140c4442d0b90085d043c0c950584a0120150425404440480c9100120508210301960220740c1c942c001102500509824005220f02e14003072051000c8c2d21005000b900503240144810301c001d1f0355802c05403058410740d0381c01c1c0e40503070354400054003d0510044011603d519010010072400d600c41d000f14162405817007404943d40b5641d48250306682c291 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 300864424 1250 300863174 300863203
    0x1060905060f0103150b0c0d121503030e01090e010b0d0605030102090306011203091211010e0414130609140a020111060603060c070501020702030724113f0a08010503 73
    0x2c00c1c801c2150b004c0e41c403034110b0b0080e844042ca400f0343c5400485603203502203803c420a0354451003604c404c40b907204165240d00c00c0c215400744401545580441c070304070b001b800001c1c00d00c2130700008a6201d034400c9201000500e01b400564500b0350703440b1800701e1140c1c8000e428045007400c1501c042200d0805000301d481c0490094010107244c3c1c41d000048003038000c0000120100701400f280003d1403a5083e018903c9640106140b0f880c220580300050080b120f9101e9050189061203080c960850071402e060358804c40b580d503801100110b034900034000303200c5254010920003000d000d43c005c6a100185400c0d032140300780c0741c50007a000c9180055540b180b0495403d5416804880022203c51031007001c1d090742d9200e00c00140c00c190143d03001070f0420380c1c01c0d08165503040b200d440e06180882d4282000d40c01090504082c81205106210745448056031041e107401c5c40c25101c0c008072806034110994040c4e140d140700d1030340002030f036406000c140d5009940880c0085d51450001c5443c0c5800f203482d40807081d94 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 300865674 1250 300864424 300864439
    0x5040b160207050901031b03061401062d0807020a0b0103140d082a1c0506190509040803070e0d0b090d0f080411061c020319020309120c070b04170106090506 69
    0xa6640d0010181f0419420301c0140c0140280040000d165000340c01070102103004203410b9604010000700540e10718a140e002040c0d0021029002032400e00020750a0384491500701c845556600c3c050303251440c4074400400303c410450000042c03100302072072004034050b4981584e07079500f1100d108403076a40081d91030303071a03a08201214203070f1b039880d05402d01520031a00d050541004100c03450203480d14590030301001c0c85031300c8208105036494a44040c2c4101c8a00c08a059680303420200401e0040c5001480204888000404209032a0045030307120042100200b1705119003800e40382222180c82c05492103100d83c032444072402c2416001d81c401c805c0e100d81d103a03100c00d22075030b52781c4804000c6140000035581102c000c20030400c0340780318100d1001003400d00a03005a5207090203800c405c1c08020703464007a88000e1052043c030211721000b158200c0d07510301c0f01081617100c45d58003407070314204502644100c0305200d00140000306082c40c100c8106000b071581d030080141a940f03052010135104201c8025922908 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 300866924 1250 300865674 300865679
    0x6040507050904050709050603070902120604050106090b07022707020a17071a1905070c021206070c0312020d18020f1801050d031205090a12050906120901090605040b160207050901 79
    0x40c40d0300c0755900235001011183c4450f031703c1154200701c1e80444031100e5201640010008242402c0c01050b005042508d81508050b00d01044002d240c003c05200030310440c440d481c200b0800142c0b508000c0c2803910348906400c0c074240003c019642e14040401151421440f208101030780c280304041d240201c1d0801e50b4440c0c58910314440a00600d002090440660740301c051060040c000e500c1030a1003030304540c4a20380b441205004112400c400640004203981c011410480e0241e880070504502682c1030420410490b901820030f00a40522003a02030900d01d00400d0400e446261407894406a000b6540f048640890302c050003030f40e4507007500b072070584070390400100094201800d1090b1054000d2424030b4010007030107500c03403c1e110180c07200500c9902030035003101880000112409454000e0078154a03001075840400c0c0680904280b03840304005500015106150030f40003035809a41c40b400401861070103180036411040c090f961075160400d540b1110b2a120300004000b81a03c00081000016a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 300868174 1250 300866924 300866939
    0x30b03120a2706020c121506030a060e030d0605030312071101140925081015050607030c0c050121051503030d0207031409061606060512060405070509040507 69
    0x501c110386007010008546188000c0041c040608140318100e18002d054607490031000a10302020340500a20692004401d18650440040c4003401c1c0c082d03c41c1c101520359201e500103420f04129080180c441c42c01c0c206c45411000c00800140b01021000c281004410349943c1031540d07038040d0b5407441e9900300321080841c61150190b00c1c04401c0c4403024001080800030800508a010030542d060201c03907004c1d000d1029002601c100e480301103030750403030b49124607032604071400d54400400d1401d02030310b80d82c3d0001400441e1000e6100c40541409440c1583d5440c40d464001c0541c00b00700015030ba40104200c0200d401d61007481c2c4000c1540c0035101c40f442c401500307540c4c2401004041c004c0350601443c526956076a440a1020300704d1810070010050700c1c1c414a04000e046501c00d080011a081e008016003003247c1d60704001e48603004e48489880d024003040d0700d007200060403580c000315400018043e6032000380b280000c416102c0c070301c80c0b002e8404107079944091005801c000d4500400700e070402c1f10240b0010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 300869424 1250 300868174 300868177
    0x1211090409061107080414190b0a05040320010908010c0c0b06030a0b1e1501050a0305150603100f0801020a0804241103040b0702150c2212050d030b0312 67
    0x7030080303000140c8203003515014a43c80c1c0c0864003c862808003c1020881c0403c00c6400c0c000e00801a80c0c1036a070150485120340c81d1400a000d0740312205004240054124455400c0d00d000d154064007043d94616000607070790010f403c100c0c40c1e5001402c05a4007040c5004180210181d44003180c072020104841c3c0e60740d980d00400d0040103245c0500c1418000300200b030301c1e070701146c3c010710350300d880d58282690f41c400b1241402001091210700488006c50441c0903640603084071440c502e5441c0000d003e07161041045035400d181042d1541c00b09000c8148410b89032100014011035401c81d0792034102c9541c602e0400e00341d02842a101d000306100c6400600801d0f00f0b0520f120400d9000d071200d842104010080d8000c403038403a42200c480b014040308110401c03000b000555004002c40c00108040130100e102010703640001411401c540c1c80200358601e903107100300241c034481c90700343d10404d0030b030340e16000207c020071111001507626100310200120114040e20400691100c0a0040c084514141c01c0301c242e02e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 300870674 1250 300869424 300869441
    0x1b0e0a0e1e030715140f0c0301060f0e0d2a0b0d0c020f0303100905070e09040231050703060f0f0b0a0917060601030c05130905091c090612110904 64
    0x1075000412110740020b480c0c5031400502c1e42140380c0024038503020108240c8044c0010702e810289600c440601040a400078282c904444079446c0504130501d03055805c49906400718811604010148501d00c20002c081c4480001c00b000803624031044180f43d08040104999440b5440c15110204403a602101454010390350b01c140a0040f01c0909130300004461455104684144180d85000780c2801450024020070360171007414038000524000901c00500505400740009101d41c0d05c00d480c410308107146d0000c0c0b10380c03400855400260a00c00080a8000c1d000448800c800240303000c038041030851a2034040c20640e07030f00400003901c1c4c608051024130360754462042d48045c0b0801e00d50000d10320100b04c20004d00d031786003003001d401c2e24104200090180d0b05515006401d01c041440f130300303920000d10105001100c400c1e0101080b65103441d0309840c105007600c556290840b0308910000c1c00c1d10381204100084480030340d2904c40e400c082d0b620800845041c01805503060320304008912140c50180c200703403503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 300871924 1250 300870674 300870733
    0x9160813020a0e0a0912020c03010b04111c110f0306030c040e03030c0d02130308090907030506131a041401170601060c060c0e100e01080c030907050d06091b0e0a0e 72
    0x800c10300f1a2900206d20064041110060384585201c018038103080c02842e58460701501e044c4800d0100040c0355080380611121400903081c1041c2c8014214140d4004259540d0803a1401e65108402620b41b80150303c00c0780e10034040d01c01c008c0c4501890070070748241c0b8100720b1a4000b0350f04546070011408000d0f4846140440095000e00208004019070803007a00194420170169664607800d00c280072500d200107180740180751510307040110700c0e00c41c000c4000e055900d9040c00203007040019401c18060898007405500507262001020604588109482c140c0d0f009864030003010091401c0f5030f41d81e0509003c0c1e24000f58007403124000140694004410310190780c108881c408082c1008030344d802400000e4480002d0f05c0407901591943c00066403500f10801340300d10382c550305c2e001c44501d03503481c03040c42054010190844041c050290380d41c0700f21000303130307101079007120203203082c00059036614282c0543c241c4100e03000f010501803903e80c4185104040d02001415115a65064041c000c1d55507031241e4a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 300873174 1250 300871924 300871931
    0x303010b091e0a0b04051908070b0706091b030506010b0f0f03090f0a05070f05120a030e130603050102090a05040207030801050906130e01021207110c100e09160813020a0e0a 76
    0x1002ea520706800c50040c00b52540015201c0e03203003401300a8100040d107400103005170b000005100e5204003091540590303040d40051951100c2c0d82c80c080380141440d13200500300e8801d0001d0300c0c1c1d00d60141120101140c0c0030340304a805a0b600d0700100141c2c0d00c100407851100d00401c21001d100800c80300041c4d0f501c994200140d4000001c81103400b410300303c162808540d245c02c50031040c001d100241e950f010142c00117950085024094112076980c942c410710700a0207000034800b1002c01c0765a000c2030341c00345d002c01d80c90900c50ad50b03881c0f6106001c4e411031f55429216808c44080481c05003858800c2d2940150150364000c0c2c207910305014002020b5000d01142c1d000700890011310402002070260032400c0284030001651510107c40201d00d14074080c0c410800c005201141e01001c010010b1940070100307080b03400280d00c0c220f0f82d00035034200b44054400d40e000348124041140c501c06e0072649150100454884a4090b950f00e040308403a0000604000d6002284401c11b1007001107002d4030591003c000f02001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 300874424 1250 300873174 300873229
    0x30c08040e04050a02030105100b0d1104120302010c0e1008160203090d1b0608060112020c01060f060519110703060b0301110304141005070e0105070213111b0303010b09 74
    0xa4250708400ca50a07a5550300c00341d05041142030034880c00d903218098013a40d1100034144214500c82d845030824208815031240344402c0c010b07100c001101d0003002e0301c20a031003d20841e8a0040e0284c00340400c0080032a0100c1d448039850b0802c0a001143c0c129207950390f0324541e9940c41c4a24450f0a0306e1188000c5220500202d031150b11544001f0350510b000303445400c483c0c0600f1000c2c8414070071035000325042005030307000e0107540d076040461000c14500007200540c80340032101c15140103250719442081e4240c0c0c509000104660054020410031491054000900751202810340d170540e003094210007158000241000454484d500c00b8402c0c40c80100003194180b103003070b580e4015400030b48040d40c2c20500103c0c0c0c558014402c2100061814050324180800d2410a05c050302c00840c0e80f16440c10f00100007010811540c03140141c8141040d061001c02849004581c038032401d41050f4150418101e040c002d801d0741010010550341281e40c50b05d901407034074400000303120001e40200119180c01c22112910f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 300875674 1250 300874424 300874439
    0xf0b07050f2406060a051213020a1211040e030406110a1a10080c01020303041e0507081c020a02090a09080c03030f04060b010c020f12070e09010b0a05010219030c0804 73
    0x160344102d8040c4020540c5444044688840d41c05441c0d248151401c00490300010f402809a6885503207c040700d2005981c3c1d080c1c032550640400c0c400030351150030b00e900416040306c02d0351b12440150185140001c040c01c280140412134100b8401580294400d201c01c02c8000e00c220000356841511800399030002c3e01f0355607011000b0b00d80005018106608004200c81c4061304220800200480b4009204040300040080c1d124800a0400361000040304056048640040c210022082d84001100c041596822001c0e89440d401c074103809203210648004140705100040d100700031900101115483d03290020104000d000018044418110a0140074155030003070002c0e42c400c0c0300d00850b401c0c4506c0c1038607080048070030ba58681c074140300f00d030300201c0c0150b1114541060b926000f0748a020040008860b034038a041215401402805c0c040741c2040f11021045d002aa8a280185c5410f800c498076440166116290301c102c14884440242e8001c000c09d203d100c01100050041014a00d01030f00c9061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 300876924 1250 300875674 300875683
    0x11130f1104030201020f1203010902030403091701060503010e0a020307170106210c06170703270c03050d030c080f0601051323060c100f140103031205010608010f0b07050f 75
    0x1038042800c2010404105558040c44600c01201c000c201811051343c5100200320940018000d030600c041d07000c80010708150148040308060036034011070214030888a0813040c0648080d002d294017035400c02400d56280900020f068140c50390003070103441e2880c1420101040300e5044402c8141c250340710080040c2201c8003060410551451041660b0301829074141424041c5069019404201a54408010123940d151192703802403014a00818050b410181c40e130183c0445111089405401108200c20443d1f04501e0100f2a07200b0f4058950f240c800c0301054040340c0d140c800c04000306070035a0001d40d03031842c142a55603000c401410007d0800d28082d44800d90044c0705e41020317098400341d0402d6862426207003507502c098203007115400e281c189522748550300e44908a200401040d103455051007002d003540c11070460000d080c0381803501e0b90b0352410000c103210074602001d0345130782ca40800403c000f446a11140d0503100041a031401c00d41c5802c1c40205258008501551356010b44515613203000011300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 300878174 1250 300876924 300876941
    0x40b070224070c031718040c02100f020705063d0b191e0203040b13150f0f0507020a0501050901031b120b010c1502090d060906230411130f 61
    0x140001c3d81c0f0b42c15458040301500b042c0c030360300e038440009122806000ca05022188078103c4260380c0444c901c01d40c04016464442088500c0e805035081c0b031894a40c4000e6075000d419031900400c00c84810f40c035076101500000501903203203840da081c104060254000784207801c020898000e00d50899055442c01001040e8004038074500d101c407400c089005400340d21405800031900b40e180d51810202060704042c3d944e120700d1085020400002c90b10b01040b0110301035480060407180e001c02800103850364000c162444035013001011915880c108041c041c4600d05035446e443d4040c010300e10640c2403100650b655000744280374101916100d2407201c0302c0e45100c0c100421001b076210416185a8120f1a80c151044210b004d4104040c510360b410101d18420b174140303011044a1801a51644128013241c4510728482000d08040e041c4242c0c0000c201d4582d01865120350719a9821803440d000f070143d40d8240d5820343d0b000d4416a150b4000d92424900f50582c1390001d42d240c0f40000d041c29001040005860328079 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 300879424 1250 300878174 300878183
    0x150a020406030e1c0f1808030909010605030f0103020d2a03030906020f12030406060e070203040e0f01060c0303150f0b040f0e010f03120507081204060c020102040b07022407 76
    0x12608018080e054000d0034120000d15001d010101d501ca50407040e03000002c8283d00411411000605400b80120b407030180746c000d054086480181c4400b461a03695025420090103045003200004c0e4182c0320300c0580c0d001d00c00711074100100d03918640820114000c191810340754600452052060041e01c0c40543c43c02400000e51415040c0c41c6040103080280d455010005540002090410b020780c04210615030810403100182c40361901d0a10200400280e000b80402c00200b00900840940000c00b030022280160344804ca143d440c070501071328804082c07095001040e140c20480c00003a010340c2280d60324100ca0458049204d41c1c0f080c21038001c0341c85500c12010341000043c24000d80001c4414000500500b0204c80400d5241004c10a00d108031440040c22100f1039804080342680f040c01101c54443e04100b401342c070380c404101e220b15440c106980482d4250b140100c8460f1079401030081e50111840d844506041c4240b9400f4820140708100c01c4110b802540c8015601c00e28a000190050b14002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 300880674 1250 300879424 300879427
    0x2203020c0429060a0c0609080405210c040c05091e040510171501030816060f050a1503030206060f04060f060c020a09060b07030c11030a210e0d02060903150a02 70
    0x15078108105000e140b00155000c0c060410150401a40002c0d406103020351002c40060340d2625030518207241d028a800441c2d100061340801d090840d0700c00300c0e07400c8034482c520070703507002d24150003c02c81203405255520012500611080c1107034904090746860359102c24283c00030600e00360380050210bc004460000c0c0c0200c20000910404000441c014544440760004007088d2481e40c625070840001440010001c1100103503085195004400b10100d559000c01e041c0302000c905011040504030849009000c1441d014001b1401901c4809030710171030b034060700540300c503449c0c400a0041c0030107400c145903001764440d440058049e009002020041050b5900c1044007031891041000d401d81e96400910358a081442c10701c8064504003c0320602a030504016440405074923020141859014880e0b906014114090041c80307940f40c0d4080c0c0300c09081e0059071000541405c26201d014001c0207464001040d40700384401802c1800c01071540c00c20040840d500c02c03052045640848004072481148546c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 300881924 1250 300880674 300880721
    0x20115081b090c0910020a060203250206160516200906090f0708071b0f060c031406060d020f181003050415090c1d040b0105092203020c04 61
    0x524400c8440380a044a0001542c105030035200f07000c1c000c980313015100d140d103280b4080b2402e00811035014801d0b4030507415504c0345080d11406810061146801800a489452205500b44080303030091244202110035070318400d0240d4220781a03000001407140011424515001242480d01000c100d02e91020201101444040501615020260401c1d000303954500c14811080f245411003907000c0c42d586084000c2d5600c100c402c40700070a01c01c3c044006100c1c40c2004000b4840781c4803201c40400d00a4106000b44124043c0440c22117850714010200b400694000c10f600c1d00e0320b440100f05000403a5805402c0c80a032503004c0d01c0550042d8100341840c9580190b07003640e410100800c019030b807c1400d04110b5454251109040c100303c0150b01070060b55a85269010001c1d414500302c06842c8140f143c0031030195020b4603190f0741c0d10946069804000c0d83c0300008042c40e0107600c942c030071140220380d41755016280c6800744220150002c100c00354001c1000380802c9440c1da201d540805032060412619100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 300883174 1250 300881924 300881953
    0x5091801090b06040503070303050f160506060118080c190308040e04061a010503060f0a030605010605070c08011a0d03020304080a0822052404120605060909030301121202011508 78
    0x201202070b030341d000d98404c0c0010001d03564089000e60480f90181030040d5581c0c1810b1450305144501170403600d03400c400400550910000050080c4201801c0c2c0740c118036100000c0c18140705030070030710500f0081e50248100710a9810306208081c00d50402c400f000220985964502e84070760401e401c1445203100440030081401164000c12429541101030a0a40002ca80000f4803510008111034004c0c00c0129070b841c1c0540350000381c0070007107801400820042d42c403003100900b150b0080d0340a4400c030469020200700b003401845240c10f000c00480403205c14482d85018484120107051064003035010501000801ea0310901115481d50300c507103465982c1c1c5480b64042e02250089945075200420940f10502c040d4881003204a01c959910820382c041b03503e81c500070071f018820381e0450360107800c800f24240e00708a640e410140c02040100c5660440b40c4d00c48118559a00003445150014903070700c034400000c10541c001d541000c0e4100c0c400030600156050b0005d851010300c0d80684c000346d00030b60303110b48070300d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 300884424 1250 300883174 300883181
    0xf03041403190510180501060803040911030609040605060a03060e1c021506011b170d0e2103060d021f020d0504120602032e06020c0405070804030c030509180109 71
    0xb00707805190550910304a44400e580c88102c07854824186a4070070b154004001015551900c8603403000091144641318500d803078880e0010f01c91040781505040e85003010307000c2c2d0420340348106030160619030240e44640303a01b406090041d0000f900b24a201c0390210100d001c500074218080852002072103245041019809418840d504c40b4085401450302e0301c1c0c01c44a50b80449401c01c00901c0c01c1e002c61003229003590803550700d1940003084e403400c0c1007000181c24110750103000c0b40001c3c2c500800c901c10f00070441e030361200d070390000602a034007101d900000c0034551040a15000080a01014080840e0764085042034010895902d030f1602c0003c206003503540d0410940c107880b00503140076801c0c2464104407650244445400408803500800000d030a2079060545604900100301140350b0000c4115030b00c14404200e000780e000600034480e4179a5a420503024660103111241d403403203e00d035501d840450700b421800404808110041001c90304550780d18070915802d0b021000109165450b007410300c0b049 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 300885674 1250 300884424 300884443
    0x20904060b1516030e03281703070f0c061409060a05010602010b030c21010207030504061202041212021c030e07080a260f04090603021309050705040209030f03041403 73
    0x2d000d0400a10500c01c503429604a940b0341d042c1070814206102a000a040c0390103101042c107150440c840e0340300b0424081d030524600300c0c0501e2803103800c0b80083c80d00302c0e030b40e2104885150118020364600c1008501c6622020902c0b80600c400180700105604107074040070017580c41085680c04107043c4812072a0610442d0b0041495000070001094000042a15507078403800543c4190001013600080c81c14108580d07010140c2c0324000c560f21f00a92402a040d90400c0c0990400510f103003040c1070643c00b251017210302361001c801038500102d0b15540c4401c41c0f0610408110218082c081c2468407840069091a00441103900c02280d03140b907030091a0310300b040baa4071411180d881019240086054080740c0c84041038180d0000d11030504401c1d0481d406d1151403003002481c0e500040c0005c9e14041079103c0c2054a208440c2008020703d02ca43d010140e445000014010380c201c0802040146490380c018807103801d0180507114440c20441d100c0341590041c0d48500806401d00104d01c03018074081c090b0509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 300886924 1250 300885674 300885709
    0xa02010212010e04020906030616030c03060f06020a12031a060901121103011505040308030f10081014010501020d14031003020a0305070305011416080c04030501021b060c0f070204090f020904060b 86
    0x942c1d16102e0084418103c0304ae0300c110034584c2d640149130400b8405c0d0046800790950103104002d040c0d07910002503503510310100540d0144094000620418403a002e520180701006c0c1003a03026081280c100545507006019a5042c00700b4204e0481007403405000d910f8103000c2d005c100c19160f626086888082510700400700d01000b60400081c0005024041681c1d00088400d44034060307984c0d80d10302c030500b0250603040008544a03858000d5000c130f072550003000c031200c0d201c446015a40d0741c032001aa0380b117604c251510040b8401d40502d2011002c21000b450340050103143d010800d5640350040b5607101c44640003582c040e08a900280103001090086040f014641c040051082c500f400c00c099644450b41840c034104040c440c00718815038401d0003924081c40d0040000c5580b4030500c0c0c044c441d4083c09071010741950155000040b40c10840c00261500440e89420382440c11040303600b00710040032100002c1f81d0703036004111100c01581358040b000c1d00c505e01c50748000543e502c00300200300662251900c00764 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 300888174 1250 300886924 300886933
    0x5070305010302011e02070e06030102133308070c03020313081e0619050402030c04020a020604030e011b030513080a0f03080a0204050d060f0908160201080604060e010501050a02010212010e0402090603 88
    0xd05d600d42c00a00c038070803a50b90407004040c6446200c00030340644600441009105102080440c421800180d030260042c0f4240349440c0441900360484204070113011540081000784000404450089031018010f43c444d10607240703444500c034014445c8082070381002e03015500c401c1500d9a507001c032800e20051808071130010403903407401038800c0c820b43c0c0d07400d01c40d40070361601d07240481d08544040265400e02e0f20000d00554403aa015440299100c45c00c80307043d00050103c10b0004495406004201401c024450310340c84910074035241030701c41e64010a402c000800416500080c120418454519402d200b1085c1c404864190b04004042034000f80c02108417030b20400c4104083c0d994a920074002540c400310225400d80c020822000805070818050450f05002035140d040c0395015410390441c45c400d80343c0068a071120b40602c030440c0c28038041d81e0300032841c0200602c01980035101800811207241700151511324403440e2100c0e840c0f801e900102d80343e0996070a201c1185040d94886500c1103040c4d0091 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 300889424 1250 300888174 300888227
    0x621020103200a14040803072004050c0f16021020010b1c03120f06060f050f040905060a080a0602090a090b0904230618120c0601150507060507030501030201 69
    0x2c0c0842c030030204894240124002524044032102c020303103006120343c40581303450789081e082107402c0006845c601d41030703070300c2600c044c8000b403806100306030048505052942c1000e8411003403041a921a2030f5500c00810324410740401039440803004810500f166640440e401644071032080341c040c286a00d071446904000c102011f0b500c0d041609490980340c01200140714856007819502e0848006020160302d051503900103d40203a82c202c0c008580d407580d511080744105400848041c025031049079200031040000b04120300564200603080f0000403d40040341c1d554203e03a0f8a8450000012500c4a40200340300080345880f1103044001c00c5140c00a2025a82c1640041c0d90510700420040c650800c00c48070324250b200c002c24100342002180304560290600803240d40491006a01c0e902d80f03446118454000c0c804913400791420103c43e04014444c036400c040c3d41603903c0d849810700c00100706061008101040c7d06004450090720380f5100005c0c1941180001040318031000714102d003502615205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 300890674 1250 300889424 300889481
    0x41e05030a05150a060e160e0307030309030210051902100b0111100c20010f0c0306050603010b030a0f05043002030d05060d12180e011404020705010621020103 70
    0xf950f01025018428841568071414180000d1513150030050b2080520300810900060340f030300c403083d44030840d00c0f0300c2250441d6400f015a030f0002400001c0009005150810050604006c4038074200a10f040c540d060114815524000004500c41c0e003005034402028420121034900c030310a4180420b01e8122a45000e40d021295240700f04803052402d1943c1d004011117485c45091302c14070f03140c0008205a1240c0c03445620030b029110545c1040311040c5401c4403c0c134554042e1003000c007201c0001d010b440c1140e29085902c034441e00020810f500044c2c40c0c280ba003071600113610485210324407803040e002226401c1c00110005000040034150903d4010340000ca00742c0d000419140c07240011200460140d80b140045400c0741941342005043c0c83c1400e405840d50740e082000d80b013108801403180b61032580e54040184c1a44002c1c46403000c10f00440d0030614003801e0075002000030900400010680e59507070720100c088030204002d40d2429080c01c5111804541c0d150042000030200b10070044410700c0c1a410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 300891924 1250 300890674 300890683
    0x190b160e01050910020a0c09020c1005131514040b071b02030c040b031501030302070806220605040f0f0302100b01051908091e010b01030c110604060b0402040b041e05030a05 76
    0x50f288552402c2d101c80d4021842000148800303903002c403800b0800b9a031100000301035007100270003041c41d019061288011005500c00c01e8803d007014441800010880d0322404a11071002131428002929004140040f80440d840c21f809039119034a01d42d13881c80d00e254003c291140554501c5000c116503501d420140c0e4000400c1400c0c40d0f001c4800203100c44020001900e40b89651201c003644100da800004180764010420a04440212080d40e60301c0d0341d141003088003410900c400200401e100a2604041245c03a845242d11030703c41c015510341c20f002d5031104191101d1041c01140141d1040c0c402c01070041e070300d0091400561007820444e0a144030104100990503541c03803044100031840c00003c04100d000c000f441d441d610f140c1d16003500c3d1021203008a0107003206180c1c0501083c101701084070b0ba24401d0307100340b58141c0700c08042e101c0380d05e070343d6940000380613250b0a19034016002c0c8400b00300c0004d00c900520003859001800c1000c514030300c55400054210341c1c4503601c02e41040c0c1b94030010070000709 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 300893174 1250 300891924 300891937
    0x1b0c030f0c0830090114130504110a080610020d03021c180606170a0807020d0b0f01031e0818011413090e030306030a060b0103090f03050705151603020c190b160e0105 73
    0x5880ba40382d020882081c440721147d40d105691050508812418100d40c2d0b0000344060314107680c0780035031660f582d010300006407909045080140d004000070442d8038400c1d8040d010001c80051039501a1000c0b042d58070582e016200c094449082031840801000701a208000c000d0214042214a01c006000c03c2e54580d80c1c031070307805402c0740800155042150b66003041c49800c19400030940c821760401280031184000c09000c2240d02c089503855602801804142e2481aa50300030703038040c505a040415003030407140d1001584d05000e89103440046044021000d0640c2c1641c0b004440d880602d404000000d46410100301c1c11150010820b001c529107002c50007550190b000b490124142914500480003070010703480151100c1100064041016400002002518003070f000b00c51008800c1c074495000640140c481c400b0030350390307007543c40e2007036000350080d01207034542c8400d0795030603078031030240742c14580005104507400940d000400c104010225026012440f0a00e00001a459940000f0709140b18a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 300894424 1250 300893174 300893207
    0x1b05070507090504080d0b011b060b030708010e010c121a10090e010303050c0105060109060915091a0306030f07060f0503090c1e011b0c030f0c08300901 67
    0x18461040c090104000c2000b02071400c8200000d20b010b041c44038a40d0000d2415060540c10114481642c0d03102e540c8100c54040c07001c40560920441d581c403c00184101080642c250280e007100080e400002c0c42903c940320a1500007080700c030703495080105403417625045001074601e0000c4440340e007800b080e20b40150f5031050701e5101045d01c0c5084140c80b40c8082d80c0c072400c800495000080105a40f0101402070410010b009000035282c4500540751101580240e00016244031f01c204000380c1100c0e82c07580844580d04110300d031315440380001890007140442400511030008140082070604001184488944102808845080160040c4030041180d48401001030100104a00d00d05c240858004004010300300c154003a20210080141c01900c1910340c0800d000e200c40764514483c2d2480c0058141e03028900416440c1941d17109c000c00700703006c6c0d010343d0340c0e05c0d4084011500381340411400342000900200e0b80c0800c80c000380401c414151400c0030a80581042c0111078103640c000c0402070f0200d010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 300895674 1250 300894424 300894427
    0x11030c03010b1e13030c05010305090d140f07060b0a06050703050a0f20010504021504081f09020d0b100902090d152003040507060201090807120e0904051b041b05 71
    0x32100c41c8940f8026251200401000001ca80200318a8000c41600720b921803800c001d6041d60f80c0e401035007180d004684800c5a034020300d02008006200b4031900400211440c076403801d011402c07440c4040f5420411045881c20707910306c0041e800d45080007502c07000703203041e182c9140303400220f0307600070000e02413020128140074201d002441030324004ca44004003030044d4140811a5040218184c0c06040165400d034000c420030110615960540d004a8090350f004070010070a0080d603085107072541c0802941107444d607907201000f00060381c1326a20201142e01503080d140d01c0c1d0915a0108205840b61750000042ca40304000c00c4580e9211006840d010680010035010382004500e601005060b00d441c0e091600c0000ba0300260b901c04800000d10700442c0900116418992610002d80c01c83c0c900070030150010600380401c00009460884541c403030001071078000d0315000800013145100100361011512600602181c0d0755034812120b014440350000c440a0000c13592440c03001c500301c04840701103000c1000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 300896924 1250 300895674 300895687
    0xa080619051317030a0e1c05030c070203030a02071703070b071110050a1509020a0e190f061115151003021b0d020f0a02130504060f05040302030c0111030c03010b 71
    0x1032611002d454180c0100e000b1030440c49038481c04071581d0084800d003600078038281c40d0801110001861065240004509402000c0e4013102680c50784c00050551200100030801100142c42c01d1010f0100180b298008007026400d00380f01c0d240c040e1000c10000300550080c428134000c82c00e000030329500820b50741019510039000440300c03420b01c1e02142c000f250b054101014042110384079800142c2d940c0b04141d00c013080b00d40300c00040c010f07032248400c2c54000071030694064202c1d140c0003600c040c3d030b031904480143c2d40700d80d02d400700c00b02841160b1000020800c0c4040044000c0d10034420f02007440c0d5580c10314000c0740791030303841100d50011012000b405007021100c60b00400c1c2c0a81c2c100d03201c601c081c0700000c3c4003c3d0f12181c4540d0f101424002c3c003005000f0258088407100000841c81c1c03807254000c03c0e191620229102240040400901c10341c0e4554558140c003006140d18492140218040d80c091a070fa0190185e0041c02e49680c81000081c20f0810000c0150980c6c0b10000c0d81d042d241518582652243c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 300898174 1250 300896924 300896941
    0x12030218040c0801080c0108010e01060e030304030b240d0c0608071206151808060103080901030b040c0909051003020303070206091f180b030601020a020904030201060b07060b0a08061905 82
    0x3968000c001d81061601e071034035031560b41003003d69048900440c00c681207003001d10011500d2840a2185e000b40740a0b600c018440c880c02007801094089014040b81e0610340e40792200c0741d030307084181c406103010801c108550041605201c58880c81e1482500c2c0b140c01c40d159582e440b1003a0505104403420801d480700030540c024864803240040001d401c105104c15500d401071014422029060080422418411214101c02c180028821903111101400080e8030b142c40d1030f0040e5009181003410545e6800326040c00303682c2d51060304c0c0d43e005a9a00c0351441802c14101c0000c40708007030702d40b03814000880d0b0104016600041100c280c40e40c16070b101903e0f80741d22030100d21103010b18501c07243e808010001d0804942c1d0700202080d880304a003c003001e01142d80d84e60311041c9200945000d070068010051103001340c00d00c60302064101e0721a200000303040342e41364800c840c46e4010310000c4071080e8887e01b05500918088481c08007038800701c000781400b800c085140390703111a03110900003081c5486400080c02007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 300899280 1106 300898174 300898207
    0x603061406040c2102130905070e010305090703080c0114010b0a0206102103020708070f030b0f061c05010f0203130302150106080c090d06020a0507150207120302 71
    0x49188000845615940d121308104980070088a060300900e10120300080c84d004d500010700341003506004008200001c3c0e03190425081c00240408880003090107821250b02581e4103544a01c100c0d801d9016001000d151b00030711000703000018a201110004088605070344c0d00707440c245d0303448a030710311100350050042100f11100c40c0305c10b4901c0e42c1d03007500c00800d0030f0090041310350855441803c1ca241101c6030b0840d41c030203510010100b0030800030f0b01c0b0a94000c1c072140c40c42e000c14600340012079500c810303105c00c0c8859140e01c0b00c10752060000a5105120803980d14009559030300d003802c0040400c1c00040422801131264820a21301c400344616030505848460780d8512164440319880901c60b0001d40d00160310002c481121400100207100400e80700d1116216961179640328180802414041403084c0182d03801080701c64001100c014003100d102205040040c0c540081100301901c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 300719424 300899280 := by
  have h0 := BRFrame.cov_init 300719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 300719424 ≤ n) (h2 : n < 300899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
