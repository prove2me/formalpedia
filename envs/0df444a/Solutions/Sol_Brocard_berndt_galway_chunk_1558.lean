-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:34:16.18248+00:00
-- url     : https://prove2.me/submissions/0373be1a-a188-42b8-b450-90f16ae9ea74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 280035971 ≤ n < 280215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 280037221 1250 280035971 280035979
    0x6090501030c0903061b080105060304020105071e0c0e0a0f060f0b070813060305040308090c09010303082508240d0204180602030114040f0c02150711251a030402 71
    0x6203100002e0320520b2501c0c0150b4020400340458851401540d0144900c6100307900081c080302e001041d981481801c0307038011503042c1c1d9558135050f2030303442d01e60340c0c048884200d21004400130010381c040359008044402400003403801001034209a00c0480880c0c00000c140d2081d039080401c01c00034210320300c00b014112541c003045150785441d00c1c84c00840d07900c031b12844003c003c00c1c250350200e1610360640c00f0368841d5220380c842c501d42c2e80b41d0000080d0780d0303c220688640e20429140042c000684150640e03900300400f40860000340700c0400d110031604404220080c001003801d400c001114082c0007000300a801480f4246602e07403960001320700c111615110181c0100c0c0c07030300c5800d411120144e050406076600098215100e585a024008a0800000641e0712807806c041a480071307280580f00d40c039120801070300100045400c51082c403004620091904046c010074441e00052141d0500c106200b03021480b65443d8984920300c10000c1d04140c0341c01c070399141c2a5100034594603038420340840ba00560111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 280038471 1250 280037221 280037231
    0x61e070909050c070c0e0103110105190e120307030324081002070201020304050d050304030219120605101d010905010e09060c0706110703050324032a0d150b0306010609050103 77
    0x140769020303c0c1c410300900031328500b0380300d4001540d0f0b0f0f990b00507181aa88101c000c050f603450390b0f800440d11401803072680b01c003181c04d00800301402400391444622000c0c000e4041d4403613481d00317450b050440d0441c0074140c0120362102c88000384030003640c0d54075101e0700306031500001746401c010031503544080610026003019400120300c030071741e07000300140d40003001d000700070841e170b07100a2400a4807230700700744030480c002c403444100d40d0603400072385260405644207188034440001c502c1d211040600000f801071103030598078074400f061a4101c6d440b0385845510700d881125055242c00090741c21644142e0041010a080806000c078071078000c40c82d0743c3c005021124140d21545c40e82043c0300140000d01400d208441e0016403a810143c1002c007941c854604060440c10390b452000300b04c42c3c800c21491002ea07054010740804c1106a94031658919240f451211801b4001e0034600411102a280c1d0380c1514140d0714401640f03045d4000d40510000c69105178060001c55161000c0684800340c1402028145901c403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 280039721 1250 280038471 280038481
    0x2030d140d0b03121308060115120f09050304260a020d08130b0a030b100206060307050d170c0105092e0203040302010f0c0509041104030c0e06010207090509061e07090905 75
    0x130408801404200082d980e03842404583c1c0c140310019030301c9013400ca8020400005400101ca02843d403046400c1d48030320340c9192401e1942e0004094026481840aa80f40c45040c040382c8100041c00240c4051054006070421008045d840b0a01c6d40d40540c0c115400b054030031005859008020406c1503000030301c85c2e15961802c60300c10803072a02d60481d02890402054081d80f456045d045144850310070382c0c5c1c2106640a25108a8035010f0440b40e00f40c06500c08141007000c2d082500e00781c3c01c0207001d10102010b0586050300012658080112101c3ea69100c8092002603031041c4180c1c0c51280240d03034806082d507440c18492500c5c06030451090995a804400501454001e401c4074040d811005010072050300c448102130150b401031003010303005920305581000d440300d00904880030360b0740110071030001038541407900030040300003030401303045001d94400000d1480c2c590140f14021a402006004285403840341508500301010302d2900291148080c0202541c20602038010f40d500120013040700d40e21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 280040971 1250 280039721 280039723
    0x10306050a1d0c160c18020a020d0f050405060c030403020405131104091e12031d0304170304081501150309080901031a03120d050106020106051309170301090902030d140d0b03 77
    0x1398050285640ba90300c1048040100d007050003000d84070300680c2d40ba80c0620541c841800ca0240301e09000150340b08460030007026005d90500f1800003114604035107840c0e224070200c0d408ea0441a201e001c581d0000c81d0600c11442c041c01516440191a00b0003400d410380340e140e101c0301d030b542c5911007400341c0c0e070740d80d280000c0c80b08603d40305244c0d82e08500f22002910300e42c68100a5004010000701c0080d00d04940428400c0e04282c1080303440e20f07100001d50800d400d018600032805244031621169120802000070000f005000b0000c03001c60503040d00d00650700d401e49000390140c440303c02001701840d1443c4035000507101000d4070721020b03003031074000f4007000004100340300c0841c0350b070f401c0b91b140c85403401c06611501c42c1c90003005541300c01242400a03980c0c441c000c4e800d8801a0180c0b65220541940c0c0c20203120142d0f018180b864000c491034001c40444054010040c0c0c020703041031150980301d10f021029810200700d45600c40300c1602d80084000070059108115005071540101e910781c0300c901012031507074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 280042221 1250 280040971 280040977
    0x70210113d0e072106061d160e131401080607110c0a17070308030a09020315090706050c2104031b0303050409020c030405060c010203011707060f051c0911010306050a1d0c 75
    0x261110302000b030303e511f40c0030070102c031102541e01c9110394111200013990101145031a600d00c200070388840044e42d6001c001c01585001c004500290155500303040502c0ca166141e07024000d09400d0b001c0d00c0d803820605001030491610340089902035110b01410b1300a504c40e105818122240c4031010140c80c0d404400d214100841030740041d040303200110a000d00040b0507405085401d1084044480b20442448007041d001801c0351046210b8000080070041c0c51300400c000c0054000d45006d640c40a00a6800d0003201140a00c40096000f00030900b8410402c802c0b0710350020541081d2022191440c40e034008086120700d0241d00c6031240c011070006401c260070030684000e4030f8010a190f031034124a007211030003504248140c001c07680d00840340f50784036000840c5140643e02d40d42e8070100d188150400994183e4080d640400158900c40800c044603a010702c41d40700c0030b41c0700341103644505407080001410b4503010740046100e085a608100156204510105100c201040091040c1e40e0342120302d5090340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 280043471 1250 280042221 280042223
    0xc09010c060e01092a0503060406090c03142d070611030702040f020c010624050310050d0303090b06010906390609020411070210113d0e0721 62
    0x16091910250170410380c4da850000c0410003561129049101c40440e0b8080fa036540310fa650160486c00c049400310350300c1e400070b80e0450300840349440143c3d9641e64080590b1141b80f60301113150008074902c0b031002c1a000c02d400c2d00500362034540c10f0f19203a5080031a2104021320402c070602407014100120484107005440c1026001017007040020001205800030354030007400781c00654a01880490904100c0060400381114014418002105c6e4802901c1d580e102405c40d442d10a100340d00090955151701c0a540901e101e65000701d41c40000d881c0c1004286005059241404100c0c001801602c2e4042d000c6120781c25a8011030385000340d4050305500103052098003080b101d81c504022001c3c46801c3e04190b000c079200b9941040000e095019502040c081c07104001e5100e4209400c0348065442103280d01050840c090588030b0b2040310071803402d410441d0300c101e09502d0003070080080c01c0c880195502c4a42c1403580c9400d2101d0206011b0300c584030381560042c0c12180c45004581d10130100f801e8282103081e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 280044721 1250 280043471 280043473
    0x18010e030a0503090c0111100b060d0c200c031009060e010504080a02190b0f060a05040e1011090a060f110706050301031b0305030406120207050109060b09090102030c09010c060e 78
    0x119540c1c003000b8540d034001c407480c154511900c1869081548a041e0300d860465110740941404030003090180040c2042c40303a1154441010312914100300064815655000c0a0340c480707103000c030311030564820791840b00d88094800303401c23000302c06403103440120b0178100320200b41c20006000883c500e0600c0051600410440c1190700c0d08080000f007000760b01c010015401c103074003101e0030036142c0e6124950702881054018207980c66500401c000400c022002500018011309441d40182c841d000315040780d19840a0825952100d01103001640d0f061142c0c0411094004010707150580c0c1d5004141e540f5070b64420324042107008109864558495094501c4100203082a180300641d641c10041280d0028001130b122510010b011a4103000000032200449501c20055030038140f42c10015650411030849200d0744580800c0010f001440c03c2c170511444a200b0480003034060722900501020007130060a010070b603841042800300c04003107a002c0c1d079010320342480c150074000030a180030301c00b600c0c4483c0c4040d01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 280045971 1250 280044721 280044727
    0xa020102040801090f140303011809051f2322051612060e03070f060c020118050114071115070e040c03060509070905010503040f0c0b030c0301061b030818010e03 71
    0x2000170a00309070b0b26640c000c1c043d80c45c054018440301d540304e100c00c0c85001404a420b0000f412035074096042846524000c2d0150b0fa66180a400130002c10303107107608003000c4e1981d03480040304810b0042d85162800060784006100398030303000c00285481d10325085040518802040d620707081100c100842a00407050420150000d41e40d41c03150000303541206401c41c2c5e540e0a0a50410f0301350800403d03222401c1d0000d80c28207c028243d110031009240d800d82100441d5215903030314802c8100102d245e0080d80c4183c0c00020400380712003a03a00d0b4040003800ca036080284994646104180008581400039140803c5c1842620380c010140c80071a081c1081d00d4019041012509016415510000c2242e03c2900d410714a035a408a04441d01d02d000d0003003a0204074184085004928008620312841e4402c1e07203002070403038440300300e80d1054000b00c841c1e051030240000140482680140050030a901c95481d1207500350300c40d41c0c0034100da00020080c8542c4000040403040c3d0040c2504807400d6003483c20309030b9507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 280047221 1250 280045971 280045973
    0x606270e1b07050f150f07030504050705040608150601031808090a030f0f02030c1009030803150301060308031605041203030b01020c040f06030b1006021c0c08040906060e0d0312020a02010204080109 87
    0x184a660307000913401c040c000d4403114401c2c5280c02012911403102582000d0b0241d0340c010084d001450007410588040c41420808991038542d0320440000e400e240c00100310b68031203000402454003005058504047c10b14501c040c01505a4a00381c10340c0740d000400c19100d6284070081681c003141c40c2c0c00902010f4503200c451080c08403061003210350b5802a41910001c103e44024001c01c02c0201c110180001d07280c9001308003081c1502c0203150070100e481c40007040301441ca0006821740c1e00903001520020380000c2400440d040b010310040320b40e00c1d241081c0e41061f1420000070541014a0009002e25842e03030f18252090f80f0034070810001d03a41c0140100070110038262040700500c900d000c110380440d488404504103052103001d00003203c81c82d900420381c0d0880c114040515451194800043c0b1072101f10450009100e0710151003d0308104000280d91032a010703000305544090401180117010a91907100481e0303202940c00c40c0181420805a5600784400041b070083c031455000141c3d551a111000e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 280048471 1250 280047221 280047223
    0x1d0408070303021908010521030910020703080403080a020f0703020a21060e0303100812041a361c030318020a090605040c11062205100606270e1b0705 66
    0x5050354006d440000c0070b18049043c8000745403102c20f81d03816275402800003001c1850310241030000d01c0b040d4810307a280c1c103583e03035035021a50300a900100ca13201030115042d00503550400a403c244403280e030007440c90034913580119030090360314021040c00341e52060000c0748148411084030500c40d406003081241c0d001d00b02d41252241c000b40c070b0352015484012000540f040001403c0842e0351203e0200f03a00c0c2c10316044d010041e480c80130104200d841c805101040b40d07400d000740c04810000d508924950355085018103d054184c440c45c1046c400c4400c280c4455401e448131042e0f4000f40e5040c100003c529a8141021001080c0008020352240850b0000b044010230350300410101d50742039606100480d0300100c140c600c2c6111403010710195001400090144c084810980c400e410304501070b80c4900582c0e1139444c140f0744284d604240326600c406040003155170001c0321080c41c041c2e0849580840301d10003442040d641880c811b87c00c0c10801003000c103100601c0034003140e840310348060600e5524040340c6811 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 280049721 1250 280048471 280048487
    0x106090501050609062a12031e133306080d031b050702060d0504060506030c0301020415140d0e06190501060c020d1b06020c0a1d04080703030219 64
    0x101410304000088900340310080d9084284014103950600710385c00c02800084840b1b00814003c403000c0004d08511000501c04401a25a03010506a5070304c2c2801951004846200400701a088444200021005071078022458942c0c8003080c003494181c1c400c00942103100c600c000d020003080e5584071142c100055440b000880305440190f88440d24071400c02d4044903003c0404008503030144a01102c9203216500030080d05200810701404d105007001d141c030440b203049038221749480da00c038148451840e08101400303044404600a514003070412031032a2101d400c447e80c60051002c255224001c8081407030656501d894108001c0104071200e000d01660340500740c601028004200c81a24040c4041d406224169907690300c3c0c00700d0007000c55080c0000050a900103540e15209040704e81d40300707850358003220014119030f4000c0101c49652010400ca98449034001d034480d042010300c1000c070039902101c00d0390143d081b101554555050381000e4000e44581c920084241140e0144e00c040705421030302d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 280050971 1250 280049721 280049729
    0x31b1202030c1605061c09240e01110a140c01020c031b0304081c0302070b16021b0d0305030601090305010609020711010c0f06050606040506030a020d0b1c151407020106 74
    0x321941c0c4200141c3c40841200300b401000d4104004005510348102d107904111606810303a40001a00302d01038850f441c02e101100c1d150b02400c500d01c028124051507601600c0b01101c05800204508400700c18105203d00c80e660080c01806024210071136140d030076200381c50800031140025550703501295440c130b440e980300c3c207405094645450130745800510000255030981d1490b400070710321101050040e01e442c166440321001050780802c0500000391103040c5190081002c120300203502041440081e0500e5410744005500f071900303d034920078070b540310814040041d4250503c55030b20f448502c0100c4090f821500b0240c0700390300f07140d4000f582d2000c550003032560300c0c081c1c00f1132115041503400450700f210b01c4110150581d141c2c1d45039000072511641c40650009001440c0f81c1c942507940021400b036030003c9500c17076400d550214500f00000710901031304295900444202d020308a01d890240c16081082102521000303410400150105580d40700180e6452040382034080d502d0038050080c0a0104c1d402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 280052221 1250 280050971 280050973
    0x706050106090b0d0f020c15090d0513120f0507120b0c04030b060f040e0a051e0106030302031c39020705010c02060c01060324110412031b1202030c 65
    0x20000072014810b525040c1074600c1c00701c10134a06421060340001500503543e4059503e5400c108800b5490400c108040d03c10043d64000c81951510412840c20030200d003048009000082150215101d200d0321808203440780f01000301e10f0640c107420700d140350124010380140300b4803680ca408102c02c100c04a91600c06403140c00116201d0380c40c3d100880d0035004600c002008042c1c03020101c2c000d032400425503182c6c2100600002001d200c1c8200e0546401d0200300706071a42d0704895620400002290b40003049012144024130000c5d1956400950307911400c1280c840d080c4d00d1064014401450b0380040c2e40b1004000b4102c0c405900c2c0c080020016061147e124440c07003945070308240450300114000c800ca0f10140c4074541c0b580d0881d024444240d02005650100f9561000040000b40c1001b002ca42002c10b44442606080a0350000008075000ea0040000211050000f007045c03154890215500c2030741440d090b491507032104a00f611188040c1802803440c1c1c16800c183c0d4001364000040c1ca1022540c030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 280053471 1250 280052221 280052231
    0x22061205100e0c0f0d2a081006360212070206090d0f11030408161a040302130207080d09030206060f01030b090a2f04030312050709090509010b03030f0706 68
    0xd029a950b0780320003c2e040d40214038221070101d5032405103c1c0003816405003040c5141c0c1600a142d2204800210400d40f2100034035140500041204000074610170301c4aa1042103000d090015152125003100c90544100404802480c851030382510f01e0800c40100250564440d2840320a0011081040715180d00510170800010b02400000880b00f40300c00b1280c0310601002c00c7c0712811128160605510081c51004100018010740c080000080d00d00000821114030750800701102d0180c0381c24062407810420602013400540e4a03200800142c0303c26000060341c42400d40f410700c62900807030540350032442c81c00744071030181900480d48903c01c07442100c100500c440100c0054048807108281c050708481002e0015500080550003015502e6000324a00d014541c1c030041561a020000e88258583e5800701d010001c054020306440801c0361008410f01461414000040420850b413085600e055211404585070360420350102425000140660303540300010062030f43c0d258808413040741c13000d10b04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 280054721 1250 280053471 280053491
    0x10506010f180510022d060c030403021b0a0801140613090803010b0d0603051606020706050c061605090a030c1a0c030f07020432060f2206120510 64
    0x4012000748184410511140542800c3c1800000110540590158441c1c150b0140480c05c0501070000304410003100d42240807820030702e10b070500f6070140c003031100b0040510512001035004180b0325034032045000da031071800c001c1c14006004c5000c00d50081c0c00030f5180600c0f0904201300305900074402d94054464624880b085246001180d2010001800e40c907414001071140004800040c5a4444064404210a5101e407202d170308002c10085456584640007a041002d01d03018031505009002c03d040241c20183d5103c072071a2200d00042036100c8501025044d00c8a00b0301034026a90a550084e04800400d0f48030324100c042c0141c28020204010101c0d280d19110300b031040104c070101080b400107036080940e04e0502c5c0515401020b0b0480e4405d0b1205801c4155020302e160440c0d20a507505401d400985050510800a80c0081c007114054801c00382181c1c4030f600d607004110a044403040c7c50009041a540a09004280c1a0050514100c0c00c04488040c86400030303452a104203c010108000c07001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 280055971 1250 280054721 280054727
    0x30a27080903060919030309020d120206090d0801030b130f06050a24120308090c060a0f031d07180b060a02010b150405090109020304050c180907080a020303030406020a1808010506010f 81
    0xc9542c0194403105c0da803801000081c401c0c1c006904262014000c1d4180d103071950358084000e50100b036203000690140741003120140013041194004006c5003004511541140c0790281106002031001c3c003940c9210000304100140800c92401d4580c1007203080141d4140030151401803c002008400b00d10070700e02e01c090031600c0c0030b1310a00880d4050085d403203030341c15180d509403001c481c0180b505030240a1402d44040e151241001411400c825540d0b507000c00754481c02c040e00320b8005015818520342010b45007410040c000589500340c4141c0000d448140c1a80c41200015159251a0326081b41021a020200540540000c480400f007207070740070000302041c031081450b4020f6114841d400f40d07e807401045800705603801103801501900035502e40070350340c0000c10410303504952b09a1032040c1140070030060100070700c2200090700c200000390140800c50380000f0303034900002e8000b40060303600081c3d9128a074000ca5a0320800211060741541c0c80717668103400360007458221084e80c0415001c0410382a260300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 280057221 1250 280055971 280055983
    0x8010501080d0e15120417070c0b0319060e01050a15050301060c111c02040b0d0b060603150a06050d0c08090d030b030c120f0d030c05030a270809030609 67
    0x1e0000c01014440c400301d00440d91000070841c01da8101d2820182c081084100314001c0c103011800302d0140d11681001d01d07060ba01072000159800c018041440100c0005214644540403500d5600c182c40d220b4494a0080c0c48030001034022060880c6494000543e0881c01c00540b4102d401c100d03102d81c262540c032a0a40c81c1501052000800501e0820041c405180507003011103c00d80a202c0e0002506a04004509200b004480042602404510302ca0071481e0901510405e44d009880c3c4c0c40c030b540c0680c0d03910303003aa01c0040c1c526445000e0110002c1c001c0c284e1b0007407044920030010704811010b59200340142055210009110000e82458004d03454103001c0c5190718050341c01ea80003040c51020b41c1004400421511000700e606d4001c10400300c50b07959441d490603220201d0384e0050401102050a19031400243d0361014041c18181900c410410f60402e0907241c0c025000107001c40c071811114203050001030285558814807440700082c1c0305000038200506079820098088485d030352a0310a01c40da0b030710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 280058471 1250 280057221 280057229
    0x190f0603050a05010c081308030a0204031e0219080a03030207050c09010e0702010c020606130e0f0f010606020f0c0d0f060605150403051b09150102030408070311010801092f07060c090f08010501 85
    0x12031f400100100254003403008503031042088100504142c0c91340e07590b011125504011000010840807d44154074061881c0112211082403181c02d4505e400030454580503c0d80e80074003416400b00b800400d00c0030501400c425240e00402d030036425a140d8101c040e208905841c5840150f2901800311183c2d8000100300d07000e603000508c8140d141031400e041c10094001500a0040d9010323503c049a0301c0203041004459082c52980041903490914bc40285003815040a19425500410080c0031030f480310240308072040e1700080d00004a010500704000a81001d50286410503200e007160f0050a2906000c0c2058034458415103040b04000702051003051450042e0325400641440458002c059040001c4980c032018015641850754903040d042c1000c1066100b5145a8040301c1c81400c1036a0181080d405481c2140c0100800d980400004841c0c88142c0d80e80404042a86c08a00c0351ba011101961100c036840740781402030003084500103080a260303209010803c1c6a2200108100906011b194162 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 280059721 1250 280058471 280058491
    0xf060518010902012a0b010602071503050c090103240303080f15130f0e0604060f140907270e010b040c020d0215040c0f081f020a0503190f0603050a05010c08 69
    0x381d5030303522298005050341c5c2c80c005200700d4545054000a00d00321646000307180d283c015203101494201c00e0b44008803542c0c2e00404151901d0304100c4109400b0064440105007803900040a1120750598900c240c003141c1c00926540c2c60782030010030036a112000c548213800e8130b4201e20301501c8990714001c014000c0700302c981d40100e06268800d181e022139030180341c0340c0c00d80c810f0210307107841024082420140141c500360380f0702c1d40710b0040300c0400c1d1080c000c014882c1c4000d422145185002c80101d600c070120760060400e00c094007501c5c428001071641c0e0880b8864109041040268a03040c0301038002c000001a00d400340c1d09040d950b07030302d660000c43d450002d0012078014101c0070580070408409148018405c036819085a08086601c081040741c100c007030410000109640364400c01c0f4105c2e00503480b640010700351300420802e450658042c003540d401c5030101201201c0b000c0c0103240407000d00607000c6e80c500c03a40d00e080d9001040c030400081c3c0460350703070040e0000c005032801e2803001c90713094030129114022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 280060971 1250 280059721 280059737
    0x5101b0f020a030305220b1f0f090f0f050108030a02060c13030807080d0c051b03040302130209040f0213030c092007030e0d060902010e030706090b070602070f06051801090201 77
    0x481c3c0079400041e0300c8050f58107400c601c0039641d800c1042500c0700800541c3d100d8604001c1040307061491041c41c02d284211190b8234182450703d0302d51600c2c2c1e403030750140d007031101d80700c0b210441c0e550a01d41100c0300415456030140055a1140c0c905c0345e072600407034540070040c0b240d100030904d007141c0c0c4801c8400000e05500c3e407510050550315240e0160f407204c88116071043e4100504d0382005080c2c0f20f0300340c2c0e066456172002e9540d228a040f24040d02c00079213000f10300f500104000c200596500c14205290b10030700b000075132920141e600040c014140501818946400051240c000d100510100001c0d41c1c0b0400d131411405880d0ba03212002c0f58084000f0040706e8140303c9406528142c4072001e00326040c46880c001c000100b119004c60604012008100d07030268564881c001150781144d90b15040f140c080d8006c001c014602600103041403110b1056510008002030b6550a10140303404413003c15801c031080d61030020540ca0320741c0040000310740700914080840d07030305c2032012018040d0740403032034050b1344602c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 280062221 1250 280060971 280060973
    0x1e100506010519050409020a0917030309101d0a060c0306061103070f02030a15020a09090203060d060c021002070516050d0b04020f010c0f050d02010b0612010b0c03040305101b0f020a 80
    0x40d00500d0300b0303c4603040c80800c0c407000030590b00320300040c0120b98403a603500030000d143ca58070204001c01c90296900c2394106208000c58110009141c2d4441c070744100001c201f0b400d00e00b51200011800301044012801021440e4003804941d40115100554680c3e081018a40e950011180300000f0840c4c000c0c107400402030240881c0401582028080c0028140c40c0910300070303618003e0b20444140718039459500860380f200b280382c000c0e504d01700501031000b007546546004c5000810401c02d11000801a95940f480940020306c00c01920003010144241199554505d0901c1c03a51950040f013031031403d00e1131860100b82d508000400a1429034005000e090036196a406c108080440d98649810000048038102c0800c6201000d505a207001d8405010b442c0e1280c0c60007402e444800707210798001d180070080010304011849082d41103c05001d071241c0c4400d54203400c103040d03100d2a400508a4411071065500c1081c0e0b540c440340c595029442000c00002c0b0702d400907544410840f08510140e0002c81941d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 280063471 1250 280062221 280062247
    0xb06030a15092a03030e0105040308091908102702090f090c180603010b150a050c1005010e0106170103120507060b22110304020d0813081e1005060105 66
    0x2203110304540d034000d0007460014550307034668443d18800054046800c00c04d041d0005e50b000c0c83c0328000c1ca48185840d08580701c0314000c0c850144440d01500c4450b5180c1010312500c01c00340050710034581a12054800c5400e04005061684400c1c624905d03103a030741038814103241c1510400158054002d0600703070b0701c1c446261503402c0018425050b60064840312640d560300c41c4080d4155415034060400c083c00c0800500d800c483c0104800e82c0211482074090540040034401d9030715040d41032074442d958800c030040032410303d035016803d03d4140c0c2c203000003c1114003404e02d40d24142d904613078480802d451048403108040c1420f02c80600000d00d1001c810110351312407402049490b0060394003186044001d008500524249034000e0000328201040c418001c200e406052041c0c1402400d0b141141004e40010f004020944c0c0f004007481d078001400551030714084424802041d0384801c1d6480d010003d0403008405441c41040a582d0042e0800001e8054651107850301850044c2e4495003405d08a040c90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 280064721 1250 280063471 280063481
    0x1050d030c0501060e070f0806011818181110020604030507200909030a0908070819140703030518030102070f0b0c1b0304030203160602100b0f0301180b06030a15 71
    0x26074055407650800705d0400d400c05c07003480c061b80203642c61100103100154010484100505440d04205203007044c80d41e903000054122098a60002e510891511440e15903c02021003900714140b20380350401490900c2200c042c820f400403000e90340710340f2400b003414040fa00d0f10303012100200410402d114a40128680128220959011441c071104010307415001a4248030200c0307420009a00000700b0083c000c0e03008100e00c00a101c80c0004200c001c0c01d04403036544a249050f210100b00e0760307070601c44007401050b0440f00c00b14041413055561443d10303814000c2c440d52000c583d9a80303d01d400502c0480508052084940c3c0c160480d40040c03010102c0d40c5d942c0111600076101401103141070000714548202d00c802c95001c4c0b20000c00940d40c80345948107040c2040c10075a10f40400c420059002c11003542c012480440b84480d4030000224002c120b0006508000c407401516055031030480c10400c45038020000c80c0380d50f801141c42580f2661000109503032283d98640041c01080d8984a20100800315040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 280065971 1250 280064721 280064723
    0x1e04030305160c1805010302040c2102030a0b0d030c0605010605031608090f160e0a090b0c0a0306090615080f0919020418030801031a0115110708032b020301050d030c 73
    0x40440c41d502c03c1040c4254011350604095581c1c0c450040045203030600c10180e266820b411301c14100c0d07111941c0c000d01101d4034500c1c050a070790000006131040c4816072091111140003014000d0a641d03d00380280704480000301281c0d0a803400e80082030981c044c0702607038822240003409c0e203800c13010603500311425040035041a2151017070500101080300280314007921001c01070f040a05040c648400350390701400c080e1500c1d940c0303403501d050741000c50b801303c1c881ea1344038240400355503450f9201042200181011390290094a1506034049003050800e424081e08401c103507201481c40d03d940c411010301ca03800303890445403584000b950203540c25409010f42513031400200005425416610040e42e4080040000c50002c0c05100041c0f0400c01c4501008100d86a500e0140700700d0340c1861800c5102c2c45040d0405d105200c0010144119040c1c10000d08016245034003d0b2620b550780114241c160182000d070910f14201e18000701c03603039140340f88280d074100c4000070503800880b030f510f480a07902001031807c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 280067221 1250 280065971 280065983
    0x3080a0615260108030703030f0905030304021c0c06050306030d0212180d0c08010b120f070b03061210020910030915050916060806041406010f051812031e0403030516 73
    0x189403848140700044143c002c00140c006950303a02c0540c034004040791203400010322031a28007105000410740c0002503e0384a9070554890558900890500201da00c0e1110b006001141040c000f107140c5600401950040f42c1c240d04940c489040d41c1020303600c1d0402d16110010342c440910040030b40004140460300310b6980500158100324464544400b07041c0307690130490700c4d030791100b00901a07414080f04221100e030780b90000c0c09100c0044400a500c402e000c4c4079111001c400031010402664544400320a05400441140e20380d9094500e0780000e50030581d0041d00c54110420800d1110303001e40501040706910201d40e856060303540400e000140340280012400d0310500804115403120300c030710400688210b40362001d0324541081000b080d40c590840030f40038116010148a2242d800c110410324a11040c00c09540701c1104411032001014079400701c0c1d50020801d481105485008001010082400b9a03480281c001d214607680b2035101c0c40c88010f00180081142c21032401641b1041c642c0175211303036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 280068471 1250 280067221 280067267
    0x70302040807090603020a0e160804020f06130302120102120a091a0a0b13060b0d0b03010f1d070806070207090902130f0b0f0306010605090111010b0a06080403080a0615 74
    0x1a02d2400c40c554001040450380c50409106610340403000030000c2c9140d41d10b0400c14540b00102e12a440c0a20300003506010f50000414119920390340d01c0b008000700503100030b49903400f0b907120b0300f0461a648810b030300441210400400c0282c1c18021154100b080b183c4900650321140d001c0d80c010900000191070901c43d40440401d01c031100d0300213074040c0030303184404039003c2400010010480d07a4040e000d42c0440c500141004110128004d0f0390701040318070f41c0028042e02e410086030250188690f046a141e140011f6800c40e06203200d140e0031080c441c0b400301d8400301d445100785540c03840182d54683c00b690094004000c182120740001c01024030241208545d02e0b01001e034601030f21107001c0302c0c0380602d80301d120400d034a04014080c6603600da41140101b580e5403400c100904a0b110350030140c1c1c1041800c1c05240c144070000d40100ca421800a00411403056881d24001e011007020f4034200c0c0000c10380404140c0f03203402d078021541a00d982e901c12000345545484180c4101070f0310340716001910010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 280069721 1250 280068471 280068479
    0xd020310050933011202010908031c0e01050108120703020f0102040f050117012601110424030606050d020a0215010611010f11040306090203190303020901030e0606030a060507030204 80
    0x1402014000c0c03034020b004280004422290910000108401030901c2510010345a44950b02d40c50481c11140354480e51401141c0500040315105404d4022807024031000030900001c0c03226101c810f81c810600c160400124440c810754509941c0b0a1091280130b500c84880c018440c507240d0010a44203102c1d004603003060900011041c02d83c0c0095001310600307071008000300070550300501c080c59000880c0d2014161981007490800a0a00b050042084e15441440120000500f58411010441d64182185c0c4490313468680160404490017070b00030440e8482c1e030b800c440328000d0180c001a5030403078649500300011514400000d41080c001c1404612509440925a5461201c0c2d9400f8141a580344c02c03050109101c50b6080d00d00d000d000d2094a4035000c6c040c0c2841e44800195020369070302400200300c0c0c10031800081d00c0c024141110300889007292008001309501a4000c0002102c2a28207100e60b144869045840e01801c44015405800112007400014241d500882e4020140d041c014189521 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 280070971 1250 280069721 280069753
    0x1002030c011503020a050d230c0a0b0d0b1f053907080d020c0f18011d060a03020310051f03080c12071205070206040506120a06080f07050d0203 63
    0x1442c180001c1100160b82c1407056080080305140a07200c15680703020100c8a603138660181c507000c2550914200f08031312104003011401e0160f400c19400040080e0700c0705440d0000c90b000c070b50200c04002c08440c07904040c00c24a00300780810071a50382c0c1d22070300030030b101e61044400e4803d0b510000030411550001d15121200d01300103807121a8601d0390308403000780c00710b981380e107a440d007062a00303c01d200c1e42c0166090213a495000034403c00e00e400645108034403444a03004204041410302d0028112804200003150800f0b0b0503085110040d03008802c4206605c4034400d0209040d01804040d40580003a0301c0d002080c4010b4200f140c1142802041c160030b280500c200c08003040d02d0360030440d403610000a8040c0c001804005e006818030503c3c20720b510305403c3e42d40f80302c038511000303112100b03000d8080782d03103400d5569103001d6034000c2c8005040150707507504082035030021040c1222403140e900d103405000b1643c2280020003070041c0c0f0b1000f009001c0d1500706800c000c80c2082490003240d05220b01907140302d0240c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 280072221 1250 280070971 280070981
    0x207061d0607120216080d0e0301020403050105071206060906080f090708030c0a0309080d08270d090503060a0c05090d021201020a0203090913170d0b0a030b100905010f051002030c01 80
    0x3005420b1000c403070000a01c020b007403068400004400b0b60800030700b0f208685001c20300b0301600c00385c1e00f01603208d1011140801e0190141c1e0780003400355481e1404008416402030040f40100403102020041c03a900e490b0701780e510800e280078210006100000090003408480300050f001f0481801b142d2909a451100c146517504c82e0340c2203966038201c00010010103403ca0b9001018100b0030024040401c070030705008003400d030001c2c1004080001018001721b100203203036a03041e081e60344400f5610308540400f0041d007560142c1c400c090007032140e100000c0e0310948500c181c00301030249030b68587c60130181c40104460000e4103907069a10281014106a01110900c000e04840040c1d802540d150a034280c1000703240100180320071440000a840c01002070100380068078400c105060300da445101d0060003034010442d44c644141c00001d003031408004d00000b4083c0601c40c881c0485040c86286d03c1d120340c4030640300288680000c5044081c0140014905000071103403000c1c2500c116801d002d040000b8a00303441c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 280073471 1250 280072221 280072223
    0x60a0203070c08071d040203060f0709080706021606030525031103040f11010f08070c230f0115081b1801030b010e0609061e011101020406050d06150207061d0607 71
    0x58408181048961708a082003010100c40203070308034030303840c1940100c2d403200b000170b103010360200b242c60009114900a540c0d03400581481012110200e03100c0902075030b10545800c0c03101f07000e08040c0e4005656446400741c944952000c1181484d010310460313503102400e03c581050301c00e00d0345031a030704020103001c0302c0a18880d50181c444000d003041507081140d44103c201c000340d0b0401000034806103040d5000070109401000c10314003054010b5160802c00c0f00c000340343c4d81c0b0717280c02e40705050108070b81c00300003074900301014803030008220502000d408104030040c54070600d4219080f00c42803402c04070309500d01c541507100150421301d03440030603030034442c945000741c0089440c6214140140680c0702a02245036000d007096820002c10300341180020080c080d00003031103901e50194100610180d104448002e030814014001399203440d194040a01250820300c60b554210b460044002031030450325412069914075074014140c91400c214084a10b001c00c2c0c900320300d0000c1400341d110003c2d126130008081003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 280074721 1250 280073471 280073473
    0x80403050d020c030d060527060301091502090f0109080a0221060117010f020f070f0c05040c090e090a1a090319050711150306220504060501080706050a050405060a0203070c08 77
    0x64a41e484c0c5d5503003111070320340115004010b5107414500340c40d428039400c603014054904164031a43d5101c0040e015000c468001422889500c01d4896441295000f030030f0b80c4c0780200d48000c140c100700801152038a01c5403140300300ca58043c05c02003015080c562aa000500d207031003420140080440d07031840c03a02000ba4041c5c41890760611000d10464000e00c650b650100042c0400e516003d0750400c1580316000c0c80a000d085401020a4002080700410340e450082501410a01c02024075040103001e000702c622840c050861050b000404a01c0c0101d080e03440150b1040d010f200d1402d08000ba41c81440b0024030001182c442000010807070b0215842a03600400940d8500b42d5440f1540307410308490ba40380007942d008103820980c04a050720761800342c030350240042d900100312544c40104034036007480c1c070303107448000c00c1c504020b002c01e004258004c1816188030204884c500c6641c2d000c11205480b0314158040060818001880140b9141c001001c5007449403044a00b09401a21900c1c01450b03190b103c1805 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 280075971 1250 280074721 280074727
    0x905120a0b0c0406120f0219230c0a0605270709060e06131a0901080105010e0708090d031a0907110709090f0611040b0f07061401060f080403050d020c03 67
    0x104900301a40303642c8030051414407400c01e86410b902a0107241c1305100700302c0380c607228100d01c003101102d581a40d882c003500c3c1c020072002e028100302c003518000c00d80b01048842d048205280b100590944202c07801c103004100209240312a41e11020001c2401900c10400209441c1034000400395008900c01c400c01904007402c500ea1811404800b02c034042d6100b82c00c0d5249800400c0426a650031b400b02c0180175a110124003c8000c0c401d05030b45400380700d207103940a109a800800d404405501c40d5059070004101240346840c1c0000607a010102140c0744440c0343d100380780030203d0510075040b050003107140810f105100c01d00e08002400d000004c4940c000002d03c03411072504141030803c207241c0180f107001e00402042e0b4003620b50a9100303060910141030641c640c090000140f60710003c9078020100741c20065291000c1ca01e0074030695119441c2950403074144021812607010315140e05040354400c1c2c0b00c0d80c480e001c50035400e03640e00400900076401e1201c144051101c00030f1500083c414402c0c01405156 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 280077221 1250 280075971 280075973
    0x3080604060e040f030f0e0d0c090606140711180c070c0b0c120906040504020726030c090d060b0301061203090e0c031f08070e01030201120903120209010905120a 71
    0xc1166416401051600e070703144244804100002007209455415180c03586124081701c1055a440d0542d0039096044014003840305e0521070f03040d407010300780c402c07584050110340e964030130813207a000d1384c03501051004900b0020480001d1450807200300908010301001018815200806a030310401c0742d80201e411000039502081010070100100540030380401e8501305204801546d5450b00b503401c0400c2c444000141e418900e40d030780ca081d10010100188150350b681000c1c5000300c51104041c0c03c00d11450000b52420100c42045410350340b0032071140340014200381c500400c00c4608240b1090079160140d84034101703641600d00780142c0c070190015a60060f0041564074001f403440c610baa003c800078004181c18824003006220489030006980c148109a0b0762056038404c0741500c0d241e0251a851181c404001481502c0311080d90480f4000d803240f0780e50000640c000800d8a5040c80010001148000003c0000005a02401c220704041c90200b440303584880110745906c3d8130681d501c2d000d40c86046c140b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 280078471 1250 280077221 280077229
    0x1503010509061b1e130608090604080a0c2a06020d0804080703080414100c03110a020606040510091505030613030207061407061404050f0d02100b030c030a030806 71
    0x6400c40307072280040001c0d107000c1c0707a050300300010981c1c10041d6040c00540340c3e03a0011074100b01c0905100d1500d180c0e40c2ca6030b07031807a1040049118811040401e07a1480018005130010a140e840346801c1039846140132100304040b01c18030b90502044070008a20982085044101030140d1001c03841420440b01503400c2900c00ba250441c0c1c9502002007241c0360040000054824042e11481ea80c1030414003015100c52034042c102284203c0100ba032803040585104501c1c400c2c2d00302d0340880c9240d032004c000035056030030310901c0c40c498a14a000903038800b201149841c1401c2d806241e00095000c110400107840c0c071103941c291000c40c682c21042d41001d400500c464581031110316044400c80c0f5006466011640e0080c1d1610243d03c03d030030501417440850082c68070340f902142d42035a4803480403c1500185800220764000c1918161514840d41c8001c1c6a43d10b0b0024030070700045441e400400c1901d41c4ca600101c00f4015440e105901801250750f40030490300d00308800d02c0c00d60f2190b1079506162408000388 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 280079721 1250 280078471 280078481
    0xd0e0106030c12030e0d05030f27120307170c030a0503040215040302130504231617071206020c070e010914040201050d020307180f050108100b1b010e06150301 70
    0x843ca0a0040351080000390400b030b001c20500307002c1d500b002480c030711410407a096001c3c2d521040c2100100040c60070b0100c1d02c440c0c088804107442c4007149603004022040c480c441c400c08002000f0b41c2e10070090003001c038044040c110001e0301803100840c64031080a208900f1a000203a180001c50307404410301c0700310b1420f0300806007000320040c507d6080c6455500040d040c5014081e000c88510741d074602040a00507145c2c3e003003a040da20390fa92032010742111482c8641e144041c10034024010014100800c200c0400603120705400744070401001001e04060078042907050342c00040b02d0081e402c00092a6603070341844240020107550002044645c5007034a02400d98518482800c01503103910200b04c0140e801030f0a840c82c90b40d00b9000161280da0300801600c0703000007a00d4102098010725000500b0300e442021031010f40d0000e80c0ca000389a01d500c40141c1c02017000c0c0c0510f2404d80824040160900f044080341c60f070802c1c0c203500106250b070048149509146007a601c40510400400c6003035441d0409000f5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 280080971 1250 280079721 280079729
    0xf0c070e060604030807050c0a0b0403060b1009050415050306070e03100905070e06010e040e0d350606070605150a290d090501050903030604200a0309080d0e0106030c 73
    0x403085041c940140001c050744074070300000780b01020219070300c000d02030100300c00010107034080d0024441c02d0700c0d540c1031011500f05110464643c0e04140409a030340c00c046080a10180c0301e5203c20380400d0030441000003510580340d154069078181a0300107490b030b07000c200590050b102c645981645100d082c0a25080c90341000d0800e43c15070500015100050000070000c040b103107284060141500c54a0040b680700c2144101c9030361203130800c042d64141d40004102041c090180351641244505001d030441c40954441c0400b010004d4004051141d03160740078000c070f52000008050600d0021035544e00000c90301d0584080c4012400c041503600e01c3d0802c24141d80240034152805106140000d815048a200100f1200d1140001088440c043d0406400c1071400030340c00f200a000c28030701410700fa6039070303042182c6e002e129609003264200e0640741d034200481c6840214400b5442d0028150040e00a00140c1c0005c95031a00e0811030141031003114458282c19004c214008070304103145081c040d00320340c00790300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 280082221 1250 280080971 280080989
    0x1031a0106050f030a06170d02301b0f0714041e0b040b03011107021f020a0605071e2309010903140705040207081e04030b0c0904060b0f0c07 62
    0x1401600c2e002001d49244070032241001e90360341c0d505034420000c4c2c45594000010306071a40c18030703034010b07101140d4030072061015404c80e141d9903000b013100d014586001040c0c00025020002d0180106502c000070182e00603000d002001e2480411845480d10150003100802a040700c40d00742305280000003a110190411a000c0c0315980003000c000e111000d1003a5040051941c604180d0042c3d1907540001c821580d0060080001c0e00b9400d04400c040d500040307080b03100304038140e40000390881140c80084031a420340d0040800c203002e580d60200500016007008180000303e0311860202c4c100c20070811808030703113a4070400c1c9402d08642d20009100c4020685e104048240140201a64081818800c0740d1700030500f000201841d01005c0e043c4240741e002590014000152041409501401410510800510f040c00b01d642c01c84600b00b02d0195000082c1000d000c000856441e80406e0b000d40310b506801000083d207181d0380c1000003d968071000c000e2119071000f00360302944a07800c5c0f011000405c9201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 280083471 1250 280082221 280082273
    0x8060607020f011d12100b03030c280506010b071101080609070c0201140a0f020f060405060601111005150a0602062511030403050a02040506030c0a3b0103 68
    0x1a00064150582c0d2a460741040590000b555180e241880c00400c14100a840701a4608100000c6034584650400c40c400302410302175100d00b00c3c1030020445041c0781e040790152601e07140300b4040c5202803e100b40e041ea402d00b0407035802e070b022500c180101d50083c5214400700317070b8814562901d1441c071003080d000d0f541400110020030031203846101039a03911070b01c02d1404058010803440140c6480040c002242039000000c100d0204040c0c1004030511103100369021610300d0001a107605903645000c80c0c0080064001c000407500a5000b0291221950b20030020340382070a0341500d05074110b850468141440010014070b481d01030410070511006058144081c0859107060100119490003801c0105104204400301c040710b684150004075006080340262903642c0e42c4e038200b8559841c500703030069105078603102c081352a034900010380c8000090050110f2001e01e1400d0034a6440c4200b440503645000c00302800c0d810030446070080e0708100080008407002720350642c01c04078980d07082d028181c025001d1341 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 280084721 1250 280083471 280083473
    0x3151512010e330301110d15080607050d020304020103060b0a02060604150807120804030506041a0a0b01020d180815040b010602030a050d1503020603012603041d0a09020603130308060607 82
    0x6503d10740c0c0d001c0c188819089501c0024000b0074010213514182d48041000465141d0120301142c0010b81c1e00c0c800c00a143c1c0c186a1690902c540f508420381d00382e00403c00400c505007500e01d81340c0240d42c0c0300f401410300203421a039551211025070f000300d04613801600003604010702841c1510848203c0a01408000030290401060b41d65441c0700f40260307018080400d0029042004036001c03540515400419074030641800d15002c509056084000c0b240d41c0707441c0c00050111030b07080c0314544850344141d00a0030906180380058881c256540300e000d04078a440000440c13601d100300131324a07010480e4190504103107054100301c6221001078008104540041220700a181c0e03000702030f501c80c00100d050000320701034000a4074440380f003c1e03030000750085004000090304402c269443d041c3d00b0340058410700010105080700c0c0d101d2245004a0810800480d00d410901c1030b48140d0a51105c00c4050004040383c180d000580710350011034040400c0b6482a01e020f007016440030046803c07100594085003000c80d6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 280085971 1250 280084721 280084771
    0xc0105040605250c03120503070c020d03121506020c0a05030604150212010308180d03050d020a03020d1d1c1d01171005030f030c0303151512010e 64
    0x1440c81501c080050210780807048000740e60341c404065800310150a450103140c5844180031003984415624030a042c0d00140c2e4290007081140c8c401c00c0c0300da603083c3c001c1e80c05508111500180c60015010030070a0074848a1215461044024050a00d0030142c02e8600d000402450079196001140c02950803507801c000c2030700c00003075168106501c00403071410410300045242c028082c1c54100780500948070300000a0204010007801d01c0d80c000c2070401c4811006406100c50310300410300050000da801c00400c48520356aa0103007001d880f0f030307243c054030300741e03100341d0200c1580d40d19030001040c03c0700c0d980103014400d01084000507412502c031090b40d181824102c050f003603203144003903454034501c071103680d25081c0e1241c00c28024442000c20000028203009030a0840d90180c1d0003107034068400c1140041142000006482c0150541002180b5613515110700c0000c0b4071b60002c8441e00112006c151448504401c40a400100c0d0700c00340c80c100381d6141020804441c1c101500880f1004d03242012503816036a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 280087221 1250 280085971 280085977
    0x30301090c051e09120a0b040b0604020d151d0108030703050d0603021c0506070311030402101e02100513050a03030509100f0605090601020c0310050601090e0a05090f0c0105 76
    0x200c51880016071215080050368180304611216a00d80400018020892070703d0000d404641c406507a1546800d0006105ca81d036900a40c001800c8441c0e81e02c0024006803044001300d0340000090005414002000f4a0b0402c4d654942c980c3c1820300b00c216000d105c201c918a040d2400046002c00c00c0045500d0441c01c2c41c2c80c6d108000e8050100b1000003401088070f41c181c0c00c42802140d018011112a00d1000001181410382ca6000c031240d0244801281209109010300c81400714000b040c141385803515820040250300000c1e9041c14085140c0c42214001c0c4640c4500b0581d650a402030b00100c01c1701c0103100b04852008042800115500c010400407500002e280a1002e91508000440380c507502211b03443c2542540c0c3c08070081c0d04010304402c403518103401a0084480668412406480703050041e07072290813001056406038404940107140c2c407011740115800210604100c003141351074101c01c00b52404200c40340440c440e113950500242501c2086680040c1c01660050706880c0c0545000a200e0300c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 280088471 1250 280087221 280087229
    0x30203041202010b0a061407080c0c01090609051005131205030a2d0305090106051201140a0c0e06030a020409110c0f07230307050a030614010e040c0905071b2301020408030301 77
    0x21032072255247c40c0350b800b442120041600300351082c0d2122a41a100c942d142d40c0242601e0000c1c074100340005415006200c1c031000d0700c00c01051041d5080d500d80c8101d60f00d411600b1014041c612001c00010111510518203a04030301980266a50b15020070303001e4081a851003c940002340c0d40c60a501000754440d0207078545506501d008104c076100c9a241034090215508403a9004d04800300a218030881503000c0d081341c103012030f24139815940701601541207550032403940700402c001150380340702071410300d0003144d01802400c00141050741310b040801c01c0b221171030454102000c001401d90844441040500c01c01c0c0c101400030f00525041c0490600e0b00304443d481d428440c402c4200d5002c80e0f03602803150030b02501c0040d0050719201e035241000d0000d44400d030310030425442d200d00003260280d03951842d18416034201046150342460038060300700922004000000304a1491040b8103030140e001c2e001082280560f8040580d0300e80b040100b40c2640020700d144170944e10410007000490300100c1035a04503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 280089721 1250 280088471 280088477
    0x901110606090f0702010e0d0206070909051504150e01030c14060313060e0712080406080601110a0b0403141b01063203160806010801180803151c03030203041202010b0a06 75
    0x6511881011707400f501c00b01e26080c01e9405640da88203c9990b001801e01d100b11101e55a0fa56441d07a250508821108140c0f07800002d005120407144c140c1c14190880341860040000c040c1d0102e0741d51014203038022083e001240d0304402ca8400300580c1e4a40002c10700011001c5505a18506240407911130164840314010911519150700c00d040302400d114820060401b074204008070491440e1510b002d42c020300501003c1003c02010660310352280405103801d21030796004060354641900ca9800311680100f0440410a1014808405001d2403015000c1d6001148686c0d14002d44070030410300f540c095402c03083c120f0300d480160a10420380c40004116588603602139000351110319020a050145100d03665050f100d280b0000640d1441c000f441782d04079a503080081150110302480c1000302255200090300702c0c0d070300f40701048002405014913241010010000a540b040760900072003039024210341030b008070343c0c040100002e0045d407032072441c4c40d191244000c020103884d00d0001440000140101410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 280090971 1250 280089721 280089751
    0x1a0402040b070b1f09050a140403080a050c0f0c030a170c09060f0d09210203030105010c03051b07151d090f13020303070f290c071a010b090111060609 66
    0x1800d00c2c81d010403480110300074158803ca03038451740d12601a0005a80091146241070500038004450010250244c0c1d032540ea081070a4580080c0d0b4009040f0280620300502d00420800d030b14201c0e154010120641d444000d15207940c0c2044015200142680bc01030170b00d03c40d4400c110315110010202d94100004a480c07a0301d80240c0c8880070b41a001d00c0c0c0315130180700c1c9404801000e000008d00881590055001c000c4c0d200205d2a004a0b01d030300083c4600f50100d4407d8082e80c00103070044000e0020102c41c00011003640d00703c200203503c0c059880c1e01c00403910251801c5070707100907030010f00d0001d0101420082501001d02030046928207100030451441c0c18142400b01d01404100a0b45034041c0d40c008084070380743e110b02c1c01c11080d101c040c113100300c480c05d03070a40c00c03058000402812a07440d80a298960035441e5200148201c0c158406e44007101e00c82c00d004080e0704115a01444070340a800c05141154507102c08100150000b0304204000340750b6071140d410401c8580c0d4945030759034480464001c01d46 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 280092221 1250 280090971 280090981
    0xf0606091a12040c03050f0c01080f130b011502010f06030c0b0f070611030f010504140601030e0307020307030c090501120c09180203062505090f06030421031a0402040b070b 76
    0x102d004448070034880b82d50b2001808144103c40702c042d001c0d07900a40c19102101800464240d41e0030450b02070074040fa860b00c0020342d44160428004d0f83c0001c1c900028480724440b83ea800c1d4103440260400e520f0b00c40b00445000d811079091098480c0c80100140c201f1545043d51119803111681d40701c1c1070040303240010045061074500c41590f043c0c99201c203050091f6050384280d43c0c83d85e0421291690700d050300b2070000541e46451300400c4100c0060b43c0f991740c0306840380c0b00110f001e09120080441144070411400c00162000c10800700214050132601d42c1d83c3d81006540000d951040c0d02c42c400b01d0070b1940c0c20a0110368021030600c112510104000744281509414074449260100007952501801081140302c03405020030790520b260110381c9007010079500000343c800d80a05403000e500f2540c0c6110482c081c0c20040000c6130040e00070b1400c0001c003618608401100c000a19069001036107848200f6181c041e0f841e035981d581c110032181503044c03c1c11308590700750320b00400707001030008003100c800302d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 280093471 1250 280092221 280092269
    0x2003040f080c0f07184817130314030a111603030501050a080a0b06060c0105070c1a15040207020f190609090902060708030a020c0106030c08010f060609 67
    0x34445102c00000da42011042800c80b40c0c0720b1040d48501441900000004d600141281c42406000c00c0d00c8090040003240d5151102040300c16083c08110410849181030000fa900c4100000e240e49940d44030701c085071000219080e18507010304840d91544501e81c1d04800607030030000b1042e030300d01c40151003500d0755a08404080a8003c200039081400b400003084110f43e0900048210194040d407014003d590780d46003840f0800c40c20340714495658200740b601e5000548850a21030308040014241c03401c002d0820034a41c2103c40c02c1d2070140100c3c02c031110780000c225030500ba100c5100c0400407880312900d003205501c40440003080170f0600c41d5500145503411555200032441e0000000b921440b070445080c801d440640006001c0d90300464115080060448640d0052400d1540e0291803581029040d564001842d0070181103500d4494082c405004400004d106400c019400b40041040e12403900703000703900311071104c1c0e08402d0507401e0050074400c1c0d580200a0504480c10740d2000b0300340580c035481072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 280094721 1250 280093471 280093477
    0x20106030b0c071101080106051905041d010528090c02031623010b151c2313050601030206300414031c0f0615080405012003040f08 58
    0x78144024402030004031004600644155841814031241444c0c0741801074031108804d110f41000940100881b92600b4070b10481d42c1401001420300c941401d48400300d00c6944021286403070402c550060040006190807038881d11080c0d13035261a103514070581b01901031001c00c070307020785400300d510b884450210501c200119032140d541c820301480c80a01501e002d581201d00440380c04036030030003034004000780007040c45070500b92040140001404841c80350906500d800c001d00c8041102c2607c50f123040000b2841c0550044887c0100181e0310381044203501c0c504000d001340c22079001032601a42800010030020302c150544c0e4040f40c0c2e481e02c1f8038418400c000100c00c05103506425170004100740d8600606520030074011440340c100c0100001c10580402c3e501d008a10380d070410300481032468a81e180b040d80c4149420b0106140c0840c2890301c4108512203604508913060014078008204424807a0038410003080c0506540038142502c243d10040b8000e01024001410801824034008108a03840e011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 280095971 1250 280094721 280094723
    0x603040c121b3503071202010b01080705070807030e190306090203060c0c1c050d06060c030806040e150c09030607052205090c090d050601180e0a02031c02010603 71
    0x1e80540e5001d54509840081c0100c1540d41074500c5044002c5142e080042440509200394030003c00b0b00303a000000d00d2211009002c5050710381c08200250703004035083d07440e0603c0d1801207070000708007914884001044040020840010484d05005c04800030b0039000440c0c0740603405240c00c08101c038400c00000e450300c2101e01d20409030070b482d40000080084941103201e5090017181a2807050381d40e01e21100552066041c100341c560401100000c01104d24042c3c2d052103649407500c5810302807000f40400c100e0b9070580000c00480c0c04003149000305540300b00010f912000c252814444103545121040e82d41d0146881c00300b5420303200001427083c03c2e402e0305a484462000301181d00e18100700e14041e0041d440905c810000d410401c14111501083c5445102120800351804c40d50b80c1ea8074000d00c0340d0360000c000302c5900030703407000354480442e80030001d103400f03001160002202d4451000d200c204845240410700c038960448500c08000d6a40840c00c04400e50508045244180c80f48100724014202504 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 280097221 1250 280095971 280095989
    0x60504090c032904180c0e040507080105011701050a0e12070807080d06030201020609010b09070e18070801210206040302010c080d1a10020604020f10020c0607050d08060d110603040c 80
    0x20741401440a6a0503a8070f2440095a0030459001c400e0326003111804800405058440c212800300400d1030b1201c01541d0003405003041d44c1a090306d40c002c250a4032001c3e0300140451882c9520311034019000e2041940186021380c04005090081486a0b1114900307640021040b4002c65184107105030320088611043d4003030341c4255280304400c1040000c108a01003a40140f14080028501400510a0344030019004040501c6030341c030320f00304540e03a8a4544e80d058100040c0031100459030689039a1500500c02c40e2141290340d03041c1444010841080c80c404c400900e0010307900310150311080102c0c0c007580d4080c40d00e01c844001a051420072803041c076007400b174110300d8040c0202811048411042c1e00320411950707110401030806049035902020b0381c01070360000c203030420b0054525103040388103052071a41c011b4031402c403950400074005410070041554a501300060a4646a83c025080d591208048920105900c0c041c0c82c0c0300701d81a40c030790405005100c0000843d041c0140040c0d001c0061003c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 280098471 1250 280097221 280097261
    0x706081b0c06091911100e0d0f02030c01050a05030a05060f0603130303060e043c03080103060606030203010b030703020a020703061e06170c0607060e070806090f07060504090c03 78
    0x810250348160490f207903a820b02460880403841c0100803200a03942d41c004d8050082950000200030704500b50101201c140002042c0e010b0b110348071058801000e50140d010b404092841e03006060820321055141c07030401a04010941e19190043c0a4903048400e480c000180f96940d100440c0507c2800b0001d66400517000c410449000100c00000046500c01d035000d211855440c44680420981560300500080507881450000d42a4411070b004e2500c91881884800c60000f40b0301c0180100e170300c01a000641d0030001807090154a02403a002405a440d04600d1580f40c240c02600302d01014200404042e00042c40c007200901c00c2180c60042c4d600301d4400c0120314600b19440016445842680d010281030910001e0f802524441d1102200240d0010304440c2c40c0007010402c0c1d035403100c00200d459540d2140e0140418208100013009001500024126803d01c0d0b40341a1a04d61090100705140d400260180002e542c020243e600f00e0b0308d982004140a0290801079015218507254012640184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 280099721 1250 280098471 280098487
    0x60908030709050f100e0a0b0408030702040b0303160b13200111010b0604090216120507021c020f13200910080f0f130602030c09090105120706081b 65
    0x240045014681588503256196950028070900c2d040350281c19620135588691088030b140110b0720800c00540082004030100e80700e0f030905000c0c0d00290400c0b0f01c10703400070900104604061080e0318014004074021810014400b0311440501040f003001041000c0000c040768000804500231500d540d4000050b5511101c00f250900da114502c980c42c50000340617a13050400302406100b200345580c0e014081c2c51800d410400424081d40c0205242c0790f0086200c1c4c0072034040350641d003100c000c1c0312190f9075441d9100300c03500400030741ca80320080c4443e68401c08220383c0010303580c0c8011061015010354200c02028000b0b41498000c100d1510700030005000d1514180840e20540c0080c550720200300c40c502108d00b420201100c0030002150145002139160002c83c00c0103054106c95980840c00580704001c15000d41e4400041e0380058560303074080c0402052659241ca01515030030b001d0b1a09a644d002181c02a1090654900d0f051080e08207200340b2a011514442d01d003d140c10301d20103400c9005545401d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 280100971 1250 280099721 280099733
    0x30c10050f03160e04140703110d0203040b010e0105150a0f0e100903120f1407020406030804120b070305090c0f0406081207120e06040e1909050307050105011e06030b0d0609 76
    0xc08000c500015144c283c84141c00c1c90184034014407216552945860340e030312100164014007620903500b1350050180001c141c2051107000840c4a140300e00381c00c0c10254904400c4498417001a0409845000355010100900e030ba0341080e28803580c0c0341e281054150b02460029140f00d14144d59254000c81106001401260061050400c4a2184254a00c0994003482c212030720f404c5800c00100081e038070a2850110b003040700242200b10b000500c0000c2ca00e540b0369906210f50321540c04890450340c020364840600849140701c650003c0c41d030400b03004034508110780342d8840e02c061002d241b05400940b540007417034a50340e00c808098035203101206c1c00c0c82104c158408254000081c00c990b013074910f00610f1038407442694030050140e03000d8a10b40c1050700b0b003522510346400c000c3c02040c04060040d400c200541090003040f0072240140044c6668030720354100b0509460058001c000300c1c800070100201c504c403810302349000301e50b081e25002800000c6000080d0904e00202070240045013480300c0c54042c805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 280102221 1250 280100971 280101001
    0x80d02210114130c020a0f230616050a0f05030a060509070201020c0f150408071a15010f09140402160609030207060f080403120203060f0a082a030c10050f03 69
    0x421540403114071043c1103950305450030070300c0d681d0040e00001207480015a108040c2400d95110f05960142510300c0117029400c002c2c04c4050021b00d0340036034207100c410f071075803402e003601c1c0d004034078100340740c0010300d24050104683d0380032030030030030800000040401c261948454054940202000c0302c504007440002d020350896100c0700720a008404c0d4420000f00000350a05020541840e61100e6580340c2e19400440e8024603401d0310001d00c01d4201c40c41d001160000684036851550500346402d5484000405140c1035001240c18004d40020510880000c3c02007010880011a400b694a40c0c002400701c3d504124213800a1425003800c6425040503004501d0005403845580c4024810002c8401241d058000b500e0180224519000b00340b922442c41d001107a0256010307009000b005081008260307040d0043e48001c049401a043c060340806002540744003050010480e0310400380c42c0c0c00046d49078005c108001e481003501c442c1d800d2145000d0350503586285204199540c5a14100d040c42200341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 280103471 1250 280102221 280102259
    0x120304050f10020d0e0304140d0203030c0d0203030a060b0a08041412041205191e1a09010504051006060512040f020909060412110c010e0312070303060f080a080d022101 74
    0x60070a170085695001c00002d46040b10300408803100403c517101c2c240021040d00f5030080e60103000400c014085035100304005505401217600a40c1c0c0d07454101d9204c0104d486980054401c10030402c04081071603401000301c0c7c1c100c1d801c102e02c401c1034600d14500502d0f21248908501e00f0300d4000c9000102c140b41c001d00001141d0082c000d94a05503048021100500c200f0b00c0300501d0700185042c50ba0312049401e0b19140c801c3c0c4a0b00c91100315414094034408850401ca0754004280c0d1560300700810050140106484260300c3e6509008060410001400074052259180c041c641040c001400340024003911a01250f0064155209414074000c031340d407224401c80d02580c201c00d078a40e8281040b0301c40e03401058000c1b948005042c58036800001154000198001568940708584012010200e404020020188a03440000711135141c54030302802c4030150380c00350900ba00040129030208841000b00d07111415544001699484400328840c0d40c515111281c145a40301d0100100c2e542c201c0500f14800c0c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 280104721 1250 280103471 280103497
    0x203100b0a020709020d0f05011503060e090316060b0904030f1803080702040b0a03050303090a0203060115091503090f0b0402090a0b060412030507021017070f02120304050f1002 78
    0x10380318040c0140c01c0c46034214440c01640282803c0182d03049540c0903185040601402048103019017604506a408c00c2c2c02c00802252120b0415100315014481d500051001e03014241f45490300c54151500c83c001c603070000a440c5500c80201007041403d0740440a0204003c00c03460f241d04007818010140644400034602180f84090340290f03900d0394058003811254005045854002c15509010181c10303650b03502d94100c1030000f070200010b0018406180b10303603000c2d4001c2408040500400d4984030f01070303000c2040e80190001d03041c6004d6001c4440000d030303a0a20b1540d81c1003825050100e0003011a41806860180811021001c010f0004503460240e40201d400d00e800e526401c55010403030700070041d0035070b10031000c1004000b241814584200002d0082c24540e041c900c25402064080c4c000043c2480007030f070340b0a020b01081303c000d00c1054228826140c006501581c43c0d0000e0350700c0758500700c070014072500803000904001d020443c6c41d01c1c2006210075103541101038012900a034200c40c05107199 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 280105971 1250 280104721 280104751
    0x16080304030914030606222a0e030a020103150e090102120a02130e060103140f04021c0506060913050d021f0c08010513020702090f01080105072d110106090203 70
    0x41e0b40c0c2c4142c0e0030b455075480240505000c3d25294200080070054687c0760b0b03000311402d8100517901d0218441c14007204e00310500c54030400005aa441d0015212814034070a00544c0700c5007080030349000410740389941d420f090000b20070103055181201d280c034550107121504407000400038050780c1900a0020350142522440003900c9201c615010380c00b407220100075400c600d0004204944440c070610750440018180080c1c0005640c0f600081d03400704075030f00070f41c0b030034508140400c40c1400c3c4500c0c460742201042d8003003003007142d03518143c031a040501881d03c1aa040300103c1c0c180c3d549038241d80c0701d2075404030407940160070640001c0d40361050381810b004178040f00300e5400d01c450a1405140f4084101d95104006c1d07a00b400100694081031002042c4055400c2c013425005840380498036000b243c1c2010b044d02c480d0b150581440c203448004013030b00200711a6445040d00071009400c07403011421040041280c4448007a4111906201503400721040d6007005c400042c0851954000c40c01441c407040c030090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 280107221 1250 280105971 280105979
    0x3040b0d0f0507320d090c060203070b13031e08040308010f050d03140d0212092416110105012903100e09010204050901061205061f050f160803040309 66
    0x48420455680c801300d4130849140c0c101d440e0911000901c0c03458240d02038240b2200c0c0c034403410075401031119104030075903c0c0b40420901c00c8141254006003c13603c02035103069800d54841c141d1070300280422000b040c0031248141014025803400314015503518540c070361200c0d039000041000b00d0980e0f0a07070100d8204400403800040061a24040c1c50700a070914420390306a907801c0701c050b10081458441840b0070312060b181545d09000528982000407020b40d140d081c081901805c011802250a02d000541c4c0b00559110041c00d0200781e202828071500f8020071103107601500c00400702c05051510f035180c0400400d03040d40d41c8100640c001381035100c503641d10891128107107251009560100007426010010407403c2c400344003080c0d0242681c4009420140d4034000b10f5403000080c1c02880c08100c2c0b104111082104a105e0345034440c204580c111301c1092030009140a112180800d002046800a0080e902c1000c1c10121552103503c10f8944890140c04c2c28000003d03041030301c040703001810b8280001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 280108471 1250 280107221 280107251
    0x20d170a201903030f2904051506130503070803041707061409060702120303070905010309081b19060225170a140f040510080f150a17070303020c120a110402090303040b0d 75
    0xa0310824540c2051209c040418003004225009050083c582d038a0001002c82c650301c0a2140a00821800c0c0c01541c4880c1409040406c10700c1c170f01c1c0306040c40d42c000e810804c6a107900c03040b00a0030b031200d4440c1c199940c91070000300d04244a4900040d400c54028225035a01c5413001000394802d542641d6030390102511403004409442511070003030140e1a080c40007d40c8070007030b1911640f40c00c011004407440b02c842001100500070010b83d05580d51680421003101c400c03072149410500c02c511060212200304659030741c012441000c0f0075951008804a0000800c0c0d008014887c10b003c288401c4a440318280d441000142d4482d0083c2401210f103076031009803081c010101980a029041103040b042d40e6000e05214039806003100d41c6520201c18200060000c0c5202c400c260f02685407070240070280d0a600b4003a1601d00552480c0703018014004a1583c2c038000030840e0a682c0b0360042c90002020f0310303840003401a0007004401c56050000180c000750704031501c8000d08030045c18803001c0c40740c041d4900c408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 280109721 1250 280108471 280108481
    0xe030c1801030206030603010e1209010e1002030a030b030111070b01030c050405060604120809060a2313050f0d0606120c0b0f04030f020d170a201903030f2904 70
    0x194003240010041c001032070207101a6502c200081e000140c0400e00465880c50152450311405221000003156041175178024105a00c2000030380b01021002c03011503000b0b5580c820303185010f00301366032a2100d02c0b0a940a41040d850101016001c5890b008c050500c084c05080c20321085500e5010b89000081c20f0500f4020326101d184c0041255007454509044034a101e031524100326501d50041080320521340c0c414015086501c0f45130b9a14800308400e40c1004011f001410300c0940c44182030040b8826008140c10500540f1703416102026149602b00200d5401c004000c8020549402c140001c00c0500d1b1201001c43c52900803841c5d2032260365282c403046a50f120310030342c1c440c0c1494108020300200e660036020321391151000d018034210410075202c540300b0070013003d004901d104001440c6240b542d0f00280c004140c0c03441c010803501c00500e584549075a00c221a26554102081070700240516000e64818a040c00c0390b810140301c1c100030210544903030318400900b100c00c1148010654558101803241e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 280110971 1250 280109721 280109749
    0xe010806040f0210051e0d0b0f1011030f0301030b0f0c16020108130f0809030f01020301260307051605040c030e0a03180f03050102031509040f020103020f190e030c 72
    0x1e54540031103400303000c444d00c0c116800b41c05015040092501e20100b03100718400c02990f000b17815071102904101a41600c000042c0c0a106007120f124075000c40c2d540740c411070407950751030401900380f00080c5d20031810342c0284d0b018540b490300044000020710040100040c03041044a48910a83c0d0f00d0310001e80403401105a840c100e0103c2c3d043c210019400380c1ca00320740186440081824000195031810001480004c0486205901140922140c00d041218445002c40d0308001d608640c10945403540c40f800808001c0315503a034240480d071007481c09000300c40c406138011003690301450324911020310f0451940300c2c0c0b0703025614101060040601c01c0c4200710040000300c018003107065458500704c070f91020f4104064418805a4000a141d100f0201700d00000c5126800140c0c617480d00640d940072005081d80b000f030003110750408020003c1c0301c4080c040c0c82d490342401c3c01600c691b108004d100150207017060344146030038542e407407400712038026005604c2c01804404440c0c5103c4210140400f004c14512 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 280112221 1250 280110971 280110983
    0x201090b0f1c24030b01090908030a02070618050a020a0509010311040c1107060c14070303020d080c04090e0f2107020f030a0816110f011709070314070e01080604 71
    0x9901082e00148070342c803158840480c02240e07120440d80c25503140b0303a5054a11880d000022410020407203501c0d941030050480702010400d1710182c1d12003080921006006801880c2d0024002041000c13540c052490903d9000d41004c05000606e0010b958120480c2c059100d100c0350b1078001080c2ca0700c496814142e95108101e890014025424400030f404110000014405118140c0041203400c00c05030000f00020341e6011b450350040d003042c6058401700341c8920301d190000101070003ca600000c03013502043c11031804003010358030f810545119002da07411200100307040c0b460795400441e0014000308520500c0040e41c080b07624464040d00c1d101086480d108a5140a03c603920240c82d100322a2103011101400b62441c036441d82d903424003203030b00170689150041d1592151809120320300401300c00303040017511408403801c81100083c10100c00a101d01011400d11000521030900506c4110011a4000c14070780040b1044400c1e0b40c0c54154a0080402c00c24484000280501002a0581c06150805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 280113471 1250 280112221 280112227
    0x504020d060504020a030605280c0207031203060803070303240302030c100513120c090504030903170c0601090b1c080f0705120d0c0306062309040f09050304030201090b0f 75
    0x1030784400141100920582e40708842e07401c00000700700940501d0f441000030146250b18411030006a51905600756070341144c1c2d91915170706003441c3c2e40004560007560782000d290301403040c001804a000c3c0c06550032041d0303203000104282003015011b0f08070001c582912a450901520310381d035021030244e0b15100c040e40c10380c00250420307a01e00700802814041d40f000c1ca88503103400d0001e4541d5440000ca9404007018009024100e414441c3c150802400313008408401c1c030503418151030007001001c26010107010418440c0300040c100000704110b0700122240d5082d60b41541e95814004010120140c07520301031400020a1710212007414024000c0503400701c0e04a080010048150f40c19030051882215184109a8280071380d034000030213499540858000841d80b161050001000d54107964412410f2207160408607000007412a62810010041410707641c46110350400200602900648840450301e41800d072020311401200402c1500d000b0380790421116920004104180f08441c14407980300018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 280114721 1250 280113471 280113473
    0xd0503310b0601030b0d031b140703020f0d0c05011b0b040c05040e01091a0c040f0312020111190c110a0e0103110f0105030c09010e06191101050114010305271f0504020d 74
    0x160b2555200f940725550b0395404100389030b4030311700c628060300b60b03208003078ac0f221000700114039000401240f2801c0c142c1e011320b02c030241941c8055051010340101414041001c00c0003100c4810302ca001c40b041500442c4410741c9040a00b0301c1c100c40103503405224011424943e00441c0725405006aa1600c0d40c0808400d215110344a903503e440e0340c019007034240d100d40c100000a00c4200d500750340c1005d03601440311001c080040c1030700607084030803940c42e40507205414810a000500c1c2c980e000c4544031460308190a4080305460311142030800d04903140d920503085100850340000c11114a4180c0c1d02c0b17040c00007401c007083c82c1081030000c1c00f000b100340018070801c002807030445880301800c0c08680605101c80388002143c001240c540090071408502c0c05440c048182c07095000001c60210100d010080215504203007807000004807440029040c19211008280150382c0e41f1642c07010104d81c01854030b64904402c003955200c642c441d011111000381e485400c802c1c11480c0c844c29014560007441101c0011071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 280115971 1250 280114721 280114727
    0x1d03040b0d1d0a0b0a0b0405060906060703030e010c180807030b0613090204020d0209011b110d1103010c050403030801080705010c17120c030a1a030d0503310b0601030b0d03 76
    0x202c42c40401c444211600403032070030004010f40c00850384101c245000f13518200f24020210b40d2040941d0748070b10b080c107040c000079849508540780c000c0e500f0303512150380307442c41d040580107803c171242c41c00c40562070100a01111070b40424080019100c82e20901c03c1c2542e81c400103580d94071140005040c0d4502903000c2145441c080041800c580740040340070036109150703000241260885060703640c160760009481c640544e400024078032200d0322005e80d02600c2d11591180300b0000401004c031030091400d10300c03140503c00c18015480000c540180240824029984010605e810030301c0304401040c0d002c00042045e1601040349000d44106039104080a22181c4412403200b82c841211141420100079111030780e2040d1903800d00c2584c4c0040e1b00c0741e03281090b40c804000c8400c0006040083c150151000b481c6540118501850b09000c4c58600d48076129000c91094007403030482d80e041200c600c4111f100400c0302c040c8200b241d96024040101d69642c0c3c680042d4240d4201c1c120b4039504c40e2109a100700001c1c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 280117221 1250 280115971 280115981
    0x50a052d030906090109150206010e161710031e06051b0d18050114090c0f030a02040c030b060c07080715020a020405070e0d05070e01150816120f1d03040b0d 69
    0x81498a0351b41d00c0d960392901303c0e40c1c2e00c400602d0401078101c10014058145120100e6810008403078070044181d0b0010701c01011001c800601311624071a840c0845c0c066092181028040c6801000c6401e040030311495100d00040103035002c44480342040b001829500ba0341000c82d0082440c2c1c480b40340742020340a020b1000f060700d08044504910118003c2d0007043c1d091181c5c44004600740a10846030402c1640d20b860070011008507481109a030b220301100780c50108500002680c1a0f5011514454049064003d4800341048076005480456001c41c9444001a003400b250300c81d070203075800542c50741c0400540c59107004403000582d000340c01c6480142419884154481c03c10b107041c0c1c581a080c2d00000c1c0200d000c00f04192071a90003c0d03410301070081c1c095822401001c2510b19840304d4090180050f060a1000340401291116400d26030b18042c003c1811184002c0c51071020880704200320b0004008003603900c0b40300100f1000398100036102d01e00004072001c1d612126541d5090208014940300680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 280118471 1250 280117221 280117237
    0x80a030c03020304090507020a060609020306030304330f1b0c030b07030b03010c0309060605100c14030f030f1509010e0a0f110f0913060b0301050913050a052d030906 73
    0x100c820040005c440c0300300c1c030800f405460240d01500b101625404d228046d83d001c0e41000b4201c1d4810424000d4a03607000003103400f129001c0c040c7d6180b0b402c0c4c40401d4601640708442000086102d04d90070705002d0f40c07003601214240c003140c4865103140960340b40300b0800098130030014081240c1005c00d001040d40409220780c406540e2501190429000012a09440d400750a100100740c44458540c1042081c0c01090040c0070f040da50844c0c4215203020003801c82c00100405040c0200701c1005043d800d800b030045543c1c42e500d60b000190b403814001c2d0300840589007199601c0c052085038802e000540b41c0801c2e494100c4044002e101403e485802582009240303848084070080d0360f13216184a0b0448440151102040920300161076900d403a0510031201c41050780c503207031a45012018400c02c0e8102c0f00f6a0305454090f50b030581180c0e030f001d510140d40b41c0e1030700006d4007500c2401400c0c0c04005000130035000403422190b180900841070500b072003410a21480c064040d13001801403010301d040680c00b1780120 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 280119721 1250 280118471 280118473
    0x10c0501090f0b061011060112020a0b040f090b0102030c0c010809010905161a03090a080d020f070f021021110909070504060206011a07021909020c0c1207080a030c0302 74
    0x10300a40d1144000031041c0c0b4111a2001c0c24403c1109a1030700b511250320003049030070440010211604525192101409100000e40350000c1a40954903010300728005003258800032a81c0b5a1501d0070000000c40034425005100d09100104620f948040280c40280c1c820500910b0b2404030032005460000c2d004100c1c8605641c1c400741280400c13800c004041c0403800c84211082d0003410060034a16528000304022000d400820500034040d00c00101110380302d821141040d201c40b0b581c103501000e8031545041080391000030488605010034101c0c001066442225590400541150155900035000084a0800306001d034400050015500f14800c0c50016550301440c080300c500010343c1d03250707050740d11000041001c1828085241c04016080c090001e0030500d03c400020451140e40e10710404ac0004e000710f8888810010340605441000090b102d05c000554580581600c180d43d1000c0c880c104502c03517440c0c9101c0b59200306010441e00180c40c052000742040502548041d100041202403c80c11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 280120971 1250 280119721 280119731
    0xc080a0801051912022209060203040209090a050703060c18060509030c0301200702030c09040f11030c060a03180602041205150402060a050c1609060302130e07090c02010914160b030103020906010c0501 88
    0x1c1010314421f107a4002d12880300182c482c282030061082d000c50017000b4902e2070303000c165000301040002800c07208076548180b0210b80c8002084040b114046204400135030400e94007004100305400c0406070401c550b0035030403101c1c1600b50004040c280e502c41561ba48083d1410f006211202c0b86900003042503a0001e0201c1d8194201140401c40341c40003107c0690b04c00c00240c4102040002910016074418000c03001040702d0400702002400620a144100d414547e458a01310510b41070700442c00303451358110004640380c1740da84017170342c14078030502d42d003103400e030096480c2600300c410348800c1c0c0d0340540d4025020904080c2e5115050700c181d03000c4451851a40b10f0080100c1c00c90040b0584c00025000f0707441c010910314a103105018000b0000c7d41086460343c01c0411a114904000482108656003d44042811000390000380d004150355003000d05555001b10103489409c0000655003000307801407e125103034650b242c80607005030000380002940701d02168086201903201e0320340385d100e2500541c00094 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 280122221 1250 280120971 280121029
    0x10f0314040303061d0919030c0209100807210623151219030e010905032406010504080c0607032d080c0c0703120c080a080105191202 59
    0x24a110807074040340060b40b580400d00400e40315491140b00620448164120340c1004190b40c1c2e103880c0014038161601110104410a041c850030148140a40141642c2442d05003002d2010b00203031702e40500500c0e8440c89000103801d800117030b0010b4109000303006443c1128103a80d1568003900070988a01e01d00900c0742504a50f2159410166010f40009990400381001590a0040000442c0000d0302c40350091600b1040502010681000300caa0510b4100c44030002d041c0140c8125060f074005070740600c1110300c3c454900700d850880d403540004001c0c101800359150001101c651007580100d00aa0308102601c2e2114102074020b408580d129041115141308064544020f110006044a50300010984c0c141600740c0c010505941003100301d01c9d12843c2c0005c170440907686402a00c002480040d1003000000a1880340b5450103816500014403661841c000e1402843d091080c082c9902c030718004180d0500705025400e80c00215031482c104080400c079140c00300000c0003050704078007803220010040b8403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 280123471 1250 280122221 280122251
    0x50f030408010b190518040201110a0303050604050f060310020a050418090c0504150605030c070506012c010e2208030925060e0607050a0b1915060e010f03 68
    0x20025044030400003c54035070810030801903910610102966800c1030304140525180c100d0310002c60001c5809140554482d031004031810100501c24009501407101c50303904240e0f15070400c0e80200d82c100c0703042c400e035100c2c50081602080141c401942c1a48a1445a505610150094180d83c04141021820596a003801010716a1030554a554041c0d4038034114007001a1500c10401821042da8204030700207120b000d4140c0e600c03070350141d03000b070180110014130000417580842d03080640c0081618140d5030355070f100d580e25428402081340d04562050b5104211031841c45800d04860800c000501c0070f0319071200c24101c0310540307604c1d8001c5a0500c103160b004140a0300040d801303807e0381c40040c0350b8155214045004560304120754040d0200c000d8041040a40c0074a180b1408a070440e145903a07089640b500900d0329002020040810303110801b040340c89955150585401440840c0030303c2500212000203412509502400000ca0006807604c030403544180104145424642000070f084021000c1c84 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 280124721 1250 280123471 280123477
    0xf0303030105090723040b07030201180210210603080a0801080d020325021207051504030804050906130e060f15180c070b01240c08030f04241416120207050f03 70
    0x2207104410010b208d0b0205942480b80c1001c170300f08902e1411210703803158005185000000d910b141001185e946010410141c0b001201e495220400204809540c92070003101c0b541050401d0004581464000900d900c400310340c00d440068664095440c007c14401203510b13042d40c0c45404ca80d4000e07142d0980780103842d014900840c0290110082003101d1815040110404030303c80702501e00c00040c0700400c00250140266010b0790001ca9500100380e41d00804a4901ea0702e4080a50080d8100000032882d11030101d00315001d07a1803503060b406141d03a600d0600c11300000c11100b0641000f119660708511820540390a9004900001080e24200302511628211102038002c042001c102e9014070704242d400615240121085003802c59060b5801c0e154a40c440c04000c0102c102400a1b10024003081000c0e04402e40b040005100308040a5401c10003070000c100c0d800b0560006008040810700802e4603001e105801300c1c182e990080030f0f030700550415002e90010581106c181c0300c0c10b2403c5001403024405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 280125971 1250 280124721 280124729
    0x3030702010603050106150918091a07030b060408030315122b11030d1112270303060f04090f0f03080703060b04050d1214040609050f030303010509072304 68
    0x4502d250560503c0307404c403881c071340c8402c0420003200c00d00100e8940003400720040b10741030148038184890402030304004c2c158208008280b002000c995034000e0a200a1082c040c4185940400006180005208442c86103001e0192668001e1000a66100031002e001c83ca09074082c10707080708803c13061000e524080c010114000c0601800c05183c5224000b040900c224142c0c03458104105000380030310716141e00c1040396044d200d41d1121072068a00706000308440c0024500c451a011031714119502802d00101900f504d103012585c2481e2951360880003041e2800b62000404122070f2004100422000b45040c50741268007403450800040032581c0300760302250702c0c1d0280c1c46610240c81c240340002c0880b0110b401013070314880300340400d01c00b54072441d084544060340002404070210410340203071604080420106058500054041101d0707500c030318100100c07501580d241d0444141d0300c3c100b40d01c83c0024001c130f54200d0040c43c0019803052103166440c01801c083c0c2c1d140c48404071041c0c0780680715070060300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 280127221 1250 280125971 280125973
    0xd060203100311040203071e0203120106050c06070905310203010605091201060602120702061905040f120b0708040f0c12020a080d1e0e06070609120503040b040204020d0e03030702 79
    0x42040c0606410010002e0500321011440e516001c0d4008d84000140301010300d4201e0b03d00b0445080700d0080044901410342c0c02140079a560b518240109582c0c8000344501c014001c407400b085142d4060714075402615401044541b10301c0c881410650303c1c405803c00e081c101c94821400204003601880103501030040c56841c10b5507040c07004c2c280302c0031103a207401004c0b26a14200b8100103090b03012500c2c046500b0300c040c040e42d460b0203a00006802d40103800e02184110605060703400080e030044010b000b102c0c407100c0402642a54ad014142c6244d030b2020010f09464950000a180b6074421942254494840c1022365031580c20368070ba1218050083d00540020031b5210b5044095160444c0c0120040c17001d9001040f15180342d13000140740a41840c0030300c0340e40c160125001401801341d6000e000c10b80c2e0240020f0384800c01414002c025000da60320540d103080840341d0401c2c0c02403080003200c1c800c58100e420000d564803240c1c02d210003513000d000b02c1c168087d0b403a442c2e0716001006100860207010594 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 280128471 1250 280127221 280127251
    0xd02041212020d3009060f0506030f07031110022e0609110919091a1207051e030309101106070504051003021e0f040e09010504080d0b0d060203 63
    0x3000b030303d03103944018071006200d0000220b8071510303441600c0c451401e28000c55a1405121306108070040c0c004024002c1049003807504240c0702c0c0c3c10079400305200c1e10003101103454280340d65031a00d0f200e80d25400048c01d07090410301440c01900b08000d00003942d001e288103c0720700c48080d006541c40c070101951250030080c4581c90030000110709000300c002078401c10104001c4142407200640140c85002503140c000c42250301030200c1100100700c090020540c40720309100400111584001700c4511070001c6104012151090088002c0003410300f041e208040d15111401c4500c4601224101900c8013040d40b40c4020491301d1801d8666042d030301038481d290340710960040099414035040080045c1440200300047c0010840c0e540c8042a04050448a0400507515008070038070a20b02011307042241440307100000c01c42030a4000e00004c204850396842c1143c4143c4800255909890055070f014050700424071a080303c148540d8000700f90604020155841c0680315543c01c41682c00495282d05120400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 280129721 1250 280128471 280128503
    0xc040306020316090801020a080601120906020310180507090e09072102040b030a020913020a03020307060509090a0e1f1503061506080402060f03040309030519060b120a080d020412 79
    0x41308012002e0070005000350b08102c08413000800141004203000e04110b01244042c046805c1c960002a9540e004203080d5568900812800c0e55074000e40306010140d1508141000c40c0342c101e01c80c150040c4100e540325100c0600e440300f00d0303107004009080c02040d402500000945107100340d0700e42c0c100032500a00360034800d0745801004103c551801c549030107a00301802e40b40c01603949002d401e40c04001e24501c4040c812050001c01d6a02c801600300035010711032503d0205d030603504400640705000c1d08036814025503543d00e070a00203440d41300c512444158043c40c0041000f928a8031121004a14040001641c400d001422040940035510640d5413950721540150f0f240d41003400f543c0600103500f40350210b4106a07004c01c078580311b13000d541c03000c01c3c0005c008201054420391003070004540101c01c495200c99111160205901c240208548140c80d0160380f42582c1009080cac1c1010031044030103000140002d4448981603403003802200110365007000046000d10040b04080c554a024020204c40d0000c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 280130971 1250 280129721 280129727
    0x402011704110108130204020d02280c080a120c0e010908030a050f090316030b06041821030b030d0c050c0a210602040b0f0d050615070303050c040306020316 69
    0xc0c0090000e40c040148100030105101a9600d0711000003840c10020a0342c0381171451078002c2107182c0c02588180000740481c044100d54010306640005d00c808a02c0024101d261030341101c0c103007800e04000c82c007011100c40100b0503100103441400c056003098030088044510480c03c40d080000020042581c1d20300420f05560b001d82403102600101e4002c6180008101024085014001c04020aa075000407651000d40b824001d030042600d04010701d400503038880ca01026440802c0700c49a004614040c0120010a410b912201e080b03130700414a43c43c412401000007032074802c080114401e1586031403140101e51003c20001d081d165440d900c0b0841c442051a0041c104044441c0d120f04c100d0503044148440d400200069141c0078840c8043d4003031000c13510308440640100d41c001444001c000c52541c0c0701d5165603000306581c0094840c1080a6980c140c01c00104010a9482da901004140b11290000f4040d074040c40d00210000c040744c3c00d151340c0b43d840c0783c240e038006c44031381c001031204a20038066160 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 280132221 1250 280130971 280130987
    0xf0f0a0f02060c0a0903111816030b06040e010b0702032e0f0528060810061d3606040303020702100207030b0f060f04060806220503030402041d0312040201 68
    0x1031800f003142c070700a501e070002040b9088034003010f0300e98114100100c00c981d5541f0b00c003110b0307107040f00750411840c07078250000ca06400c080040360b0301080c2447c03420001450010704880994505071344a00c1c0d00c1e400d2160b20110350304079120498241c0f0400854402c1c4580c1911100d00c0141c49040401c0d000740207000c000240c0c7c1e0700785c1c4420000c90921050115194041240c4070303840301c2502042500320058034400001c3d00c3c0304d500506450280900240644440da040242034a055132455001220403041c00d40d6074580485500002000c5510030070400c8810301d840c06000300c1c682c1c1c0841506515503004a05048040e81c00320701191340018940d0440c20845907034000f11070203002524480e8a140c4910142040041c4003084500d80440081e94a0341d80c004019045103001c4e1003007145a440383d0040303a60300d505486003002d401c1c540b00d80b40e5180c0800109110100c3c1d020f0061070440d261a805c2c03001806256824004d928000c804003040c00300104013404004010307501c800c0c3c0301e0819000150403d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 280133471 1250 280132221 280132231
    0x9190b06040509131e080301030b0906190e070902040e011d01080c01030b01030608150906010512030f090a030f050309010e12030a111905010608060901090302120f0f0a0f0206 77
    0x940d05000c02c0245a8440550b19480a4420500d004021003031802c0b00c50700c14036074540c40300b08190882c540c00340101d050155050fa449116100010b07140e10b460540e50740720841c1d0380d5024240307140052030000300301c1c0c1001c251003e201c0300b10380d001c1d501d42e1140310580c1c2058010f07010181410004010b01c50241c042d880c600212440703001160b50400f1401501c4403014140340e4107041e2280e003442c00c240d102c1e5000b80e004144031825540801d0701050750207403101c42a0707407000301c61103690300115a1746000036450a291a80310b00a518181c0004040382036600040d040390307804410340000001149140f804481114421005150344a10110002d0045058080100d0145030800100032000c28001f0840d14921381c02e08207543c100c4101c00c00a481c101c0303e86500d034041c800d0f5038810010014150815000d0740e041c542030340c4680d82c07a0048a402c031580485d003e00140d00141c1e404c0300324660280100b0a1402040c2405e103071a90751241c640c0d46600c0300c1e4103800043c440000354801960b062010316002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 280134721 1250 280133471 280133479
    0x9011506050304060509100903030c0801060f020706111203070203040905010f0b1b07080d020c03010e0a1722062a020a090b060c070305010603020102150702030d02071109190b 77
    0x2803410200010715a0000900080c035295807640401e552003c104000c3c03003060141030b000c0c070201a5919004024006540301000421085000840c620b4002c0120381803d444d036a0051810f5440e01c40c0071100111420b00e00e0420b4000e280c00e5070003402c0042e009500ca40d500d500103590b1103140440304002c03030350164019407401981c04030504c40c0d442c204088070154604000f104001640d040784a80c1025403030361101c64140b045840c000840758000c90781d58101c200890080181986c4442c60301d4841401d0300c8010035101030144400c0c944400400540320700c41d00c072030503156040254152003d1070318103a08241d011038142c07095070280c03034810900045024240001c0e0442d49080e64007084c80300c0c61501404000ba903c80c00004032685480099a0070034801c03004888441d51360307041c810300804850000345d0060140c0c0c1003440680e00901c03421402154154021840c0202e0085c4a20094002082c00c6400700c03010b0a5042c01980c0e0220410700500480401c2d80c6400d0b6100300c040121680b0800c0c140c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 280135971 1250 280134721 280134761
    0x20a0e21060127090303021201061101060501020c100c03020f070f1a07050d030b0609090408070501111c0506010c1506060801050d0b0112080909010f0e0c03040f171c050901 76
    0x101901c2c803040b26a00c0000c0f03050110752800c2e5071506601900624003500c003207151110000841c0d07035001585803085007243c00208409511840126103401042d01072903040201d0740100c20300030307104a17044800315001e44180c900c154414141030303051003a2035000b0a000d640484081c0400c002d403c14840311a40c01c0c5185078503003112a81c4140d21100040c00e10b000381641c078141d0151030f440c0d030001c45542c1c004c0100089441c0c500742c6022407198005010503900340d880c0140c7c0d2072540e40302c0c00c1218411410380303d00c0c1000c900c01d03504a20251500420342410414400e888200003982170522061402d070f5600b020800b00d04003040100f000e101644201d01c03582070607410318040382d400f00c020350541c0c03400c0f8154141c1e454030382040304080c0f059000050b00410b03918000540700580041d000d00b5640129074036851034591407950b60031030105035000360a10400c14000b0000418588400e86c10120b04c0440c541810880d841c980714007180c0c0c403111510281c4032010080080002c2c0b042101c04580c058035420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 280137221 1250 280135971 280136009
    0x10c020102060f0709120309080706020705090f150405040b1e0c0403060b060405060a02071404020403080a20161406030c040509040f02090a06051206090d03020a0e210601 75
    0xb66500015210380c000c20030b04400320b4481131054210501401581001d42c1400400c0c0c0703001041408a0300c590140c6008005002c242d1034800300e042c008a943c001d0007445a902c503040e4199014001400d20728503042c00c81030128650301e480c001c06200c1c42c0101e50340030852401a10310303040e01400c6050800310030800f0b0100089200c0310402c0d507003541c0d04080c4c000780080081c00822098402c03504044e61042d800b03e10404250740c0045c085007510101040c101900134107000380020380c050380c00300411090061001c2c00e6110300ca030503003181031090780d81c144500c2c15081102e40d040620b0a091a503818400329010b202130121500c40c41549802a0f50080c514902000a01158007407070049034410541712002c5418402180140040d0701c1d0001e19031149400c0085035040280320501c01e142c080d042c2e51415150004000c11000e01c107400c0e40b00070b02400500b640c001c030029031012421905000c16421004e076a80c54000220401080313038411003444a0b00180c56902c1e00805078041c030031811801c40025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 280138471 1250 280137221 280137223
    0x1203130306020d0c030603200a03020d08040f06030b0102070614071b14090f060d030c12050d06060f020a0b0604060b2d030108070e06010309050d020a060b01051813091208070e010c020102 82
    0x3100012307a19035801c4c105146100142581c08580e20182d03000190041e184103000340d890040c400c44510805042405035512000c2d0181d0f000143e1090150308a85802c100d0075024142d1040c40c5540180600e10b8180303a540d81c910815100d000d20000d403122202c0030b0191082402c00c000c2c9200d004c403880d4240d841c05c184d114454403001801d113801101c01c2c103424010140141d001410150b88118410500d551004005281d83c01c914150414070317080000005025006800100790540664003401c15400d5944a001c100c0701c1c040c0555400503965880021840030000c0a030882d00c10704680c007055082103d0010448100d4114600c19001381040100140d400015581085460403040c06c003882d074600e4010b0b0000c082662015040b40110860420440d42c0441c600704203e1240008100049074140111075a001d80b034140706800003000c484040034906582d4401058480d224085041c04807a44c03a031900e1025014040b0100d01e070001441210f5030172002c042c5403c00280b83c2090308013050340000f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 280139721 1250 280138471 280138493
    0x3060411090108010b060f0a02030f0d090308062718031303051506031e120a021c02030319020c3d09080315031606020a03180608061203130306020d0c030603 69
    0x147e000381d00004d070100304c01d00038030644070b15440d403541054803050003144400241011034030860000c0d200c600019130314504841f400d01c1e181110324a15400070100d41461000d1140a01a03d00709818045026000a410401094442c3c82d07800c8201c1d0340b616520b401490066124101100f0758030046c1006059180000d406400c2c42907240b200118609424406060141d01c65500801010002e0498070307264000076696071000d901c2600c54451000484101e840c0d00055415620b294001e00e2550440f004a8000e0010024004207031251325500d1071403500012070151421082e9043c4000891981504131643d900b80306601c0c00a115599265a8588992200400240464125070000d40c8543c038204514444211501560b15038103880f004065035441c110300d402c4001411242500042500c0b030000802150740030f4581955948644042001a954000f408199440180000d100040c056004c64000b14020800180c1c0c503544c41040c0e03410742e05d20050079014903042450800002c0d1581c124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 280140971 1250 280139721 280139737
    0x31e0c031b0d290412080f180c030102040e09060903041a0f0d0509071401030b09010b0f0f0d020712020303040b15030f030705010f0e0f03040b0708040503060411090108010b06 77
    0x10101d884489450558100e141c811003031441400c02182c80c19458150303505150007507000e282002e01261106404a80b2000200c2c1e02c7d8569400300307400301d8a2a00302d613072820404200c110550b4440512000880c0c00c80e0465405481950020310601090780c005019880d00211880040d516003420298072300b00341d00a0074180072301c40100003228070b001480d420a5907640d0003455001d0002d4100780741c0065861031603020b19030300c1000810940348203601a124030208844003828440d01e0340e10303040300131005400040d0403c00700402046503946603031064000f441400300140e001a01c0301024102611002400e19a580555100b0800d11006c03e924602d40c0b684240000611800200c440001c0380c182120000202018840491070404021041d00249203000d9240c00400c00389000c481c0c01c680e129018032642000e50410001400760aa60000402c12a40188001c80c50282d9403400f082c5000411102554548000c40011141e4602020300600412540000b44004010000060400e208003c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 280142221 1250 280140971 280140979
    0x1401080d02210c010c030504050607180b07050a12020714062a160306020403110a050901090515090c03040b150319060905060423010c080408090a05031e0c031b 70
    0x80d02002c85044040f181011074050091100320143c040280c081c007010b41d012507082c02071030009000e8621840000750020702000840c070820740782420410340c5a10416050300c2da8000c4440c0c00c00400e1410041c3c1840080c0d682c000c00300c2515101000c1e450a042c00e401c00d00c5504104081d201041034004031403911042003107600c4000e0140c0b00800d01e0011a48212469490040d00c0007051080c1030740948112805051001000f030a45401c0190b8944580070b65580b10701154014080f070a0303203038032040d48020040101501710092800140070744500300c52244900ba00041000200b2466140e001d400084000002e66540e40d1540004d44403400c60303401000400760079a20109001c1d0a4000940c440d030031600390740c1e103400d06050404200c0743c000320049040408030b80d02454043c05200d0031085000f5039640c440c03d41c55596451034598042208654051007d40b40401c10750b42c1403208884409030744400c0c41100390b104188a00b0015030760b103501d1080c1c225154900c0508600180c10340d012030100c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 280143471 1250 280142221 280142263
    0x207120f02120a05070807050103110c07061b150501031515050d171306020f0304050f04050901021c02090a06020721051002040305030904060504150b0a0201060302030f011401080d02 80
    0xd40e003030f14000c4581400b03422441611030005001502042c0310094800a1f40c0500905035251000c0401d8413a4252090f020750200f0720400610380b141d03007423108182401500100001054541c450000c42164006607011fa50f14010420480d42c601c070a00384a440c2c07801440310201070841d03000e82d8100d6108090050f40510700b9107003004024818001c04c8100092a280c444546d45e0035400e00700a00d010720340241c4a112a00c4500c2c0c0c5001082c1d60858400803d0005007a81010500004d040054030154044d9001e1140300164280c504179002030f00d8103d00010f8842c3c40c000c0c00c100d541c22550f400f142c25500200e02c00d00244107030042110040303014101390510301000d403902c240f07412903001c1c1c0c01c1039007440401e0120420001200805e10740d001100c0c00d10000762501704100440b00f07800c04180703c242900600b000120355500181100c040c00380000505140d403038001ca070800c3d113094280b00b1165552000c550b0540480c880150142c40e4080040080e04c03403501c070181d640d0402d0f011810a0115a1b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 280144721 1250 280143471 280143499
    0x20d11120303040506040201090b07110d0212010c02011a0d08250c0e01030303110c0a17091c1e020618041b020a0c0b0306010c02130b1507030207120f02 67
    0x5403042400c58995541100d07070301c0c606070030320507128030050718101e0028881000000d460310340340082d11085a0072910011001000a04008406491032800c980102c3d694601101e01e4200b07100b0a203403c038040e000801d80181c1c2e020588210356020701c10f503119041c00083c55020942c494159005124903200b205040c0c0031142940401400b8088010450282204c001c24500c1c1a16402412648681c82c01d0002256031480512280039803a2002002d2f030004010350042041140074032400041d0610031881d0050070000705051074a0038428080d191142502401003203400c00086280f409145000b00d0707881960343c0000d4440c401d86034107001c00310403c00da0b500660b40740d80c49443c00103031684611100c1500100d000c1c0d110504100c0944603413000d1140007031340d6035000044a10403041652480401011542000110f00440350b04010b0f199448610824035220015001200000004c0c201c3e2194100d2600a1911b551078001c904940f031040e039100000f5201e00200da1141da03040b01c2c04140100d01c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 280145971 1250 280144721 280144729
    0x206090d052505030a1106070903120c021f0905010e09072709021c0b150409020d15030804030210090302010c020f0103020d0f02030603150108070e1b0f09011b020d11 73
    0x30070031001d0f200e8040000c0c28a07016070025414400d070300c168000e0798103c0d9540b0006441d4161103120103446030284000c001c2c9000d100b41c1e0200d0b4250b2000340116500b42d0643c5c2100c400080720700076800410b90840c03041c4125a0401c80d500f40380380007141c0052140c80c007108020401d03048403c0d1b40e940b102d005a0300d2003042d443c7c42d40071000340544613401c6444000340302018070148128203200c1d40041c501003d041050812200a0b03074540f8040c814549090300e4984194001d500c1118082074050340c6014512070181c044101400550062140c0c90b101c508600420400c1444040d1400500816450410041c0d810110410b01c040d011250520b00d0040200142c020b07208a032500843c80789004140000310516a0240d40150401d40072142a0300d40d400402015000070301070281c850b40303c91803c010303181803901480d80c0b000b0107034841c0350640c07464903491509401003020300141203000304142480e544c0c09003101501034045403000c2c81d04120b42c1c001c40c025a4581c1d0019108404904104105482d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 280147221 1250 280145971 280146037
    0x30902131109040e010b090402010513440d051602061b0d0e060708090316060801081002180907051314030c030f07060806030a0803040302010c0206090d05 68
    0x110564140320086118002600950100540b584990701c1c00d415000354240500c100250701ca006045a0617503210f40d001528150002000c80840711001070022454803003289103202e6010100324011640305c25000d110348214103581d2043c0310070602043d10300f084400040d24080090355820f0095542062108c000c00d200f00c3c01401039000300340011408004081681164880c40724001030b6041104002c504555941232001680c0d8130400510464000c1100300c4002d0462040080c212040c6503c0d140f4208201c0003d0703400707000860130000040021110500400c240704111070f20452601d060b03800c0715030090f0034100c99607000385a00390015194502a4048948210100081c480f01c01c0e03071100204e081c0d000a0303640318024002c10741d648441d030074000356113031700c558258014221031400c0003400c50303008000801450b414460940c041c008074840038011401540070341c0c0041425091a00003074500300015208480c0d46d840707480d40d40c0040d0317406020b50340030050542044030000342002484075118 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 280148471 1250 280147221 280147249
    0xe03010f020c0f07060206060a0522050c031911070609170316020f0a0803010b070f021e01230a050903030c070b03041b0302100e120d030e2506030902 66
    0x14400030740b654100500081060514142008958515807505401c81c0c450f90181c42c0d0540055004100703122916248926903961150403a10746d203a0070b034024034001a41c0058846041080c000410702242c8125240c0103078204000b108284014031000000034003d03ca8a08040d041c15505c040c0141082100702070036089040c40e5802c1d0751a0f04164070b80b030801c56000003104015209115107100181400f0034280003964201c10301d2400d0da071800244000c0c650180350112140014040b1000050f5100801c0701d1030040c50504a82c00031034040009480e03060798440018031140701c002100d0f03290541c0d000701d13190030711075240c4152a4055003000c40e02c2c1d405041035031403c5000d880c0b00400c08141c0e070400b4610442c06211016181408043c00760400d145074000650003a03533244c60480c1083c012aa61002200d014154400f050012020030342814059424034001070b80340c4001e1480040704120600f0b00e80c1c08150700b40d032003840070400c41c9117208041c4034040515450f51a84001d40d030360f148a0007141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 280149721 1250 280148471 280148501
    0xb030c040606020f280305091302070303050a0b0405240d0b01230109030309090203040c0504140a06060e0d1101050f1803070f3f0302010207020411070507060e0301 72
    0x4191920000f949410600c01c1c04141d80c4600e00300380440c1003a48100c4c2c6201060031400110b40d07500343e10212074641c1300602d0f841d00301a10602039000720001e0701c010092140aa9400200c1e42004203084040d14056000c0c5403140d070401c001e2048008001f106410745a032910060b1128030042d03408202180040300c1c015280c0c0b0131240c00001c0c03100d02081d50482840301503568130103400c032090040d076840e00140409800640c0140d402e11048a880e402035030064051000c4540c200d585800040039500341c00c10a4020584040503c881c140c064001d5101500c1d003030419444040300c1f240428020707a00d2007800340403500450141e80e4164042c4040f150041e0030920700f5541c80081c2030b40c41d03204035030940c041402441075100c0001c020300414616010740300703841d003422400e181201185003010701c4442c0301c18110380a41c20f00106880380680f8a481c1500c65000035803980e070749004010880b0407854403841503240400181c400200c01150001c01c0d15200e04041548850b02004a8014002d0244c50010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 280150971 1250 280149721 280149731
    0x809040f0e0316151103070c0c0b03070c050609120d0b0a03060504050717061303110f0f1f05090a080307020a0503070b0916030804090b031005010306051008060412030b030c04 77
    0x6008206000e10744030f500444c480c05214440d00c0f50030044505441c400c2c0c00ca000107001107410b40f8403a1142c0000540641d0403942d109403612030842c49640141e0b004800b28081d100c10a04201050080c0b607804040311b0050200582ca450280505208580200c0c0303003550340e038204110640c0d6032155071000d990040400c000501e85450203642c0c4560f18010102083c0d28128900e41807080043d1a0b803080803038075103040078940556819140381c481585041228040d04130340c07030702c000c070100050403507a240391f0002d290140075a04101e48011444100b01c03842800c00b010000183c500140c0005116441080b1540d00c6e42c45030403c80c14815032210040c450f000c00140c070780501000c44102030080030020142c0c2c080000400d800c0c0d611204610000f0b04825080c4010410306d1074661094800d52000380170350303107234074070246640c03003110000d07001103c41594800c140070115002404c001c0103415240020f00c217504198403010300f40c0030410010700805071038011003d100e81301401048a042c00c00303841408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 280152221 1250 280150971 280150987
    0x1050d0f18141204030f020f12160f0803040b0f090d0605040b04030306090b0f19030c090e070b0f04050409140a0f12022a0301020705060a0c0e010c0809040f0e03 71
    0x10451070301140c690b940d1256480b030b81640c2580000710b070101e960144820b0340100d8035609000e1140d0390380e001d49600081e030140304120480e0034085140b010b400c19900d407500c44d040050b80c881d0a417903074120408503401404103000c0290000300300c1c3c020640b078840c819191244000015642031003520000c01c42e07801d1000380410004980b100d07034001da209440600c2501e441d150b094040341c40314045561b01c10703c1284e21050a040c00646581d10044c601c1c440e0740480d4698880109411032039000240150359030340a200c10389010b1000343c3c080e018400d0294980410459102e40501842c0101ca01c03580c1d46601000c1005031300c4241003090304c10344007510910516428095112451800c060307580e0500141c080803d180702166180c94054800c48503c070740079070185a48100c0c4200307000c01d60559800c0000c1c50101c6c0003000080e204101400001c07801c409281c2c8020141030a080500e1705002041d1848800203035590165100c804040d00c000500c0e001d484a00300117481c0c5400302200901001a40c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 280153471 1250 280152221 280152233
    0xb0117150d05030901080f040f0609080d1d0114040f1502160602030a060902040819020622080c030102040609171002040b070311030c0c13060801050705070203060703050601050d0f18 80
    0x400c0001b42c0f140c640f560341e12480740b1748003036049400410b45490040e86000007041d41d401500c0d05409280c116081ca504810404101c4000c10407022001c4c0b40c1c1c4080c4007101a003400f466100c0c1901001d00d065a04055590710080f00d4030740320082c032000390360910411031a02c0e03505550000c1b01047c1c41d00b05074001418900b000354419105c0701c00c510708040c030120b000c180c1070003160229400d410081456042c10030381c2c1030400e0034018040b03038026000c200319a07640e90103051014008128042410505141050b100d00d403000d601d4089010342d0062104000c603e41120f800380c115400b05881804500c8861151800d020404002490a500c0801c001c10004580c00203080d10034444e40381d01d075801c800d02070324036500e01a46090001c298424910b03c42542130030310132000300b4403100801180158442c06e0b41401d40300304070303011800100040b41e16400c2d840c040040540006441c101013100b420f026000174000d02c0f4210211001c2a1210082e81340d0031700d00d41c0224181e07000201041c45881007440c1207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 280154721 1250 280153471 280153477
    0xc15071202070305030904090c0308041e060c05030301151205090708101505240a120b01080f0403111513030f0203030c04060c02060408060406050412030b0117150d0503 74
    0x80d203886200286291506000046500aa90b0808004c50403c201d10701000013525207510308a40840035040f0000001c2d240380082c10281440780041c85200103011546100c26440d584120304011074103082c42c0110b0341c08002c80381920840d0a440f00020a86070091340d4181055a00000c041d24110800c0219000800d50b0000e695421040d110a42b4000d8114015a01204101540029411402c001c2441c100c200c01d074114a00249206408141030030340d1000d50440c56810010600b440004181c0000d030b4849d11010000c2400c011005084c07440e075181405400910003428401c0ca240ca030704440e04100320103040702401906094503032610b044c1e00b90030301c0307410076007140802c142981d1034940900202c00e40f8824221107601506142c6003079421215110321090503600300808000100714511300707221891290780200c0020807681490b2038101070202c00740562004042c42c0c8980c1d122030382c1e44001c164a482c41e10300102e100e00d440da44140c0300400c8207500d44030341c4a1314111100e0104440403003d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 280155971 1250 280154721 280154723
    0x105041821020c0a03020105030a0c1b06020315041a0904110604140a09090803070e0d0f050313050406050d0209040204020909090703140102040e06060706110a180801060b0909090c1507 81
    0x740c803500d1143c0014044900e04c140030090205030b062001031800291079004660850052510490f41c1c41000c905141005488500b6140c040d00002001100201c503d002100ca032820745d020017451039503044190803044a506624441c004550100d814030250513030350a000340008000a41c1c132547c0b44060400b1a401080d070a01a200411000a040d403880c4220303214a50072808a5203556981c00c000c4464000c030102581c0d100d0f07215868400492103407404201c0c218400c900841e904c560072040c020004040340c1c05035124a0a1207030910250711441e003402080c03541500c401c0c0305d5803507a10005010340604500a40c014030381c00100580400c00007051401c40f0b0090f440c0c3d4654461640225081c1d1151b4060b0941140081300404d44d5428a48001e000d502c5c010304000400c0a002d8080340d42d103500881100d000544410b034001d1114914079100300081a0031070082080700d1802140d59034901504601d61310400d210341c0018212041803040040310030b0010a0361a00f005550380070003d9400c2910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 280157221 1250 280155971 280155973
    0xf060f090518030412080f130e180c0f060c030307091706010302090c2b02040f08010e0709020c0f01060b0a031803090315060f150201110a0503010504182102 69
    0x8a00008082c00580140e08200c030040c514050500c00c940100a040810171946402c0c20850b004460303a9041c060319045801c0324144020600d4a410602c0c000c0015084202e15203030f81c48001090382300010341c1c8040da5000d883c415005102940000c002d4080ca145561913404000208031341c0366402103600058540e8692054240c400b41c240c00d07990303241d007404002d4022500e140072403c5c08022102070300e4a4030070b21094010b10021031004510301c4400038214506e041e008541803290004c2003072810003400ea2034008010356520307000309940d80c0307805220b81e440441e0700048194060b1001d01c09482d6944110000f40700d015035400342c0310002e50015006c04000303490705803003030910301d50200d1301000540c240c0d803128a0642140c807511024040043d01c00101551403038006100d180c10f1180c0002071503000e42e071706640b009020b000f07400d4844541d01c403131a00404200c031842464221080e00e0540b40c00b6100000c030030741013094612608483c05005004070031040040c40b0500200b048801034104558 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 280158471 1250 280157221 280157231
    0x303030c0e03101e11030103020a170309090c0c010207051506010302130b090102010b030d0903060b060a0f0e0a081e010e3403170903010c0906050d020c150403081e041e02040f060f09 80
    0x24bd41071461003103288000f04550001c0140d495031703250500c515a088000400c2191800007084245801c9030b07c2882c0c100c0b22904040c1d583e0104403001510181d002e5001c1c2825460030035000110080c3c0c1e01140904c00c144100410410001d9100354003a1003107800180c120754150105000c0030f081d10b200c1d44004c0b600d49040c440a03400900f403400940321041c0c2c0945800801c8580020191420300e58925400d030480c0720300b40c1c0051091003c00a030319800b02e278401164074502c5018642401e40302030404000ba144e02c1100b410300c28038400034600c214440c02c8010300c02d82c03555000c5403d0b0690f1003584043c0006224400c0b00200c0300011006048a80c0c04030020003c54240c5001078920020354441c100c007045061010050041d460f40007450303504004015921048518000320007101b40039a410340001f5450405c109801c800c2000344100b01090070150030241c035041e0340b030364051b0080306184850701c1d110140d80b00840d2103580108161100020301404155120801c0b584414007500c2000120b90a01d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 280159721 1250 280158471 280158479
    0x30e070905040b180c01050901030b01030e071401110601050a0b030a0204030629090c0307030e0a080a0e10031a010c051e010e150c0301031101090306020c06010303030c0e03101e11030103020a 84
    0x2503661045c070042e191141810300c041c00640081c04881c4209040c580c03216043c003090103003402a803000d411807204104036017810703000041103000c41d000312040350740c08400103109550b542080302040390243c1581c80d0b0b99680d1001a0320203402194002488241400e013603c500d40900d45a07981e00306a80146890090050410072440d5130307040e00d400d05041c8040011030400c5100f6004a40b10780600412100344000a0f40c4234407840d802004c00c030001540c500560f0541349802940717580c183c0e0451405102d141001e0182da1440c2ea003104046040c4900102e006081060611480c2240c0ba043c05c4111803006030842c2407406007801200d80c5006002e164100c600100109030311500842c0c8041c405801c44e030851303aa481d010a01d9804588c1800344c0d900c0d002001600a000606090712000040c0c0b800d5455843c02030142d40c2459080c0c030030720011404070001074400103019400070444035004182c0402c9142c01c1806009030f000d00c040b900341030170811851070012100460480780300f514a2101b540d69 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 280160971 1250 280159721 280159723
    0x30d0b10170c09040e07150305010b04060203040909030e100e190e13141207020301051303050307030c23070b010e041709060d0e0a050f1b01030e070905040b18 70
    0x18014114001e200e6400201c2c014010440c094640e105018000082c0340508419242c900b03405c59000d8011030603c28011104c09030f1501074240108440c80f40d20303050504100003c1c2d140e02881c05468403e550380d4000005040c031800f0003030034254003d0721140c0d88200020000303204007211100b99014030219405802000e12107441e140841c1c920780103000294a0b0301e454800b8500c00c2120030388550f02c03220f000c9a54002c0500810150000c8104200d5032030a80d44181402d4400080554050001c0c5002d0070012a40281c100c071707445000c500d40080c0c03800d1510b40c240c400381011408060030f51145010784030380302c48640003850383c0c0d0b000b0508005036a81e602010b0048040480b1300030840c1c0464440003140d1881440a010101b000905c02c0d42804038090003042101c00645601c111944100c020400740401441010200e00215010b000c0503031803614509064401054118105541c42c040803027503200c2070206001030140c0c04420300c07032414607082001d98013a00786c41d03070341c0121034412680d002746030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 280162221 1250 280160971 280160987
    0x50309040b0f010905060c0106030b2502030304020607030e0a03140a0308060d02010f0f1211070339020f0904050105010503060f0f010605030c070c03050f0d0302040506120612030d0b10 81
    0x605959004880c0d090401b480031039002064100c03019921841c000c070014014082451007205034550b0800f500070018840e06542c119141e1802c15904100180405a01d035401124802c6405041864092103c071012441c80031169002034010410740c141e00701503c0300803c403510030074040d41d100c4400c1c0c0c4a95003000305840c414400280466010015010007a000c0e0001c14810141404d003034003521201c465080a44620031589407084c840041e10004040e00043c0c41a00000c00303010458422980c01d2000c89088071050080a050211034600f200310f584030308042500f40400740500d10700c3d040038541329018200031300403544a405440c002490448078403a2251280c0d1200003005000d920380760703040c4e845a0028040740020f40e010403202002c85d0150324842c000714840c2d801003030484035803072880e41040b0481d4100c101305401008100841d40d43d000584405010a00001905032159800101c50100506104d0b10a00000c6a00c03940200280d0202c040802c040e10100c000c80e041354001c580450b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 280163471 1250 280162221 280162249
    0xf030106080c0f0303190903031e08010614070c0b030610020619090f0206130311121c02030418060501080106080c070f020a0b040b090f0a060822080403050309040b 72
    0x2d80484041c0800b4034107a12203d0443c2d8000c3c090301d143c103003552016074100b100500304101203030350401c04004241c0d002404d100c15000f45481002000e040c05c000400c0342406102c0c3d103040101600b29450418210303011941c90781e6010708c65001c2c45540e0600c040c5145c0080f0703411841080654041c500480c00070410702d00c5050b8040c602500c4440200f421001050251010344d10100c3d07050040b0016150300004000030b1034182c00c104402495490413000b6891441c00c0c0c0c50180300f0a0241400300000020390802100c802c1d41001c5903030185600c00c900d18012688010b0340303403010448280000c40d85030f000b035040e500280d9644032103a0301c502d02a074240e601542c1d0140320381010050036001c1000e10003c1c103507007072004000a10a50381d400c40008540c0058000c623a0a41c4d002500380010324010200000c1d2031419155013210607d440000303130000310300a15294514001c034150383c0d595150044428481c2e80d00440b0142c9031074484c189940c1d250070150080f8003d514050b804605480c04c620000c0c1300c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 280164721 1250 280163471 280163473
    0x501050303040303081005060a080406050114030a0204020c030d02160507060315030605040c0506030703060801060e0115081308070804140a0e16050c1e060106180e04050c0a03030206060f03010608 86
    0x803e01d155400c0795000f100030715410310280e030008080b640340d0f80c200040928030031030341d1480d00c00e05180c104001102d0042e804040709d541c0c5413101881589020590a400c9a011100142c894030034003901415445403182c6408550b100150b01021004445450b00a035400351085401c84da40b01c040644c200c4807900d441807841d035044c500070800104181c0006600504c10000f4400160351100802c580e50825a15000440c0c0c0303542c001e200c1c00300d0900c6084001c00c17205203643d442c0e51501d06080c0d030201e00700d66014200b11141c000940071071b12170340d0b00f038074a203a1205a007980c0e528035003000c0290b90450b002c0e521303552100e00d201da0b40360329144402d44103540649241c0301c2c464a07000820095885509100d500303000d400d1100001c1d00c10184031300620314080c01711840898500490203410b0010580100d01400100e944004444003066850f07400c0c0c4182e0260012a5200c40c03c00f145825072600c201c0e54003d8041c2c0c0003000f00741c0e012030158002c1d80c064520703030b004401c40e00c209800c6e0340e8140109601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 280165971 1250 280164721 280164727
    0x403020d110c0319020d0b0403121a100f0c080a051b010c0215100302090f1506070804091d0d0210060909050a0209150303070606060f05071a0a02040b040618090501050303 75
    0x41058130031203042c0184014100c101c15600e40d621801c50400880b402d501192515039018030705c0c2d109004a0106c01c16410041c039a0b03000c00b80002c1c48480101e40d13580c00300145803802c2c04070b180c003459804000a820003603540d2500d00380300008115a0104151882654402c0002d012645050151100c00441a00a0300c8002800715940b240600002d1008149003050b0200002527154441440d0007008201c960214920b420952010107800300c0ca02c0500880e0204103040114102000380c1d800c5d10455140403602d003c17107801a030b4a940102d4400f0719507009600708a4403c1d41c0001e8080c403d000c401d4000d01540c3d0b030314182c04049071000c136009056074006004400051403d00412035001e0107041e01c40591415144c0440d20b940c024440440d1060f0b03440f0030030303c1465040082405000240d1424510300740c1c1c240e50300980c100e100120410380441d444080765400c2040e4041e100a4020300040d103803910384c0c81200508130004c40d10758018140c43e18038007103030f150140d00a941c180c49000c2c0003185 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 280167221 1250 280165971 280165993
    0x60f02060a0c02031c090b0705070807060207080702130504030807050f070305031902041e21080304050c040e1b040608071208070c09051905090c010e0103090b0403020d110c03 77
    0x350241034504000c6010402c2034905d40c800c150381242405e40c0717114001030840d8851820203a0000c0103003442d018880240022400165a10121011103900c81009030315007050346081c0c9024007807a10000d5000c2e5401720b80b03409040076030740300b58410b90003640d40000c1c645600c94241c6540c8a4038102e40303d1600c04000c00b03c08240618025074100300c000d40c1d914240314041d8100c00881c3c100380c0200e10f0045a0701c0c0615103400600c5482c0e40600f580324184420090250010441d14164004c001c152060200000341071007814000c108110a000d001072080b0038a40801d03640b0780a104a0035403c40d01190040b146904051184000f41c442c40001490201e0130101d4852040303503099400c03034204408025882c001010003480748002e040c030080100706810521208a0490039920b00450700a2a0900f084051000020103211b140400c0c2000c000890688004802803c00c00301c0251409a8580c20722081650001e610100141030b0754030321842e040200340d21034071082e12460a0340d26a0254152070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 280168471 1250 280167221 280167241
    0x380f06030606012006131203021303030c0303151502120702030c01140d14240f01050307090e090a0b130f0b0601050c0d03090c150c230a0f0606060f0206 67
    0x1801c06600c0c2240241d222030034445203460720900301e0b4846072852802d486c1a08010503c00560316074174083c2019402e06403600803691080140344400750401014461403000d1500aa02811000e0f142158003104291650b80b0901c400010707240d80d04c01803151442c00c2c5200c200c20410784000c1507006025103522005d9100461701e041c1102c201005940303040005a00300e10440c41101800810f42c02030000d80c1ca0918400c1d075a0842d101078084007114284400100f03541d4142070040b40001c00d080040c2c81c0d4640c51012540541250480420120040c0c1840010500010202e00d054400c13115030320036954009080030b280108807801000100c041d4520b000080354000020390101d410301d401810000144036aa1501104049003004695100d4050081c00200300410380a44a441da900140e5543c4405c01442102c901002510001940c20100040c60841060301c0d030001350503080355000c00170350800e0300b1440202042101c081c0d1401400040c006d0103010298550300c1c054001d8002d070f0355032110b10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 280169721 1250 280168471 280168487
    0x60f18031b080a050604030215091c110d020303101707060503070507080301030f030f090b0f091c0503030f060d0201090506130816230a12380f0603060601 68
    0x441a01c910100e1414420421980ca09000340d0041a0a05080c00c000c5d050400c010341c042c21041c40a010001b1201001400c0c41c40007820071b040807043d03100038404036007030780c05101c2011050040b0301c203400c012580000914005c0c0d15241a40688943d500e1030070400d4207401d01d4000442d04a444204011805280a113512620608055103007100130341da03072403150740243c00842c1d03c181a141c3c00f20505910a1b541041019141041c0080c00e0410a18040d54000d95400c280343e29000151410582c1352182c2c40c0d26600040003403880d4202c42c41c500540c4a4108688805a08265800203000343c0782080c3c0b0350100640607111400c40e50b0a10702030180030750001000c80301e03602c00c546000850300030410841821100300c0107240c083c1ca0921a030705249000e80980d84c0b0f00721942108410140c2e4800d24010700f00e40744492110001000780c0f4000d010070502d941c50007074002503009500822081c0b110b01030101080d12007409090f6550346868008031710155004ca03015484407000582550041c444 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 280170971 1250 280169721 280169753
    0xd021002010209060f0c060a050c0d0c2001050702060a180b0c16060b0411120c160b010e1608090c01140403060501090b03010b0109060c021003020f0304050106060f1803 74
    0x140c50104020701080103a408914a1811000006481079541b6024414250022070070001886141081101649580102c1c8400d80f41640d54052911b4001d0064444c074204100104c440c02c03100480c6211180207042c11240c00c00940209400203203020341038811801081c09490f108400f200342c40e02c4000303100500500b0007103003e108000d050041c1107040d0500c403605209003004180c12900708240400e80741c0003040c80e1070b90b420901c00403c80d51400141c0c1d6a101005581030b030307210302d5045140406038a4641014149000d040008a0465000d09120b4880d1819002401070701d40614000c0f5400c640c02c5503444c0c0f1075000a4005180e0703600c2105d54504004030503032000c0c00d0503141d807104022144280e01180d91581c2e01d50702450302d0305082c0030f4241c0c40002401c088042514002021304241d4616100920504e9002d08128a450003075041e2031034500758011881d201d07c0d05203802c0d03000341083e000342c20109008582c0c0b8440c00348945500d100c0310092900740b481d001c0c13031a51015480400c3d014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 280172221 1250 280170971 280170973
    0xc06010311010309080d0b1507050a0b090a2f10050a0f1e02061009020a050403030c030210050c12250e0a21110d02010c020904020f060a02010c0905030703020d021002 73
    0xc1800007154000b0046c000300c0342c0003040015540c0411040040b84115050890f40e1400144035210101d440482d4000c40107410600d99203860340e450079a2800c1c02c05596004000d45d41140c07104248503010540345107040c500d5042c244c02e035046c0408200071041c64a442d2800114100204000640700e00c103200f012414a0400303100c0400050941c00c0740f408d04c41207201c0141d005c030080000005524207103200401e81421700718034207240c0c9440207255215500003c1e007032065030000502014420441c042d60845492410044c508001581407240e80c0029103110501c1000c101207802a0703250081141500e0070540e00301101300c030200382503880b03020741c518250340070007861400103002030500150718400824000c2300c0b03001c00382403400c00300d1b64030080c590358041c1d40100110401270b40c018140b414010f80444280030903a0f114400140c9410342d04501680140003c00c0d001c1c09940c054100c40741070705103074a8110100743c4580078541e0f0b916040c80043d6104000107a4080907041400240c003d8800b644 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 280173471 1250 280172221 280172231
    0x90506060a0c030c0203011b12020901081f0f0303170618012105030c06061201050403080106080a0b03010614010e090402150c0312100e1608011e050315090f030c060103110103 77
    0x14001034219004050b04000400040c2381c3c281c9500e5006440d4403500714038980440c14002c0c4400000d20480c4018103251103400c09900442c0002e00c42e0f00b4030001015011032021301251030b858010071410b00d5654131203150a101c40883c0c3e0a20700700c101000840030405200e44140c0c80c0685108041071221941003500780714005000100368240000d100d40c0302520010509400c00038140710401d800100d03010f00e2070340f41c05c0600c00001c3d0300080e100c1c1100c03040c1c600b0400a0700e46c0c65a07d4002c0504805440c0d245d0310f07110b40003a101346040c1d19262500401d80b50140d100400c0307424086110340c00c803002540011046c508907503902010000e0091580301004032802c0001c01084c04540d100d083d20741c000d0003940d50008200c55110007004a50004410740403103541d484e0000b005d806014180100c0345000082c001e403103952143c1545050080c013000f0300300e541c01c6c2c94248139550084d0081d255a403540c09018549079603101c00100719070315030700d041700240040c0c1c0c1303580ca842e141154200003242c1010b441e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 280174721 1250 280173471 280173473
    0xa022206090603030905031c0305041e120801050a0b0316020319050309010507050405060a0e031006091a060405011202030a14041b05300a080c0f07090506060a0c030c 73
    0x68030030200540081040040d0790380c258140a403000c0d51507031056100c0c1e40060201c0007504003c00045035007150a081c003081070f4440d85403204104070311700d0350850700120095400d414007680c039200c0c60840b443c0c0c0d210540f0a989800910002d030b055400784603000b01c81000800d107801c050b01070f503201121840c030542c1e0030000b4001c081c40454014000b810700242010061005405080c810b40781c004a00c0c4c00c1040c6441c7c170b02004a006401445222030500000018940040d102400211000c1c2c1d02404200181601c03400c86800805210900224101c0101090081c40c140354040303c041d500161075000741c00aa80308070801942c00108000203142c1c030b903400c8002d959512580c09009510a0100061104070b06004000c20740107988418030603040d500072944c413a01145215840c0d115000e440071000d60018407c1860030180c2100180513000004401d6030010700802c40e901c0304850740055418540e51401180c0686030203407186c9920a400b0402143c00a01540c8482e80007440303410088039031019 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 280175971 1250 280174721 280174789
    0x206070804090e0a03080c13050d06090605190b061e030c0904020a03090b0f011a130806010f05011d010905090a180818030f0d050a180801060504050c03090a02 70
    0x9010100c102e82d0b84031403862401c168205403080e41c000c3c00e0105042c103000070b0b6400d06110000351303ca01408ac020401048052106507041061550341028080c40b043c2481c5456042d0728074020407003410320b440c1040c80c44582c68582c00301e51101c117005e05107510704c2d03510b02c0192a817030f031002c1c15008441004114295003511580081c1c02c503841c0f1503c0024000485051204007000020001307034110050800501c102e02202e00800c0c03003081e1003160951600c080d251110030030b9502d50440710652245000000714118003c0800d0700703681e001c0e41d8403800c442c1442d800c0200a0010740d5045c0c007041141c0014081420100b4140b540b100004202150840030004c40c3da40248068400f580c00d66000200c04003881c2942e114200000303001c0d40108028952210255100c80d48207624030208080040e10500300b6202d0b03e41041490b02038004881902d640301501c6009180e2403251034066400c3c540000d0300846c481e0250381c4501e030014094500b0344d1907603007001480c00d1600c4480030f4102c1402600240210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 280177221 1250 280175971 280175981
    0x240c07090c0e090a0e06010e0c07140304150203030f06060a2a0b13051005060d12080a0b0409121218081b0102070203030a030b01050f0d02030a0e011503020607080409 73
    0x1416450742c126004803282848024800180f1502400d0300306400070300fa20100054080c1141c6601c01080555194032102501c00c0c0b04903100904248002c8603e030100181c080300400840d05112480c188918085000340e07240e000c02c961080300d0080f41800640c007410210003c0c600b00c040c43c58240c0c100a856003810070300381c0010080c00d8404105060301c40c1000350310310690780c202d034802200d20032020b929950176543d5140d4040080d403060f207a6011517001e441d044c800d9030185600c108042c44002d101400205950011600614540d0406000c90038600309486003030030781b43c0c001d000c421203100e66200c151424000200e20b514010355078610405c0c626001021900f102e81310303100d0b10790b03900c0245500110104040084299036481000541c0c01a9000000c96259941c1e901b00403880c0c6c0c1c9480b0050701c1901032448001280c48002600e8902413205070b0065106c1c2c0d80020b810054000c492414500b01c40d1000400e01a1104900060000d4940380f03002d440d483e80300700e10440c80d0545030029081a64 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 280178471 1250 280177221 280177241
    0x105072001060e01090b040e071203121b051201050405040210110c120c09101d1003210314060303041413151a0c0c010503090a0f030e01020c240c0709 66
    0x3c3c6e600c00b4610b4480c5403e020b01c00070001c0080042018a0a000c00b80c541410504d50090170301c00ea120001221660a801c0300d1180e288107181021a14410b80c2d000c2d0442d88410000c03000c0102030030012415240910695000715000b03001d103242c515550704103540520f28080d00520034401c80d44440d2480c1d5519001d42c82281b020342c0600010000d034004e002c0304a0000c1c0611002c200d40c580103003d00801d030250ba4006817040712841d01c0b9070721120440c0c0b8078010b140d08040c0c001005600421513030f031201340e42c1c8000d45000b03503020002d00340384020b0790722400c2d070540714140c2c5900308000c00c2041c40703004c0e2094040b51000074120406031b14100141e04c1146c0c10b2050100381c0d051480410800b000ca0b1001d40341c260900004003501d003000380d0801d41d07183c00d140b1760000d048c0280800880d660000800000c8540d5a002801c00e01e0049a410003401421340c4400c0c150042c45201d100a50342d092205609071400804d00d0b041c3c5030007007190352056668000303c0c00d0313032140d1140580010703e0544500440e010b031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 280179721 1250 280178471 280178489
    0x90a031101060b0316021515010909050c0313030c0c0905010e18060609150310200301080a03030507052b0b01020d0504120f05161a07020d020f0604090c030209120105072001060e01 79
    0x23210042001510b020480d82c0300e428454644000c01055441800032a5480f86a8108141d4065803614041d110790020003c0603107019041c1c000403c0050190b031280b41605c841030307104500c5039030b00c581d45540203d59205088031500000b010960380d0500100e840d41081c0300d16170041865480d540803074038115429403a65103240d241c040d00352400e411800000c070039100072017400740707158145560545c0e1002030303410041c00c1565810000301030324840c00a4421601d28183c1d0361101001d140360094549250703002078070f003407842d0082035482c42d07000190160011030305848143c01d1078505a140078128142d00000d82d001d0401d0291200001c0062207002600700014154484280c10a082c2e074411b9000d00a038410604010003100015a0b100410000c1d195130440d1314620002c2e02c000811154055a40101c420b1800d008444481a4054001d00198074040c0c50444001c00400c4207982601c00550344000440d2410410800d419440001000d02041c20000801d04a98070700c001107410409910030006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 280180971 1250 280179721 280179751
    0x90918030a021c03092402130b070506060f0a031704081c03060e01061e020f12070302010b06090603040b1302090f090d0305010303020c060c070509090a031101060b03160215 76
    0xc43c0446101468220420700e01081030f5240e994800480014000b500380901462422240b2001400d804545480b140481c01c581a03968403070380d142e09034200310b5046500e400341d440000d0060a01e0f000d284c0c44040c00400c980d9005286440d450300c103018400491280150070000864903d01c2001021402c0f080940414410662a4030080c100c41d80751f080001c0501c0068010401c10364480400c2c0d003c0c00400d24038009461401d481a841c0140c2c9912429203401031885e100b540c8810000078103d22402500240000806082003145038407c801507140c3c0300f14107001040c082220f2841442c3d000c401c110424dc440406a00003c07644202203951b1548074811000300a9002010300c130055410200703040034405541550b5002c3c2d101e0184800315400350710701141801e04520200300d000010900601100c5460804805c1c482d00c5101400095001ca49080c4144910f681c051040d08220f0300c901403000d0035610303001c625100a16450074014214810040c415116452609085010780d01501710015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 280182221 1250 280180971 280180993
    0x60e01020c030610051003060305030f030730140112080a02031e0322121404030f110423040b180d090612021e0304020301020712050c0c1005090918030a02 68
    0x4000071080c040c5004048c2070002c20800141c00009407080076904910113501e030742e124441140d41e10052a61202419040300c03c100d2402803189034282ca00c081c1680a0107641c14941c6d50300c6c0d040400307100790300c04d00e113110440c071000c0b07022480503042960a5105032440d03c407102c0c41c80107141000072030404100e1400002c0c00000100c40c1809120f82c560031000000300710380f54035140d02c13100f003141a01d02484221802101d406540100315030256a00c20f0038401400c00b54240340c8805040240e075a4004c034549040515030188444208441c0d41e1300c2104640c0039640d40d5200030b110600030349403400c0441c00c03a2444514410600181d5500c001964800d140d184c68a98003d05a0b80c0c440248450740b4070400c142d10130040d070041600d0082038405d20160356034030b45202190081c420074030007a04111143c0300005107681c0c01002008480c2d06201265641d945d124200400e24181c4084540454402c05c5044e1040c1845000107034005140540c00c51203103004600907042d035008891003070040e0000e00c2c65407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 280183471 1250 280182221 280182229
    0x50c0a14100c0824031902090105010503040b1501140406020312060a080d081302030a0308010305160e0a0c09030c0b09041a1c050304120b0106080f07020601060e01020c03061005 78
    0x8a02840705410500c28049078800162040b80701510310b2030381400c1000116201d40c501c0b20f01c00c0d52000b01804a900360020780850350841c0480700c4049124199080c0005129072281040d2401950462070303c0c00d50341c65542d440b45084040c1551b00c1e05001703c1040100e20881618042c2004001c50340282d035071298415210070311b214006041501c2020030004c00e12260380001444140c059043c105007885840341c081c000390020100c41c000354507104162640e02013551026240e8100c0f4030031800c039103038480e4840e0b888200062174068424000501c6000440c0c40302c450b00040103c2030320f418240c400c20b4807500e48400c2030009030081d035458a0005180c0b030240c10188101c0c40398085018032215400c180c44005049402c0000a6103503440c60300b070407a01481418001c640c001d0003840c4030455400e01500d0f140083d045c0034482c04010861503c0011224800d03e45000d01c91009580074100d20382c00d21005581006103044d0041c11441607540d4520f43d074800304845c4c3e004e0190500d1082d441c40c9014200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 280184721 1250 280183471 280183483
    0xd030818012a02120c0a0506010e0432070303050414010c0506072109150f02090a05010819020309010b0a050d05120f0c0d110c030a0201080604020703050c0a14 70
    0xc66400e070302d40100001c40800c1180340325900c0401006002c500c1511000492905050407030095920500007900e08010b000001c40e510150311035015546603030399440049151490449025003459001000c0d81c10503c80708144144900b60260181082c04004050310320341030750344d04201c0216000207001d00540d480040301d003e1401007440c09e8900c4044650f24a5190f0304098005002d0052411050101c403907a1000f000b01c08404c500300301f1030640d07941803030036041650341c44400d41d003840c10000d0040320400340221032002c94017034013214066151030011078201100030550018800215120b02181d03600340004d6014141020010a007108503004011a01310f0b603601ca107208007000c01c44503000480c08201a09091001c050307194464904507566452031152501240d80da0150382510442d1a8024008030000c0b80f0910440e01c0100d4403406042d0b90354035540c0c01a01081101000444501d0a900280b104c94401d14185040c050f0040102e07191440b00281250321480305500f078000c1240800103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 280185971 1250 280184721 280184761
    0x31b0309012913050a0603150c09060509060a0804060e01060306050405070605130b28050d05010b0a050d1503140a03080f0c0d020a0e03100b15040302010f1d0d0308 72
    0x40c2008400c14000160080f51510044040ca9444c1d10009103804c2c2c0680c0b2080045820001d186048a61900702000a02c5100c0420340030403007002c000304425200708195980031034040d11040ca00102d02400ba50340c1e62006000f100c0881d103500040c2164042801103000070f6104190101e964149841c0960500740f041d0000d0302001420b0103001c41c60360217000e8000444100310681c5030b8841000b0b68001070b559170101c00300d02d55001d68100c054919031100c02084c001020410070012646c8030000041070f442601c01c0703003000074030500c02181400c811303a0111660180241064014070390f41e40e10319101c41c4100301903414903008000c03040240340d00f007000c2070782c865441240034405262111381101e05006810081d030030541d002c10364010107030090707002d10b4507114014205c441a65105007501c0180c142c00744078074018416080010f02d1540c02c44c00b80c0d41136980c140c507803200c6601d40d00c0d000c40e80c20200e0113100c1c044404080005425407107000070708032014080d40d2200c45d14504a5012805002d004031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 280187221 1250 280185971 280186031
    0x3060f0d0c170123060906010f02030c0a0809120c060307030c03140a0b19030b010303050901030207170307180305060402010309050a080c06071709060f090708011d01050106051e031b030901 83
    0x401c2001700d9481030011035010030242801c1c081c40005200032071841c0141c2400c0310300c42c800e00759610b0178000844007424401d071040301c40d5190000306a0b2451303100c078200e11310560855018030103c0c00060194000340b0341e180031071400003102001e03405d82000340001a2001e640440d40c030440b0320250b0416010004030104240d500144803480d5954900003c00148406410020041078400701a88a90100c0380310f2504840c00c4e1a20b15090140d170010350348191001008038500d043c00141a0185000f2441102d0308040500682c0e0740b26001507020740030340c110444090060020080014001c0c2002e41142c80c4103d0041404d45805000542880280300910f0100d0707105004010801d600001e116610101c60300208556444405100349030200641101809509040e085220403074540d40f88881480040c6c001d100b070766a90881652580724226412022502d04040a40c10540082c000d5422150252034440400d9140392072003415041601c00051030b9443d0355551015005844600565580c150b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 280188471 1250 280187221 280187291
    0x3070f0b06090c25020f060703030506130e03040b030c041805041b0e07030e0712081c020418090201090e010306151a070b0a091a1b03060f0d0c1701 65
    0xb1008007040e0013140d4031210b41c1d200a019202191030350710b49a60154409465151280380d24a8064003503c5c0444d5654003c45041c000036564062034003071141c5188900000d276143c036040c04c00c102e0260788020201405d020040000040340725285410b0350b566001c14000040340d082501e40b00c03107001030211009400c40241c03181844090009110242c1180030b50a0005050f0645a0f04508200850380308030305a60403194160180613201c402400d8120400102c085c2d407844e0120380f04128011800b80d0079034407011043e106103442c0030b940119011801418080b211643d41c1b50484001130b400d0b0001c980e440c1d00c0c0d8200c00d0540310602c41d00c1000c1c15061080700e03075a46c4200c000011070b00503810050a005156004250401165403085114a030844120f40d0402d182c50421300080c202a0748802004441504c045100c80d004400c1c1d82c010b01e0020800c150400024081120b403480390032065549400d090800a80101d00719000d1661700745d950004104164101d01e81c482281d00e0b07100c4c04000e40002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 280189721 1250 280188471 280188487
    0x1020c01120504020a0506030a0e1c1403041a1305010f0501080309011809020403120219020d02040e01020c0d020106060311070b0103140a12200316030e0303070f0b06090c 75
    0x1481600c0c00d807541420015659443d800001d4000445501c5160040d5001092203640e410b2a00b010003090442ea0859802d04025001c0340d0702c104036030381d032350000410002c0c000c1645407c403001181c1040c0500c59031040c1441e00307040316400340015180307955404403a071414000c205d000e00541040603014107040010758034040b0f13010707160b2007501d00f41c1d4100100049880d22401a1220401c00350407100740464807142c0300e1501c44549200340c04050054402c018490804040d880c10792540340354050300280c440e034455403d110140105020b2145079540902541c441d42e1401c20803169840c0c0c15034000301d10b0707a24251002c0c04403038070341c801146601d10401860f004506108812811a540320f00b01001600d51603c240c0d040466620700100f62070841c180c2020000d07030100d00d203c1c9000201c000040d44486041c0915580d00c20030340e500b02d0b40805000ea47c1d000c20300541911503410000342c1a01d1620000d962400706036041248101e4110b0b001000340086401c1c1128119849000c04140718078040e44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 280190971 1250 280189721 280189727
    0x1050f10080f060c0f07080d020405041d070e0a0902090709030c15020a0809030307020919060605070b131b0605030405010c0e06042c040f02030609061620061006020105010501020c01 80
    0x90200f85540c03000179103520405520412520720075001070809032039003c080c0300c800180d8030030300c41c4500c07036400c100c1205804105141010725410003040107102c014600110003c038190001c001c00c503466038580c41180584c84014010f8402d08896503160b07001d42c2103191103109815107400100c03e003030242e041004081d40025079114086c0d000f8064a0700d40e449040006d242d440344480094100d08406c0c00c0c021080f402d24941648a40d404100340701c116100d80003240d46005110020341103d15805c0410a4481c9500c8400307809800b611b04c006542003c0703000c00a04081c280c2c4080300291001040000340002807040b69281d02062820070701440703901c00050203500441c0201a0b90151001c1250341203c1d080d941540400c07020440b01600e440c02c0d003400000d0b0300c0004c00c140d009006843c0021b07085140880c056116000d2103004190204800c3d208a4941107003591424201034180700225640c40c081010a1290381a8000582e4160510344003c0c2551411f0340810706541c00b9000345e80c02e03613030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 280192221 1250 280190971 280190983
    0x3020c0c010c14070b03070f210b130516020c1806280b09010f030c0917070e0f0610050301300f05030a030c08040803161101050f10080f 60
    0x4024070701040d0140c401d08043c0010100c1c9014a40b072403003103500024194044038050341c480d4605d5224244c0c030f80b80915083e03510815210040744c16414002754011107800310346c0b2642c0302c2000504014400c02e606140713001103440944040300c6034907542d100038003150f07410004581c00c600705451800f1000c5d02010350000070b143c007511245c81180e8100c1c469420300c4044c102c1030603d110008411200da40d40b01d00e511207650242007134600007805442e0040e0058000e01a0803083d00c5941d40d06040c05d03140089192441402c075100d00c01c0c45c05420740014004082d001c1c42801080b0030300740c1e1140390410720b08100501041000c10810300900344010481200080000301c514084405040703035032800c171105c000700342820040041c80010396100801c103000001000e0300304054651070030015408002c40c142e41540c41118000e080f4101040010502902e6003810f80700e801103404c003214402d40c0e5005280c00d44078101d481c10790040545007008280f056504c00a4000d008034800303031050a6104594941b144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 280193471 1250 280192221 280192243
    0x6041809050a0b13030917120c07030804180e120306060a090503030a08010618030510020f090603010b03041109070c03110c0402070605010905010504140114040b04110901020d03020c 80
    0x195140240400c0c0724052080a0000358483e0700c145141c902025888003500d07040000f540081c0b55540040750445d0f164100702c0554440d00c0007441402078550501c802c5611101394052140500c0000100040719040644080c0486840c400b80c40414903d60200f2503a000908035002d511010401f00c0351039a03007017280c0e00000b040c0c2e0200e0750380821201c1a15581c0c003d51025805110000e00c0e102441e9208440700d040c0c0d15160740b07001c0c1c40007003214501084242808040d240da003082c4854a00385c65582c0c000d0418824919600d801d001a0a0002c2d10b6500240c5c04030620100c00030030001001410200c0941910080380c0c01940340c108007a000f042080b090030014140301180317584d410070040802140b940301e100107000307540d191014541000a083d081c070601402509107400442d0304d1405001d804220680310040d004544e2810310490302c4180000e12141c0c00039612041010303182c948d0300a4500c2441c6e00b2812070307900c0da024400245401c0a04100608161043c42a10b80c028004980d80b0414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 280194721 1250 280193471 280193519
    0x20a03080c010605090f06120606010509091b040b180d030e120f01020c0708010b030f0a120e030304030b011503052202041103010f060f0c08030f040501021905180604 73
    0x5209507a12442c014030983d007040c0e9024083c00c00b0484141110745115100701d00903030b1426126248014450b5a8050070707525203010510600948495003001c514180d400400351000000c2c0401400c58440703907a105400c01600003000042c000304040007800c0c030062030b001c15980010032245503280100464207004840740318081548425118280402c003041d04940e04600131075503840b640704a00d40d602d2191080c0ca115508103041078000e45404202003071004130030f40181c007840d02c0c0c641e50b015080d480491460300740001905c1006480c1c0382000030744050343c41200c6400342941000c803070b2404641f45404007002c250812041004003044681c1007101c8042200e0440803941aa1002401600c0c400502071607081020000160b6401c0425040013191030b030ba200d5450400c0e01d050119091000d105024180500820125400d41407003900b05a0203402240014104a000e0984020b510300b44021480014408903607080940f6008a00002c131060072550645014544005407692003880e401074104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 280195971 1250 280194721 280194727
    0x2109060d0e030c0714190b03070503070903050a0501020a140711041112090a020f01050703081f030807110f010c050601030204090303090516180c080f1b04080102190309020a0308 78
    0x1c06102042942e21100900050f14150780d1280b002c0240c220140d0038281c45510b459100b0224880c00c05000000c0d80c00c990900303451507554081c15501980042d1100c000c20014240000115a0600410a12900c1000003580d0b400440750024068207010300c0201c021203003008036030005401103000040d0005c040d02d0101d031004090b080b52210380200c002d00785440c0071120412030803510115107008400e00c00c40e86801ea5919600c0112005c1c091145d0040c041002c81c4040ba4500410703800003140c0a10b1400c9043d1080d031240e840c80c68035080715004031401c04010b081407240340782283c12201d9030720003031030320b4a540c0d081922003e503100300c1803102a00495940d0740d5042490304c66000841016080000c441d1105440944101001030500c41e000e80c1002c064444544d4844a000740c01c3e440800d0340d40c032030322511803071a88001504081c20420034a01070495901c480722001c0301400c0100010800103843d0058006000d24a641d0290000c0c10989040003030b40050380c40b81c190384140c1340c10600641d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 280197221 1250 280195971 280195991
    0x70207060905090f10081902030706050f07080d0605041a0a05062a0f0715030501050105120f091005010f0e090609071a0c370c060309030509040e2109060d 68
    0x240c540345401900880c042d80d2100d01f0003002294503000070510950072211500c4d07455008a80c6070081004007190250104135100200740020045c2042690314040020f455035603800040c00c8454034802d03140d01c25466a01400c0c00e251240302d100c014442641c40707900e0252106c1c02c1404ca2002d1003841d00300d260000e00c82007207008003004007011240b032006c1155511621580c03204109a400d601460000341880008100f03540700b00c0c1513800c0021710396040c040d1601c4003541d03c500070074002d017000d0807486608800c02c005403240c09014001c2080d2000c00803400e0804040d100c80190090140c0000c0d4000d00510101040008849048820059408600800a40e40d56146101c0c1e046c80c900ca51181040d100d0540c00707640b4100d00007220700e40d481350110b0307a81c148880d02000b841e280030304600403a59007001843e000342c0091849a1080c03608518204002001900b00e400080381c8114560010480a4200c0c20b10000c1e0003520030700c8180b0a050000d0500014100e00c181808480280e889011041c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 280198471 1250 280197221 280197241
    0xa0c2010030c0e1809060109020f0f0702030109060609021902031305091003050109211707030c0908030309031b0a110d0303020c0102030a0507090504021201031b1d070207060905090f 80
    0xf100510040c200040440389091200c00e214060b5105481401907034000100038182d8421030b21b620b0500c4404a05040da404c1450025820041050340c055403940300c5080082d01c02d10a0300041e064948006803608081c3c52881441c0308000c0c2404150740c41084100741903803610b0950380490b50100d030b081c08140c2d81c00c0c1404458001c940d00050040d030910759100100050f521040000e1003518040c8000d40f8049882103900700d01b803681e40c0132050515400300e120f061091700081d8240c0c107603003040300fa0259561111451640700300d500034107540010078450003000c00450880c403403030700e0031005160284040c0c9940d060390750b03001e9025110301007443c103500c01c00d4000e4064500401300c1d030000315100d207001c0c048540a42002c0383d801c00080e11580002c2034900c0c1034400d03606007989002c824407a41e070940e65081e002c3c00380001c80100d030000d403450004000e40c1e00da000344803010010501d8111414001006458841f00c1e4000a05200c8405d80500c51a00e408194683c4100400d10035010b03910750178005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 280199721 1250 280198471 280198487
    0x106230a0203120403020a0b06090106081506040f091a09010f060e0d0b0103110906030d320a020a06050901090b040b10030b090a1506080604031101020f0a0c2010030c 73
    0x3050b03003c081c074040005040c1c011524044590060040d48001da441c1c004218496009004501c00b03c0e4030310021038081d01e4142104010064050a403034601507c03040b244031004600d51061102c0c9490706002e42e910200d40305441803484080d0740500340340d41481081c00079000f05000e0081006021207403050700b2790b02c0c48050030529030003100c11407895840c7e0a10388031020501c1c1d0054000c150000200358a410001402901c0040701e55030b01c001c290700180541a01030706403412500360804094508003101d1107400600d0740300f000340c00900c2c8143c5a80340ca01e090310402094280903034500012403001c641d2821015620030360010404e995592824940c00900344550005003100030b1244c100140100001240c210807070180404107075540c110300440f016600e03e800303000d55a0b040b001c0401d0010380070b4032070032480c0c1031a1000903007000203401161915811580d42c140001d060a8011001e00c8544006800d61190340c9041040b10500741001c00c494116041c041001c040d80d881d43c0703015942c031442e28 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 280200971 1250 280199721 280199737
    0x303090607062324090105100c0b0a020a0206011205060c1b0601060f030b09091207030203120f0709091a061c05041101111c120609090501090b0106230a0203 69
    0x1e49048031100e0000c445505002c880e004001800400ca1030b20f64250b8401401d6004d40040c0f024034039030b003880144480d1180441115090088405105000403200180c282c07188034500700042e00e078030194200034580401a8484000f0000000100c0086000800c545034441d01e145c1400340e650001c5908034a10301c540c9024401c2d24000d010000c500c2603401010600206095235051112031107501c200005584155001c19584d8418414407003c0d0070b015000d4054075001e40180ca0a19104180d001c5090b0402c0300ca420f6054808402c01c505160040700f1f20000d0302030040c0810a061014052036280e40d00b502c9000c0c0b0841011920340d461022200d08000ca10150310001e120504251401440107900500b602c1c2c0410001c124083c9400c2000400d4800034600b0844012414594101a1504600084400100c54071080c0100c4c840301c0c14003030b10904600c03c100000f0321412500b0606018003040e0043e90030002c10000344814020b84842d0301c41e20245002d0503903a98420701ca416440c521079074803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 280202221 1250 280200971 280201001
    0x3010b1305060d0501030b0a02041d060402090a03060b091803030601120b041410050330131403010c11121602041e140f04030c06060317040612050402030309060706 72
    0xf0303003210303100080d80006040301d104003001c10040c2c45011180041c0c0c0a14019014000d2000c06041000a128540720f0b8012502070b000524042100c1c0104011a001d500142c0301940c4404580385d85082a0001c164005c0303115503603900b8502202c01e00f549a1102401d0b50313041160081d6a507c409029511120b40c945000b402001240252000540904002c460b03030141084c51410006050402044480034061000880c0452405c801000c0080345244201c04901c100b044c400e09815030b140000c14806001404209810018510101750075181c40f60400c1040098035103441c28000000240010303041c4480400c2602d0b4070005500500503900c404020354030904010301e208103665011503003400910310000c2401441d12030b20b07981c01014003c0d02c0090300340170783c80005000b0a20400c51100054444d10780450000d54076204c0801640403031400e000d2100000404100845c0c014141c0c0d08200072080701402645400d4002907102c0c00b4445400e030240070b002521b082001142e078043d246d000d80c811 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 280203471 1250 280202221 280202227
    0x90c050301290f010207120611030406090b090a0c120312020d061e030b0c160203060c0a0e030708070303030e1507050405121f020a02011413052103010b130506 70
    0x1c200410316299001c00064090341101900001d081c14100c65210603c10780090040c9498a407801c3c000c07881c48030003605e04596805809580320454801540114025240414500021304102d003440e4409084254140c2c40300c0c1c0f10200051202c0c2500d4121480310b11049415421030400743c0344c4020a540082c1c4103840001d00548248841e4410300c1074401c202141e0b004411581c3c0707416002d40c154000031745816040b0001501103050b00004240240c4a00ca06002a00003580424038024081c0c51700034103854045024104183d0001213049400380881c02400050300d0716005584840752404090f04254644019400280080201001408480d022080c103480d0400300240107402c05cac0074061003510b81c000b10301302d8101e00281d41c1811a5100080843c004000040e5030025030040d41001d0541d502d445240144404070540c00d80b0400c4514644000c0441d00d00d81326060004a0040604010340401c00c40f8070b80480344281c0b81982c284003c070590750402000300780c0540e90b880d8849503001d4400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 280204721 1250 280203471 280203491
    0x21806060d06090614010908032a06091f0b0618061204050a02101d040b1f090503100203070f03020309120403050f010f0c0512041a01170d0f12090c050301 68
    0x903502850071550383c0c4094403105d03540c50004491b044580c2c4030302c4000350310511042c0b100342851409481001074405448144425603042e19040c54000c0390a9000c640012000604422003c50000b842d10814141040755510a9001644601520088820714440b002007840940c90382402c6032100e800c10100405103141910b0116525283c81200724040c82c0c4039140740043c04c3c042e90314100700520003140b00800810f99410b0000406028904650103510030410041034450700c1d141e4049880701c0d50719000c40303a0400382450b1520344214414040b0f14030400401c0001c540c40841140703070101d43d1602580c0e80d1142c19140b854170340c000f01c01d485031072000540001003040001c2c201d0b0301014010f0092000b603050b501c00b1400c90300742d2250310010030810440c030121103c501098907030152180c0324022042c800000e0140d00030009800c230280d200090700c550000e90204004030385c100e00c6589400c18183d0903428008100300302e141c010050b104d85500c0c442040000d00000d504c003603c4050700070440d01c40300d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 280205971 1250 280204721 280204739
    0xc04030606150215040b04030c0201020a080a1805090403090509041a01141011060601110f0604061e0515040c110a0507140a0e22050a030905010801090504021806060d06 74
    0x1c0e0b02c04440580709528082213150050f801c01c920036130b00140300c0700306a920342d01c3c160354440c0311a404038118001d00f40c04100007640e0f000a484440403640c0c2c3c09000d01c0441065280d9240703550002c0c1d04c10303c2000100070010ba4041c4040054800c143d5002035592118500040452242d460081e03071040307000c00220740f62495440000d040d08003121402030000c0d288006598081284e2810030b182d402c02c1c0c000605c554090b02840e052038140301c6c2203402034074501c44241d00b4034000399812100a034513a04204011b0020b05d10810407188008810049818100c84070703400e0348090445940aa515510f081740c60300c1c0900703544c44281144006545070b441107458440d0f1582d5450044108040c0c034000e80f04410b0510000301e0080e1800c0809519060315079141a007200c41e02c811aa00140c01c800511000181041c0240312881c0e00c030b0f07142c41403924180700026016a00503008410b80526200401000d81c0d20754907518100b1604215501c81c4e610f0320300204100d4400c3c8040c4008850501400083c40d0b00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 280207221 1250 280205971 280205999
    0x501020406030b090c090a091e1406090907180c110d2703150209030a1b090b1c0b040201052104020f0303030903030711160b0306100906050406080c04030606 69
    0x40200c801300c00f60340d40c001003002c180c00349982d0203420120902c820300c000c40c6c40e0360002007103038101d011410010003441c00c004180c409401da907041000c010384c188400d6040c4042210780005d401c00c0900000744c1030103a403513420451200510708a50725a0101e4050601914070080724450071000c0d44d040c0340948401408600c101d489040d8104003580300d85001d814450948000d69900007141c011000d06105e180001c0d400290b44594107000b00c3c0d030320b00d000614442d00000c1200300c9440340ca0049141c07001450031540c1140010b4011382040c08042c07010010144480c000e150b000065031401c2e101c60004031080c0c010104440d000740d8040520b100008040340c07004e48201d00c00c91f0358400c4495441e050540b03d01060340e10043d180c0c400e002040b941e50055a86422515204080307a5100c650103049005110940e446004482c0000040c80f060f410131040e442440d070500e04040519505d000300003041403040740f0881d000c0164690210701c030150030340111b50095400800512000d602c0307202101c0005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 280208471 1250 280207221 280207241
    0x8120a1814010e030613020f040b0402031e0a05060a03060c0909020417120405010509090a0e0a0c170a0503190e0a152a03050304020315010602060105030705011106070318050102040603 81
    0xc2c00d1062400702501d03002170146e00c90040e0360081d030304400160307091105207207036407e495610684404a1150a803114805540305410b401d9080183d0410f45580211a07400504020f007076508210401c503841e1034201121040302c1d8800b00008007a130030200e04650072009500b16454403030000400140c40c040c59501c03829079901003000d60741085081c3c3d60550841c8105d100c0d0b9408110188404107462a1100c0010341c402c08102c2c4c040f1300030602405150070040300000440b0395507410481400a01051142071861560f1800240001c0c612502c0c0d0326640e00907094412a0064695100c0902610494103c0000b02c006004040816120042d0b41481100000c01c5c0300045c1c0c20600c01e0700c1c94000800b541203060200c0302403d00d10525a2000c68003035000800c281e80600c941c0080480107003407400e2190007810b040d409081c195041c40b042600703015083d80312a04024034018004540000840c115400c05114180003410108010780c1405000c8090405003140d4404680003403415051b8009503445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 280209721 1250 280208471 280208477
    0x1116030b0709170705040b010c050a03211e0c030603020612011a040303050a030f020f1305040507050711090403020a0c09020a030f0e0c09060f0307060507060c0908120a181401 77
    0xd0b5444104a9010007581e401d180d00c2c50340883c0c1d040000b8142030307206892600c7c040c9422606403045444d6030740707012071480003100041e050480a401c0d4490030300084a080c02001c2c4107220100340d0284100c1c01880000f41891510b81d203802c0020041d010740e106500840d80603008036210b401d8039035609140d02d0244204800b0409402c4640c41d030070000d00803913058983c503403181c40c1400a81c0d1011401840c50582c5290520750810000807200f2941003d81407081c1042c59030388840e4140020700040d00c0010706000b0034040240001c500040c150340c1c540000240c00e8543c0000c2c0d41d90350604924011600760040c0c580d01c1e10120109254200350010308010307030151000c0c00104504c03080142155680c1c1400c20013601301d03021070b08852415070f50700382d0080c100071310382c00b145034130360000905111035684003c0104900282c00e0301001118095411494000d00705240713001c0c90410b4054550fa201c01d01b92868560008010101d1030003242801d280403030100a030070803070b41c40b80e000c000708419043c403083c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 280210971 1250 280209721 280209737
    0xc0a05010318080d0b090a020705010e011a0f0a05100801060306081903120f0f0b0f060f0301030209090a06020a08010302090609070509120705130606110a020d02011116030b07 77
    0x455000e40030b1100040c40348000c02c0301842c20394540c01c40d150051440608065161905100140e035001d5180d40621081c84d40103070b4460304c910f0520300b110a00062601c0c00d904240c2d280c000313561800f6001c000440107440500480c2040c1c4001060100d15421055024405500b50507007207502c444610305884868034200041c07a2180c400641d183d41b01208402c11106c03074007541e070000340304500b03980c50456030382c2c40410703080d24094901c401d071690f4103008202c5941d01c2108260500d042e040340b030300b003e84c156000b91910044c6950500c041c407050001901400c1203401040f14010200700d403544040d08408115124009210000c00c1c0560a00c01030b8490a003141c0410b1262400700d502e2400760503213482c0c0078a084145404e01115604841003c00d207030050000000b12615020012100b0400314500040d0b01d508002000d4020f03503504603140042c0c5e000c3d001c0300e401038907005406140180c090a10100d4001c1040c40c42d4a003035100c0f00e007064401e901210002c200451182d0850181702d0548600c25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 280212221 1250 280210971 280210979
    0x40303020301031707020f041a18071209080f0306010207030b0109060501030c030c020c0f030f1c020f0d08010501030906020f0d1a030307020a03150225052404060f18050c0a 76
    0x41d09014042001e540640301041d00c000c01e1074964880842e030604070827042d2200c0340c200e00013120b0001075a00000380030b60f12410001d54692007122485200082501000403c055445506082c05402581031030350000102060160b0300803c2400021a806010102590384490034180640320307a12230140402e05081c2d51b91a4503000340a006050105640100300c00000242001181030349074422503014045e601e00d100744a10240480707003848a80b100c0032a11f405118600034a022200d441070500303038025030b125811944d0b019217000d044650910700840e0444060810100078841e24103040002440050720300600c9450750450250341c820350446607040d001f4103081c1910382c42220f0b0020741c091107150091000803040c45c212041c3c1c00606074014107280b40d80002c16110614021507040b22001a2000002c00c00d04100780143d22000c80566121003103480f030408580a006000200400c0d22a1454841029190302c00c1c1000072002c0074001da0100030381007581d240e103880d4074064000d4a600304089 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 280213471 1250 280212221 280212263
    0x702030d08060612040c050d1406070e0907030b030712030f020615210102070c0602070e0c130b0304110a14011206050a0b1b0619051602060c0a0504080604030302030103 74
    0x648a01e102401162904884d1000c803580907900510444509007281d4012403d40c645ca0b000c030100a00c00c05401ca440c1451003900ca250400c0103160071b040185140c3d08030410744480c180b040c1c1140d07041c180410000d075035400280c03d000311034202c2d040c5440418001410702d03a0101c4a540300107160303000e82d41e89854208000740f0400365002c80c036801070142011002d050031266440150011002c000500f0198141d0710f03003071400305075801000160710203507090001c0300102d401c468016400003103e600d0801c1c0060b410700001d0940c4185451050080300190901092414800d45a00020910440c5075202c20550280c0342200044500107417002c400c130103140500344500703801c3ea5802031088003054601142070046078040140d501c017090316090603c403071140810107140201e04c00c100d40b4503500e21300007507182295002807040c454200641100810541c01241081d0012608155250303100f16030ba02c203641078804d42c0d1080a20384507070401c10050580c5a40614103892048941a00d100d613807031a10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 280214721 1250 280213471 280213487
    0x324010e03120f040512010e0d020a1109061c03110f0106031a07050c150105150a0c0b090f0609010e240f060d060e16050a030308040803101503020702030d 68
    0xa980c2590018050b44020742c80c14024000c0100902c402c0d03480c06440c0e0010801c031480c80c04098403682c0d140c0c4120381d00312109001480040350f41713100600c0002282d40b1504001c907460121140a2032030000881d040d42c44040c0700800803109040110504c504600d0b0040032075000341d8001845005003207200131a420306001307030300403a5081100d200d01100404404000d2240c043e04080c2440010888458909020b10030441082c031032000817900c9600d4130013400b05014100c1c129904003242000004a00d81d0402c44091030b054202c2e680c03a83c60782c0c0b100d4049182c08081c06680c0c1c500c5c4100390030000d4180054101d03107180d904100c10380e0550442c4204c440010703450700c01d5140c4404900c20002d000300c0d01e070b030042582c014401030040a11070340940310728088407008501c265407500032503412065000e1480b1860000c00c030a603007106400340f440c2c034000d2075080080d1008210340c0c0d0010110311901d244081c0b21018010310340f1140120311184801800030750184604030b0086c09600d00384800030303000b0829 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 280215827 1106 280214721 280214747
    0xa05150319021c0c110106030506060f01020d05190e090a02030709051c030e040207060e03040e010f060504030204090312020f0403020415030f03080714032401 70
    0x312009440d000c20614085900401200c41c00e03020998500110f0300e02200001201c000440044a100c44120100100342d0700700f050110a01c04041001401000d084541c01e03d00e80d0000700598a492401e920390000c10000c4c003c5131070b01c2d4040414a0514186440e110314082c3e01c1c0c0000a9008400741c50804030254040100b003940c523003014806001c1c0a0032999201c80305d0315500906e818044819004040184045a000343c82d00c481d01511403080d4401d8050220765620800c41c0c1e6030381c00c10b00c6101000400b000000601c00d80d05003106042c0c40c417035650325180900f55024000a040c0d0040c5c11820803a84180c101c070408554030180802d801e0507800e075030b501e903c2c50040000f6071345069881308950040c0b0788d00b0000164540801020140d0600701040b039076407090800d0f95500104030070101c0491000003003009008180d55402d0200c14842d040c1018032101c2001140c096205c007070 = true := by decide +kernel

theorem cover : BRFrame.Cov 280035971 280215827 := by
  have h0 := BRFrame.cov_init 280035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 280035971 ≤ n) (h2 : n < 280215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
