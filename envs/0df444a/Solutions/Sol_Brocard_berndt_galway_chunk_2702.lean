-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2702
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:24.84643+00:00
-- url     : https://prove2.me/submissions/f78fbb4e-7ee1-435f-83a4-d3f95f685731

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 485791366 ≤ n < 485971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 485792616 1250 485791366 485791379
    0x60a0f03061406060903060a020f120f0a0e0706050403120309020d03030b03071a090402090d050a08070b0a02040302130902060f0c1f0b010906081e01030501050601020601050f0a140a03020901 84
    0x2000740358200c0140305400c800090360f40c80c0280855070701c0c8201402814258440e0701c641c0c0069000881c071100314172800e00c07429140b44085400e02d88140c4507408480341c10304020f0190700440e4081d54400c441c40d000141d0602500760814100c40031654031600200c81045060b00840080c00c5891000354400c01e541102d03424903601d074004502250044090340c4180da55a254802c40001d00120701c02111001e01840c500c0c4d1400750b0140c2903070720000d0011081c0b414181e40c1d00d03081c41000101103816042c081140380034824120740285d030021210100314541030841c1c00007200149801c1c600544903841b481c1d81d0b002c5445000a480c11010b039100101d440703141d0070078000c0d102e901c00e03459146281340088544101e5000740c09174006001c030685070118801d0401c0400c03030742c948004120b51004082c801410503c0240d0308041d83c0210b0007a0000601801c008000900303008043e88418803401c2e00c40401612546d8009460048a0340b00c1016000448001c0114456078615400a0361000e8808000501c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 485793866 1250 485792616 485792621
    0x3100204081b04020310051201090c23031504021002010b031903080604090803011e030f08070201081e010902090411160b0a020c0c04020702011701090e10050c0d0203060a0f0306 78
    0x350b648074048400301c1811080c00201d0004540080d40a09201c03070070815814a000080469450100041419102c0752503000441c60759501c4000d508100e4884142012140040c187c1c940134121302510781c0001c01c070003800c0358000180c0041d109012409211480714002d42c841d0345051000340c142d41034201010040a412030b400b10007940862181800258640382502ca0a071404e5808800c0c1415a401c1a03c084600c2e24140c1100700320301200c200101c00305020481480421f17109408241d600d441074800108281c1001d4500403000780e84407a54480d40d41008809419901003004c01605e0f03d10420000d00945101c10030640d001d900001c0280001040151140c0d000e0301aa075841d00645501000d48101c1c0300748803145840d600309211408043c60641c00410109005142842e100034080303a0781c4001001c283d2180b10180d43d207009032460104203200c86248021824030400c441c0c54207516400304d921982c40a580d4084d800000a000340d6642c440c81806014040b1203a440c2980300c1c6000c000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 485795116 1250 485793866 485793883
    0x12050106020c1243030c0312110c040c020c090430091e05060d140c0909010311061201151d011707031d0705040b0f0306150310020408 59
    0x30303e0503403680c0e003040200064003038140c003032416041e58082d05040e0210070500c4940448010762031414a0b00c5881c40c000345001c80910b00a0b041501c08500d14a080794980360101c144805000d803004019200f4400444d1030600e02ca400d8402280b0301c0207801d012820004005422a4045040c0061106001860040034410025a0520b0801e00c4012424400ca0032450101c3c500040414805000c1401e41402031b030220301e03402d182500c2d035507120703000500d46070000c2020702e0318103a40b000075080740901c0c08a01c907040403240942c3c40c0740101480104008440500010300803003101c42e500c0d1070303030746a0404941c055840907008590558464012032a002c4074a49030900040880d1130351139011140c20a038804004050316240c0c00e40e400c40f01c038403000060090207201803698076004100d040202d04000c4203c010050080c10b0114144030030032049410494905000d924852011000c3d5100000d2180d000080f600c400c803840402c2c907000034071f07000d918007401a03014004140001e40f908001030100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 485796366 1250 485795116 485795119
    0x80a0b060915182b1e060b0a0608072f0102070f0c080c1008090a021002010903030f0207050c0108151804030f080f060402220602161d06090712050106020c 68
    0x40c44843c80040015451040d505031009828500d41441c490700c0a12205003643e1046484041e00d00b03205a88034041410803000b034800b291034147c1914a440d002d05104040c06150820004030708207004028540d0f920104040e41085803000c4c0328141d00950030564602811180007995070b1440c0786015410680304020854400442e41c1c004030318200040b455001c0418048c0a000902070800c0301200c500c940034110300940d0281c1c0301d2000250715501c1c403451440d805c6400101d0300c5a41c61a005080781c1e114078140610b00e10621040002500c08035804034410b0091034411404e0300c2d411084100010406c440690009186061416440120003c0d078416070181c1c40307140010301c502c8803e42d045d003421070796580b6114250340004c400e4a010350181180c0c000f880a0842c1802841c1c0e400790514045400807009079104a80f00092203050308000b4015107203090b09190205d200000e85d0700c0c3c1c110007401c114421800c8000041d038551203007036881c824042582e4240030300e503522070340691241c41921999 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 485797616 1250 485796366 485796397
    0x13121b06030b03121605061006090e011206090c0b041e0b03040201020606040c0909050f090c120307030e12010c0906020d030605030a111809070501020d0c03080a0b060915 75
    0x19001c1c041e1081041c5070b071024003e4045410800f010115981c8009240003d9288207240080443c0c01040858450155002021541420000041c000180b50b03449400c05904060051103d0440c070009214802d6020700b0118030403505d03250800850003035400c10380905402040015511307000b00c080071040207081503100641130712070b5010051440b040310041e0240e070105010903138a00703050348203003501c0900f03141007091503072100451419035038155000f41070189400d00b03001c060701d4144aaa40f00c220100c07048402100c10b8200680c07a801041e1000c1d05000e0960703c4213080b500e40d14051803001850200801504200b564098480700c101c1c080c1b00018441d41c00450b00840c0a8070407807081d00c80c010014400344a25a071048100c07820380d540300d9009031a40085188001640d95941d000360030301c402808055090600083c030b04403d4400040400c03068140300300c0802c1e0015030407a0000c80071320002c2942e9880030081845803050401413a00325038200c078041004480b6402400e031019010001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 485798866 1250 485797616 485797619
    0xc3303090209060f1f0203160507080606120a03030f06090204181125050c03010204080601080f210c0f03030c0a080604020304021c0f0f030f020d020f07050613121b 72
    0x91280c04a16608079a400950020350f40062217061000981024601c1c4126450031240c500c1c10081180c25000440342544420004d109000b0148210382e40318000383e9401d03890304522008280c0d83d035001803010703043c5a61030003000e003170350486d402130800b81c01914000d40d42c0710307681d840050501e044a545800801c0c9421049000c0340d0514086810340c0c079140c001605940c1d0b803104060b54042040c034040390184541001e50310b403914280003500c01040c000028200561401c00e04504000c42240100c8542c0c01c01c158000e03804895200c10105621134140603529150002d170031a14041d80000030510b5444048200081156550f005210710340f42503607001126220300041c0710a9000554000b984415002c180a4400105905801c1d0740fa001e0b00d2028401003c640b595481c0900c0150140c0c0080c020f8120481d025404004000541c00c0610043c509411841c200315140c03082802001d02c85d06001900401c01401400042c0241c01e208002c0781061129240042019040240004a50040c800c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 485800116 1250 485798866 485798869
    0x231e2e15140d020c03070c1512050405151f0b090f060c0c06030c0f0a03050a0b06131403010906060e06040b270c04090504140f0a0c330309020906 64
    0x30740048550707480c080c203800c0c1105400608040c0d005066802d10501c820302103070010075001c0000344000c010ba44a8000e803031050b404001c00125925070004504c600380340601c4000f0f40e00292819a154030010028101e4485003180c00c0c02e401c044020b250441a00c800110350088104010000301c03030201c3d800b85034a0010010300c401c41c043c40140341550742048802c0079407810044000d6a004880400b034610300b51100040ea0141d40103400d108002079039410412945104034454549504e41c2210803c2c1429003440c80000c0c5880300b4015585a40c4060500c00e002d51400d412801e031060780300c081803181e95145c0c8412070025108903103140c4206c1c20044068032506203015400c003803041d182100803030703c10200072550220001801c41c05500704104000a410980f40c81a075020b40d2052240001c03a400a070300191402001d102c80002c150001282540002c40c000e090600300e030382d01c1c0f42c0c9018080383c41907030142071001d002c0020301041210180203006ea44c15484109120705c2111142980d80382d160 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 485801366 1250 485800116 485800127
    0x120b041112220825021e010813022202090303070f0c1502071e3503090a050108270709061e06030b12010609231e2e15 52
    0x4101402d0103c0030080b07120480c4104060301514541d040d4291300000743d5502003015290820307040c0c5031480c04183ca1400940c0d002520b503421000c4c01521607032580d41c17500000c4031034580c101054942c403100904441c210325940c059403001907004064030380f20b000a0a1030380709002c01190468088294100100b002544d08800d02004d10b41c41e0300600c5400e0a0000801006200d42e1030300101035a1034600007030443e074030760516644031900c080340300000c0318450b1902010f454a82c040c0c00290802e00c08000a81c491010b800300310340c0c00340390205440d2580c19500420001521750345140d4490406051040c050006841040303c0d000300040000d155103128950a500f0220350031000d449120008021080c03098200c62a4140010920784002c481c8040c0d003821038030198865045261070740c010044202103460340d40396652941604c40c2c284e02d130000c0540c40c0181c1c014141c4100d90122000315000303100040140c944d0019010441e04201804000c449000d441c61048001400c0b50040310264644980c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 485802616 1250 485801366 485801431
    0x2107031a1608090a0c090e0c0f0114090a08030414101706010507150c110d0804050a030503090a0c06051c0b0a0312030b031c090501050a120b041112 65
    0xd0040350411085074011102c40d140a0041c080c03c0c4150300c03d8402040720510848024000000c000643d0503400080904003810114001e1284510401030500c998000c02c0000e030000d8a1914141d894000d90005134906416400030f0103d444086804500c0c2e90b046c411a0b00c500500312002500c080340038204840c0041c21081070442c6040305008a0300d00d500407000343c442c151048841d840e105101c0c0714681c0484080120300000580d40340690b0310748040500203405058482d1030001171a103000e84a01e030362250b40007401010040d0001c000f9108070340620241000c544c2c400464050f5a503241c4004205800030321111000e03215403031140300d90090a01c682c4050a40280c461528540b0310f4444051003c207209040c424103071244007084095805000c441c03181d501110385a418030302254001001c3d00d0a49d0172aa0610508110300140130b90001d88842034501d01100214085c045d0030086400340082c03c880c80b000340d2001c50003094208054821038800c0011383d0100c05060720b03c0c403800b942e0300140d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 485803866 1250 485802616 485802631
    0xb0a080d03090602090907030c0930030201090803010b0301050a05120c210f07030b010e0603100c0c0807080d0f0606320a020a0605090d0e09062107031a 67
    0x18158050103900980020b590079004020050a0000100100310745500495006c000259074040c1e01c110f02d0b402c8600346c0c018000c01802202d50b81c1a44c1c4d42d0b0b203108028004110025003a1200c0401094401d401039820f555100b190b0f59240c2d40d40d42d032103a8854100780242817091007107800109450500c40030250705404050000c0c12085002d01c1403024104240f0060501c130366084801c64a01d410070003882c9607171003112005110091070340c01d004103100c8040e00190707080c2100ea402d101085c0d40010b03c501c2d40004c1c42400207001c5129500071b40d240400080000d04040011803a041440300c0c080203821002900d01c4103010101a510040048814a0113154041b8494020006010105c105008010b0603124103180946040e003003180d55039000078180c1801644118104410230455002d019004030001b0300800340c0b85417040000e49411100c60f03000e17014040703440004403141d1b1403104880074079001401c9048506060081c07643c450a050206440407505c060b0300e203000b0484d1a0500d80b182c50b2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 485805116 1250 485803866 485803873
    0x80109030503010b0a12050114030111090901051c170405041d0607030e070305010e0606011b02150c1509010f140f01170a0813060e030a0210030b030102040902040305010f0b0a08 78
    0x202015130740711340c1021a41508000c480314a107001070762107125040c082c040031006100c243d4604c1041600b502c019030080855401d0034030503202e0a07200c0c1c0b19541d05603041214805411601c019010405150020b00a8101034074074060300f000b9134100000300300b5500261070a101c000c0032070580030503124920780d00611640c0040000780c44284280d10501c0340c004e544c003d0320452aa40d407211420b55007041180e4103150045010b2002d503680004002c038003071601310011031244c10070350002100c0300e4851006e40146140090304070707403052080c00100380140e451100781e07031281480004140201315a044004905140c500804840c080403400e03144103640c0807814510303a03801d1a0000209040d02d1030700341421302c00d20045d00005010b21014121725600340049440c0340b860200d00078000b4002d890018082c0d0020340c80381000da210700384980c0301e001140c00c002c983c0c03480301004a070080c4103640c41824094800b0501008102064110f4561500110b5082c400f8000c0141002421580781c443d11402c0e070f2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 485806366 1250 485805116 485805119
    0x36050607050c031e0301050f100e0108150d05060103020a1d0412030213061d0117161b141605030d110312190c0f050a0c020310060e0a050108010903050301 68
    0xa2040c030082c524000c2c1c080c140d908107041e1a60a00c80001031440c0c8220f000f101100600040c10001c2d0304401d01c49040303d05811002d4001e4003d00240c0500d0b000504105c96500040c00800f29010030000c1890007a14150782c40034282007a94503a4000e0008030300c120900e13040000c520041074884a94020000900b4003245c4440c0d40d491b100c161605520000d054080c0116103403400301c0d00e0214014140741d2105c151842d4101d035003003104030b0040440f80c1403210f070014440780c0b610184811035100000703010001d1b4404201e84155400740c1d007164041250003149018104002c20190b18941c0c2500f1401114185d51403042c1c00f24a06055001d66509940002e4004030124402c0041c01c00a00c6040d042d60f1510742808801c41c6280c1c0300f1500c1c1ca01150f1101030b4059102e000e4410a10604e00c2e0b480d0039400d10540c003100401600c00d215020381000b00080541040d5074040c044020f010340300b0001000195520041440c9415046038003451080c50200000b60595041c0038040c411641940d0742c91960303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 485807616 1250 485806366 485806381
    0x3181502180306311704080f06010b0403060902190914010509040b06010f0302090a0f030516060e0f0a080d02060603060c030103030c0b0c0c0106030b011a0702060706020c10360506 79
    0x4800c46030b844841c0c4810950745070081208008980305505d980c02d403640c2c0e078508140019241c070480d0091094158040340c01004044200c9080da429240d001d9008141d0002c2800015140703d03040b40e0700b4900754102d070700004610354075034012509807031106100401680d0302e20030042100d908460140110340040005611503106040c40c41d0190600d08005091200c5400402d242d5041da800040640f019a40c00784140502000914488641c80076204140360802e4030040104004000e9240901064014104503030784803445c000c06046c5400c100c8a100180703c030001e61714071041d82c00b90b000f40038400c04210058078100840341a00c0d09612203082c035101903a140014000000c0c12060001c40c18040300384029420f0080b4401140100380750070070341d41000c0c100341840060307540c9400990402c01800e00180c842006407025103401210058440000c03400c064100000c2540c2000007a03d003440ca41201c00c4104240e1401a000711044068800d0444001074001d0381b03800042c1c510380c048000607408 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 485808866 1250 485807616 485807671
    0x15030402061204020a03240e010b0f040c03020c0307111005040e060904030309140a0c150e040903170f1b030c0304110604080d09150e06040603181502180306 69
    0x800c1c800303404a00c241b1780c0ea4076a0701d602c0130040b10310105803918a8042c103640c0001c0c010004110341c1180208640c80d00b03000090310301d000c3e03052041e0113543c58800c6000601e00950654094034441c40aa039034900725458400844280c01c42e11520a013040a0784584c1c4c5407060040d070741a2410f0712100392007901c40c40200090107000400031010503807200344c040001441241044000400716005140c551817500d0420220240e0703400032540e458900800a030302d0b0f0307409075031440c0c0c002054400048559181c1000c40d4801e51411401034a000c101d4144209203100200d01707442101c3c0040d4030b21407010481501202c500c0192140c0046440c28404200401d0500c002202d00000090041e4541903560710702c98202403502c440300000ca035220800b006281101c000d215001c406514000e952843d8560000d009409940508801c2650310032014507400a00140c855401e504038030180001d42190595001950001800d12001a144c0800b003840b8140090780701c0c002c010405001c0702e08200b240a0800c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 485810116 1250 485808866 485808871
    0x40311012f01110a0e130c0c03030e0a020418020a05091006031e06081005090a110f040b120c0307080309010f050c190c180608060a1e020408070e010f0b0301050f010e0a080c150304020612 82
    0x80d82d0050846080c0181c5c0c5034401c0c0c903f45080000aa02641602d004001031900246c1c490350280d030440c020400024070920380d80e0140ea00c01e04000070b280d07034031304045150000f94401c1c181000d4640080824045000142d4192803088508288440d03661580c0f03140e1540e003080b0004090760702d1003044500c1450102e0000f074050101800000da2030000700000740924009680d107100980000b906800c1c9421305010020290103030400071480c040b5407100003065009080a4081001404038400c0010802840103100c4001c00000001d21500ba60400e0024801c42d846000078a502c50104011708074000c1c003c0b01d080b2030140307026007070940d541c00000c0c1c00307040d042d41c40301c00c103035203046061245d900a4400f0b08040c040d5440100702003800c1040e000901441a0080350221180d001c04014035035482e4100d03030554205035001c0c0540c0b102e010060b907c1e91041c0809aa12190903c804603c00000140501006808540300c00d291a1595092006880140d030040c1d000803041007174041c1484510030030394 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 485811366 1250 485810116 485810141
    0xd050c0a0f050c04050a0b0a060813111503040c09050601022406031f0504120809070312091d091c0507020603060f0a030503040311012f01110a0e130c0c0303 69
    0x100f2030500c00d0000b60803104116244807201d0342d50903000c000b07402e02c08110405130985003450f4034241080081c616900205802c000c110f070001513001c1a0640390348030350002d0300c2c1c00f50001035180e0803c1d29002d807601980e4007851142520b0100021141c0d072000644a01e0a1803250003000813a81d649001d83d080c003401020540c0621070f040d0900310007001c01d0a00703042480700503000107850401b440c02c0359980074012041c4040141c5030061100300c3c1808285581140e43c002c21481291280c08001d42c0c1195040e4020312425010051017582181658003041c403982208080c0d0302d0070050107880c210340300304100360140091003c0c0144001414090000c54020384000c180c10b1120a12400050780c10a07a034000b2251500041000c10030003458003020b04940900f400d10881030849034107201c2040309200d200003006600051515150301081d400740c088000d00f0100135130303603034180079014082d000c800803510b00a80c0d06040d004081c56152061503060f4110b03540e65100601151012806400760000f000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 485812616 1250 485811366 485811373
    0xf06011b03090b040f090c020a0305030c0a020c04090f020a06050a120b280623030601080415180302070b03160c060b04090c0302041506050406030c0e090f090d050c0a0f05 75
    0x82042c8110f1405440107042c0c07020201e80c00c1e8240900c03a02035581180c243c90956001d40c028000294111090340c0d804242d00706007680302e0300e001368128900341c4a107110360741052074071006000740004c126884805a000b40c444503080f5903038200c1102c0c28031a2903170100008041081041d0080d80c9900001c07e0440001d100d00b158030340084062500200300c00e95a408859a060200322032604002c28014101400f040710781c11070622a03404a040c030004003070504000340d28000601b0091032103184d041841e1841000c01540840707944620725a0341d0550150f0142c814004005441203600c01140d1050100d064000c2c4008000541590800061030046030309503210b411506039619284202c0c6035250007103000c2010a0302e18010f01080b180750203220944191081002c2c4076240e00117040782e00b1680c05140004000c07050758001c1f50314402400d24568004a08024045c850000e00700e4140540c4500003540e4104074403000c161075030f200b11103c4100540161202c00c002c5260401d031041e00314040c2003507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 485813866 1250 485812616 485812619
    0x160315020702041b0203070b01140112050405032205040f02190309051c05090411161e0209150102060903040806011806081e0c040b060904020d02040b0c03120f06011b0309 75
    0x32000c13007054202c2050040c0d10104480040c030042043c902d005161030b1a1003001410f08000080c112020400c04480c0c00c0e80b504003180800c0401c200b20b43e08688401800a4802c0320030250110340360380303403080d248a242001000c5401411a1085034001c4011148040c03000c00ca071007064010b442c43e20307801d4071580500f00f482c00041c00ca8002038441164540e4400c0d0f65403103660f0800003180e505840c030442c0180240030058130a03181c100f408211940100b98516112901c03060b41050211483c0c0080d0480040c81c01d2089002107940200d403925026002c0e54101d40e10446003d03901d029510524000703038005801000814003100030302d003000c1c2c07049801140d5240c1f1344042e5860700d0b070005440c1ca041c0c001c1142c8006112024400e8a15a1200311014480303805e1407400078079180184001148210760008803400b0400e03d69040750020071130440a2510703400103255498072500104400482644018005295907000e6044079114010585605a02c403480401513409141c4408040701130081c1c1060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 485815116 1250 485813866 485813891
    0x20f03070b0f03010f0e1608090304150201050a050601030e100b0105070b012309161407050f071a03060604090504060e0124090b01051c0f020d0b0316031502070204 72
    0x5140b4003841100450ba65454012001c18961856015501c06000701e02440225101036a081c11144050f1800703000d16114150301a00718411039100c4c103070713580101c0c042d41062a01034200b11300c112145c0340100301aa495000540035591502034071185078100c40e050043c03900281c1d22000c070070007040c505141004180d45d1040c1800c0d5003a0071496194840b0b056461a44c40e04081400d000391060b81c1c82d448609001c03a0302c59142d05c009a07a60240a0744000d910040c128045c29501141d4100044035000100742c40202e86401c414007900e450b1445000c0107002040d01d1408a82c054032000e8413041c070b031501c0c3c0501c080007008003820417a00651102074650350241c090240c100e40e12200b00c541e01490501c0312035a810024a6403004045174140480050b11381c0c0c000c015561a00d0300c0c2ca42c06841701c983d0000d4071006001c89114244860f1001c03030000a140116884003103001019411110304940e1500c0d07401c5032400c6403100408090240d00914150b413041e401600b5003902c00f40c0040303000944e001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 485816366 1250 485815116 485815139
    0x10605090f0402090a1505010309081e0a0807030e03090d02040b03100c030b1e0f060f0301080303012105060c0c010b061b010c0c051c0905060d140603011107020f0307 73
    0x1c89103441014090140029480d10410603500440a0740080003119400c0d41c4c50b09100019105071414107950310844414030100e0b0044410500c4a19042903620110000708500c9400075015107000503121360000c0c400d18041d210f21045850044000c0d400c1840103010012500c000f41c80c101d811a885084417141a10104101d490000d00175901041c642d148a000030308680e444a01f1910a2060781800e4841d1902c4402c0d81c41501420748041503c0a04007000c228244074040220081d400b00100002d400c00c0d000c0055410780d0640c113586101884031156085d034043c0302c84030180060f0411070201d24502c4d066002801204a480008528641d05900194594101814882200c140c044481040301800e00c00d482080403542402c00354a115504c07907070344e96404290410100158045100c22050198061038001c0070700806081d1303144241c0100001510b80700d01d02c550650398a001144852506009410341a5040c811540c1000d40c941c0801194481e00c3c09013036018015480b02082550100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 485817616 1250 485816366 485816371
    0xc010c08071404180903110a030c02092d06010e03010603030302030415060605072a0602030705060903031506070206040509010f0305060c0703050d0209041116110d030512040501060509 81
    0xa45a14855140150002d420210042d051880d10b120820050000c001c0503aa000140d0388402c0d00007402910038903050300d03c1c0580f840040345501c100c188800030160301601c00e046040c07081e18142e5058176050103038440119401c041580300d001001c2200f034050118410107500c50414908040382c20b8039000840c1c01c440c1160030540000f40c0000c1000180047c11184801501501d50104082860a94000c0c941e02601c0c4008003945480311480c0c49402025001c1c0e4140412101800151642c13030101030743d40e502450089840380503110004d403100300040182c80c86507000e80c0a1004800316201000000e5004c401f08982c440818030000ca0b940d150410b80c13030f004e010b182c40004801d9055040481c58814011f12058200706c00304911350001c0c2d4404213131141c115200c9400f41e110003c800c0000c002d0550502d40d201d4035000414503100041e40e40d0440c041d400d0080e015411001e400c8020b00c1800703408020081e02040c0e0403c109400c80e050316603403950248c014000000c0c0c89441d0310000c4c200b650705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 485818866 1250 485817616 485817641
    0x822060203091e03400e090d021b15040306140117060103080f090607060e0c120708030703050a02190f0215160204020f0c01140a050c07081e0c01 64
    0x1d240181501d1815118800f09a0b2000c0d005600f030a1307090a02440208560600408200707101401c0b9688002200030070304c0d21481c50050394200f54a4514825280c0310440d40c8001501c901038000c0d84da40d002003505120400e003002c51000b8501c84405100051100719512607407060100b000201054040c800c00b81da0750039034000305103a5454080324050b80c01160703e401105811240040001500000455207440a035103d15a240c851950004e0000d00070400701502d45820110305503c100d6001c41c800a21483c1103901441400340c081035a9542c11480c0180f554541c0b00300210b002090080d40075101007409481210050966007003584061400300c0411144c000d2115604011441c1800031201781010540400f42031030300c0358130584100710b65444044d020f81c0e80061042d114251850485030f0061041c8001d00802038403046030b00030f010b801c84140782d80c103240c000420521880c20041300c0003a5004504582008250300191800642e4481540180c0004000301c41000c0400c3c083ca241070800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 485820116 1250 485818866 485818873
    0x25120909141501210614031c0c02210703021509010c060e010207020a0303020c130c08040f03020c060417010e01090218072d0905010201050115030906060e0906040302120a082206020309 81
    0x1415040d1409046d0301c11405110747c001d000d800001d14804c2c3ca00c5404101c072032030700030104030503800450551100f1140380c03051441101c4d03c541602d2000100e00e000c0308d00c252040c428030200400a082d06005031200e072400a080c1c510403a000c81c0d03c1d500403400221182000610708050f5500040c900b800c0b5074011005600b005000d0485071401c044c1040307807070050440520074a6070800000b040c210006100500c00c203a04250708050510030070039a4450140500000c0ea00e54454072920180054110040e0007982000c250706525070040c05900c8aca80d6025180f5516141e10000841c2d03c01001040c0d0720402c01210406d0050021007070300800080840d50120a4220108400800c60307001d641080b810341e0b06000041002113000103030799040380d120746000694441e5508e000310240596500000704904000d0900c0b5601c00040703036890080f4070a4084565001c0042510325060090a0013500841c8000c80084c0c00d401c004000c101c10f4000c081e10304400002240d076800100d0708207540344600c0c2d40c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 485821366 1250 485820116 485820119
    0x204021909090b04050103021008180f070f050d020d031101140403030509010b090c091e030a06060f0f0303081b090312041a040803040b251209091415012106 69
    0x34490f10801080340b07015581844950b0454000c101420441d5210304100005000050052940b00310544205507281040d1105864071407041951101c8501500360102d10310080000c041c40c01803510485194040c00501c1c80703402070385081c0c0e900c0c06412410380301c654071100060300403c501e203151482076110f501c000a207400c1001602d0700f100c900403a540d0243e000081400440c0c001c1c50291483d4010884042010181c16002c071842181d030f89a409416101e00d4101d441006610b401c004103072205840c40810070b950b0f801601c81c00b2000f6210140101c0c14580100d008042c2010344004410039813801c0602e403403551700c082481d100054903162410fa03c00b1a0602000c100d120144c190750000c40401c0d03007440d0900b802d9a841e48640d00c54007508000018055030076005120400414500101c5000d520211a04058075050503034a12030700066403580b40401e012041d4445e0250b031040562045000d41e807581107407580c1c034a084c02d0071410300801407a03401080d10542c0e101c031505100f0f0342012070105d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 485822616 1250 485821366 485821379
    0xd050a0219120e03010b03060a05060111070b0d0c02030a0c300908010605010509010815012001020c060601050c0307061104120804030b010506160b040c0b0703020c09061f0503040204021909 83
    0x3c1407205803144640d06184944041e03950005d14a9002640716000060581718280161b41501e640118450940505000025990760b8000941034024480d8010300c0143c2810300c04a071644181912030300460003004105020504812100c820001912800c0c082e0302c0118504114545003c014400040c03180482400054800e0103403500905003030801c5818044584c0001c0c04080008003042c513080a000d0001b4002c0c1e00c250056450851501c500031005910720220601030342c416200141d5921808001c1141948140101c4030452040405141880c0d0b041d900c69025241d0340501922100e0180000308107200120715024001e40304186c5d0680d901c1c0b035468002407690741680418072441e01440204040500380810054041d40031942e02c00d103075240d1626000c10080385d002800f050202158180805d0b400040000c99070340119503480c001d503581c4c070400205110302c04510b010400d8003030003102ca007030140e00a1900144000d0002d07003007114060b0304040d03290201280a0014041c07880c204403c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 485823866 1250 485822616 485822627
    0x11224110d06050307050a050f130c0804120903080319060b0a1101060e060a030209101e06080f04031d0406090903030b180c0f0901120e0f0c010804050d050a021912 72
    0x2094203030080c00c01c0c0c6246c4400654080324030f10030b4138041d94025003200815500c8011417880303100300f41c4040054041d50600100000e40032035040f524940101840c81c0014001c1c0d52a1007160750085031f151455a0301c0348046401800a8008022551a6100403078440420700141100b00d5260b9504103d25000c500c04a003924803a61082070300142d200c1c10f0090584601c144081940d40684402d203464440000c2d80a400000303520004000600742600702d58400c04c42c4258040390000c0c1d0340c2c2d0107251206d4811403c0c0c6002950006c000c640601d52650640c421421544000003000707000080450b5500703442019101c4e404000c500090b9134580c52000340c41d00c000c0d90b2000e142100804146480d043d040e6151038031444c18100043c400108006050741e1140104101c00600e05500f804100310080c0c485a985130100100c0c405c601802c1c440309065403203602502c4c81150000010a000c200a207800c1d00c0701da0214032208114041e500c03001086094801136121118820840c4581018821000404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 485825116 1250 485823866 485823869
    0xb1507050a050618071e0312050409050f0a050f191d060108070e07020313030206070609021e01021902091609171011040303050a0e0f13061805011224110d06 69
    0x3018086e4a1000c25135154604101c2036070303402050604205480310f8241c40f54000c3d13034085030b207040c240310800071080280440d5502070b091124040c02540c80e5000c46000300c01c1d0403202200d0320540441400110340d01c9030001c54070403244a500c403404940c00ca10349414000309810030006940450800c00c40c000702000d205034064800e10156003041500920300084040d1480042d1080c480400d00009002d80e0b9400b81c0411580141420084012072074803080301c8940540aa02502070342c2c4442c0d00052044c10703220803c07a8001c00c020402d6036248010301c90703084101000b01c00c010340708902158011074081e0299849038640000d0003c126458884803e54641540802228a0506c42000040d401c8400d994244003a82421985d0010040c040b40c40800c130141c1103548061412a0460007032036030740c480c0c004d8a10f01c06070807540c080b03004404815500300784a02c1c01901c0415a00002081076104919020380701c0354181c010008040c404202512040010070b030303008d00000b070494205030240c4180070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 485826366 1250 485825116 485825129
    0xb04260a02130504060605040218040c03020a050702040e0a0b0c04031101140a0f020f030f0c010b0406081504031101020a09150c20010c08040f030b0a0b1507050a05061807 75
    0x5050141a80842d2081d00b41408414a168844010404003d003d4000c44083e0101030800c54035401441e03d140031304c114106405000f00d18110548400d17030b00c079000700c40c081c030381030b0300e40a00d00009603007888000c000c04440d07003e0f42c0c0540d1300180006244070319100c0c050101c3d11603003030f01c2c0d500b941490801c41901324201814490108413150f94250203600b59400c0220500b084002c1d4039030b102080c5c1c01c0004d00c490184c05400300240021100080c000600903880b05a8000c1051011000520085540c94060020746501070304002d114035000f0600c90b5071040c401c1c9415105440301002031030990f088000454046021311400f03004211000780141d0303000d441d92401200c824030940b6803040300405500e080d094440d81c842e4106450340104904c1e100103902100850360780303541d0700d181c024017402400b00312003082002010803c3d20081c0d000340c201c84400203141070301288500c00041c1d540d51009000700c869002d0348602c0c5000c51402c0c40240e1090f105040c4003550214103001860400c2202e40150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 485827616 1250 485826366 485826373
    0x301051c0209040b131703090709200903150903030f06040b090a05060312120603010c0f0518040e15061201090309050603070309080d0b010f0c03080a05040c0b0426 72
    0x22000d40d42d0380e00142d40190b080b8400340003d40300c0384154000001d4100c4044c10020b103083e0140c0a544030a00298418024881036450007506c500500003501c046603c81c030118480170344080b94940030b050081c450742d40001d0441d00320403003000520904c0142140c0c518019000131040201c1c010701d100000b58800c00850b0308112894104000401030b10b8090203a900b800e98030030010b40c141e20100b290000320943e0801d00e6440d1581d1003810005103104840c0369000f5400c002c50402814050031104200c00e003903803546400c1c803060381900e540c5c46c030020303000d00d501c5500c403000400010f000344400d078907030000011140704038a0450103101c14490741d4004083c3c142e14101c040d402007944600b820003a1035048a00c0b99403a262040201c0141c014014040c0c50f05400042504030241c9541c809040303175500707890300c0f80d452488540036915064691380c080e01207008040000c050000c40d138840c542c454840c0d0100d03001c03641c4a4010724143e400c250009041c0700e03a643c0070724240034003003d02c25403480001c0700107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 485828866 1250 485827616 485827669
    0xd0504290711120a0f020a150c0305090a1206050406060f05060405040203090312180d1805061606020408070e0114010905060c03070609031e0305090c0d0201051905030105 75
    0x11403025115008025080e10205038140d03610340d403502d081c422000a640704849407410740303041103c0f206035284012449011200300000e4240a4400074601c1118075455981003201c80340c03011344641d4041082560311841007480030410000140165001a0103010005050318003454100b00b120b0958102c0c034110480c00c8000c20850781c2e08000c0300c058803002c0d50056103903121046680d1642c05000c0c00c503154000c52408001008481103e403c40c4079100008594003000894826599a02b15900c51001064090420b101c41d0424000600c01c2042d0f050000c09203118941351401207801c40d13040100c80d40c10111080060458801006015010880880780c4030340303810700080c05849503031103140d005420101d81860702100070b02c29560030a0304681c050060003030503d0000c0c002d40c1c0352081070381c040706000221040e1030700c00d214991042560000030001d8108442c200300c1c44504070f1100300e0411a0070400f1a11014458820591050703050711040e480b035040108001420004440031580b4001c083c50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 485830116 1250 485828866 485828939
    0x111203010b07030f0e15070c0b0c0a021e01020712030c0c15110c090a050c041d011a0a080c0c0a050709020a030e0303040c1e090c0e0109090b060706020d0e0d0504 71
    0x7491440c01c0c6c1aa041070742d00c601a04e88030312403407941d6110a214403008911041e501c01c0100362031468a1007201d5054011440341d2050805420f140c0301c0d5401070380a5030b014800c88100c82a8a81c0c180c0c040c2c140304c640c9041940c1e40d1007009149402105003200110340302c550442c5c00c903980c280210b040300045c0c01c071001c140000c143e91020081201c1200e540319000314000504000c03c40b0080e142503000c202c49150103d102160200d820301c181c02d0205510348101d5103201d03040054440940241d65598070740d880300c134000125a0403204042c07500d40600b04c4450700141c01044140b0003800d82032000368075440303410805000c0305d090307100c4444190010070402000956170404013060b610b070311140c40440e400c0642801c1c82d92203180c00000c104d80c41c2c801595460342c0c20002c401703032440c0c0036602d485c0c1c035a48949400080d10215000e0070f4022909201d0304c800501607401406080301804030010f900004114440d00e020080d20b001804a100001c0522201e103102030f900480341c0c40381d1402000301c1c0380c481 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 485831366 1250 485830116 485830129
    0x6140d0803041707021503150a0503030a0c080d0603060902090a200309030d060b1c150e0903070b2a03010e07031a03030a030e010608070302010e01111203010b07030f0e 74
    0x1040241155145003003c80f01c10182416918a00c1d000340c0021040c1081110480c8154000e48901c41001d070007a800d40e0992800c001050306a58028001d5810005c9048058440501542045614410610801400c01c94503c6001c00440c01a28040b0704807a207401408040b01c070240200810341e00b810f888119200040c1d000b1032503480c090f101c85941355500b00301c29086015080e029182c55042c410005851568000503104c05110800d0014948110982007021030700c0c5880c00d076400307589441d401c20146204080069101c510360040d28030700040e568810040307031011540d01c0c0102d0340c01030b000c0c080c294068035801c0005440800c580c1c40c55040c840310f1110188020540e10030191100f24a0f0100d030008004040d20a50107000c0b0ba031105509200074024000d50014504650301e0148009401d03500081c20508072034061b196061040005001100e082031118998442d80c412010b41910740d005500c0214002e0807001c01c41d43e00c0f0541850000c05c0c12500d030103200204802040610101c1e0b27038a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 485832616 1250 485831366 485831371
    0x230d091d01060818030f180f0a15030204051f0f020c010c023f0c1e0d050f0d0203090a0806090d11150c0d050907030f020405181006140d0803 62
    0x181002955a81c514138180160303080e04500c11410302000c919482c0c0c241c10710b000781902c41020040c1c0b2032038400c03070070074000d0b1402c1000007140d205214110411030405000407004070f0030900d14016290603200d0000c9600100140c01031000040036400140307100c0d034030048242442c481840075240d00d00c100d8000900d040081100030348600404208803600e840302a40c0c01c0d403007035451003190440501d0114200550321490b04014154080e459400c9414500441701c9008084e03a0700300030118160203804e00104c6c113090b00d81100c551051035283d86003940200b040d0450768070325074019952602d0f0a41405045090b41d4030080859110b5014020710490100d40209071f040c051610385200c451803801e0501d407401e400600903180801c142807005410000004200d444109a01844103864003500c8550b81ea04c2c40c03101500303c5154072030610052420f60003080d00100090002c2000202e031090007410000b004242a502a603115010021003806080c4208262400c468041031101d803922160080d2200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 485833866 1250 485832616 485832629
    0x40e07062715030e01091407050a060203031b0705030c10060b0a080609100f0f050a0e07050d0207050c1315090204052101110c0604050f01050c070f230d091d01 70
    0x80382c00d10004911903400a2114400d02c00240300d95140c6080c140125441591621400e00801d080400c8030304103240d00008441c81a401103103555a48580400401c10156120f0400031081020784042442040585402c1000001404816001108190455481d58400119400103111440159400441c01644050151005210303943d5003010100e1005070b54000d1002d150140d6404070303602c0d010440d040c0c160740b01070314291242d0752513250b81e0340020400c55071200041c0e010454010000c50fa038015020282c4a68100d807400e0300c0d100001040c903544240c0d080c4007207a42e0a40b000c10030450182100c020141404118503103420040440d520703c02e641001d8180d00100e0541350701850342503001e00209200303104590344030b80c034154442d03403105401d481c141e0701407142c54010081e0a9061042600940c0214111407070410281d940000c200c1d49110150340480910490424000a0f400341d40c038040da01101900c05428180c40140c10700840d40c00c900b902c090340d200540c10407030309010294190b440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 485835116 1250 485833866 485833889
    0xb010c0209100b0c0f010e0102070f2418061b050a03180c0303171501020304061412010305280b06040203190e03030a0b0603070801140f040e070627 65
    0x10b80c103408454910301580030200c080400a05149840000704800050b4050f500090051000d94441d8034242e00940201a140740c4801e80c1d00380004501060003210526014501201001007001d641c00300d50a8180384041a100c0d0003585040244601c514564140d40c629a0039107a0b0343d20000030443d0041caa980380500d5a07489407010003406200c450040349a0040c0d04d550490307224500102100b4094401c4002c0445007800b180340c603d403440c0040c01801040e8021410030f8a031a0003203513200da4400c1d071003040c00001c00c02c801c0390500500c1040e0180d40240300030400c1402280c20420700e0106031441151020400704c21400060f0058103482e00a10104d84c050b84944501075150411045c0c4100502018a4000180760b03075000440918840c0e20300c61b80400c8210320500500500b44421600007000031074001c010302c0701d04a9850702c0b0385e4212014141603404460000490f04844180880c590658030150040059607440320700450360881c5a12030306c04a0658400c9042100f0302401846e0142e40c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 485836366 1250 485835116 485835121
    0x1020a0f0e010509040f02070b011208070204020315091006090b0c0604060e3d02190c170f120703020a170c160f0b0c03090a060518070807180b010c0209 67
    0x2803041050704c400010080040113107070700301c038404002584031040031505952071314000102800c803a11150410703500721008500e00143c1d6802c00000b540b0003000b01c158540702c1c03a040a50b40e1141007260384904032018001c40d09509180001e422814664040400c3c220100540c91441342c010950b260000d502003000f084040d00d1003403142c00d20311200802e018501d07105da000340c040d8003030028500881c4050040c3d070031000c50841c0884168442c05030384000b6650500c54200000e44910074a804c440e000d1380c0082c00d04840703241820134070362041d005002c01000100e840000388110340d091503084456414214940303001400c0241142c07a400100c80504034507600014460740d02c0c174040702ca003035070310708200204800c8503d084030a00b41c040805070741501901d00040e004645500c110390051900304024400d8400541c0d5031405010020207080f13900c440d44100001c106000c104980140c06a10082c0140c281007004082c45250444581440c040c10034496030040c0e40c012005006c10344c0c05980c0a1281c0c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 485837616 1250 485836366 485836369
    0x110406120f0215191121090a1802070302010b041404080f0909010312020f010c0801090c0203090306180d0804031d040e0f0102030604140405030f1b03130f050301020a0f0e 75
    0x8010308041c120000c00007000c034801c4e40010243c2c98400d49a80300c0e56141080d0740c1266984041c81d400880004800750090801076a618002d0300841d0310040100007102d86800c40300d220b00995848400d2035a8010642c001015028002c2100c0703240c00369000c0016021003e40c407240208003400141c84040d00061890004c2441c03c11500b4400c0050b0540800e96564a06200c10000e802841c4005000b4100860300a11040c000c0304034105c9250307035804007642088142402130104850340025071008201000c43c5840a12016120f501107607402c8001300a040245810002440404e07400c00004004200000c0d80102c66481d4100200c442a1031061360030340854010038600d18103d106225640310540312580540055210741019201804545c0d898000080136510540d802492504144000d42c0300190070801b61204103985403881c03030711103020f510140c1550301c01d0042808110403d00e00340020104031206a005003401d800131490500b04407001002000c411800d03008104280c08010303031360b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 485838866 1250 485837616 485837629
    0x1e05060309210d0e0d0c141f0b0f0d0b070309020a03140a11010504030314031e04050307030e060903150712020d06050a05100c03050708190c110406120f02 68
    0x40000400d45003010300d141c030540c981c05070008854100e07100d041c803258180415002c03824000805981e142ca04140200fa0340e14446049051f4210503248940004464901c2d00e0f407840940042003d040015105045c100340042d1003004410302d400b03542d1782010a0300082503495020341c010f030103190004003180c80d4400030b802c0da07210f46c3c070241000c0540d8250443e80c0c1400b1071a101c045104641c40c030700d0a0358040042d500f5015a20015002c502d0301ca45110300d04520b04000c541c007a0b04192402e000c1c0d401030038002c550300c0c415a0700703403542d03400850f40000f015040a91240d2000d021a2900e0501000100003952200c00c3d0150b0210800b102c0b020070303503039400f0708012302d44950201c03000c0d52950003440a850040c07885208081c4220031030400040c01e801c00281603140c00c1e0a41d80c07441c00900141e01c0a86003a80421400c41d022320b1f04201000d101c1605003030041402030a551000b5910489007400320344001c004075124411072401c00d040060010f00c040c01242c0c0c2e50701c2001035803400b540f80002941c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 485840116 1250 485838866 485838883
    0x303040206220f0b030f09060613050a02090919060504050402060706091401020a170606031006050f0f0a0309030806010e0310091104060f260c1315090b01091e05060309 74
    0xf0724002c59101051158500c805180301d0980070f841008155117040406545100907903419400201c1c1c00d410810f007902d150011903025805d00c00262800c0e40700c1c40403032104202200d5000f1160f90603034030152004c1d002c2c09001c0052000711814001410030741c000800c070740b02e120703001030941d0b54401804080114102044404482c00070086445401281000d0103440106000c1d1120490060004040d0710300401624000d16000001d064024145441900d8943c0081e81500c1c44d540b0030300c80c01d080c40c0b880400401080d4925600401c02c95140d103000b4100c49000340680c0c0c1030010410291081e500c00049041d881c02180c41f021070440581e0520159000580d075503540c205007008004188102810240030817914a580e014100c401100140030a890031008010781c00d4101003000046032070200c55040d03d000780800c000405424100d603200d4144130940c0900f001d2600e80c1e0350b2a1056800121020040016400b280f800c206149110b00141b0400c0c0212071240b003011011540381001042a0034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 485841366 1250 485840116 485840129
    0xc150924020d0206010e2d010609151704030302030601020f0607030f11090f0112110c010504120c080d0c090b0c0d030c020304050112050408070f050609120403050c01350a0b0102030304020622 84
    0x2803235071103070b600510f0301b12180561040c1070b000c0c41d5a203902c14840c40c4119240c040002c05844d05880700c1c3d600300c01962026150b00e0440c0328280c24140650401d11005000d003556850010b40c046200f0b980006585410402180f0030034140650b85254030344c10680d10001500346440300ea07502d00f0821050007002c1850480359220000700300700c1400c100540c08140994012002e000c81c0d882800012205501c04180082c10b40d44140040c5100c641150080c105001060501d00e200d182c03100c00b01010342c0c00200c2c10240e0355201c41c200304401358061007808060200751000d14035060420001a02080c816807100390786643d40d0f030000c0c003400041c1003035403030b0194806070b4170b42d04d1440d5091003551420140e800c424a07024001c0e150002c50910307800c46080782da0140141129610190040d65880c1c0006111070b078402070500c000032182116000d0321340070408100d4000d07003410010170301d404a524042490381554810000d02016a98001c20b40c0c0154000701c91040e4140ca01d002c202d18001000d51100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 485842616 1250 485841366 485841451
    0x221120a0306030b060901120b150603070518150403031407120804030306050405010e0601030507020c100f0e0a06020c060c03040b0f04030308130c150924020d0206010e 74
    0x80034030551641020040300c1c007801c10b403803a5031a01c00800c450080280b0865100502d4901d0007000902c0c00020160312110480e9542440d01c0908080743c0150b2044550600181c2c00080b454001280c42d418030f0038040080e02c000d981d40703074160941442882a400040c0038070040d41a10103400140300308a0f80d02c1d070341c00b03070f2005140c0100800281c804042a00d044001c00e0a0070004540e5051601c5010f0480c0d100050510b02c6840e18401034005000c0505480b00310f00869060a0503a140c80411840802d02076032803144c4c00240780c0008000855107c0454464034840004215440e40011070030004d90084070784c00d40e54075103c94140c2c039601c9142d1000c0034400010078420088001d241c060070407070340a81c5903000695201d40020180381d040c41c000524101508409215500401400318444100e078208203603107a8982802095801c003014070300709480180c10f03541a01503414805480b000400340003e00c400e5040c881030b503400c43c00c0100035025400b1482d03d16205081684402d21f025180070585 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 485843866 1250 485842616 485842627
    0x50705060c070303080c07020303191205010b0d0c03090209010509070512070504060806030c030607080703240603152117132c06120106080d08060406090603022112 72
    0x3a465030705500c410784c0894690300c0098801c84e9501308684100b0303130003405186083c4044000d913002441452009042102c0d841d400741c0355000c0c4e03105550290a000c602d036916a200607001405503600540a030f4109820901d4010058071881c0d09581907400840742c242203540d410703001f00e80600900c184600c0d040410f1044c03190342a0442d0051007566841c0c0d4900d06607640e40d60905070386020300030455416a00000c00246454800d007011900142585000f20b145c43e00740440308460380c00304080007856043c141c03003040101e805201e030329503031261950503012880c0390150400100380900c9490814203046590b000401407200810080c0c1104142c085441c0c0c00742e0f0034800581601c5004116188043e540440d21203032080c11030820f002008200700c40c0c140da880f42030251081080320000d03800e40d00c6640200e0480710074842800f403160140d441540f0703458030808000503100103034004802e191900b4001c0c005a00d501c2070b2000009403000d9484032176490f803003041e40341c0038003104000060300c404070300e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 485845116 1250 485843866 485843887
    0x30f0303070e1903120e210c0a0e060306160e0405090105071202180607050a020324061905060304031e0e01031401060f1b061107050d02010908090d05070506 69
    0x103104505581a64001d841548043c0140d15000c000d00001d031200031444040d0030014030500c4142c0345603a0140c204a0b00c10100c45030461541041d1034040703d80d4101c20800044c50500004400042c0303c100001c59260500c40c2c042500c4040c05401220b80c1d09180103810a49401481504c2c1d10b107601330b004020310f1402861071402441c090b25100000780d00302001e082417654900907900c00d4880c504030111120508401c022441c3d1080e10111861300039100d00002590342480b07014500d250503200c509558246090001003a42c00420592060301415111002182d0303440d00700c0306440094940c1540d80d20345003400d407000c0140c01c122140941003040c8282c04035078446001e8550f0002030701d00b442410a0044000b425500074003500300082c5205140b000114890f118800d130701a0301120400c9106055140c0a0565a0305190f1118a01e00040c0b103908100040142c441e20000c0b900c004c00c81d04440703a50b460b04501c11f55020710301c22038524043c1c0062140a004d0b0748000c040013000c01341d69951029 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 485846366 1250 485845116 485845127
    0x130302060310060e09240a080102043507030609060b101110020711010f0519260f0103021509030a12020105070c050d081015090e06030106060914030f030307 69
    0x3c0000107415981048440c2c1400d400c441d0080d09000c0d81d4030702069a1030808100300d480f44d00750641c4021000d400180c03d24080c40240084d118103070000c51049500d41d09040c0c260300101d10564007c1443c0521054000301050590649034441404544210b0360b083c41070240c4690300d88a540000b162404811554106d1140340760500d0100645036450500620b91040b4080d250b0060511008000030346036562050340c81c8c504c03199482c01c020b4109442840080c10010043d080c400100c1c01003602166901107854590002003003041c003421041c6803c007003c001186040c84000c1c02607245180145500240e030040d542007c4002d8101e8001007058103001001a8880044402651030700012a800a210b56a20081160001c1c000d0030b40c0b00e0000021540b80c180180402c80b1070015000202c1d94a03081c201c2011594600d0b40c8412611f1b003044980000b40e030014116600c41d0389020030400402d40c01084481c2207810140103c00402070703040200381001c100c5a507c55280c0400800c004003540c02c40f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 485847616 1250 485846366 485846369
    0x271e0606050708030a05040807080304061a090c0d090201120c0903150504051b0414070c020108090601081906110a09090b010206070c0b06121603150203040314130302060310 76
    0x40060001a584030015200c9100b40034001d001c0d110b0800019000d41c003950002d540141c0700b0340c41249000440e403542c08140d0420b450031160161102c401400720014078a00d0301400740220f8205405013030004171340b0709900c00c464400748802c1d01c5a0030001507a014201460141c01c4202082c0840241c03218003c0a42d4400d0004079800d410300001108030810f103128040c0710b80e603c8801444807521880412441c203c0c4011400d07407080c0c41d00315035130030712061103900c44c018011500d54904810151001401840c4000c012403d60350001004001c10140061001c000f10802290080c80000c00c5c28024080d1004026880825000084480344582d000e018001243c05041c0b040009400c568012a00d42e43c080d41c000001681800036407020a12001c100c1d504200e0080a405920b0609501c05c0d050202d17450310091407a074a140100309000408450300301184040fa011440e624103558050311800c0500e031000745100c801314403100c246c1079099040014640080103540c407894400e000f01a00b412a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 485848866 1250 485847616 485847671
    0xc090a060501120b060906250b0103050d0c03020d0c020102032a120c060711010b0909030306010f0306030206030f09070e0a150603021c0b040f050405030d1103090727 73
    0x1003940105108143e8410380d00c0404009056503d4040d0b240100449604030341302110305083c14800795101280c1c0c18044940b40c52049405545a625604100f42000c50402400701407000c428001d0000a50104020381a203505041001543c40c40e800103d03e54000d00c170000340b07480c0c00580a400240c24070400d980c040b1804104403501c01803224060442406041d8014902c6d600c1003012400190003a600000c0c84c4030801c0000480d90065000602e0b0581c091300c20003100d400001c148560f559002400070312404203400c09009407403441d03002c00c1591000a040711810340c0c910021404100d800e004a00c010001c03503000c074000342050843c800080ca07181306109119040100c0018100d40a4001d660101e207820050102d03015440c807000300130f003156449990f805a6500a00403000c00c1c0f41c032400d8040c034080d00085403203c580c0300100c07003244c41c1d40e00d507407044983c24410029509000600d81c000d03641043c240254080c040d05040046249178541d05031003501f40b00600580c55203512106025100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 485850116 1250 485848866 485848877
    0x20307020316060509070812040605070311010c090f140f040c03020c0a050706031a0d11060c161d010513090c0308070303050a06091808090307090908032a0414030c090a060501 77
    0x7611080310f55202001400c4c40003d0900f40000c003c6e40380132f40080c01d903140c003e0404000303c02c0440030250842d03094800e0700b00030030400d000900c4035094070700d080406801d00c0001c41c941d43c401c0c4070000b0741580c2520b480911898035950900c20b09072081e0191401184070004441120849141c5283c58243d240a6040002d10f05000303180710007402c0010079001040035145506605054880caa51880d01400042d0001c000700031142020108115002a440c4c900103c8408103044c030307201e00200c0e034100301400c6021603c01d00601c80b07541e400301c84000c96001c41000040380c40d0985001a0f070443c41d6400a003141d6808a445414160160049442050010410046c480c1c40300788031401c4402c8030301d40100d00c5800500303540006040b4401031542060080440d0120750b42c56a00c00140c4403209002c0314401300c04030500881c4808107204216068034008800c40310080d0503206181402248921140265407045506841c2c40921001c2d4045030003800f08819803905041450140481d403299a00151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 485851366 1250 485850116 485850119
    0x10e090f03040e0708091501121e020603061c0b010311090f04030e10120608010e191a0a0912021c080108060106031e060f0e0601170103030302030702031606050907 72
    0x100070044405031588503010f0241034a8041007102c1000004100002030700c07801c171402c0611400282824001c0c41009480d261300030b83c514003200c003c2054040c2c0402011000c0082d001a96110f06683d400320303040d60000720700715284410031b200b0301921074064240c1c41c0d40f100220903c070303404e407107103101d210181c403460070b19182c00240d0203001a00f01d4002d400614a1040f29005281c10300d501e0505150500d4a6a144507c0030704120407035104c0e40c00f00e0700581d9549800c941c040400e00c0f0004c03654412034580e0b0780036035082d2144448400e081c0e007108807549000300050400d50340c56116604891b00001c40441005100c20041d6072422013543c804400720210070380e40209442103400c0f074103803a0b4140141c0104d9180510580140500d6040340b51000c1c2c40c14006000788045100d007a00400f8005001c074202031410309002044030001e050305040000d5940d05000c0280302c921101d04495042c039006030f60740d4800d81d049045000c2d1001c28980f6a20251001007842006e4018500030400c1009480016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 485852616 1250 485851366 485851393
    0x2040509060f01050402090406051801061e0203030a0209061207480f17071509050a031409150c070e060a03030f0c0c0602031801030608030f070606030209010e09 71
    0x25030080350020160b80c2c40e41c0040c8002d0800da00176110805021708081188d0307450f10000740100c0c0b189041c02c00440824801004103d511a0b03005042001d4064100c000d0040344034029100c1c40001c0c405601c080c0c0000d1100056181c200488010b80c40c1081e50032940e041507040141102211b0303000348400e8421003210150b004004d816900c0d039103d84180b0220116440c6010a4000d03428501a0b030003180d100042000b255011440d0602682958030f0307c4d990340b902d031402a03140446088880b01c0c6c5458812008006000002d02c42240d980600707154007209402642854070380b1481e03a40c640c1000c6181d8a030f88142007aa00900994410681641e51140e1140004d409001c0101c1e00d050340410407200c10400b190003444040d00886d903603c0c00001d80503164a03148841e80d841d500150041e800020301d124042e80d40d00300401d0380c030401d280c2408401e01c1d000c00c841e80ca000d0320310902680d08000072407400b0003070980c0c081c0c0d00459000d0089005036940c1d0030090311b03424003211440c501e8040c011024490303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 485853866 1250 485852616 485852623
    0x50703020a0b2404020a020d0c0f0c030b0703050f04080405190b04170c03030307170406020d021602010206150a09020a0c050d05040509010f05210102130e150d1703041b03050a02040509 81
    0x6c0f68015801402220b003c41402c230b07401c0c00810390542c0c0c0011209025404034200080040c05180101890b14407810701c4540113003290781c0100200b410b031396550144800075018100316012194115100303126421540c807583d640b44071651080c607100a00040004800c0440d00491860303840b2481910010808041459201e1100700c4d042c1c000030ba0f00032000a000003444004a8209019060050400c084c0410310310413640302c50b50800346c141c0070207882821580e040042c664000044900402c0c5a011900824002c903018011040420340201d81000c010707104003d40348000344c200c400c5807000c05580700007a0440c7d006000d50340c0103580c4980085007009160404030210340003e080b041d44003442c148401c203048060404051555004c00024900c4540540844050f050742903c03081541840b0113201c1c41c03503d4801e8140e004050351180000440c50310943c001105a151000344d0f0380c0e039514030f003100e90341a40c58142113800481c04408002c0c00f03400188940400c1c42554200555101d00800b144d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 485855116 1250 485853866 485853877
    0x30f101401080a24090602070c05311410080c0d030c021c0204050406050126030d0905070305070b0d0b011106041101111b100e0a06050703020a0b240402 67
    0x20700d50040c2030b01d100182c000f01011040e10007a94450241c0410781c107161040e030310700510541c1c0721350700840c091090041650809c8020001111038031014081821081d08200e0101d0000004111070500409210501d0300004581d115011000384070341307440c0d1045005041603025402440c807803118007141c0380c10480a00f501c87c5405403900c18a114140c0d08000109914103400c0803540c000b900c255006031100d0003064043d501c10b100200d078544c1003080956103c2d000a1941c0b071080d214a00d091000d41c1d020003100c100d504103540101c0d03e4250b5003000d601e01500d50703100410b68030520200090094a044c00391984ca031352584e05000f07504540004480501d07260160440c2c0341c200c0d0700030070009901d80c0c400072114141030612140c2080200c0880d420580425840f03000148070400510841c42d11240c40d051240103424846502d04110000c03800c034104a00130102803100025442e010705008004071520703a42e1040907540d5a00e42000c50f49001c40403149000e2040380b1041110400345001e000703488 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 485856366 1250 485855116 485855129
    0x1c0803040606080f150c12072619090606051801170c01120f0f02040b09031510030b04050a0605040f1b0303050313030917031b0106030b07050702030c030f101401 71
    0x20085c5c01c04006913001203805070031030350184020440e1810246914030b489104d024170f40c5581070105511070010300e840059810b0300e039000c0044010008840f00d00c0e030200c08092031a1500181c00b59491410900030a4160029540903849140001152020301c01042c103880100400c20000040101a00d41d60381c4a40f40150214a241807038040000441d03001c030340c41c4140054049014005080c40100f26441074100c140c10240000324031840342401c00c01c8003402c0c4004203245006140800030201c0500c018040104800240c4000c103051250412280c00f0f178540000c006c00407820186031138007403401d1900c0704035040c482c0340316071074590b200c4c84001804994154450381e141d6950603d420031480c80c0c02404034240300031940086000c0c4038001d041c210601c490f0006690b542414a10060992181c4140d146181e0405500340300240f2201d20705074211119003803103502d900c00c1e440041e0a01d100c6030071094051103007040c05154680c0c00518840c81c041c9040c2d081044004e00c2c00794240030002405500c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 485857616 1250 485856366 485856373
    0x50303070816022e02030301050a150c0b100608010b07020a06080601140304080d050115021002090f09130201080c0703020a0b060d05030a020a0606120b06040504021c0803040606080f 80
    0x40342805005003101c40503007040c2c0c0701092a0303a001800c008140d101e80d00600c4416194400040d28030241e0015103941800103500b198500f000058031210207000f45a0040c2440da2a03400c942e0080724200c00b540d5100700310741c2503860b0a0005016114651041e14001039079080001b40300310a4030308440c4110307006031140e403c16083c024280c504003000f4200a04102c0003012840c50120450080c1d0b01a510590450780d0340e00b408940c02050b51410f81141440700d0040d5811800780f90000741600d8440402e020150303c80c40e010000410616541d1403c9030040b02e40001c1041401480e00419040e5100740c071f43c50352540340c80c80104010b014450008000d030740800d007a50041418861405e520007402810b420540245984039070a60304011103080c007507404803001e5001c0000901035140a03101c2c01803640d9020751035480720402404003a003800d000c0d0f66200085010354442c500301c0407400e8003d605c41500d03c0700503d03000520754011541a200d840c50127201060641c000710300000d40806c1a4004c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 485858866 1250 485857616 485857627
    0x70f06320909330f030309030715030908120405012405120309061914030f06040207050f19031805010906120e2b18090e030403080f07150501050303 65
    0x1d010300c0c440094030043c0502c20a4203800b00102e02e100d602ca0000700b0041c464140b510042c0140800c525540084074482c1e08140304611076501d001910350304850304031010700c0720b200084000381c004001c42500640f550800007000c60380c1d0102100300038042c1e48074200811a2065442078007400c01c03086410040d031503031040000c11851030141c1c11608040e64010980303240a40e4100007903019842010001084003082a208031200c1e04020100c5840300400c0d1005d145181401210f0000c650040131144503075800300e030307802c2400b400300034100304a1390107800c0741c01725484a209215a00d50340c03542100010000201e100005c40504080c80880d10b040c0c56400140d4100340d400c0c4d6500380015030381005242d5502401114020170000c0c103030040144608000354240c0c0004c01261710b22410b45401c140140f081100c44081940e080c803a0480d010400300013991f184500015055118550024040030b40206a03c29101502001848890b00c40c1140301060320208200d803064034000d2045e181d00d80c00605c00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 485860116 1250 485858866 485858869
    0x80919020f15090a1706090a11120c0907051801021f11070611040302011e021c020a20010f08190906060302040c080a050109060305060c070302070f063209 68
    0x486468880070340c0318250600c4502c1000c1410701d1340552200c9000c16103602c0003103002c0c2007070001c1034201181c030000d014620705a850720301c6003111403040c240c01070500c1550280c1d103800a102064038103000404500450a00c1d9400501c40d40000a042a1084515100307169542c000503070242074000c65148034011702810b080c00f1700103100e410401030100c00e0800c90b00b0000740191041c0e01c21840c1608140d07441d14218000184035008072402468100080d038895914183c000a40c0c1060004544c501031408040c0d05040b810005c4032803006100641c401142c4801c02003a2110040801e800e98a08240544281040f640030200b950441d509816200c1c03070507a48100c5811042d0b55038003c0b03401180442d540e40c00300c0d0494948039001c60024403c2c8050049040c00c50007001c2c014000d8032810300410f030660b00d0f040e80b5107902610503103000c200010510101802806800000e199503510210442ea890f4000303410344020f526000c01d509901048205444101d1140707140101c0342100c3e80e0b060891260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 485861366 1250 485860116 485860129
    0xa0309090e1f0c030501050616230a3f050a020106120302010c0e060a0516151515024c0603020301110406140a030b0d03080919020f 58
    0x5140c0660255021030620a0b6485400c0800e03404480c074009942c4103582802011150180c0285101d40300801407281c80c1e00340001e001131983c1d0092040c508020403080410f405890741d42d101c1030503003d4803072a2000e00c02c02428080134500340b1703a414442542006014100c5200c0445036030f444400442d1000712441c03191001e007038440071a00002071000d07242c01038400e1512440e4402c4005179101da00e507400c6030390310401c04500ae0708203a8005041094003c00604203006002c5c9520410300390781c805005000e4000302414401e00d05003001c0005140d0b1000700d548403c1c5500a201c0e03407000346404854800d2000643e00c20119940c1240e030a496155000c003e5030790721820401020001c8044a10031055001e8220b602c0101c0396500005c1c0ca620350f105041c03d4621018040b2481001840200285a000001e460551041c0b84030590f81c0c14000f40306400401c8155151030300038a0744415a002c040e04074030454000c100180803100b10b5124426550349091308400020b4101002c1070500300c9504016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 485862616 1250 485861366 485861381
    0x21070207050a030c061e0f1d0603070503091212010509130606090606020f03030c090603040f05120702012d032f041401091a0f09040c0206010e01080a030909 69
    0x5205440c00d5075501c1c0005021100d00c0c1c1c005031401c1580c03400800c22250030032000d004088018041d4940614049000362150050a41b07503400d128054082c0c08030300001e0820403054000c002e1909403039041840e0003c01c2900120b651540380d225075001e4048102c042c2090303900e01800c0c1450280c803a824081800700114014080d04604203a50b410100000c000340200c102904181c0c40010711a880c0040c02880e115801e10145001d800c05c00501202450f0356089811034581039442d5507582d00d644c90300c4004904a00c2d800340050203031994040300d100d842401015054005d0766410f40792500d40c141c1080d04801e840c440b05030204140010840380d4080d4200403050110003201c07503040e103000301d014141085800c405000840d00060180010a201e04a0800f0b000c000e00e00001d1041c10b00d41402070030048030392010546000410200526008601101d101c084094002d20001c140c040c4007954515080c000d1820700313012030b000071450039000214441c40302d4141d0380e54201c19140940c014014040b0b03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 485863866 1250 485862616 485862631
    0x15180403031a030f0c03060606073504060f12020406050d11041a030105030d021507031e020d0212070e0607032a080c06010603060312050d0f06181121 66
    0x411400b505195014402034050500d03070000361094008440805081c001c000300300c284035120a1101c0340c00301e441c40e280300d40d1121044d000c09242c1021001086450024426000c044074000038000c0380c10341c2d0085008504040039260503501030812500342d41a8001c40c010240080d006000c0c180c40384030182c002c0c51075242c0d01c046851416488161480441c100c2274884500210000010043d81c2010015000402c00600c05004910403208510701d00c898040d01e280d00701520f45040030b88a200030b0144540c5c503500080119902c1c0b56415072140a5040000c6604804c090100000d142070b004e007814050280d00186201c0c50420f00355007e4900351801d2900e03009890700900d492800030340703211100b0301c0e0710700500805442c1c0144015152408805801c00b0040600344041000000c009a12120080d5024200a9269000c10700044000e0040020150138242410700000f441003c03800501c4203415080c0c000c1c4509803a00805120a200b1203540d5001d6000400c6840d5004141c248002e810050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 485865116 1250 485863866 485863901
    0x12903010606121802060d091406060d020d05011b0f030b01170c0d090f030c0212150a380a050303070b0c0c0f060415050f1306020f0c03040e1518040303 67
    0x245e0040358039a00009000301e84ca43c0d68180d00c1c2d06000300800c40280011b00303d0300500e090304d40f0502161440f142910000d0107a03108804040420500b074008011512815904410840c45080c0050642d680c204240c0301003460150302e0300195105500c80201181040441d415a071116011070310107600c002c0c0b00511b019074550b4010002180c910341c1c7c0744224040d543e607008401003401040260b04c201c050303030345083c0d0151750b00c0f184007504072050f107610205000380026075160310b1101300d031540d00141344158140000707020018901c1d090211444092070035140c08580640f10030a0594a1103120740c0076001e104101c0000e0542020751005080349841d200507174461300840500300c2d1500700c0580b42110382405000d0244030640d0070344102544103096a40c5050b650070700c04141c18007002200009070403984c0002d0000c640340a40001c881343d41c03040d80112a0303169a65000c00f0801e00c001d45101e42c006001084101d101c0c074103050309007200790740700450001a03103540d6008e4000f13103030805070b0f03400c0c031038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 485866366 1250 485865116 485865161
    0x105150f131130010e060109080d0906030609150b07050f0a060b1503010605030a090c081603150b01090b0c0a020604030b181903030504050c0301290301060612 70
    0x72030701070144980000e00c00107449460502c181c404460790b240d040c00d0408903c508400c0c20075090300d0107904640400072400761544552004070341da044035030880d19480c1304076030f22078100540c02820601115129981005150740720b20503042580d0201d4503a002e41d881020050121103103410080850300e12400456408a152004050404580b008240c030f82c0ea594480c0c405070b9082460b001c004110005a10624560410b2000b4029010280c0300032003141c3d448102201b040040400c5030042d0402e10112040b01c000d5010501100c405404101c4030712507a8005a24aa00d180c050303d03d030000161181103401d0708041c00c0509641003a45141e109101e058402005a00d55900800144d402250700c041749140c03418030120400744c000440080c6600019030301e84060040c09100760165418640455580c5950402e1441d0031a03007000640e05529100150250090b04d0001e0681c80802025040b20007900c80f00b090f00300d80083c8a0740c13005c40c9a4100c522130312000e40d4402047c000a1603455440320 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 485867616 1250 485866366 485866399
    0x1081b04140c0403030306050306040c0b071a09010b01030608011401050d050705100504061701030816050a120207051f09030825081804060308040302090702031902010c110105150f 79
    0x2004180c1d00b10220200000d070078014140d244c041d13100034090680007421203080580d540388008010340700e529140341005c11070b0001c228031125076251030311122200803580c0c01c000749410b000b0202c0844d000c1c086441c00000241110040c06052050482d4006001843c0c0ca442c05001c81c14001b8101141e040c014208081043d81e0740746c1c000e03d4a4a80e80e07544a4840c2c0c00e154020b80400450100f02822080550041000131034080450b04ca07004d0340c0440c0a203480301c52614901c0c120781c845009107500081100580d109500042070030849004650a00f0001c0c00e40350400c0520b480300a100380040c890302c84c10300201d0141d000500c07284094070490110020501002400c5082680701111a110001585941070b030060207681c502d075004a8041114902c4c0d07030354a119034400d03884002e0043d412071001584803030003403065907846090070003511005003145000a00800304d520000700840d031210080d19111a05100d907900c05c0e0045114011440f40758010040480340032000703140c0c40540a41541c105 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 485868866 1250 485867616 485867651
    0x60702190e07090b16080a030609050109140c0c03092b0c08010b150d0c090509160212032205030906071b0503010c02070308030c1303080d110301081b04 67
    0x600d4091030341082824140c02c02403920215078441d0b4001030342400303c0003c08112289840985034040580e980d03640249000350003a104071340c4001070140c0340400000e03140c041500001d01d2400381c11540003003944c0d42c2d1210340e403e00905419014581c001c0c402010242014030044048d050909480365403000c44954069408050f000112080e0803050010403518100f4010301d01d007500b0443d10f015100c11f04024189480c06007503580c0000c5504c1d41c0001040b54010f801e124060240981451020f14100441d071610961106040e030040c0f06050341d8025448204007601e0180061040d01d800c245001d00030280e0b140d10201043d216400b0401c01c40440e13640703000003004280c1c42522008400301c51252004e101c0d042d141d10940c00399043c8041303d0803680d130102d55801039940c4030200580b0b0741ca903214885101d0049201c3c200d943d40362a00007205201c020300150040b07800948040c486c1280181c401d5000d80401c0c41940c0c0503a000500c030140d062420721a46c600341402610004806075040e0301c3c104e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 485870116 1250 485868866 485868869
    0x140d06080307050d1103220503010213030b0703020a05030406090203010608160f0e1003120e040606170a14011203170a050402032407110c040509100605030f0c06070219 74
    0x141d00014281080000600c0b01e15501c1410b414203842108001802545034418201e4540502c0703150b03c2860480804903555001504001c0d008540b10705e08a500249a06001e00040e505c284003100083c80782c0f40300303000301c850f10243c0c1c0d0f941504585a55607030002520368a0b800700c3c1e02d03548510f80032446880030002e02c07415501c0b51119a02e0540b03880c00340c605040b00c039003004e840c100700038042004403081680c0d0324048a82c8881c000340c45000851003203da0b0350300f443c0c5069001d810f005000481e16404150300d0485180c2c402d296003541c451454150845000076040110f17180018010000007000101c00008203006e41081074401d5a4070700c2c448a03020084a00c03c41243e641d030284015814200800c2c0c0601c0d1075048071a440c81d420745845550000002c1c112020400100c0c4030401551041c050f00ea90820080c10a101909091110780e031600449500c0041d840c0c0f074003600050030b00d000200f40d08090109400742c0151030440c0240086a401440140d81224603040c1c0714540761a02c200460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 485871366 1250 485870116 485870129
    0xa060f020a050d0519031812021606021c0c020f090a0914030a020106050904030503130f060e0601090e0316080f130f03061a0f0909160b0408010606050403050d140d06 73
    0x642d9200e6142c110b50705c00c81c81381641c2007018904032618058040a5a54010068004040502e00f10715811b08a180403e05581010503031f03409880003401c141c0000380c49100c403080101d2034000c54041c1d01b0132100c0120f0048040c0d803010300c0710703186412820000700050700038000c5407010449002d50f80340ea40e0005036000d0000b85c0d5174000038120710301e1503081c4501d0b409003404070351944007414542c034020140d01001c1c2400d0344011104d240749003080000c144009480360301c40c2c4180902440380840075100d8a091203082e28031401e01132416041744c0c0c048202c40408000440304aa00b10160300c450049400c102c1840c0c1c0104810808000701e03020f908032030710043c1000102400d07072504600c0d0a8007076411040e13501100d07010105d0703502913640e59100c1c40044000d0a41d11002a40d8480754440e240600c0c16150b411315080e80c503004655032007040700802c01c4d1107020000b03005d050350715102210944590310011f816600b14003034881c40d0354810324403170003410f02007104503081800201c0c22600b111550f90210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 485872616 1250 485871366 485871377
    0x30507030606060801030b0c0c0109140d030e071802090324100603140f040201021002130303020606150f0d020c01050709230919090b090703140c0a060f020a050d 71
    0x30420041070b0700800c006000285051041545141d50300c90000c03d028010005001002c503291414120942c050341500390061046082c100760711208548a40500941034006410048044c045000008480c8203c40507403031b440c6e034220031588101009402c40c244580d4140502c48242503042103607201c50f480200400201c0d001c41c00d010400b140c10018551100c001e140c140b40c140400c00c540700c121190700c01c040b050407030b00b150386030b100403820140b982c0c1e8500f81d00d51011481d680008602c2c0c8001003564480d800300d0702ca9031694002c003d0fa07482a43c3c842c3c0c014040800000c07100e803240e03070040c09603003007580700250030550a5541d00d03003501e400315590400a05d030414100801d02d001141c0d55000303a42924450010301c40e0801003031541100510b120308002807040144041c60321540281e40712604000e06046a013000c0181c40c0e00c03101c1078401174400c0c5003400a40030318a07130040b8003a0725084c0d0040405840070f18098043c3d0304d8140c0006200c06601841d007200300450400c1c0072616403242643e954 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 485873866 1250 485872616 485872619
    0x30a09020f150406080114060d02030a180507170c060304120216060314010b070b0105090c0702030a11011e02250b1606060b09010903080d0b0a17072c0a0b040204030507 74
    0x5101d8041684504e408007c186403904003500c4420840b4601250f642c40940d40340d4803000070401a0011904603030058081503819014080302089a00a507010000e10350949002417620302e0b90340035280703c8683d014108001040002c1c84080000c003000405005540d01d1000d0b00c0900301c1007042982c009070110341c075013410701c01600320407041ea80900780400c00c1c00e007454403a0b12620b1f07901005001c1d160098000d030010072103510901c7c0a03a801c8960085c01c07241d8502c0145452000c004c0708002080c0484c500b4821203009030101c4031f0304140c0303519070760081000b900c420107061580d113203181c40c3c0e004201c640500480c04031100f41c02808085005030000080f401540342042c221002c2d60300180e085542030111501503030307000310b20b44212030708542d00b80d85038290060b80300002c0281c40c508a5000e40c0701800000d030790f07000c00000c48a400e01c10080e6544a981c8a4034044031121106405002080d280400d40702e049000814941099011038005400c0f5031301c00c041801c03640a50401d503035662000c0700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 485875116 1250 485873866 485873879
    0xb0411180a12031224030305090405010504020304080a05091302030403020c032e0509010f05070207170109080d410c04060f1d0a0303051804050c030a09020f1504 71
    0x152400030700003941a103142040c162402400514070a0500042c0ba803980d01c1c03507038000b182150009405170054408032840f82c2e2440c000e82207521100d00a4082c1e81820700005191601d4402d1300e01c1250401a00c0f40b610410070012140c5078040c1940a51010501845401d5040f01e0b102031403060b4440d40040c8682480038040514000c661103c0b080b06002c4840017003e200c901c0130100a640400380004145900c4295009014011503203e441d100391501042111b0291700041e81c0040b100e01a0780c6101441041d400582039a10022001c1c0490000704100c190904140d0300035a1426402900b03448401c000501c0d003012401114003500d200f140b525016550351600c1104203420021049815150900d0103d01500ca00344d0458510700380064009810381450000c245c0d4211440002e10340499140c40f032030b0142164018100d01c981036945a058440c45003031921130302d4002c0c00d544000604554404ac8000003600c0800c004131b80107050ba040e800e0300c1d6203070b0582c400c608080307450b1425241e41c24800c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 485876366 1250 485875116 485875129
    0x80708181f020304090e100c0513080304030f020f060c1b011d030a020d0c0906060207060e040e060f0c0f07060c1106010b041503060506031314011e0b041118 69
    0x101a0740e00991514914854290000115412511503031000310740b506c2950045820400c90b40d644041041c1460b080c10304550744a001005c0d12684401c2c18000191101c2c1030565034062804003c00038030034020344602500d0100c50728000001c004080b980350548280f4a903040460001108000d0304e1507121140c103668000c1c42c04082000092030351048000700b200081c1d90344c8012600039000300e8902031184180b080d509140806818401300034491a80d80742002542c0d61628803525000072030741007603240702c1c1c80c0502507030041080201c02400039480e40c0311405024030001d869040c41400401c02d0206a44150380505561400343e0710015241204540142c91215030710b4001c031044e08450014046414543c00355816a02c110111010500220788260f008011541140d0b81c0803102004011b0345c0800d0b070030140c2280d882a042d548101869103490b03800d8502003940e401d000101380e460314200b880181d1010b8001c48006201207000101c0d071081d00000d41c030211b458015502c8101d8440c03441d04000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 485877616 1250 485876366 485876389
    0x105070509130207060b10210614120106081006170105040206030c0310091103100e0621150708101409060d0c05030d05070302010f06060207050d08070818 68
    0x1400d1041ca81181c10707001402c2000052940c03104554007050040503c082980860a0890b001e03103004124205040c018006001004814210b04501074002d200724500e0f000c0e0303070102c5101005000d03200c00c141040048620070511150035565965400090058042101030140c10704080c0000b0480d0030b1500600070541e05290120045e0b05100c01c0c0300058070b0304000c9950121318441c6694482d1600e00e80c01e4080c072031130b5000020190a040316000c0b10000c8c02c005500403070350b910f840c102031a61080c686110510440b0a540d01900d40c003650788094042411080505500b081605c0c050b58100c1820101204143c5291000079006401c120349aa6085003410103000050b5501c3c020121910000f88045030083c40c442c05003089260003c1080100c49040001e46030040a8407280b80300300e20010519000504264015820040044460165842004107851490303024204090a1030188000801008004c07a84000200265404940d20131301614100b100040c80c42110788444d0100035801102c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 485878866 1250 485877616 485877631
    0x30605030f030f0708270301050702010b240403080a110f011802010e06130303030c0f0912060e15010308130806070801090b0d051002070303050c0309062205011407020105 75
    0xa42481e4180000050b075030074960310b002050395402d052030402c0003030041d20003105208920b421000c3e03802824010409140c0000d0380200415034070040308130f09a07451030007c01d80180c14201c0148001c0101d03140a407056501c0d441a900d06640c03a52188003d0f07100c2000f5a00160817070b2503400790782805001134500c0c04040e00c0280160503180b2040a820440004001d0500040d400712183c2030311654103543c2d1240304414161001903036414090081e10305000f0300300004050861a5100c14003900e1000b00744c801071103452030346510503940d400003440c070403452071007500c110b2545500501c0c40080a030b0103180b01d450115200c030313040503291640540b41d80041105400483c1000300c07550340f00c2241811568003403000b085501d400c1c0c0205000c2028003102030710714002c04844444c0481142c00410403907100b950b0412180c0c2d00c0c400180114001544c00c2c2d03060790810700c0410061009002d040c07040b00300320f036a080d580c2c03c1903a8416003100c0407400c50f0004000540100541c02c2c2e020302c2102c2d07201c0b43d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 485880116 1250 485878866 485878873
    0x1b06130212070f050f0d0b10050f0d0c0509180d170109060503030d0903032310080105090d12140702011b0201110915090424121a04170a05090103060503 67
    0x2e24215150740f014a01419010b03000075110841d40f41d81d2500c04501058000d01e0151507414004580c840340740c841c0c0078050040200b103405000070705011140c4503040d40c21045000c445400d010400ca401c143c0580740f008100080701c81090b5900c000d1010450064040d01c50415a03250003406444c6a00140d0281042c0340c0781904c00c00940c0c8000c41165070340e01510000041c62681c0e8903080d0010030040c448905002d184840041c0d600e0411802280503140480604074615682c4240c242611002c03503040300c050b00452916201940644609148058200c2000c01e5460118034440c604050480d80200140e449040d4030b8018000d21508070700a903060b20080c03140031085245540d9074030800001e140204c00b4045044203009a080c1602d4103400d000b0000d0000107108500740d071960603c014000f60350b0981c005e00240c19040310214121050340706004030108112203090228002d002802079445030420392140f84030a074a01300a20406900c2e8603460340716800100014121801c2d42c1000b8000d90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 485881366 1250 485880116 485880119
    0x1b09041503140f0f0d0e010507050708060703020a1103040803040b03100504021602011806020d2a030306030302150402090c03040206090409051014010f09020a12063b06061b0613021207 81
    0x20b6228881c40304801c004c8c00d1070b43d5902050b2418a06d019580c0d80140800e00649041c00911a4140c0040000e500a035603a0900c100103040c00c15201c0c4124456923510764010802044030681c1d01010b036034040b80c04240c0c2a5103907540c50105062b031340100c00c24103600d131150074000215070f00408072000818000355508807480c18800c0c040e603550501e079100420f0001e10300300143d144400981e0228000e8444040702d02000c105d107800740c084c207198001207003d4020780901900e505481214180300d1034009000c4565511b644403440d10700e51010348181d81285040003c0340d1192034a025802c60b90344030394020f1007100704d55007100e4200c030300030110401c00c2c1244400400c2000269207111066a284810060343c43d900400c09403040000d07802c0e44940c003410694002030040f0305450000002090030f0056402d204038009040760100120040260440503401007242c6040440280500c80c030791800344007445881e40703001c46c5409004c648403031510629503038070f01c21401c103800c01240750b00e0760784010860300303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 485882616 1250 485881366 485881393
    0x21020a091a07120302130305010e0c03012a0c0201030902060703230c030d0531050c06040810051005041a0a05090f010e130f0302151b09041503140f0f 66
    0x1c490003e5100b00301600441c8420031003800700010b0000b5540040204102545050030325102c50f144408944a94684140e10f00b88180f10403080001608884511507115041c01c0c3c02da4010389c4d09039090341095920100180141c81e2100280741e4140a62180381c8444054010f000714100b20b04662105402e0600c0741148034000007080d607448000c07200c03005c90b0960f01c50441c510790318402120300c000d5848299800c022100c00d03103841d5404038024010b440c40c8245070303000e00a82d44980d20440301d29a01c07002065005903455486507402c00c055440250b00a40d80b40700180a4500070412903c1200555003000403e192900e4a0001450243d032414030510307044000314080d83e01403282491021104000034903c06c070b81c00038046426409039090301d01d0f501c0d41c10002d5842840b40c80e0317400c541c400304000c22031112101030002052241c000400780340c10f43ca0b03820301016014080c40303083c04450b500f1001c4000303145102c2e01000c586011000f0032201140340071240c602107130780124030100d411114080240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 485883866 1250 485882616 485882633
    0x71a0a0f0507021c092102030a2108150f040f0e0d0306050f0a0308030105210a0305040510020627010f0f0c08010906030b070e01270609080f0d21020a091a07 69
    0x2c10b00358584211086d02540040390910303164510080c02d0310000c4804904d1001441010442c2610a82d1454002c0e903960041e2080d440685010f5076010960343c0340c0d40120718054120582102e100900171800c940410b03545460218804295800f0030f40340c0205102c0303420710b9000b03010000070440385c40103c10300e15116900c140c403042c0125406001a00ea12860312070700c1c0e40c0148940d0041350708a42d8140304c107050040c401d400c10700401348101614442d00700f0141c07001920302c0c054030707490481c411400001000d9460071141265281c03451f54a0b0501c91410001612454804802000c0c001c100c030346182d04028191001608080742440c030b404814804034141d00e0316158000c1203400c1c0301200a40101c010f84100c1050ba203040424500203a03032840c00e543c5103910780200c8030103840304180c0030f86801005844404055007411282d20426048804070302c01c5240076010401000c80d0011240c050083c04143d90100344071101150158038200300c008803803c00d0400c5200c00e82d03506828414243e85e500007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 485885116 1250 485883866 485883899
    0x60c1912110102090915190308030103060b060309120a1b06050106030b0909030a0c0614150a091103061c0f05030a02060a0902030c0d02011e0309020f0105071a0a0f0507021c09 77
    0x40501030406c030004d90321030304404008641d2140c0405030b0155a850034040d80d0740309010880b62070382081c40048081c1410701c182d0340500b210801a0103485030001001c1c0d110740000302074608105101246404107502d0705035070890207018610128413903042c060054240c4541d541c0d01401100c2d5042000003200010091351a51104c1e45090820b030203450900b8000b91035400c40f214000302d44030301401000060b40309661109502680c0000c0e01c0c9075203c0c4810300300c60444580900e40141080003c1440c07601c0a0301001281c4202e110414102c11078030762098040d0244c80460340b9510000d115820580c04100203944800300d04800d0240040680c0441d8958070025040b42c0600d2001c0100c0045a00448418144105030000c07600d400c4001e00c0c0003006490061403e0780103c611580c05005544a2703070884044540100848441e442c1c503200c1064241001800e50203055503031640240c0801050181a010310116401001055981c01c0c1c0303000f01440a00d941400e01c0f100c20010044d41403d1550000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 485886366 1250 485885116 485885131
    0xa060e0604080301030312020d02030c1803190b0405010207140f0111090117130203102009030a12020a0507031a070801060e060f04050d080301061706090402060c19121101020909 78
    0x402e060700c242c01c2c69008c0e004082030704015130f002008100030a65510050800e55612074102481c0c2c00982090607140c03810a81e201d559003501201c08000b1600e0013040d075402512940c00146040441c0d1183e0b0a2240c1e40b4001e081550003520041541941c24025000d001c01800c40440ca0b050b001030029018044010586440d202c0c07000018808003070f02c1c016024400c0c0c01500b680ca00c80320340000300c4000c0210001d0b0690103c60300e040303511540c8810303042e00e40b035400103001007042c800961201190902c15020040441c0319650503140010000d0000d00c0046100d41c4418803644d407a0304800d0070000005001d002000149001003205582c0444900090341060340c900b59149528141500c40781324a40144d0b401050321250842048202c0d8002c6040712240d550f4221681081c52005520301b1094400651021a050228000d407410000405140002200b1116a1108000c407401e408120440680f4550078501106109a030046888401400c12200071480c040b1030000152100704007401c0c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 485887616 1250 485886366 485886377
    0x70c02041d0303011d040c120c0b041202010f0338150919032f12210c1203040203030408030309100b041e110d0e0a060e06040803010303 60
    0x4019925294071409100036000d111862018100403207aa496000384104904020122205084042111407690142d540448001b0380f41d0324201401f05411703201001680c80c12001c21000442405c1a0028402800c003402d0440000300d0b0750001501c2001c020312504149801c00102403884d54000c1c2c41e00315039200c16060646c01011003901180780b04802c0c0040ca07004002841c4041c0c050b00c807a0082c2003414800c440d0f0016022000d00d40d0038000049200041c4211030032103c00420701a40200c41008030443c82540c01e03041c805030b000400c4c01d07040c80848a0180c010040107000015940b006071050507018252902c0c209074000920342e2516603007840c1d540b020012012408568081c8102d50050201c001181c0e22418000c070039548460f048080385942504c3e10981d141c1e10b0419008214604d20102a0400700042000f810000741c90381800146015600708400e03001c0d282c59104440084030190010114000c00745041d9044588090b00d5101581c010001c000024580302c044078103481c0d0510b400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 485888866 1250 485887616 485887637
    0x5010314070c2003010c0503040c1401080403030216120c031205090312180601030b0106021c0f05030a09290a060332011d0d090b0412050304030f060212010b0307050307 74
    0xc40111403410440744d615500f041c103450400c40c0d211010f50302440c05032000262060707450602c100c0c007100c2e151496000c00d001e10005008640245d014004a0307034580e07034141803000d181c1e07941e80ca4412712281240c003080b41c00b8080c0085c164412079040000b05107903400c0042d0300300b114509a0380d008603c10114030400940010380f5810b5182c414022a140760812501d41d5612840c1480541b03009025003001840b60701840c802840c0001c4403d02e0040041e02c548211000015040350558001052101c4490f1a010134500060040c1c42007080c0a407000054000385000c04a01100c8042c060b05600105042c04800d00104810b070010820b20150080070044604540352004050380c0712112902280d460009009800000c3c4c0c440224000c070403105840024032150340a4680c1002400b40c80010784092000740301d0300482e021426030403806081124141580ca07900c0240075210341108132005d507004a5004602450000c525015241c1c0d04200c0d411440c045070010560302005151500300a0b40412 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 485890116 1250 485888866 485888903
    0x3080f0a0e03072d0e0132090106030902031c081506090f040b1c050d12140c031003051c170403022119080403020c010201110409020a0504080a0c05010314070c 70
    0xc0c078100403c5014600201981e441d16020100e0b4a50785407007d20740e0305032000e800c0305000c1d0b5510810044006044040507402e1842c01c400a0086170b4049030107100380c50502c04828280c5030141d0031654650b0740d8421500d040c010016956250b66070450040303a091107090702c0c1b03640e00c44200c070700c0b048180c40025501c036411001500c1d1045858054481a8491030710101748280400c040d01010200e440e006801101216004225969941c1b4010091080c00100c0c07512111faa00560300080c402294400395034890301c4490a0038400030340750691128100200f2201c98010854080600600f41081b40524140d24040c1d102d00d80c44403010000f502e42c0da00c1c064480819020b840704450b50a2100320710044201c0c1c00b0307000400c10b40702540940f01c0e00c0c124011781d600c14041c080d8540110981681000d1034500a035000e9000b50403d00b062202c14017002c01d1000c0c040014001f1203009420a1140380c0c176000024044417407241000e11010109401c115030740c0e030045103080420758000c8083c100c8030032814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 485891366 1250 485890116 485890199
    0x623012102090a080115060801080d1d12010b100201060b0f0a200a110a0807030813050409050313060504060e0111010902030607210b0306180703080f0a0e0307 70
    0x203101590004001501096944c01544000d01c52000c58000c5801036440d000c06884021092080003280c5c1d20004442c0200da00c90061942c80407004008034035464900000500d01e001000c5007000b0700d0f9507820130029030b842d010b450300000c3c8409000811220b030030030203c0c8000c0c1c4590740400307241480c002450248a40708090355010300a581401c9039400c0030840506454a00b8203d003940d06a0000d40031200c103107000d0000c50104c4444000504585296542c0c01405400140103015180e00407103000501d074455019501180d441903000d5640c4114080a808203102c0703d0308400204001800b091200641024046000c00301c01d0070150682071249102c940506141c1e6070081d0503008901c284017216800684e80084656a00f00c1042c100c01c82003c2c1c070040310300c00c1c51180c0d850350100000c1a413055000402d1044e0b02c64000c02e6421726922516482080da0000f825240103820000f40c0b4502d140e44043d28038000703c0c08034068640a450043c40803160b02018a612a40d6001082003007004403000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 485892616 1250 485891366 485891377
    0x804050303030f06040c2d0c0501020c03041701060f0620010e0c03070e0f040206030c0408010e0604021216030b090304230a0f180506060c030d0623012102 68
    0x5003142e42d01e1500c2c0b000326142d03a00a840081c0903a0410041d4080c06001e0410410038242d50180c0062405003000f01a088650610050040c8039008030001e001c02ea080c0000c0c0600c40940340150341c4c0ba8940807504d0b0049010300c8489030103074900f1405025166100440004644281c505501403035850042d01541c0e500d4650503114a600c3e01c42c00305c5081c40c020480c2310358480c5c21025140794a0b520103003420000b80032078000380b8000415001800501e001d80203182c106c203508403c82c3c1070984401003542101c000c06c00b4562650311a070200000c500e004408104102451001307021481a075200e020170314041c80c08003c000c80c1c0c520002a280c6802001a10001e141401507420f501c005a0601200c80044c00c1c45280103010120000c0f6403071452410000c2110800e2020680c401d03591200d0800600c0050215a8082c40c104107601c01c903841000607200c1c4043e40d1900082d100d14100c5117499484a45100810304c81c02c120007020541c5e0017020031401c040301211442c81e214041c50281c002440351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 485893866 1250 485892616 485892619
    0x31b140906130f0504030905060a090b0a030e06090a0606090b130902030309040c0504080607020309150a03021303110a050108130f02030a050d1205090313031101090e011d13080a0c080405 82
    0x903d0742501042015802c4540694003e0320b9000409480340127100b00ca10400b520007000c180d11400800418582c24010309510005103400100c5ca10b00c2c1c641282440d1040c2c0e02204c0c50f81c4048000001d101d010710501d0010240c0039420003400d00c9101c0400c21005524840c00380c11551440700c041592002d00c210707002c50100074010000c030034804a01400c1d582080c01106040d01c07910000a044500000442d02c241b40c1c01441c0910319502c18000c902107502c0b03402c00c0350400d6020303c000356102c078003029400061032003202402004514002800003001d281d40c00641001075000500001000c685240e45081d900300600b9000f4902d0f13800807030714182d040c0300c0041240c0319159400b081c041d8004103101071000031060900c4291210000a0360b640144603540001c3ba0800b41f041002540801c10f452180e0018100700c0c141310303601c2c100e40b610300c0026448a000d1401060440d4941801c80e0b00340340d4804609182510281015102c2d038141c0d0060b0300e0b008051014900021003402240d0b000ea4005110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 485895116 1250 485893866 485893871
    0x31023130b150307051c1814070f0e011409161101060e0f100e280e010615020d08010e010515160821070210021c02040b04031b14090613 60
    0x44c00c0c10010003e600c160a003480c0c180422070029110540f43c001c2120001e04550940f0701c46030561603201c03200560400f020828440e258000403c0903021421400034010300404042940c1b500ca03507148212200100b10b441810001d0800c4526940304c0c0d80104440024503003000e65049540b0168010311079904242c003410500381c10410f49141001520b0300c5010b048043c4014250388113044500c8070380603200040f0150504072004400d4004040402c20602000c0380426014601d58009007111003903001a4203640f4039a503002602501005000c80481e000e1a00c002590702d440740190171002c041c06850b00c200061890400e40200308002e8403004555240740f400d40c00514580b840040d03120041121005906444090407000310b0138966124802c03940141281d48000c071160802944440c030006010088400440d45a0381d0034809040508240000c0340c0d92281103043c41d00840341b560700d01d42e59140d90aa02800880303807015021342103484c10340b11040940c582c0b40c0081c1185240300d03480341c42e0b1171 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 485896366 1250 485895116 485895121
    0x7060609050103060608121219140a1a01081302010c0203070f0806130807060f060b0c070e0906102102150307030e060705040524031023130b1503 64
    0xc103a6000c203040701c0c0b140000308462541c0319406a110008002000013510742030203540b07945081c2c41901c56110000c0418107441c20b01441c80e43c1c0859807109030741911048034404000b403040c1a4828a10111810f004042110422200080c00c1d07581c024076000400d140b5440003000c69026000b4032809c40d90040903220307250303240d40450074028800e105441042c8150008680c4d4090000b10100b103842e013006a8a14050351030321107034090036030381c6040c00030255210800580c24040b24090090701d280302014144462510910716040d00000d0b0070642a40c012005010082c00d02d40c07089001c8400d00d0000c541c510310001204070f0b81c4407034540e01940000411002d044442d03a20390045100d950745c0d49003000b00d4000c2d05402c82d690081281d454010a00811080c003a601d481840001092410b910b0075003c040e0108076040300b40c10541c1c119646441e841420310003020001d00c00565140541a18001003010800280c0104d010100e8000110307034581e4a043e450300d8042c042140c040b888282d5582c4ca0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 485897616 1250 485896366 485896379
    0x30c13060306050c1e21040c17010c080901061202100306050a060c050105090109083a091a06090106050d020912030d0f02130e13120801030201110a030807080705070606 74
    0x1680084685e24115080e001c450748905c10180c169040101030046902040c11105018011214003810503110352000342070005021000004c0344001840590000c25039100380302c805441c2c800060700d08403c1d43d040410a00400c000c0910403036106404139020800086040010f90041076030787c00190b0044011807021039280d40055202d081136100c1e43c004c0100e40d441284480c22240c498000600e000001c02080b00702181060300007102005c0e5000b03c1c0c81040301d0030f203000c6044105003000f0900649881c40c81043c070402c02071549442041c044030218074a0070800041240c4014003c110507c0808203d503809400594103403404c01d900601580700000d05004030550300d0300f000d50b95100c2203042c41e007032001c05822402621038018020f815482e080d804c0103d000d0b110000149410080317030440c0117940c0800c034070229400444406403500d0207154110b000040a0102183c0044030a80c0001d0816001a9005015035402402c0780b6203801c0d507898881c022540d034424694041c0c04541440d02c00b2604 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 485898866 1250 485897616 485897641
    0x201f020601181802010e130f05060901080a030c02101704210908070504020c0c0d0b010905010b03070507020904031103040905090f0723011e02011b030506030c1306030605 75
    0x1a03408140309142a499444512410b03603c4100452031070110194403040103501a281d107040711000105000703d8540007000180c1124074850720305c68955103a80500c54141003c002d05805421003c000c0e02c0c0780b407110345001c5c00f06800e40c04001c3c00303214900030010364a40b1401c000204040c1000000410b401c25081c49004440b402030703900300d150b01800c1071031314403400742840300212814007007d03142070391070301003000002c0d0051a140b040c80e000390f070f20740e500d40d54036580c4000311140708280c48009541080004421180d05030490080400c04105003d0320035080029a60b00c184c0c112006000b80e5a140b800b140c0c1503112501c000080d100101d80810985480d40100d40701d0700144045031030002e0b4010400d03540710024403c10702c13040060400d80ea4074540181c59218260010304014501c0c0d14035000c0c80203030a444800210060f59124140813401900d1031501041da4034601c3c00380110b09000d40025110789070703c00464071903600715205440d42c13042a0011001183c111500308914035114441156 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 485900116 1250 485898866 485898869
    0xa09090308010e060d020d110913030813080708070c05060c0102071b03020a0e0912070f0b060d0b060d030e0d0b07110303100e04030e090c0a1704201f020601 69
    0x1188607000007042d0342e4001040280304420041852040d010b19800748007903003a10407800d80d1060550200b4000d261035040009014500310340c002c14000d83d950130010003a02000c0d0dc45180c0d01001410240412414026030742002d030004001650b841c80340c40c084a9541c441c0e80b1003a0840404101440303035400641c05060002d0140c1c00310b40d50300110b00b190903140c403101d0100a40c030581c00c084c144030310001700400c164400c100c1d00441d91141d90880400b0000e800210f0226440520751001500f00140700450355003140054811200f0460035903580c11a02000906450040d04c40f0300000d024035100e40b0713070310115030f0024003840b1108100742403005051204841c0700d4041004994007a120030740010132a0301c0b844c1c45c10072a54400c4e00b0103564210360100503205034204204008070380116983c1d20b00003130144144400880e540d0318881d2002d44007003a840c040c42c4002400700c0422011a00c00e001c90003005006050041090380b04600282810f54240422030390480d032100000100c0750006480390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 485901366 1250 485900116 485900123
    0x908030a0b060309061303023c192004060e0105150a020c040c0e1f02011802060301050409031e05030a050c190806030f030d0f1109090f04020406050a0909 68
    0xd0200550038010140300545114105910000000e10f00d05c186560f81803c0c0d9100740305843c48951300444480c030300400c600e0320001c44281e0152010408100e42501002005440060402040c04a015400002072b50708040c040160b00d045103542901e0103000100d540400400400c2141d88842c48030a146909010b11401800c200c090205412401026036906005580c000e006481010050002800c8200e007004d05021900180c03d0196584081003900442104d40e50071842c014400001c0c2903071142080d41e4003512074403c0303100260b2501030469064800c02c1d42d020460705528030b02154080b40414602e03120a1020400c030b816154450000e5008203010101400a51501c2c812424140301c0d03d501a00c09500f11000044611b0040310065446080141a902220042c8601c0c0d81580d000d060450140c80d0f4421511401c52038034450241403204094419061100317034130104040c83c0015050f0402c0a01c0a40003904540c1c1d00d410071400f90a0190542000030303900c601410140501c2c0c81d085 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 485902616 1250 485901366 485901371
    0x1006090b030c040612060b15030f040215041217040b07050a0b01050913020d02011806021f05010b04060503040f060f050a140601051b0f06011d090d0206040204110903010908030a 78
    0x141114507103030160100360703007a0440551403405c86680740741c01052501011900442c00024588501d0040c60246100c1d12284a00c0700f0149818810460b00a039000c4201c01d0810042c4400d2201c03801880d40381030303c241c0c0100024101d200c64051480c0d41e01499100360080c18000804608100c00407620080052240d0400344269817204100840031200319114440300510f01841000340c035248040072100d0380181811445460016240709019101d9084030000d0713884a000380e08141402c4001d41d17481c0d209100304001950401149a042d80300d00d1040000b00800400890b041c0f2442024880c009a8402001c1040380d042c580f6003800352004030303030403042103180c103407000442144900f2051003100142e60340c071310b082c0c0c61003980340284007022002c014502c1242040545100b0411200340138003074003501c10343d036034040003071005165000404580468002c40c88041d5100c0d000038546400581c1102d011400d00040e031020035440c091240415815801c0550040612468500a50043c009220705 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 485903866 1250 485902616 485902633
    0x50f07170d08190f021605070501020c03120a030c02031215040501060e030705060f0f070803011a1201030b040602070b0a06033e0a0513020c06010603180b091006090b03 74
    0x80d98580c0c012244042d1491000102c0c0503034554540c07120302c10084c403040040c100504915030003885403030010101c426600030902480150f804011258109804400801c80c0030b002030801501030044800b00b0b001d0540301d200b00e032081070081c0240c44100c04c50b14105001031070500e0046007114020380c400340c0140d10b0702001240881c4143c0003418162006001410034034500000e010340ac3d880f04101848a0905002203140e80c034460004000c0d1601800030162a541040d09880318806058a100781b617440411503011001d498503126811aa0841c0200d500c50f9100d052240182c0f044880040003c2c501104101e203941d050303840a01924010303c080300031030303068190800400c3e5514810840c548009048400200c045100b135000003880079005003030540c0e8030340c0400d140e84001c00001032000e402050f080d000002c204150350052685282c02c0c00300360b1a01c00c00e8031080300180d40180c8444005800985040010450300c4a05901041c0030006a40ea4082080080040c11103043c41f9001e503150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 485905116 1250 485903866 485903893
    0x80901110307111f020318060c01021821100f0b040203010602150a051e0604090f05030703080c040f06050c0c091618140d030c170304140721050f0717 66
    0x110401307040480c0c0043d850300e84110305601d8442c41c80c0f1505a80000c0401030484040d0080c000b51082600b10412000030280301c00c20812220785124480340a81441112054103001c0000d0400940c92034180010355203840100440103007101c2c42c81c16801c58000800082e0b40c070341c0051410446082e0210040e00d42d100c160741c01c0103a0707038103031541001c00343d510702e900b204403021080d81a00900000c10000d80280c0903a54000810362008041d90181c00105041c0309140d0400c00495108031a808840e1406091200008241c1c20f180241c0e4100100411021141d4200700010200c10700014146402850f00c65600c02c0f068440c810000b000404010000040c40d5812410310152121100383c0c0e442007040740c0c14403641c040d603141e00390101305207400340c080400d07000c584110b070200c030923020300c1d551389460b060028501801508081c45a03116440811410718841030b0080740c10b0303008040d40f00100a50a08614103441c401ca4200d10780030701d41d80002d800d00b42e810600c12460400c000d44414a00010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 485906366 1250 485905116 485905159
    0x1502010209042d0509061b0d0501030b07140c030d2705010204140a0f06051c050903191d0112020d050c090319030212030703111b16030f08090111030711 67
    0x107070300c00e05c16406580071501303031114880c09850b05200005102d080800f480092420360f0802e03802501e448020340d00f13005c5030303540c0004036180c00c00002c031465107040704414500b80c1d03a1080210103252242d40d03003001e030342c8080042000c000782c0e422050030500886150404a000354090f04c00c5070b011300d0b40a44000b030203081480e842030403144030042d6103c3c090724281d030545003940036030081c0306001c04203500c001e8580000e10070700d4041c00d03202e4003c544840c10b00c0303803407286079007520080f0092000c5114429070700744090244034002102032800c2c0d00d8560060301041c020b806083c40e41302c46ca501341400c000003c54480c014051501d012400c9a80b0304140280071006511030780c0c1c1c09801a0008c241c1c00710002c209500071504140c083c40c0014000d182542c45e21042c1d080000e65618001d95024002e600078000c1040c1290010b8001c0c0350118079103580d4410980c8400301000902d81640800c41845d568041c1450001c0700d40d04409607580c4240c24540a04026040700c010b503c0748081c03000380041f20140c1c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 485907616 1250 485906366 485906371
    0xb0f04090b13050c090115080117030d150503250902070503270a24031b03090c0906030f12050301121e050304080708060a09020105041502010209042d05 67
    0x203030348003400ea140c2e28200c1a402e45441002d0f01c803132048014100d80707070721481c03100d40c0202a4080040182c1b030004000070061003069100a08042035200d010720401d03400300c103c610b0010401800161408882030940d09002558006541030080e0741d10544100da2390001a143d21313506241d010a450740707550742c02e0124020554041c1040d402802194911680c007244034401d528001403007407515105400007000f082c40e681183c0c21280403100c981c0f400d60311240e0a40040c0f14142401d00c204500c4440081304038140e212020100354072140387e2814401091204000f4100340e94052101d191242802d03403841c100c00d0000c44103072031150000c1110b18810001e880c140d80c101c2e46040c041450b583c40c0c199651031101c0b031002402ca40c02c1c004000141007080100020a8031001030301d0036038035216030a41058401400c90640b0b0381464003440c0180c0e0300100f11419144802114903102d0207a076001ca0080c0a0006820381052a0a1000a0b40202007500084500d0524010301007018105d40741c80035190103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 485908866 1250 485907616 485907623
    0x105010b07330906021b0c0108060d02060d05010f1806030b01050405040615080d0e0a08030f1308010e01020702100e010e150c03030a270305030f13150b0f0409 70
    0x200d007144048000d0844005046914280d201c207010810302d24107003c540b4206000c4403000e50006800c0c41c500005407480e07071081410b4015102080026002a088000081c40180b241c04520114002c55a503034040d10b2400c550010108141d41c1c458142c41c01d4110503020740f61081c00f106000c0700d40030450340510020781e5807055000f505c03a4a4036040c8005444040c100f107840e29140c41c02005154901007a01009101140c01042c0c03038610000040c04c01298500001c0c05081032250a025403000001220300079801c003a4910f42d86e0120700740c0c005000e58150808082e075401c09510748000d8805401402c523081c000ca80010a055105000381c494030036a04005000c56000400040d043c5001d94000303080780c0d96401d100e4603146004055608550003104c2a45003240e441c044d1a04440d029000031f881107952046500885846440250080c00024400e1b6040001000081d500c01900c800e40c141c040d6028040f1321003a18a1a045009480c3c85d0416a0007264003140b000540d1500e070003503c034250740 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 485910116 1250 485908866 485908883
    0x31203020a09030503190306050303040e010b070309031e1529061317061003030c08030603011b081e060a030b101208250b0a0504050a0c170105010b07 66
    0x40010099000c0e412120707200051203210000000030900a200408482da400c9a02248040c0d11210140496045801c018005d0717000703120500989c401e0900307075415600b40340441a22000b0518080f9040d4210f5040142004d4400320b1815542580c851a00c8529100d80d00b0740d00d01c000404010022207001683c0904ca624007012014a90301004250800341c1002401d41031034902c0483d03004248240552040d01c40c103820326520700c2015008e00c81560000c04081001e40030a19640700105030350000707000a08903210000100e10156002d501c81140b12002a080a05000007030780080c017240c030112030715040c00c2000c03d04641c10400258000b403250400600720441070b41140c0342c062883c0b41c02440b44501e0b02d049a0007051801140e036841603164402c038422540d9500c4180c1c0c0048a103400d0414526441800905200242d2200303005a0b000c1c0c020740d00059190b895051a51501d1045003015085641c4040042200a0300704130100344661031178024085a6030f01d6014400509c42c2000c00f030151003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 485911366 1250 485910116 485910143
    0x31206031501030209100b0a0e030115081e0a05010f0b03010b030706140a031d0c030d0305071b06090f11040b0303070203100b280e060108090c0f0d060f0504050601080703 75
    0x545000704580000c4030075071b003108040d2105449442603024150600200c1c21454400a01d85000d01448020022140b031664040c0d01d0000915524500c00c642c054030318103000e151441000040020400b442d411100911000141c0410703103004115a1341140d00030f50910b01401d4503402e00141c0002190380b26903415409840494086005800c801140c904064664040d0049482c60895403d00202c840010301036030b90b041d07010140f130980360050103001d05040004110b81641c1044010b0001003192580283c1c900b01403030500018104081c000701074040880c1c0c541c0601c080181c04200440007903508201e039a0a010804d0f0b96402403c00c000d605500c029041d0701580505d8028034071104025140d04d0405149000d803822021200f0708244d08905440c004100405d6000009500000d0a003007c0b0410b007001540740e522090340e03050040c0520000c0c000c514554840b1890b0030000c540141041001c00a25100031002c0c04091710b0a4610748215800071a0540c408100342040b06d503c400107180c0d18 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 485912616 1250 485911366 485911369
    0x6030a021306080105180d02070e0c0901092606090102070203060a0c0306051203030709050a0636080a02120d05030a050603030d050a14070f0504030f0f0203010e0312060315010302 79
    0x421a042007254a07101c9400091105007401590b00840307801007171141d10006441640c0c5401626090002150f0117038608002c00c4d03403017250302c90b000071402d51002e54a054802c0181c902c2c0525500100f0f40020740c456048941d441c0301c0c94103544034142c1302030303603196103811610600340d0280c0080a50705400500102d4000c0c0303055400700508215508012a06540d101c00007590303600c00201c0003125420010400c840d2690060350764014001c1140c000d81800d0506500505480098442c521218403a41c9100c0105580340000703c21764030640c9a9604981d1a140d00584072902c01c01e00301d00030326504445418489020a00c1480781015946013400e6648141e10000600406440d40e505030008000e00003240420b40150f5204000c0d00201249901c80306401c1c42e04401c000b08034408001c8040c04460615500c48200e90880c1e4001034020b0541c1090305040c14070322024440254550700e010345081c000c04022010307000490311680788518640c0c40c18185030312665010803220201d6582401480103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 485913866 1250 485912616 485912629
    0xc030d020f0d1b0812040605010f0608010902070c080f100e0321041113020307021504050d14090a0603050105130605030d05221707051e0d021503041a010e06030a02 72
    0x58074148440107684802c5515115001d5026507420fa031740490b400304002c103022560007401c3c01002d100620110452230aa0020308c506e0041c040c03d41850b1300060f0701000d100740a503840b00a054000305a40c610340c0c4d502d103660b50783c20345080500c02917030a10230340e40c1d000c0401001361030b4007400f0a41381c950300380c20f294554070820f4030003007080320400e44d581400e41140c2c446998200e091b8010800c010703aa0304111001074034240b05a0a00e040740b150500401000600c0403c81d80300b907006c00d0925000820030088110074600407444101e400c01c20b050340004066500d6000941262015a0411010b810b07c01e220b50590b10207000e61074140e4054401c03409658480c01c0103028501011995041e04c2e49103d01c1b004000030740e98030480c0301c0103424144402d101c81c04e00c900d1000f4402190148262161200740d03106800c80c003010903104030841b01505065484000c000c10b0601c1d030a1090540e00d140c54a403145c0c280381001c0301050b1039014103001190364030043c807800d0b0040f00000c00904070f143d80c0d90700b003004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 485915116 1250 485913866 485913887
    0x10501090920070206130e252a0206070b1005091303080415050a0b0a05061606270309090b040b09040f08040504020d0501140d02010c03050a02070b04080c030d020f0d 73
    0x2040081000504076640904034407070098001d034040700c40d490a01040520852511000c1d40b640d4051100215189030b4009c4409140c06101c141c21a20341050240a6a100b05a500707019401c800001500010002c85400152150341986105101c00e915201480080d80c4112041c5546006c1c02d242c25012038003401c4d0b80c6038818803d490034017603800850143c50503550207581c0d40a5041c1ca03141140010b1504030383c00e030080c1c80156541400c2601c0e21280c3c000407821070304041d221030b42d01d0300204421042c0180400310300507010b0b00301402c001d07149030040c10384030280b25885034a031901807407110341c1c07409000d0403003c408018560b400b46c0c0c403582c0f01d001514030a041c045071100001c103c005075640f00c40c000307440d00d6999100001255850440b6a00b5440452032102e4414070f01c1d260f00c140183e8010302441030490300b40c9041910707650780c1d4000342c1c80c00200e41c000c18100b01000c03034009003c50f00002c0341d00100c0c130241c05480b1800c1840d081a42e4030707422000d0080d50b03900082a10f0340258880d452091 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 485916366 1250 485915116 485915119
    0x20d080118021e13141c05030702100807030e0d08160e030d0c0213020c0303010b072d020f09040507120303090c08070e010b0c03071509050708060105010909200702 72
    0x1841c28460820700d04a1000102034001d1043c404a280f03803002200411000081959041d8107030b2680000c1d0000d80c0301c81d03090403a001403000c44003844090001c10810354828035401380040150980d000c0c8042c0041070101c0d0800002400e04141e010003080c0850796502003903943c0c58880a90b20b030b000c0310522000c00c40740c01e201003100c0c81401c513089980c204100324000c40c8a0f141c0044030800c6005020004402005541046004005495a501c070000c122130441c0da071030810701d494161f40c1c03030950740c3d0498040e0003840040c1d0302100ba01d01180003614080200713101701c0385045000f1188060195206040b18090969000384204001c2e0030280404601c0f81032203860b00042209480d42c882592140e0782d00801003942c040c0304240045060700d40c03ca13000d400c0c0d1101c607906200750514030303555a10450a0040c9000001c4104405042c0ea580100c06038691001c25234041c1c585400030240d8444c000d01c141d40c0050150000098803260510076003401c14440341d40082940b41e044104070440c3d2140904a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485917616 1250 485916366 485916371
    0x10030c15021c1b03120b0307050a03080913111201051c02090903070503040902030105030f150114010c0b070c02010e1c14031201122001170a020409110c060106020d080118 75
    0x42e60f194189101051050320075100e0185c02000c104008003110b6500c2e88242c001e9228080501c03259803440c1c2080100c5c1ea00c41011a03858116101080d5007010400300d00c9209030915083c0070b0f80305100c00c043c0486100580c80f5800580e658010000c101030040c5565001030801c0c0035800c0503080c40c01d03c03503521040038000ca034a05802d81d940c0c00d01d15032141e8070402d502540030005214030725042c0041d1070b16241d0480240712190074055081c00040d410321504005421016a840d02c690203507026100c0c641d0000240481803078504000745c5162481c0804030b000070211070030300100349060703d0071501d6507448050b16443c510303055495880d0644d207000c2030a0707144024400c03800384000e500f0505010745a803030004a5803210b070b03181c6545100c10110302c40c0754800f00d540b8516100d03680040309802d90412007445034015250b18045400901c074a1300010303400f905100035840e1849100c40101a131030205001c640407aa40c61300b040740c81702c448000c0c80f000514110010007404169105102a40e01d880380d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 485918866 1250 485917616 485917637
    0x8040b060105161b0e04031d1f0512010b040b0a200f0a1109010e0a1a04020a022b091a2203140f0303010501030e0708010510030c15021c 60
    0x3490150320f401c2140c11134006440c207880c01541c00030400c000c200c048807011003801e190b50041c100b809002203203400200c0305100c001107030f40e8500303c02c0c5e140011010012000ea0a00b40007d01983c80b510000b186020403200001d54580080304803001c95041900c0c41d401c00100c40700840c0c40b148510f180d07130500111000c200d03d00400501030140c49101000081c000b4800a103800342054200004041c89099040010400d00860280c4a0340c07001c1020b8000841c403640b036110600d10801d44a9041e009071012815000141e000644500162684826101041800162403880034a010149000660034038030800035000c0260f2208490020291500e00b05208454038602c0380c05071540058800303500c08020401d000b510403181192210300c0c8041e00c40700d0b1901c3c1e503003681d900c010b101d83da0400d507480c1404141800c082c0103800190481d08000c1c45281003103d04284502d102d400240c07134500c01400001500e078044e070705400c082d06960b000303407603140492045c9000342c1210f110b04405003c04901c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 485920116 1250 485918866 485918887
    0x10e1501020705062b1b030c0f030b03031b030913020429040e07020c01030f150e0a0f050a0c03060e09060406150b0d0510060c050c041d0304080c030d03050708040b060105 75
    0x7554244041c0c960015000144002e10381c241c0000c0b0105001f8546055622400b659000c201024002503070700300481e8001d148800710b851481500084400100000e601e403001d40030120085c900c1180464852051710005100003040380b141e44a9103411a1000040d000610000c0d44084140ca04511010303007001c0e617a01c3e20003000582110840b00503001144441482d40e018895108540380e0030000304a4994141d4426078001582d000d1850b084400400040a050031a04046102e03410b5500610090a00c41c1e203481c0a454444a0040424107128000c1015200c2089030351182c0b4401005150360344850715402d006088000c1d00142145000c07070082011006100140180441081d0001e4240340500d60341001003002d802c880100301000c0607071004280f0000f4034044480d41110009000d480304403201050140c2c2074000b604501010500141c8410301294034404240c081d005e6400910320395400f2404c03030b8401c603a8100402d010754082004211014400c5602c07206c1810194501840c10320b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 485921366 1250 485920116 485920177
    0xa020303070b010f0906030f170c0a0614010605120f09030904022b02030105010e010333030312021201090c0c061109041b0203030c0c071805010e150102070506 70
    0x4400c0c2c0e00b00c1c0d40030004010003c450b550070002041001010050141540d84003102024412401f50100d81c6113801c01b01d040048104a880010300b4004480031542c0a29120010380840150882014041000011058041e2044603074050030b42180e5109039481e8002404d500740058560280b038881030054402036190f51004040d0b2651040c01307000c41d240028514542090203040b03890f0101d00601c0100b040340d8200504104246003400d01141250042140c01030740300c1c0ba04e04003021965a08902009031f001000d0100560340296a100c03081c1812401c00016482a5002641d81e031042c60010441c0344255400f40e400f4100d079140441401c180d81d160b51042e51105110920031502c0090420058609445145a0041403140182c1c11031014403000c2d4a034080240003400801d0002038000c420b440500c8802c014089140807170080720210341440008007000d028008601079250085080b00c2143d8411081c3c11805a00404081d4101420b1064a401c0315011021849400092118074108034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 485922616 1250 485921366 485921377
    0x91f1e15020a1712071d130b03070f061412010303050702030313060809010b0d050c2101020c060403030c030e07061107170a03080115080417070f05060105010201060816090e0a020303 80
    0x10840b03441e442400410484c408020b40f8107010310012604000e01110480c0c01840c8060044495074604003080c10070b4006040812a0103600d0f0141d06404600c100c10391140c2d80607142160b0380e1002ca4005000c0144071441403651404086040038010000a4071600080240d02c1c405000d84c0d0400312444564444d500650f0050800b04401d04100b108205003449401898642168080300f405055202d80b51a6031072004140d00440300003001d01c484d120180400c009004559008541c2c6190800840341c07182c0c4183c0d02100002e080001c6a40954030901a423401e41c51090080d10105140c00001d896452140e6608042030050844c001034092010030012100c4070b6000c06048039520600d001892544140c00c10401d51100500b1070600e82e074040d02c096170003640603c111300c0303010307444054800e103005084d0000c05020364112048100100451064100c0e40c00b0b800901600741c031800225144c50780320303d22421800c001c10b000c200302800354205901c2c0300b0254040e11241c8415801103421359005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 485923866 1250 485922616 485922653
    0xf23060a020607080702030f0d20040902090109050406060f0309260403021f0f05070519031205071e180503030c0a0506090a2f091f1e15020a 62
    0xa10b0402c801c20f40c000f01c10a0b4071410301d01c003031840c00c4966443c551031230190b003003a5081c0b203a480030304a000c1c072500d0146000000d075141200b82c855075640315040280d0700c1a8440340c006030368142c0c0020141818000c800607146591501c0d02078084101040b40240341c078020654a1004a818100c419800c001c05441c84450048000b65100c1c103500500150009048074042c0d0b071043d00404503d003960151099940100a180c05a500c500d02d08080d45002541c01c04510340584d0441c0d00b0040503041f4806140400f0000d5080c0100d17904e0100c02d07103111040400c02c9039961840300c032504d506407051140020441000e484c2e2164181c031040440d207107400c10503d002132a8800c1c1064000d1000c10480b065202075002d004018003070071562806004041540c0d04803140c881e504100d20324440c01c0c82c0f16040c54402424201c42844c091b03032143c00c000f100450544812044c103002003240204103400003001000b152000001c1ea250042e00c45120501e45198421070142000c2d440c00580319600701c81c2a90340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 485925116 1250 485923866 485923873
    0x7050f07050406061e0c02190801050c0306010212071b06110f01090818030709060b07030206090606011205221209080a021804031202131505131401050d091202011103010f23060a02 79
    0x13009d01040c2141d2010b803400540c03140500401c00a40e03170000d081803000055012242c1c81d10158681809030181c441608001c00c000d4090104065902c6000f0340740c0c2089003801c40d50034102d98000745003214961a8003801c00d000410000e030301e00c1c1c140703c181c1e10802400350481d11096901c0c5040e02c201c035256042000318503000625281450740c1040b80d15000043c6002801441c1082800a403500c07541c4a031481142e600c41300000d1340301d81d07002e03040039800501400b554405030003440c249580c40855000200841c1c06190040380868000441d420580d0380940f4208060502c01900c10328194010002c40401c4220110540449a0340c00505104030300d82c2d1024610600703244418480d48001e020100402030240b01e0300044040d1000c4040444201d1585450089030540040311103105a0150404640c00e203441c8004003c0d80c0e0080402c1250f503a4000c01003007120044080c05440203108002a11000c1c2d0400d001c01e0074100300c101141428015010030408a070b1000c1031141e01300310f40349005a007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 485926366 1250 485925116 485925119
    0x2160503041415041d07030204120c03052413020d15020706230601120b22060e01030203030a080601030f0e0604060507050f1e0f07050f07050406061e0c0219 69
    0xc00350b0707040c11038080001100e818a400d01c1d24000c04558054502408103c0b90b170040b8606a0207581241d010703003034080b10710180c420076052240e440081c91000302c50a00c50350000b00003109a0616440281020a0358004240c407040d185150ba1080f40074240e80c400c840d080390300d00090b42c000c04c80e0b956a1b90604090380b288007038100b800465030a80138010b404090b5500001c044105d050070a0750040090900a1b420511021104000c080e50034801d1703000714031300000710005105112007005c110300f4544103000d142d0f12510f084454000a1200075090752007480140b40c1ca42c01030303080307980c401c1041c0340000e88c1c544400c41c00c1059500c8001080d100703400c1007050001303018850180b950301c2034050038140d1a01076a0104641075110704010001c2091a58590300d4803507038076600300c1f0f91030700700012002d455076450f00340310f503d41c4100c020842080c0715140000038181814000c4070200c8100d44c40e01c42c0b4000754007080175501600c0c0c052020402c0f000203481c00042e034445d8112402d8103101040303400d646 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 485927616 1250 485926366 485926369
    0x203070e01150f05040b070b0910020d0207140f0a0b1b0d020913090804170a060c030e0601060c080307030c020a0f0c061209051902010216090504020a090c12021605030414 75
    0x40c8003403c2107000300902003000f440701d4180341c0100c4005a601c0002c102c0705685082c00c482c10320615184145245000142e0a0341ca0361b800c4d00502011800380319070102c45102410880d40e030380b80fa61440c10711900f0901c044400b190114040c0f5511864100c0381c1003409034025040c4065601815070349841300d0340821992400e0504c000002c81d90134400e81c2c10808605951100c1030310340100e1140c0c0034800d5035130f503000c4001c400a10100c59610b0344218103020151030494042e0240082615005030346c0b140600020704240f0451a102241d904488070b40c1c6561a581d00440c0a8800031000c1c40c1944100c100c0600002c7c42d490400300240c0c00fa9002180c20703030501400400240c050201107200c00d00b170a4110700890400704040c7d0302814102c0300c0b03000b082124401030b0300300200404460200404d03510002582d5507d42c1080f4803e0340f0171515203c9031510744005104913070180c6050b81c0015151803448850302d1300381d030013480404001584c6d001c100c1c0f2590703540b07032a40e4010703041403c14890341140000766 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 485928866 1250 485927616 485927627
    0x6030503070c09021201230d0b160206070507031209120908071215150e0916061706010e030f0f1f0b010c03050904060b041419150c0203070e0115 64
    0xb4050480f07003945001990f0b04080030b8144180280260200c01225210354981142000c0c02405c0c80600700413025605130030603003040c11048901c2224030003245c001e007200602c007003001442000342e5286c403800c0c10501d071811206900682a0804483d64510a01c404501c801c440d612404c680c03580c07140d03190307410702c1c620f1410304401c0e074400c172062500981c060f4009139410124014207400a840000c220b001070f8110f11903602a94020b0f02107036083c10904c0344444012640b44c0301c21030054840c030b0b4a03a0751340800f00c5640d804003007900c20801e48140400e04961003030700d400754143c000408aa5551000302441418100c07006002c3e02294483c101c044030b4941079550120140c940c4040401000541d000068180302c0900f0005040003400250540c407540c0310f50101e000303059081c0c2416100c9498160001d0001d14844c0114414200c003400fa90380701c0c0ea101c0460040e250300011030301601401400543d0501130500007245c1c540103021010500000580c1140d0003412003e0fa2529100c0c0c050201900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 485930116 1250 485928866 485928869
    0x5160f0207080a0615050901030302070602011109010e0603040f02031207031d010c121116050108060a03050304150c060e06100905011508071106100611070503100c050d06030503070c 80
    0x150740040310100005040400e5880390a50803042c0030a9412480311440342c1036442d6001254003400900000c0281540000c0e41415601150002c00400d550520302d80c0d0140900e0440ca030024041404400c02030400d80041d45d0400e02c54040724007280c0940e40024107001400169401103140400c24605041d40300ca141c00303000b0105882c1100b18901e080c0000c06441d691100034084000d280020324038144102c100d18240c107110000c0e142080800c401c460031905d0f0600c1141c0c0050034110100d501450b0200340041100d9000300103514251a0410a5900039910b01d905001e0100e07441e6003001061013030240e40c2c801000704000d001b6038035100400f485842466005100c1c2c0902e0240144001000c2c4698410500030724201284a03690343d000480d407880303072000c01d1a40c501903c41131100528040c0060400c1c1d44868803002000308c40b109a250381d0301c51502c1940c0c0d241e440303030091082c5c0310a1740c0e01400c2c040120b4a4046c0c58241c40341c80c66019603200d03030300031141c45c1c1c00040c03101c0c24080280c52000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 485931366 1250 485930116 485930147
    0xc1805090405060601030c0c0b040305031b0310030b06210703030305130b0a2007050d02060603010e06040803041b0e01260c0f04021b011d0303040b01120507090516 72
    0x24035030900da01c4065942000130501810305680d481d442c68194002c0c200004810750210110025290910b00205039030020765007864185040c0c42103410302d21948040d2032241e4a0000c0801c040c0d0701e141c50b4408603c8010703045a401030702010700c450405211000c6042060041401490224a54940102282c200070404191021868a103000042103080c0413070304801154808560340f122a036403d18000f02c426004450444002040c03410010085101810440b541e020f4500340d0f80da00044c03500340d07091141c01030361540045e40014002070303840300610b0300180100700d650740302c3e210705005805038501c54120703a01c0031890030700402141220000706c0061003a11204044e5255408548641d50101404154803d010092964415807110707070686506000744041c69038404805601d00340244101c3c610f6400c00065500f0360030346070000000301d80c0666807089185940307078600100e04c8100c04020b081200c85004076640014001c030345c2e01441307004580c0c51041c040e002c1580200a4011847c01c4802c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 485932616 1250 485931366 485931379
    0x9060616060b0609040504230f120c01020702031f05060f0a0509060d3f21061e06080f370504030f08090303060a05041a03010c1805 58
    0x420308480e200d59260031540c800d101045089031040014264062500410781181c5054100420300c480f101c10030300b044846007058201a01c041d110980c03a41c14280002e4215480b00c012040002c0d440001080034100200006081c000d080c3c0c000b9003068500400c1003040704614200c0889401c09200d440d410002c201d4100c0b00600c0d094000c110300150310b120f030b54407c0406c000090041e4503084034059503280c0c014107084051140110312400200012404904804580d504c150704020300c0c1c14800700082e40c0d464200c84908030480712007002d82c61a00f050000381c0c803481c1c0010490903a40030b07410681220341010603001d04121000f000513000a0403401410a030200740b01c20498445600a80403142c81c61340c88ac251400d002076070100402040e202c681628040402083c0360b40150b0302142c000c6680e884000580303449903d959240070a4403040d40c8610442010080c5150980c002384441e007070480d104800110343c400003030031100f10000c502e000c2641184040c004401c101c020002415085845 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 485933866 1250 485932616 485932627
    0x15090c020d110a0f1b050105030906010519150e01111605100c080f03090607090e06010c0201032316090305061803090901062604020105071203020f0c0c090606 70
    0x3503407030358814030341c0c8103210402c0e600c0d5121040601c402d07045a5005051311102490510389a018511011594102c620709201d0200d420340c80303142200d0050303144400400d40c603401d04080002d8018009141c009107941070100007030411600f165051100e02e5038844440b01c014140014141c180b5013819240300390401c0141207236640403500204265002612074056070542101c040d0f80e0b6090b14607001e0a0315001089900035a0305d24070080d8418480308007079490310385031280103444a40060040f40b90884442002030001d5100e41c02c02c941881c01450040740c5081e0315107090f0014001e404ca8000450324000405c04506105c036503203582c0014629041c880f86146071074550300d844000d848611385858151806a0f0450100240c1c0d880307a00041a035080b551b907e5030003402c00b20940c0c0c1c0210388d241d03403400010040f8141e008003e01c0b841d01a1500c0c1d1915045039a000d003541d406d20909402e141d401c0c8034841070385000300f024026001c84000140000c004a10070040b014200070a514400c5c03004105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 485935116 1250 485933866 485933891
    0x2011d06040606052d041d010204080d030e030a03111611121c0509060d150e090703080d0e15010f05121b01050c0307020306072f030a0c03110703061509 67
    0xb24000d60318445c1ca0302c904844507900005014056003450050001c550007140540044194020710480e0540030849112580403d03045d010f8511819034401d00390418482d125000740a5040861200f11942c0e00c3c42c07034924007101c00750b100c4841d40c000303036541d03031000284008504001084048529001004101d0590a10342240044009100820412002044840312500c40b00155486403120318010301030711800c1c070107194422210340b20311250312001d83c0110741d110501003040002d4076000540c15280100640b1400c02620040d210481c042c8505407100e8038603550058030f180a003014040c6800040c1c0707000c007004903200490404015030b0300184c90600c1401007121100c0400c00003803e1903500c40d0400f007e070364111b00441030003a405008180c20004003d51102c284954424200d0444005ca017102c1310b80080c1c074802444c0c0da000355004101c000c0c0b80e00e000c2d00c10041a00c0c0310b07207049040d849000c20400e01b01071071a8011180541c45d181240642c2c1d50300070080c00074094100c400c000047c000d61 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 485936366 1250 485935116 485935159
    0x5071506061d0a06110c031c0801091103010e1906090e151e04030c1509151a060c2109030106120c120320100501060f0c0b0702011d0604060605 63
    0xc213200900c050350b07079010045002801940380122000301580c811001d4515505a4080382e03000142c0001c1100c40046103110940c0b050b0034200286c6240c440c216800c00b880d825040a001d084017800c0c8610013451200c0101c3c0e4040c00005d003003100004140c0040c14000c141c176242000c44120485210401004524501c98a9070500490b0402f545c4586403a1801c00340c440040172074020b8040981d14940340010030348c42e0043d8480303522a000d000b15030440306032101c00b2075070704070b200e500402d94a41c3c0c164083c3c5402c3c0f010303200c244560070a0b99000107246001c454120f40080700446548400300e503901c51443c080c41036600404086070948034540305030381c410350200aa400b80d02d203842083e10000c021b0521401822850800c60402c0400000070149000d80e120304c000d12414910b0309001c00460340350b106100c1ca00300449030383c880000101282da54000d110780014166011596501c420300c502c0b6402051803003041e00c03000c01400250a0508050080d1281500303d14000e44141c0c0c8400060320000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 485937616 1250 485936366 485936369
    0x130e0c060702040e1606080a0204142101090b0f010506040315020304030903020a060503090d1809021e070b0a0b040204050f01110c120102040e13021c0305071506061d0a 74
    0xc84800e552203245200207802010941e5100200307201d0410103503481065048117006a510540394074032140c0e12103208200303038415800360000006070483d00b019541071010488a020b8419400e001c0100b038100d00b05400c6828404042c0d6601c004842403104452101e4441800b50606444a0382f900342151140007070080d0f100754407000d69030f000001805151141869001a50740100030810007561034000030020b41047d22058110301480c00c54070003141c0100010310110350102c4140060341c3c81c04132800001e4005500350380c4500c0c0342c403801a100c0c8a02e500104055071092094179502d043c49000781c001c442d00d0403101405148100000d00c40c654540d100c00024150902e007101252001c4c3c7e0f034180c101070841c440a82c20520032501c5d40154030041d0098000d032401c0105c04050342c0c0ea84805d0428402020134040e410046000411100d07110a0880108040c001e0900364985107507942c880840c164004d0055500d40d03910842401200c2e8005c00807c5100c00064144160050500c001403003032066 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 485938866 1250 485937616 485937619
    0x105030a110904080f0301030311010b040615110703080a050304141204030b060d06050405060a0e071d0405031207020a1202162c0c030105010905090714090406080a060b130e0c 77
    0x42c82c0080c0401407041c0403a208042265403035510ba595a01d00545100c00e1464041c400d5402c081303040f9030078103051003100b00700c42648580b18000340b0601400c4c3e460603034000c2c0519503402804d80100118103000e00402400101b540c400d42d507890281890401000e107240542d003240c0100e1065595078002209031f03000d5a0b04440b810700b6035110240081c554100703640e001455541000104000d115012410394841c0060950901001c030184103910b48138031007030081c0780c403e0369280030644201044000701a4000e1084088a01d000c1d4501403008144100321070040c01a400041c6410811019000d8079580303030001e000610300c3e540102c0583e00c0701000c4d4058402c440e1540691140ca503111000c4040079003580003545285410b02c0100e1240d03580c42401014046040d0100004907402c081d002548107a0090395091110350000c0400082944685e2000e5030054131804081940b080910104042900c929000038900041a040c8008060042c2c0da03c02d00d68508041c1c92240c2c6004100601e40110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 485940116 1250 485938866 485938879
    0xa0803070302100f1b0c0c080312011401020c150309071a0d09060b04151505120a09060b100c120e060901052215030b03060c04090509070513060603050105030a11 71
    0x1450240100510100303040d02c40c5c46481d104102c135400c803501c0c10185000b00b03800b03118140c0361000700340d491007010b0200b5005e035440001040304503543c3c4114a4407c20520544007584120380000d0f000032000c5202c460651400024020900c43c10445d800040131a400d085c03032100da0005041c40c1c240903048034648080e8071080e000c003c1141982c04005560002041000000c04540958006491074080c41d640c140d00842020080e034007904c140c40d1500803100301d0048945d14020181c0203007076002c0d0200e03141a02d4020050881d034444130a44100b0000d9a1070f0511400745080080e51210808540000c0c001a000e80803e20348414040354403412007030a200399034400291015040c1890080808013200808002154000e4a0030b5640e456001d240c1d014000000010101a1514000c3e2050800d00b4010841088002c5503234008950101251090b14000c5a0310000700d0081c1d0f8138000080c40085e541c207000e0114540520515026040503801803114107955541c50130702d100d170041c0040c85441c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 485941366 1250 485940116 485940131
    0x1905071b020103060810023004080708070501021b1005060306161809020c1203061f03021204050705180f0703051008070612061221020124050a080307030210 69
    0x90003030300001d0050144600700c49841d00c00346000c5d8000e42007070410001d00c995082162211102c10003c0d00f02e0702303900c410061026140c580d1881565486580b0403251502c0900081021481c2840901521507651100c903582c015000312513030429070347c0426440e9261802d424008661000248958030210882d441c0400441c560000d0710000840b444201504220b0500410041169009010b0342d0306000c04840788040d0184400c0355601046441541061708010031035529000881180280784880c03c0040c6420350300340f132904c1c425400312015180b41d804640200a14245103080602c8640c101203030603218280080c136028002006046a0101622a004280c12040c400c4140f4000c4c12140103c4640c20340e1070b540640500324040002011034074003880003403911003400c5001d5031a0341c00051200000c680e50507417195490002124411076603181040007034a10001c0385211011840703440110040c1ca8030b01044400002034112100d030350014010580000c1d0005807003001c41c08688004910349 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 485942616 1250 485941366 485941369
    0x5180109050c011d0301060803070b0907140f010507060203040c03052103041b0b040306060e010b04060c020409030e040e03040305010e03090a0603090f080d05061905030d120f0606081905071b02 85
    0x882c4c404030503030307042d40392000c0080c54041c00001440114400c3c4030740145551030b0f108030760712034025200d60711044000103910103003840c0c40608803d09440504007203007004455218981260400c51301240e604004c08030034004e02c6000c015482400701240600c03a0100c0d10380400d100300b40405400101407403003000e400b40540d04808184405003000c901081e40710f650301c0c1400300c00780040c0d12442910a000380700100c0e06d4021130b41120141c0d00c0c2d41d21a001024080d40c00c1c0402040c60550640410214036203090032591640904141540c0140046032030f0350943c01e201e802c40f52044201070182d403040103416190f4592a0f207007011542da904001504903110b04183c0103805031040014107445c800110045c1d00f0b640343d402640501002d42d039440c031100d1203249008902e401070013401c5e85540110012207125200300c2d940c05400c440004040f401040f0705903207105448407500400e010481010030041020350414075144034444840c03081c8441c1c10140806881c442051407042d08030011500c00c582036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 485943866 1250 485942616 485942657
    0x110403020409050607090510050318100c02010f14010f05130906020f0d0b01080103210e03070f0317030105060d020904090507090b0f091506070510050a05180109050c01 74
    0x1950081d205111000c01c41c680365880303020442e140d40c0800e02d00b200110b07d070f00308281405d00355811600c45034510344030810317400d0b8200c1a51100018920958052940101701030003580e0000d00a03030004603500301e041000c0c0d0140e9643c1c5ca11030425024410041246035150105603003160402d580c11850340f00340d10480c2000d40081c2001502041c0009100c456403441c540c001d044003410301c4070030005c2e104807200441e6500c1d820700c03016024a800080303409484030044121107030031503542450805014500003007800c0013040d520035011204070400c10000d01c2101c10740200e0740701d103101611f40340d50304140c00603403140940b030066080030760302080c0c03080b23291510b520058445401038111440d4540c2c40c41c1c014050700c40880058001e100d602c116a14600301590014011580341c00100d85180096003884016005041e0543e07841c445e00b103c3c0242180e05100e40746c080c41420341d02040c280740c10324001d41031a140b01c2c52009240e00d007040c004003058000c50400c051020928205111180c0171000114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 485945116 1250 485943866 485943869
    0x2070305160e090609060a1512050703060b060307301505100203090307030b040f080d05071808030306040c210902040c0c02240d0e0607120b01121104 66
    0x41e128540801030702952089078041200d50340e285148150f0350b4040c00c1600e5044c269030034030b5298401c00203c0d1840e401508900318180e101d8404400040c2c6d0388840b0080100c903c4015900381d042141d050041c0a554040d001d2203800955185180d4100b01c0c0000342100343d002e004032102000181c0ca01668a0243c01d9001d480794040030034491081000c20045030301400e0311078a032040311140304110361b4034000b0040e540c00c0c3c007004000c4c2034114610f40303800e0980d05004208a80e041e040040c0200003c1076880502004c1811074000140ea10f44903002802e400010008054400c00e940c10800980000004490344204c044d10301161444581a0682d860001c010340d0080d003200180359290403e81d1035101e10720741c40c02114107211094034004155240007403400007a400840c82c800004442d03141d1581001c2c0050205801460310102c00c651004a0301204551821904900184015540e00075001c1c9900009003400700500c032292400a000044603825001000340c41d40148660b518074642940d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 485946366 1250 485945116 485945123
    0x80303073005150f03030417120d0c0f0f050403020f120105090d0f09231f03020d060e0f010312021c0801060e0405010f090e0f0d0e011103070c0b0d18050f070602030909070e01020703 80
    0x2500d4050810640f4042e18020000e03c0024400c0d01160700780333030310403807480590800c0354960616190a50f024803450044500d03025802051001e080079420b07100340314581c459180c82380070780b200401c446401403581400c030000804014051006010301c400000c0c2e07500380825240e0116801641060208102942000003040c20001c56440010302c1078040d00200944038054100f08101038403036801134181d03441502d542d94000301e070b10010720028020713428291407004903004949411505890109040d84001002c10014802c480100b200310340015491108040440f400e20583d814044078034680074051240d900059207421207100241c0c0140230400450020009031130082030241720291021603c4c003034a50010b880320080035003001c4040199031b2980d50240300382060525004a1140f13541000800303401040d600d940101c1c07011809640100400d1150000e0540e40b002c0084103410184968000c0c000d40d002004082c1d610741c0c811200070b07800892810f0100d0305210100040345060845d400c000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 485947616 1250 485946366 485946403
    0x402010f031a3624060706021603030c050705060601031a0a08030a0f140301030f02010e030105162c133e04080303073005150f03030417 60
    0x801c91400d900e603c0640f0180714001e05542c1e440c04421848041c0048841c41d081040c4004942103c00b180c41058120f2280140440c0c1800b40300c0d11040100c0c0c0c09941c0809603001428255030400d40c25001780180826942803803820701082c2c0d01c80c40c5d201c42d80140780707a041542e1615200c1c12044003001c916800e100107800440250740764602c2c5556a400441030601040e600d04c42005070700d103d200400b0602e540098806c0c01c40c0d185035900395a62108250407814801001030802407902e091048600c200100304444205d180c5454003d42404089000102c02ca0000b0b103440e094042007440700e4490b48001e4400708000c5502c1e98001000345421000130700c503040c44440c00d001904401170038040501c4098214017083d400310205003500d10452280d60b01d103400034400204514001d01e202031410f02134200d5100d05104041040460f0410702c040c3d02d020503031390b0040c130048905441902840f204e0984040c03240448000c0003030742c1c074022841140d882030504402441c0d404401c0c17141d10326241142d40c0a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 485948866 1250 485947616 485947639
    0x1a10150507061d101509020a0e0f09100b1b070e010e0c07030807030c11010e03130902041a0705010902030d0806040c0806150d0b031509070e0402010f031a 68
    0x3009a801070205440b00ca0503c1c1c5a00c103c082444102d950b00340060004004049514400300c01030000c1c540c0d02859035440703003800201c80c401ca000074043c103203890b60782c4d920f0500c0c02e00400c0004a84d5802c0d840c001c100c2c0101304403401010380310310b1041cac0b134460740e80e10b80b1000c2d801c0b401f040903544410070b0805402208000500003c4800109050b43e017850300900c240d6a900c0d1200b500e500602002030000740483c40400c144c0d5029500900315480945090040040144502030a451501d00924010352002510448000d012480703030011b8080008103524161520310702c0c00d8000a5a0a1066103481c00038000e800c10000f54841c42c07101e07a0240a5030b00400a0480c05403003039500301ea01a000d00d003812951241030b442403001602c40e010007032800c42d614440c18109a000e40200d40940c1a4a03074803081d48c0400d0350304100e660320400c3c004000861900d4106132050410300c80d0b901281220303e54205100040c1e0b000000b2944501080ca0700054040c0400c0e050684240b01c0d40c04140c211485184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 485950116 1250 485948866 485948909
    0x60210020c03130e041a09060a05060d0209100609050f0d020103020a1b0c150c0c3f0c123f110c0d030c0210050913060e060103091a10 59
    0x4000d4812030080211071000d40992000d0b18640c1b03000c88111800d500480e0014035248443c0d809660096009014203c1d450b00c10340c042034011905403031044225110480412000740d008890b00301a01c0c0540f04484a004ac8c04049040311740700c241d000b41896004112007149038451071400314071a803200c00c0c40d00780e8100c07801e041c00700203454019040c07040039488008110a01402e600702c00c0d160f02c00200c040813442c01413140c11841580c20540101564007203004c00c111101704030484000510040d50106034140d00c1c0c100700c4e034001d6601015820100b0345107503003c00d00d00fa000c0c001eaa00c1c018003d69603c0340c0701e0702811908035082003d04003400d025000702c4540b43e1141401d0803504031081190404101a02085120410140e00a0004500c0146100141010b151149110b205410854140002c40c0d00040c68079103030118400e80c0303590b50001001f0020540040d643c10400c2800c1c104145e00b142d0311802c8c14003401e1031101104010060204111703901c60f00d4003100401c0c100100185078054080b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 485951366 1250 485950116 485950139
    0x7061e111603060617030306040903020321011701060b180103020d02040b030403180b09061602040507050c12040f030f050c040c0306031a010510080a060f120b0709060210020c0313 79
    0x802d071003840c5807400200381130301c0d0041481d452819045c015411595030b50f0400c8041c0c0601d070011011800305101043c140c840a1340d1507c485402100301c3c054540c18000080c180142c83d604811080c0e0422404202e44070b00744044920300c0040b04600b40011920350010703000703840b442411055641c800a000038030041c20101840c003540c46580d894590800394903201c40c41c82d4440c000d54200c40b03020006450700e0b00d00031006000e210f400700b00000c550319064001404890ac00c0f104000030a0002a0b000c001c4c0703c00780000c904165031240001c0c03c0038108900e00c411503080303000083c02500713401507030814001c080000e00250b0303c004005121282c03400e100100030308000e100446856442d00c00c9914440c2d000c24000e07068a4002d0881081c090002208880186028008140c810340e141000714804d00201221800b4020401c8500380a944c289800395048600401d150200709441205020f555404a07154001071500c4c0000358440c014045503c4c103603c1104114410740c001e00340300140c031400c0030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 485952616 1250 485951366 485951369
    0x130311040e0f07050402090d02040f0b1f022d060a150f080606150d0507021b01180e0c040807091508060c04031e05010c1101050907061e1116 62
    0x6440600503032210001141e030b1041550070007000c54000d03241c184501d0615070b02400d0308540c000c008504030380141e0040340844003d000d440a2864503480d2441c028207020200310740c044006120316140c0c81036108003c0d2a007a105040016282800c9045400c5c13801c0550500409a1480103544580c285402c02c10018500882420095034800300d000858a0b030103010038045035400d40150203075544590400a4001c41415406070b0400f043c0080f0185502c13920415200b40100c0e0010581d44510842d14032550705030303078502810002c0002030350102ca4203540c025000c40703034014150041c548441e161034055024a030808000c1d44503480b00050b11145030380002c000410042c01da8012217854945498443c10100ca00503913a400c02c0004000040308034800254511000c0c8440b03000405680e2450300707541420745200001002c0c1000035030302d80400c0c45402e401582d641c3c01070a0791441c08030040c19460360041000318160190407502c81c8c0600400e042498500d0752800e648140c82b52140d8070f40c850079035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 485953866 1250 485952616 485952619
    0x6090e04060b130e3f07171303020a090e0a0209060301020c0d05091504050303190527030706020d140d09120503180105040305070f030e060c0c030f010504030f1103130311 75
    0x403403811088001054008110f008040d80c8080300f1150317890740d0360400303030700c12041110b650195019030100c090300c84000e040586103040c1040c854514600400c000210b29810600c041850402182407207000001c0b40c0d04003d80c155481c02c400d50344c0400007402800307100100076090040724400340348150303c0001450001021aa81c0702411040605800d45000d1030103200e426034130811540080307050890340d492a042407071400601d820008034642038620400038441210040c210408062840d040c0030000140402d0b200810045481940040c070b80c0800030b401052145000800c07441c0c071211604000e62072900724010454451010000030420382c001c4858001c014540c2000704818101802040d02483e055034980d400d00d030854079800d8500804010890510090070468084d9885984c0940302080c100806002440d801205050400540d81c9003170360345903d02010000040c2d041907400307003001e15504d0920340e40303103000804629500c1031543c070503034052451800108001150041880b030800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 485955116 1250 485953866 485953903
    0x26040902070614130f1b091a0906240708040605090a080109080a0807120608070906082b051c1a06032502030d110c01050106090e04060b130e 62
    0x88010380342d4900f02c00703079401889031149910142c0800c11004081c90030368000c8811155040d0001d106920100c450741c81030004940700c0c584c0a248090442c00074143c00420341c0e060038180342c12000070b80c40c070f020b4494400e00e9140500c00e0f00074021056060701d030855400744400340d66541310540a030617604030784c071a9846480e15a41c04a450807042c024819403550089000d0300788402e2040075200444002c01c4442008980c20001030920140e0042100400d441005410081c0c2444270410070b4903129003081045a01a03090300c05071400310149803070186043d800b00d4030f11101c0303044211100d206089640c0034603c03c601d544a400d0b055544030882c01001d803202c80d40e414800c002448420f0100302c070040c0c40c04184000b50881c00c03098242c4608040b80f148192841d05081c501e001040780c19211007507001c0d21005c1001c1107540d0302445031038090051400c0042c1414030300741156612110003040105029110a030410050b1201d4118044040c030b1030308240400104d0b06030507503844036001c990039041074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 485956366 1250 485955116 485955131
    0xc0a0903140622080f070809030a0f050f010e061f0f030303050f060418060e071707031401060305070b21090f0106050910090b0f0301050403080115140403260409020706 74
    0x56125076410f580c0c0d039112680b9400e003583c82996180d590007801d015031760700c8800c002c1c85040b0b07641400760241e601d2054010149035802c80c1000b030716216040088580a82c500104184150b10003e4015070084c004074074000d007501c44401095034171b070f110341c0301f482030b4240014088201070f0560001e520a40680b100a607856403048200415580301043d5800348071113200c3c0001c0452520b030004101440540103c48016680c0c0c4036001da01d042210039010309400c008014001c004540c240c075035140b0901c400a0010a04644445403564423034840d42400440001e42003a0000071410002da540c10322450058440c601144000e45aa4a41c0c042c1c5042c0c1d481e184021802d482d01c21002406406071501008845060868020042c40104c258640c408581c1400707402c0396509004031407040d4400d950360861075240072800855520390b000703050180402c56800580c1070102201707403000c40342c0022800b080710b4440c0307070130045801c100701e5400004000007801181c0c0d11081e800600c2c0c554801c110820490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 485957616 1250 485956366 485956411
    0x72d170f10060b04030b06040e070803120105030c01020715020712060605011b0b16050d0c05090901064506080601020c0d0f030f120e0606091e0c0a09031406 69
    0x581c010700803c22000c50500c000c2c0040384400c540d06a1000d00540000744145039000e101307182008031b910206e0540d000081d03501e00402c1500c1100c1c01440e068008000c1010700340e0010b5240d02d164010044564900e040c0200224420061400108400480c1c1280480c440c14a500503220502655000c203080e041120101d016828049030483c0d08042c000303249456203484840b80030002d040390780801005001403000c88142d0300c80d442c1200e49503110240d44240140900c685403005901c804244200b0303d02100c0780352481c01c04408190002d84c00c0d5440d8011440510311440904040c080800e4285200410391981005030039000300002d0302100c200140d15010440c3d60101440c00505200c00c0601c0e80300004d00494000b4445541403c0003004480c1d070744486400c50703641c903000840300d9000205102e071608204500c650081d0010316890061000780c1a8002c540740c02800584141c800080c805803220300c117002600c003540c2d1005804118840c0d11a2048d510f0340c0070340e81803911420450b41035024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 485958866 1250 485957616 485957621
    0xf0708030c07140c010815031e010f0f150503070e041e050613050142030b0405060712180f080d020d02030a06140a0b0d02040b03010b031503072d170f10 67
    0x40c03000040050855030340c0396007c0d006100c549401c0b034072740307649500202c0c00744441802180c1502030700c0e98001801000301024502c050005500c201e0082d00004002d1000c00032804480d6402500802090240444001040716412100704082e1150207607005009440b03900c0058041100c2c040c9000b401a40b448007120141c1e202108000100440c2c0c1c1c400e8101001d440396441c20320518000125000d05640e900c1300356200404660488a64102c0d00400c0a6140c21000612602520050400501c0b1501c00c81512103841c603000074112809041002c01000b400740211072074804980300654071505500d81c50350203500199041c0342090b00b0410041039503010f080c100b843d4440c005202e00040c520700310a100882d40010b0003486425001c01c030125030b1640e600c0041d8000e1004040c074940ea450034545810181c00850f8003940301c0c0d00120000c00c030500b01f411200505d81000700c0d10310b208241400c4042003c1d00c0c26445020f85410b03140d80742c0000c51000c00c5a00c1c2c060b80310b2090305d1440a00307601000c01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 485960116 1250 485958866 485958901
    0xc030605030d0f0c050f121e07030503040f0203070510090305060c0313030503100504060b0901020c0a080d11011e0c0909050f070503070203160b060a09020f0708030c07140c0108 78
    0xf03558002800300c10348a841d840e184a40a6826500c285051051031030030508850301030005010002000b104c0c0745030f1035050600c6a003900070781c01d0a10742e180e034005182c0c0c03002401c05440849092003550035035400784031500c0200b80040c080c040d04400e00301d0141540c6240d10055500303000d00000983c0e02244042281e1143c107415880014001c410b98041d28160005855146411419003010039070341c0f558440c4902801959000941700c0c0300c031000082ca00312a084100c3d0003209c5015081140ea0030020f02c0c040300101c86d05083c19001c40711102c2d1401071080742c41d20040300305400814504c00d0515072042941c02c0d01e659516200940398003010050302e07029035015101d46818400035014610a101a5804c4104d907c10340e480d1800e8104030202e240c40c440c3d41940d11481c00000d2001a00d01503401b40004c02150905506003001e0340b42800c09030061b6100548083d00000c0020682207000044441c01540000c14801042004401c1d9946c1c1e85411200c0d07012580300000700391141e607503844003071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 485961366 1250 485960116 485960143
    0x120c042417180c01020601122303070b0a1a032a060d02070507150503010e0c0403050f06070809010b0109050d2904030210270602040b042c0702060a1a04020d0c03060503 74
    0x28840c203a41d18041c00c114142900049c440341c140c02001c060003800100100760041c0600079442c02c0020105045072440b101169002ca001c04a207403c0d0745012600704640d19849008644000001c14901f41501214244d1940301c1c0c03000480d5100c2c544564060008517000c5d02c00c0b90f916507103e20541c01101100750b410b40c04194188010006401c0c7c102a4540c0241200d800a0400fa034070b80c0c49524000503402c4960054203c04104140e6540c0b005100e075000b100c1d04002d00010380400b0010340014824012a80a10485441c80051004269070300903174038880e00c9040745212035080c0320307800d02c0340984007180140500e501d19840c80280d402a2298501c0d41d1424016050032500c0040e402d018103441100c00725004d00c03002a61080d0503014100030000c5511034082c1349110780480301c10070303c1010b80481510740f92041c460207590005040342c1c0004480400a1091641441490790340d00c04416164000c0c000a0300503401c904982040d60111aa600c0074092680c6680405807202d5080c140d05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 485962616 1250 485961366 485961389
    0xb04170d170c1e07050303341215080a03030b18010b070f05030a0309030224060105180306010303090303122904060305060c120c042417180c01020601 66
    0x41c4111040b040103210321a08540103031140600d642d090300803908890f40c242e40c26007002c8200401303180686a502500400035000c0c4044403000c8404121180300c520303181040001c0480b00c003c2442c06680140d10900c00d000440c0c00d01e595510340c46d940c4182c0c1100c1140001e0a0581c680e44e18100368081e501980b4a40d0450310481c0c1c2801b0640780260404a020340b20103645400400220b01c007400108108041a60080794456150802901d0f0039042208420000380803140307524280c0062902c0381e000842440c256580d4611000c40789842680d03a4070007a81030285800007c20150060340d03a10469100e51940150001e604560318103d030301e4401101c0d0584040784107007102c200004000c2400c080c006000040d1961661502407402204a4901400000000b000c00c100031614000a0f413108007848120301e05801d00d1101401403070300710245060b0f4111540a401024000d090990a108032500f100b170040c07034a002114602c80986114400034010030800404075440800c80c1c50680c0c08607500e6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 485963866 1250 485962616 485962621
    0x70515060f0121060b0c071a0301050d0503040314010b0405060105130e180601031211060103030c02060f0715050114180c030a0207080a02010218040b030d030906060b04170d17 77
    0x6440d01c2e84010f000c0d031079204009488168680c0b4a1040001034482e2401841d1038003004001c281c600002070f0840e030300c0301300c41085090300840381d0002c07603041d1907060b15001c0c4148070520b4168503600450b007008001c411001c443c0040c0307500560081d804071004179800d001c291580b50041da082c4c8110020f80c1113990400000b48030216100b0b003003640000c0901c3c0701d8000c004243c1c1200d4140701085e00229003141c0c4140e240d82a0079070040b0390907141c01450b40034280c07035451a5005480f030748180e20020b004040c0800c480c03840c4ca585a080d2164540c015003150b14410794098001e0042200340180380c007010155a9440c0c507801d2030b05004c00e0b1040141040c40c85c035180d041440c401500f00901c01101c55400f0441440051180c902500d2404916000581c507050182e540059280544001d107000b50720708100300469580c0041c211781c1318803140c10002811200c5040810107868070303807c210240c1c04002000a41503102c0310001556150741001e680e840c20741602c0890b14598454070f04030012000b1000f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 485965116 1250 485963866 485963869
    0x20d110a05030106060302040306051506120c0d020a08270c0f1f0923010801031b21030207080105061039052b0f0215090102070515060f 60
    0x2400499650040182203056901c4000900355565600068006034021504100700042800f5203a0080721803648585a48103940118000b0b00030306103036605030710b0408003003610b162001d003c440c2c00c80e0b2104425980c50108940241a40009803202c12a102c0b440c50320740345410b600546144403840c0c2c1005030903c1e00d2802c0030440f64545000d49030361f0110b041c0145002201c80f00002080500c0d09841e00200c080c41c1c0f0317584059102c3c00320002c0401e20401c450484044c3e030b1140c20203054075442540170851980a00b5212043d0095401040c40040c04150034203c01030013113522002c1038031950807252219220075020f070076a0383c01d444140c0c00084148261030128050400c04010400d1224004a40416441c0300c0111043e54000b4800f460032154802051040030300035401400c0000f04a018188641c4500d544a04e41502e0745108024441040003205442809071103680c9072515008549401e08502c554002d51080b001240d8910a071080302e03491102c0c50000f140718010041116400c10b00304030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 485966366 1250 485965116 485965133
    0x80306090a05091b1f02011b031a090a0b0d0c080d09050306011214011e0e010e1005060f040203090303220b010603050414010903230f090609030102162607020d 70
    0x184c0030360b840341d124900f11034805405181c44d40c015003554004150401030314800310304e0b0262120200b04150501100c103c9201c010b4102101c108070035503d405096807a00307102070060241d100d0542d8041074001c99501800004080030098589182c00d43da0300140c401c0054504183c603208680c2c05400010040000207640c0c074800300982c0c011800e09003003406100710103003100c1041c500c600088401b07403500c0d50b4a800c01e00c11402d01456410007000034a0600c18259130705c0a40620403c50f01e903c80b00040c2c1141c40c0c031420550100d0003e04295280c0c14050009500c9400458481d4481244810095118681404041a4982c1140d441c4640341d00b408030403800340c600144140c0c0c541b41004100080d03000d0034814003d0490080c0c1e101181d101014184d03880c0e00070011840300114606000050300703100540100c03090100129074655403181d120000c240680a00b5404000365a2401e0040741070111100001005030215100804c0101040c001c544e0360380503068000e900401c1107954070001400e801c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 485967616 1250 485966366 485966413
    0x17070306181a060406090e06060309100b0f04020a020106050f060301123804050601170c0f0a050a24080712050a0b060d0f1b020a030f031107080306090a0509 69
    0x341c031070044840602d022a405070b1096000c2c0c0700003442410100040f1070315003c0550000c10031240141740d070401000c0540d1b200454a00c00800a42c1c50000d4503699480030004000c6c035034040c10942d1078600482010b80244101d10a4500490f6002117444262138510101c9043c0c80c0c905404200c941880d07102da0750410581c246603003820000e80d000403005070203102d41080100b0300b09481c0c0000d103400e160041c1400341c1a40080c0b4246c044400c1304644103004249d0b02e0f2510340507501541e040008000080d0000415809140c01c20307040d00d408034108084c916005196008030b5514103400c00c203600122860a0200d5112000464681004480001d0f5410680e0040e0040780e0120b041c0f1503480003e6100d6003c80384450300c40d65152103400440c030242c00b444043c2082e440507243c01055450f00691200d0444800404000d1022480b020b018000c2d0301403602228540c103c50b480f100c4a2501c030105078010740c2c98a100e5a003901c00a241c0c14001d016480c41454254050841c01c4542510f41306c02c54000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 485968866 1250 485967616 485967641
    0x150f0301061203050a0e0a03080703270b09010302040b0f070c32040e120d0606080103120c030215010b040e060f0a09020c010b18100e0f22060c1707030618 68
    0x2445000c00e079280f481020180d4012700501d5550f071803030b02d0041c000720302e0102e440100401403030300c41081e100519545002c4070080c0d000c0981e61084480109d00078032660b048801e4a030004920342d580070140b90042d2507054890072140d41403544444c12030340301140d08038a0340c00280000c00c15544480c2e100c603182d07006907809000450301694070040c090611000c140c859500040100781a0110400b500401c0010002424014020b50540e107516000da540210440300f801306401205c0b003090310030442d603c10b5814680c07400c8a83e50311010b15060580c081e2045503400c145520106026141c080d140c40d41040c0b009290481c2c9500e041c00b07042c0650030602d460042c84d5a24001100140c44440301c0081d000c400a8800d002c516160042e4100b40e00941c00001182c0524420041000105c190081d0442d1481c043d68117150030702c104089040a26541c0102010308064444100c42e421040307241e4941d400e90b109121030742d147c80040b401c541191207600d1a038074200f103940ca1030b80c00c140e001c68034003080e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 485970116 1250 485968866 485968877
    0x8030105040f0f0c0201090c051903140312041b0b0906090d05120a030e01050a06030f030e0d08070b0702010c030c020a02060708040914010602100c0e01030e0c09150f0301061203050a 80
    0x6200d207803c00b12410256941c0160b5101d0b0020000c1200c01c0c500c00b03000d080c1c119824100c20250b005024481e030b066010003030090f110a10004c480b0700c02002503641e0710480720814221483c15160030203140100f070740700d104d4543e42c0d4080851480b00c500c0030f4520710100a0012400c1c51020b4041000890000b00d05940c01d0082e05c0b40d00102c0100c15004048030304c45a1000308032288d400030458215003005080703c548070700c0c03d082071001488806c56a01015010b15040c00d009851000040500c1307181c0c50000d0811800240303030b208201040c2c08841c460700d01c94008001c01c050b2030f04203606403209100c03004010f810141d0f072a401881d103240608016070080700954103207030319421a10110350303080d03000d04058460318004200c425810000c82581c40910310741030180d0f44a00740045d1074506148210340c1890f4a074500381c2c5d0380c403004101039850040001c0030340985040138a4039030000403400c03031301034044c9109000e4080c403401d0500965003241c41c208285174141120f41c60849840d00800d110404006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 485971223 1107 485970116 485970131
    0x901140702010905060706020c10050f06091006050f0c2d15061002102c0f07030320010609050f073906050103050106051c08030105040f 60
    0x160082da9086d44800080c6040801b900505208522a204084041442c0003694001d2800340c154901d103030b2480e8480c881400010034080301d60100600780c13004104030700c9209000920061400c021601d041c903410246075801d090550001e400440440c44100102c03001040510703488040110080005042c8021448001c1d4030003014113104210720100c3d001428024081d45043c44241c500422000407852070030742c40d03881c1031425142d5441c0f084a032140721640001d82038141ea44600c00500c0b2061541d07404480c054058a00004450441981880200300c240a00c0025055400001c102407030100c0500d00d0212000f8881401c2206602c21055038402c419032034061030b20b42824003800c1c06030b0f0705140040d11000342e030001c040c0c629110001080c010194031500540c1c0040b602000c20450b000280c2881050881c40035206402c2040100002d203416400000150003003d80441d052 = true := by decide +kernel

theorem cover : BRFrame.Cov 485791366 485971223 := by
  have h0 := BRFrame.cov_init 485791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 485791366 ≤ n) (h2 : n < 485971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
