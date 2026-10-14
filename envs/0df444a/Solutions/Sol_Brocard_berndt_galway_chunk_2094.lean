-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:38:18.906635+00:00
-- url     : https://prove2.me/submissions/bece6b7f-58e0-4148-a785-93a52fae49ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 376438848 ≤ n < 376618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 376440098 1250 376438848 376438877
    0x90909030804030f031514031c0f090e01230409050d09090609050103020a05010e3d03020331060603150b030f0a03030f06120f030e0d050a1205040b0409050106 70
    0x4c40d941106c034103146204240007031016001020707a0311401c1c5001022240c80170180440c940b44c0c401403490a000084a07450424130164000600d18050110006060b4044d030500070807210f10310306a980003000c6424854101d101e5241d55009440042d006404da641d07540b00400042c0c0b141d0400c0c4268034071246030910009000c1041d1003018160f81d80103040e41a51840e2030011213100ca601c59038a070380000020071555000d40c0d9003102e65551400d100100070b0002a034549081c05a016030441c0003458010410030001b44d1803020100303a2101c0300c4685c0f0036030f85800703541c03a4501450410000c001601c1c1c9180030050040d560000e20b0a520f48030b40030b0000c40d000400389511006030420008a941c00761400748000b90003a042070005800300c440004a03140c1ea495002030101c1c9055040c0c480f400505850014541e03c84040401c85000f82d0300d8003003130192070740c4259890941000180003612040302c0d07408164801c00c00c40b03000346074101500740ca032510340b40c008004050038800d842c0402c0c3d014a26101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 376441348 1250 376440098 376440101
    0x5030d0e060c090405191b081602060f100506030a1b0c03020d0c03050f12150109050d03030b0612180609010e0304090207060f05010303350a020d14070e150309030712090909030804030f03 82
    0x145c9d2105a01078421516006844804858045d03c054001c1801e004081101c6c1c0302d9001552142c40d40000110b02c2001c0301c2e1600401d40d084003c80fa042140308000500840e4001582c0c1281d6aa2803604002c0005641404c940f94003a09001259080300043c0c01103048866203411800764030100a01540161440010b64003452940308003030300140719100c1000480c2c020b900c00c40043c100a04154035000e60b0910006041100712a503d0001070282080c144005c0304006441d801501c84008010700c02c001141c541d03481c020340c800c00b510715800040c04001c020150700082d01101d40003c4c140401d5840b49006020b00c0c02c0851407040b10310854000315101c00e00c2040180e011591441c1d103821685030038240b0000796010106810a45440741c02207003031844c00700030061003420640c0d204e03001d0201c8041000110005201150404c18041c02400304a44005c03080b02c8031300d0360240207040c51f0300001c0001c1e6501040c95019143c2503107071a4200b41890340145034207114510990341c501d480205080241c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 376442598 1250 376441348 376441381
    0x5181006080d050a0504080105040b0f0609060a150905030a080408060a0b01120f0b1003020405130e03090108091207061d0d211805030d0e060c090405191b08 69
    0x7040d80c1c45031080024543c001c100520036201c10740b030000d20f041d440f0f0507201d0940710141d50443e000c1c610041080200f20004400c981c00a60440b04500d4905045001aa40e9281070080303c0d010f00c81421007040c03550040c101440148030250a0301c0045100341481500c1c0e0300700d0f1140000c5406000d000a42940151050001e55407050319989130342c0108003000002006110090380b00c04d6543c00c407801d400e9444210710300c10320695580143e80d4030304080c144012a801144c0c0441c4031381c180640f65422820110545143c820300380f802081e00e5940b582c150380341190001000300d14500010b9044140252500015004c24003002614400f135800403d5564581c25440c9d188009885811001e840411000401d00c684074940c401013402c550041541c241c080001200f292286c1c000540840c14690a004081280380c000f000340c001c40c900074440a146200e9071701d020384200c0d9102c0000b10000c46981414a81c807020b61010064800c905110b00b5030030389501045d00c00b240403040021404c0807100700d441f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 376443848 1250 376442598 376442609
    0x130e0a050c0703020a0f060204180b030d05070201171005061908070903050a0b07020f10020405090a0921050409020a020c01171e060d0f03020a031b02090106050702031005181006 78
    0x2000466650346a014100001c80d000b2101715030200000991b1080040001da1140ac074420700007141c49000040610b0302010310005e0081c441c0a1008501503a04085032801c0c1030840f140e1207a655660802d4914080c0e41508829405100440d0f040d1200807815201c1024030703a2520f903c00a91100381e030580e00c00c081444014581d074462400301001480d01c1c80c4090f002101401280c0a08402c208010309000c814090082c8079680841c1c100071919003200c5480e00448013002c00c004404054950540d100d403140682e4a61820034803030781015612600c00c41c3c0013400201030441d01c41c0005c800013504e86016000441c001103488101c011b514041c07001c454000c0048a10b040791103030a01005842c0c0200c005c120f9540020303035086070340110f0300090b00c1e018903038425805041080e100340760140c19480c0360302041c06440b024441081c0180c60b01100d0781c4c1964110f040064881c401c62000a2510350346210304d07000d0b542010f0900c2181c0840c041c2104080391080103852030410f0a001c0442141d10512a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 376445098 1250 376443848 376443853
    0x406020321010f060c030905150d050f0c1b0a0804090b10020c211606050307020d050c07030b09010b0d060e0c04110d09030c0501020f040e0c0c0d14130e0a050c070302 73
    0x4201c4d660084200400b41da200c0c2c102040f41d55a00c1d0002008584500c055555000c000120780d1702100c81446a580d1007182c010604019044c00c40011245004101c451800c8040581030162041d1040084070055544500495a100c2c0c4542900000c0d040c041041e9015039603042c0c01090460000c500c803401c5c8400500400c08642c0250f46129145240120000c9540507008148000700359000e09403002d00055255184e59003042c140003480c10314503030a9201007050a0090398120100851468200d075008141d100721502c8048115004010300c0c01e899600c00301182c856400c10030243c0109101b01105000d0b20b20704003504081c00f003a1603490703115a40c1003c08001152002c1050f03400000014000d02c1c0200f10070000b03941c3e02d822a8444d00e01c0c1d03103501030041000c00031040c0c08442103078030145c1c100c140350404413480c10440c2c0c2c40d58040702140074000d4001c80c4012900d07411003543c101c0b0500584d0011000d42c0c80e180f206a080b03058880c0c2a4050030500092003a50f4000c048406070784e41a1700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 376446348 1250 376445098 376445129
    0x190201030218040e030306120a03090b0d1d0a030f0c020109030f050a0f0302010609110901050a0f031b0e0315060a0b16060c030b030c030601080c040b06070206040602032101 76
    0x4500950003000b040d4030110580c01a1003a41c0c03114400c4064a201007002550340307091200403c401c4071224204030b55158469840700340000d82c8001210211480c550699881d40c0e003104100d8090115800300305074185024502d4032101e44005080410540039031281070600c02032040c00c03240c5410014019010407401802000010342c3c020040c4401030080d03054400c504529910039100607031013101640180c0d10f0b00c10900040049201310381c4ca64000c0d02c440d41c84e1075201c00c0042c0850103400003201c00d0001148548400a020b074100405a03d1180d03024421500c411402400d4a000340c0c4c980c3d4068894501498141001c1801d003e02410700104a070352601d1070b040c160f401e164040f1100c1b50b04160380c4450040010b9803800390100c100304a480110b10140c0c640141807400b0400d0350100d2085c3d100e4030040180400210b00200c071a0b07030955010410800c0c80e40864800e00c40c0384002500420300160008074164040058260389011006074008100c03140c0000300200420700070800610302616 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 376447598 1250 376446348 376446353
    0xa12050901090f0f0b0c0319080f010801020901080f06180c07050106050d02012003091309030215070e013b030708030406050d0504021201060b041e0e0105090408070c180b0319 77
    0x802403d0241082c904407440d20b00d1890040114400c2c00d008d0f000441e17034a1042c000425200581c880c00740840310021814880c2402c0002c081003006004000d0ba44007150100302d280d01c61241c84481c1c25903001d4003100b00d0071b1041c03002c3c07401d900c50300c2c00b0342c0c17176518210b4007107607610f00700443c0d2801c2c5405940d288008001c00c1c50b030581562286080c51080e00c01045101001c1d1120408c1e249054840703400012180b50b5810081d04014a090361002ca9603000010030041641048051050500a10300003910392405070f1650100741d60301e030f000003400f98441c4007014080c0010041015051041e001c0e0746103e075442d20483d075280514000e1001042040c4428510741006600c8540c0c0680002c0c114014500024813041c2103582c580c10028411900003000c2c04200400c00c2c5565080c100e0303426005840d403030400c4c1104c02c8041801000d01c00c0343c045c00401d05001d0010103803024560410842440310b942d46007041c540c0e02c04141010400350400c21904064680403c03900c202958078900c030780320448590b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 376448848 1250 376447598 376447619
    0x114010b1305090118020a05190207060e0402130e07120e0706020f06010305030f090f061201051512240907080103030e0d083f040c0906030804030f050a12050901090f0f 74
    0x51f0b421104102080c01401040c0c16203980408051105030090711140b820081c00804030b08045044070700880c0100048110107081144042c100d5100103000621601d400d02d08481100d00c9800c590100b5041080d074031543d86000c5048021544103808039180341c50b40001190300c0780024070028000c1c0e0800d0004501380e104210080045550040074501044508030001d0415048041c218101d004500014407950905280349030b42e1a10f1080d10604140c0502d44064400320000c00c0308003c45047c1c401e6410310180da14048500a01c020500e00c400e24003160700424000c1d003480b040e00080c2e00402000c40c607007802e121005d1142d41081c00d29190002c1034039030303c040107900032261030f8035409407440c442c000714036446d1490043d192001203481410715003015a01c801c03032900090001850700100f00009030416048600b1a40d104420b48003030780150400a05014070204081d140403100d0300c45015240c0c0c0400101003504098895018180d1120024120084c642c0034100c11806081000d00560064 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 376450098 1250 376448848 376448857
    0x7030503041b080a0b09060105100309151e06050415090527010204050a080c0603040f0c0b16120f212c1203090c0108090114010b130509011802 63
    0x36a104004140290b0800040141c0d203910a001c0c581101240034108014420001d03040f007500340042c00c85504020002d18226a00640c09003810381c0e41d50200100100806c802d922140c2d01d00080020a81c11080d8000e4800060917551030f03a03150002c00325061602d8810794280b1101d20340521040c60426440c20000c04c0040d1480b82d182408149c00207900d00d0700c0c000301202c02201c00001d601d031441d180034000c1c000e1142d0000d86254002d010403007030507201c181c00e5962058000701e620f0704003281420400c010a02d6078004021841000072450f000007010041510514411034409180041010341164101c08260b5004000f4940c3c20724030050724800c1c640c0c5020340701c4101e000a12038822071007100040190030105000482809900d0803407403028000c0b8549000e403c40304034276518006420a4690300007002c1c05042c0139030040481c207024800d40c449480084860f100b4005541c40f04280c0a503508184010305c0030a03104440459113080403011281200c909005900d0a4120304e4021000b9411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 376451348 1250 376450098 376450103
    0x60b090109272a06020127110111030a0807120e06010e1503150709061e030c09050d0b1b090a0504050406020c0a03050307090b09010c0f05010216060b10030903050703050304 76
    0x50844000b20f01040201845040212240000c01181c5000340207400d5811084030b90710303100f40d480c10b10414401c450120b1420f0a40c0300c00e0014820010f42d00607512055040b03102460392101040394811560403031155401070300941c80c3d03801c4034030514003400242c0d501c5401072240e42e04600c004003d403d20300340c01c550b000303100d031082120741f090520040f0f40341940480151380222608400e00152a4100c2560703400b4045501c2c0000c808044042e401003500e00484040c41010340e15608460100e1141c40c0380340c05000010044844000b030b60822070405501034417011202641404120409640d000840c0c0304d1040c06072142070324504d40700c204002800001c0c415a9060340030004252a44028404515003e00c01e88602d6120700b03002500505598103a00200b07000c1c41c2c10441d86126030780040c40008465480354404940c0d09052038140c0c06400f07006403034118008001d600d20f00f009640e420400b0288002c0d9111f0b031051100460860544491007005404250104600c4c2e003c02d10403001140d0260 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 376452598 1250 376451348 376451363
    0x13150c1403060d031107271d1b01090308040312030c0e0a0b0d060506120f07030b091302040e0712150507080c0d020705030f120a141f050904060b09010927 68
    0x50303507444801102251f6000702d5031003041403054422400c0b618420f00c4c12500e0001c505000d10180139140e40e540d1607005640b0340306042c4004900072907a01c02c5254101550340311709140e071696520300d05030400409488581010034200205d1403103291040d0f030300d03100c540030050101c060b5600d030641404041d8001e8584582654580c0004900798850f14004c0400c01000fa201d56020314003103058400841e000361100c41010f04000340b4011179030340c24880d07540101e12600110b950b43d0140c40050000d110844461846009640300041e42c0c840da4030b2440152400b444400100e03840d01032788401101d07012511440492540c00100702c4540c0280c014020060030701400510f000503030344400b0314503003200141103110000000d503a035103e100704d80d442e5013180c01c0c40001c0c040203140600c22591150010302c0c0a104180040240c9a8100121403c40050030080d2200d0001c3c01c0c1414010040c003061001c0502981d03e540000071259094810100000c170940c4205c2e07400000c0b0b0700040c2212800c56420b4078110b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 376453848 1250 376452598 376452613
    0x40803040602301e1603180f0c0605030c030601080916030c15020a080a08060a090f1a040b030c010315090501030807031707020604170909070305101401020c040513150c1403060d0311 80
    0x43c40d47d034130311380380035000d02d210b4110840c3d2880e00d5011124280c1101041090600a000c251180c010589801c29424240324800b0340d2205201d44c58203502c191804d43d00c0301180703000428040d01c080b0031070a64001001c0c0003412540c110307003070346e540150f0070006048030ba04212480c2058032507100f440e0841e80050031661003d40d91b90424041da03600c07400714000d440d0307144620081030400d96a5920210720580e820f0000a0300031300081d85441041d00444e05240d2601c00e080c00d2541c1c2c0782c6010018000d10b410400c89540c403804d01502c0d5810400c42103000c0748030071054202003000b40c2059442480c456000380142c0e6500e03a02c401620501020008074078105011441032960b4030150300384907103074643d400100c03441c2c07140f00c1e905000419404107010002018800310566400b08040440080581f00460561034144035490068202c410240800d400240085080345031a00020107820696031008840044405d103d085444296061980300d072803880414006406201585c2c02c0035801001c1c0c9004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 376455098 1250 376453848 376453871
    0x6071403090603040309060801091b0c030e0307090b1305060d11150c0f0c04020c0304140a0f06050310061409012d0320070209040803040602301e1603 66
    0x2030f0420f0381c0440105565030740c00e0100719802500180103080651061162507651100011280c03654010f0340c00308515004030006143c01041110383e0350350003030226030f82d456031000d0440090000c103003580d1040c20414070071400d010341400f0f89801070000401071503204540e81d841044031008038940e1030b084550f2000d0401f50822400140c0384000050014201d6006036004240c102003502c03003c07074880c0380306200003000311000100707513015176406004010f0101c100c00c1c00070b2142c07440b41e800100007442000011410640c8000030b5401240040c40070b2900584403072090313800c460042000c2030003410500030b42159600c1948040414099504024646d00d54005031240b40c1040b03058410200780c40785040c91015081d841c0c0d0070395840c80b102c2c1080c2440800d0f4001061030101400141c4610004800b240501c1202e50468070a01c00301110340300f41c52400030350400441e00404803103401840c2480019044a9644403a01c801c540039860300741c90b45d540828590780c808000c4503e00c201541d0b9040c0c60300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 376456348 1250 376455098 376455109
    0x1c020306010f15140a0f09090207050307031704030806090705070c0b030709060306080c0613090606090f0e0f190b032d0d02030414011710091a0607140309 68
    0x10b04400d140e01c442c4107003450300110344040c08840110801101001c80e4403802101800c0e15402400f510301214540c0000c0001c030342002064002c840710610004501e020002c2c00001868003602c04c1c0c0307a00040151030050a9a02941141c0103404038000d100010a07030f00c1c1443c915680305210f42131240c10040151581640c0c0da1468000d4000d140d8000240700d00c090b0046c4001307000340118030b800c5c480390741400c080a84508032000d04c00d019400200706400031300f640011800241100c2041000200c1c1d803607400601850180c8111981e8010b04d40b80450807100000c000c5201d000c1100c0c00309a41c0d220b04030303440740d8220b401d0349070700792990346014180d4242d800344003900038104820300080c42d01e0754045000c00e0b070b248814540d181c2a4030121266200980120903541159070380300320708a0860b607490040c2c400002d4140505680f220400c20460038203038001c811402e84170f81040800100c031082e0361442c007852450340d80540c072400610170400010381c010f02c0d80450069034810f9030304001c1d20380080746 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 376457598 1250 376456348 376456351
    0x71b020d060e0319020f030403020f12250f0609080303070e030718020705010b030601121b050a0303271d06210f1903090303030b0a03021c0506010e151c020306 70
    0x113040300030303980d0743c1106070f040140864200a140c0a145858039541c005480c040700c1c14595801801e200803800075004081c40050f81380314000b00c40710b00000780d030002041b480c5801c0c0504c03441c01c80703031072400b042140c03068803040180d0b186080214903640301c1c000203486d414101d5801e1136051250b00404282040b50001f9038004203501c00c0c0168840714540f81550075079030780c00c5005000c6e9002100400480611700c1107005000c5d0402d0b442c3c810006425040c100644aa410007500200300400c0002090350050f82000b12500b0f25481c240406915928080d680d40039209102400b050a070301110f11000c140803071303504003400814400181400b05010440da04414401900c140c002c0b14041c1242d050078803810000c0c10302156110885016603030080e050541c00d01001e000c265481030060780c940c6408001310003940e00103010f4950030340203180720344074420341e40d0003129280140c600001d4824041d0f45250300841e220200a09821003080a1002890401104c4500b41400d1203a12015860a20030700303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 376458848 1250 376457598 376457617
    0xf1506020a0605011e15020709090f0204150f150201020712030e0d020606060a0c02030109050a051605010302070203030706020c102c030c0c1e090901060905071b020d060e03 76
    0x40c400721015041540c11241e050b80480103198541c0296509003008480ca48299210544102401403003208201e1803c030b282d402410342180361407204014031607000006082d00e8400c40c2c0c18002d00d015000b000e1000b0301184100c014038a030001c81403003454491003982e600314400313100040c102181c503241c2041814120b120040800d6076520345001240c8280400c50b10040140020036050920ba40440c4240c802d50350640d04020919841004554082d04890440c0303070808110350380311540d07042164460b0b80d1203079000001c4414000000e10342d402030003980e01c4103030010301031401d000c41c0d522030340c02039408141c240c01d04d40a044030048903100c4c1c6206905001c80c0c0520044d28080d184042901c180c01070028214266000340b00412241e0030004280c2009030080d0307a02c1c410600c00ca10f2007514503a021055030b5000da0310b00304100402c04154408011911100e0041c0055101e240081d00c4009202e103c0141350f200090308003000d40ac0c0a80200981c5115480000300310000b001c2e46410364010b500c81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 376460098 1250 376458848 376458853
    0xb210a080d0501140a03050d05030a1b080906090a020a15110a080d0501060327021507060f0b1012020307020c042d022a0c04050f0f010801050f0a0f150602 68
    0x1440b0700ca040302c4080c1c4d181074042c1d40c040d40c80b0341076480b11503480c9080c0400004009000001403104c440c0c81c2c200f140460b480008035480c580c030340c0340060b1131580c08642840c180e110700800200c03c8540026a40402c58010303020b8042e8904248044018200d4038004070b052100040302103a070100100484a03038540038406007619085064202026210180e11000400d810880c107900300c1c407000000754907403619881c03103001d41c0d104038404a01c080b43c224040c1d183c1000c011900710203201031904030705000011500b041010041c03400802011044540d00440041e010010142c41c0c00d40a41c002e540005041c012180c00c45a484000340540e40340141103d03000d20030050007491002e00384207811030000b40c070302c1c250f08040420b03070580b2951440300c01c0c018000200b184007000c154810700c6214004ca0000c2d109101601c0d00304a100405141641c040d00044600c6000040c03120042c41041e0268030000d04144180d168580c0000c09051506081e40900c2c3c1c1d188034002140b00f80260354401400103401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 376461348 1250 376460098 376460101
    0x9070e130b010f0513091a070309060506040203041a070221070b0a06080c04022101031101080c03091b0613180e1605061605010e03040311040b210a080d05 68
    0x74903a000207810f074001800c0032240c040611607507485455800141092201c00540201103081c411000002d1146440c81109036509015071698981c000a040c14094141400141c560b001031004a1208882c042c0c03ca02c0035080500c0c408022030525500a02580704440f0700e1400d001c01034130ba2200b0000059252280011900c00304030450a00c15401f84200e082000300c0b40c80e0441d041e840d42030081d00980f0840d400502d007441c455041c55003070105203184214100940e180d02c0d040c10036802c3c41c40071902046085001400510342031040301c2c42545c12102402c44403900000d501901c496072400700e94025004c1c40075100c031040040f5418014640c079000c506440300b210710318000304d80400b003c2800c83e800c03020b500314004c242d816001003100c1c1b080c1ea0442c3c0e2900040c0114003079503484100200f01d5400c0c010002c00d0742074000060300640f40900080402103041001300001c58490401580c2c00c01440c000c130070100481c0440660341e81c0039082c15265200900c0c2c0e5044081c1c0e200c400002c5105a84a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 376462598 1250 376461348 376461353
    0x18060c07081c0f0f03022101080f070e0c07060c030204120318060512150d08160303050a05130b06030c03160e010b0a12050a061802180a0b0d0509070e13 67
    0x160034020342e8030342000345401d0030280c0c0007404002104280310034140c00103442c900052101d10552414030110703c1c10300003540c40c3c40c034180c2c444a004010f14601d10600300081410148441900c0c0103090781e420841c82c105042d52160301601d8050f504106055003440000350f100d072407100c5119518407a645140d48215141e07000320702c1e1140b61b080301d03041101c1401241400702582c0708094004100c2104496030191080001c1d190f0903450000801c80100803401402c0411790801c00c07868180b19880a004036640d403c80601107035421200040018109803035000460285850b8541145015003520152180c20020034680480f410610882c2700a00c4020441100c07455191405007540c04086880e200c14054010000c01080b5800300c0920b5072a008949804510390000b801047c410041d80407404c561002100250040300340350600080702d00c005403085ca040c2c14040142c07030030070003014140462601d941d0000c04008200b40102c0c0b2a654010030341007040c2c02411700c11000011448090506031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 376463848 1250 376462598 376462633
    0xb0301150608061e0f1315080f070504090c15030b04051603060b090a030b100302090403030f0b18150a050901080a0314070b16050d0c0207050102070e01050618060c0708 74
    0x40d1103100c446003070707243c800089645900800c012005d04458803020042c1c254451030051880703a1880440e400d9900e40020b2405c40400c0d0072403213202c805e06564400342d81d442804207031110030070000e1070f02c541e000c010700c001180b6403a4408215418a40055000d8000d0b01040840f441502c2c0c6800c1c60004000303d5001075032502510020780030620076141480501e40206040c00d03020301008017542c1a600006049401d0b04040100464004001e0781050510b070401800038914450074800a904000240d805c2d410b10302502207c18904490031340701c0b551807026a400190609400c0c42d40f1445594000609694813a401070203000103c6c0a006044840d2a001c0d03d6010095080e0b4605003080c400d5001095041710502e034401201003610402c080441d504030390b03510441b111800d0480c035003020345207501e41c0003803120103585c1e080e02280e80e510748442c8980c8001d002403141c268014030800401d21451101090004008000303840241451021010f0f07500b401c44030381141616505c54000700301c180c0e054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 376465098 1250 376463848 376463869
    0x312041b08010207081207020319080f071806110f010f1a0901030f020907030f020c01060303020f150606090f100c020112061203080603100e0c0a15050d0b030115060806 74
    0x480300210b02c1c00e4402d0385d0f6092507000303035025510500d00c07a0001500c500d00a0007105c84201d000c140f0f010b00c3e00d10060300130302504002e4842400d041c003210b0000c0c2c4554001d0f03139079442c1c0485001202505601c1d00304e080300da40c490400000690b01480007a59101c0d4024060201c1514180390b021560003802c00070f1026071050b080803984500c5110004001040001038050003d1760140da1208155641c8001580074110443c2ca401100f440007070b0403200d0300d0044d0700c000140c034402d41c295000c180c0d000d00d105039a5180072454100010f000d802080a034035002d40100340121000d090040d10302551f07800601c480c60060302d01000701e01c001c02000308640c5c0c045e40002e4443c0300341d0410414a404e110344108518a03440340281401821000f0880541d4200142400b01042840500008a0f0b2a41c5262100c41c1c0a11041c0540c19030100443e010303440b440510712040482d9165811700c43c0030b04092000e04080b4021a8065594044445440003042114000b800c0c55854401040c1415028005034150 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 376466348 1250 376465098 376465109
    0x100306080a0506160f0f030b0f18180303072705060f0a020d0309080904200f0904180203060601050d110a030b10020111030c0c01060f0602061008060c0d09050312041b 73
    0xc044017882c0401d40c01c0014064800103500c0c000a10600104c08918080b00380140d0302d5202003c118620650350354410001d102d105885084050b140c42114919a2800180d5603030780031866221046007040c4c11011450540e0f481c5c10700540d116940c4201080c1b06511010000740c0700350b00000c00c011015010080000c81081d10314041000d16165101e03c0924000c400b4400c0c451519850001500116031403080c940c10119120540d41c1c000c0311280e54103560100315031303e0103541025814902a241d100071005031070f40240141100c2ea45180044445a2042224050040c1e0301c2c1281400058100301a0109e401c035074500290703050b140300070468400e981450b11804c6a05110407100b218501000b502c1e0000d100c1c0c8455600d90000132480342c0374260542080c071841c0c0d40540c001418036400554079000385000c5405e240d016844080150300d5140844001035055420040450070340c54590144002c140501c0969041640320050403410300010340b410f8540ea04209160300503e60703503050a000411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 376467598 1250 376466348 376466357
    0x6050a0b071a0a0e01060f081509030f0c10020a1706041b050c010b03061512030705060103030516060915060801140103060f0e06010f151d100306080a050616 69
    0x141c0300e507103a6000c1d81d400d40e041016095010042a0b050740c0c2034001ca40e0f041d0580000740412038032000c0103100c021051040c07503428480c4210008000364601400c034056041240614586110b800800c1591750101c2c0301c0702d0b0107108282d17542540c0d003032030301c0a0050b036178466886010f0264076012158055001420a07480b95242c4141040c1c24071000d0b0142c0c0600c0041d042080c3c0b01e5591620b0540108000d010741501030049a080000302c025001880403411000c41d0f0182d50059001010f0f0791f42e00a100d0f0090460317101200500101c3d00907406454500600b515100864015a48000075640e1020086464250401d40320300907503414040e0300c0250150400030410001e06082d404a500010712000d031050356140d680c0a00c880d00798000b0101c0304150303012540c2a59684802144030540c1c1e221380908800449409055107101c0c640110746600b0000b02c1082d501c101d04200118024450350314000d045e036590300014428800c0c0f180c50915805500a45401c0c40c0042404095400040400e405c21 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 376468848 1250 376467598 376467607
    0xf23122508160806010203041508011a04050612040204060b0f0d050c1303140f030f03011a090f0103020309010902040e03090a0e090703030f11070b0406110a0c0504020708040306090606050a0b 84
    0x5001c6a00d031440385180701d02d84020f641e03c1d900010703411817040d50052580082d01d9000c032551035401215840c1280c065420b40c14400c040741c01422801c2c02140500380d03214400300300c20b1020394550b10a041d00240001e10000d005030f581c00712101d03543d004211000140c1800714240e20100c0036071258643c4030181004081ca02601803221000240c0c480c04000c2c0b0614180b000d03a40042000c000c018088411442202e40c0c0e441203182200d80c0743c01c00d10441805000180c400000081c011040d07681944016140742d0601108500550184d0001000200303259607844004015a6490044c0c0c11040c2000c0702856503100d01c04103002e041221500029201d03010303c03050100c542000112002100d4161416180603090903a0884800324925814182403091100c04550a2513000c002c004450403916110752846440c00c4080d100e40c0307214000740ca8030010050170001030406800a010380c601c90b14007140b81a80365502c03202242c14000081d60140c0ea039900030302646c02c0000c0c03040c01030680901010b041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 376470098 1250 376468848 376468861
    0xd020f1b1504080d0207050a05010507200d0219031107090213140d080705070e01080607031d0601030321050a02030f01060206160302090a0302090a14070f23122508 72
    0x4c3c4120b52401c240c056000442e0028030030300b07008030390791154440b000344403e09003040018a0001e1000811300b0158016000001c0e910380000d01c40481300d5140c001e4082029140149402d24504260039810300c5021302841200c0c810500445024105407200140ca039035540d0002100d078401c0c1d812105000d00205003400c1c09980301d41c0d14845040d4010880341e5180224608941801402d500c95000342c18080004612002c000c1b501e54401d41495808000782caa043e00541e0340d400c0e1103400020142c0000d001440802d1050048011141000c03104c01404118080c04100b2100111181c2d00c025501000344490104403508090040040380b0013080942440d0380c101c404080143c0c1c01405041e8005031440040e1900d90340b010056800818003a440e143c181c403103102804202060241c3c91402c800000e03074442c01001e00254082140e1f41e0500041d1506080d00107503a90103a84e1551050280b00c0d81803d003000185032441b4a00300f620a40e4080f05100006405d03ca14100e460248505441007010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 376471348 1250 376470098 376470113
    0xe010f060303050d15050d030905031209090415200304150e1b04060302090108010203090d081623130602010e0a030e1c02090c120c1e0d020f1b1504 65
    0x50311100e0500181030000c0e0414880c0c05c81c01130380708540160824011109054000b1181c0c012500203409540c003440da092040c0c140b40c42502c0300c0d290303c80b0f8248082004101464008401a41c0b407250002e084618511201204040340a08001c0120000100300420075440c00e240410260302c0310074442d100e801c0c0b4180d0344610029002c0e142820b08200800781d40d50340c1d42c10850041d80c014060910550f1516030180c041d60003140c000495109840320703010128482c20101c1e1280e854849090741c2c02107107060440d400f142c0020745012000c175400f0704c0c609801d0041300030404282c0f4100103801092800d00b0280c2035424525044105810144030304021a0700250004080041182d5140d16550b410900c019120611003002e07400c00100c00410448035070b0300303006041c40109041d1b004415034030750100e0b003c1c0f84120003200b0321103815803088a03900200540948407500b01024094104860140e8100c0150054044028403418040300e4005800051021152000140390400040d107800e455414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 376472598 1250 376471348 376471357
    0x1809151f0221070f0303091a0702030405041109090f040c0603021303290703150b0c0c04020c19050a0c05030303060a0512070f030b060f06180d0201210e010f06030305 73
    0x1504820b0200d981502c200c50404072800303142d104468400100035400c005000380305002046808a0729001c400c11501c0c0701c6841d03548500590340c001c6243c1800d1600703010142104894a522212060001540d41d40d641c0466512414070102c0b120070a280034140b124041c2c42c0c0390b00260a0500c100300985421180d00101c00540b50000310086a8a0100c4500000c0703989803940780403248a007800f4000a0755043d004800100c040f60058090591900344d0a0f520384601c21010040d5444224000c01d1401c050300034180e0f000800c0207541d0003490b921100b00040b4012a4101c401d6045004008100464104440c014010980043d400e42c940100800d06402d800c0c011940703e00d20b4100100003800041181801505200b19405c2d4115034a180403220340303a05407002d03071055a5000c900022401d202060700d09060b2a1030040a081c0d41c0e2034184030800c000782d01c0030b0f4100441c418842d1401c04006d041c2002400300400d000907882020280603086950554107080b207d411300d00c0400100c0d134071800b40c0317 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 376473848 1250 376472598 376472623
    0x2040c090609031e0618060606090e01120c051503040201120e150411060d0603020f010c0b040f150e06090105090f0d0825080906011202060f1809151f02 67
    0x104c00c464079510070030420f401d01100a180e00c0c01e0524401c07201c00613062008002d4480c0c0700c18002d59441d00340c20707075030300c4070a010719003269542000400000144242c072030003103401080e5121000f40c4503800702d140205142d504039001718000007403004550780681861400410f00700c04005560f4a445c1c1661134035001d9001c01000320007180070500344850008002c1c402e8000a000913692182081d020003d4003540c4005d170320070103041d000c49109501650010b0103036644a0300104481d501c80ea554602d00000490075503640c4c3c00004000d01000e41341c0310711500740080c8001131001d0300d000380900342034900003000b040c241e400c92580302d00ea480700000c8421128525041c450103968803c0d580c1181d880e0f89000d504109401c0e024050038440e0040d01d1140036070040c60075541142e0302d803503040c001100031030f1000b5000b040c10400600c00151001c0500b098040708004070001c00301301c0d00041e0074204180d130556400301410400205a140054811420b0907801603040307001c03040194080d40720f03005481135 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 376475098 1250 376473848 376473863
    0xa0303050306121006122603010302010c1106070309030b10060807030e1f020304050f0f07050609041d03130e04020d060908040b070b07080c0c06061905030a0f02040c09060903 77
    0x100845600f040c06080040d1080c19010081c0d90340d1283c00c076102904428044d206040070f40300690503541a00240342c60400701c408001d01e585d285500460300c0e851126010390b0903044030344a01311503a0703031800200388041c001e654104141d4150300b410303a140c4030040d22620541086080030081283c004e41c0440d4460500d090010b04104004100c50030802c6089615481d040c88801d000d1900e403c65001c1c1d40078600800031680d1120b00c20802580c0c0e0310300c0c81030501c502d5000d04410440c628041c8004c0080000c06440440d001200d5038003001904c8450540071525000400c0300c40341070f031408090000420200d9900c16440c28650082031358040784c40e00140406840e002c00e081031110034000c030350080450300000d0b5511159402c1c140117900080e030301d0300c000075182004034030801521402e41e05001c060801604207526003d0030042d100c650308101d614640c0c0c6001000495035404c1c00b042c210a80103d100b0350442040e441000200c031500580c5209001c0400c4041c4501540b22076228144c9601404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 376476348 1250 376475098 376475119
    0x10e0301060905131a010602101d030a170c09130903050403081305040b01210506040605030102040605190516062a0f0905030d121104080106060903110a0303050306 72
    0x46405401e041d084400380310300b010280804101c2c03a00d03048601c0c80c0900001c04600c1d011080100740403000307208940041e03126600716044007806901400349100c10300c00508144030942c16490450300a40189008a0807c40080c1800c624961034186c0c06070101842624000c07907000000c80401d030000310500219924110401014000c400301c0e0091500504440e4460180140421400841340900b500803400c2490018140d4043c0c1881d222840500c070711504034811000015000307040080c4410740c400d40b00c2200151940b028801000a06210f544e01c81d03886100c0c03441c04542010300c80103281002820081070600c84400c00c0305000c40c13980700c100462010f07540d40c1814658646840f2108034038003849070000c7c14a0304010681102041d070340322200c44580c0d500c02c2649070070749a60084041001800e0381c503030443e0503074404494555081401130506407a40c4045007107503882c0c1c00c08000b00f11040707024028404d6a10009010a00c100d4110240ca4115035004260340400781403103009907001c45 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 376477598 1250 376476348 376476377
    0x10305071107060c0c0e010e041401051e070c020a18140106020c09130605010e0402090604110313020117010e0f15010906050a031d1c0c020a05010809030c061603060b160201 76
    0x30090061194081b110401c3d40c4075010125000c0303055504441c040c2500001460501c018040c542c400c11101048040a00c2c14664010404030002d258030104411035002c08010303074846040348003074000002c60580400e480b031892401c59a198507845804600c0c0001040007a900085840c2d24403000c3e2070035025a2100703007403003081014420000303201505200020902c1c5ca150303510b19100310b00894010038a034481c50180011290403004108481c0c404000041c0c048135203480340030b207551040c0b401003100350302c0b5410107260720400c0e08070303407440c030b00840078130000d4007004d01d52540240f00030b0b1011045411102c000391080c14144036030001e002c40030900c100d5040c0203034454080794401e9502110074001111000383c86070310f440144001055081c03030100d8074900c030300303564500c0070784c0602124042801c090041d140008014500c040c40e1008001460249109100142c0a80000040601400c01c07038000502a10042d030481082d60b2000e200150050800c030140200c565028240700d0320000350074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 376478848 1250 376477598 376477613
    0x9071a040b0f0c011b080a090f0219051e03210301330c0c0b13030213110a02010510050405090d030f0213080c041b020601061b0c030b06010305071107060c 68
    0x1000020035441e1a9180e489070483c02c09417203801c041a80ca00500396038040d201c80448008001c0a0b003069200d41c002801400c20039035034004401403800c0a001c1d00c1d5a840040d4442d0107a8036240051910103110b10110306040000400f030140c03050411500d0403400718050180c0c00144259040306003031030b030304209801d0a5941114086c0014080201c80001c1140144c1400f070340f03040880300342c001d41800003201a03801d030035034400c021200f002e0050f051650302045200c84a00034007481d0661f4078410490446050002084403d05640000c0f941d4600719140d200d9122080e071007980110304020070880d600388085003244074000c1908001501c8400c940d2480001e0040d403540e22440b248a001c017098410001450345c3d02001c00300c03403d101c00160300540071441c0c101071048034003507400640140101c90141164000d40144180381c91909065a00e4003e040788030f03540181e03011104e403424050603507410700500c4d61100c2d050074414030642401c0b10303003aa10000ca1044100f0000c508c2079250800a40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 376480098 1250 376478848 376478857
    0x5040209101b080c06090601050603061008060a09061d01062d020a0203030a0207090608010e0a080f070f060209040b01030506011b0812090c120c0906150d06090509071a040b0f 77
    0x2c00441d803580c240820860792642e051b00c101c0341622130500000b0b41031a00c3c0040b00e200744400340a000c041901507038140c031760780005080c003507004121200c0490815042c4c49020002c1190604000c9070301c1c544460348101c003006821410030441d00c01150114041590210440c60030409621101c0c40c000c08070407818000e008100a616000001d0b88181883d80010908140c2e42990f00812510769074a10013802c0b10810101450305810842e080d0740810049409000e40091380050380346420210340e10008008541d1004881055004c540c1c0d002c2030600d84a8644408800c0c20100050704021001a000d290002000c01204011400500030002c901060b030b00d403400045210030542c00c5c42c0528036120121029528011250401096000b80340050b9605071205d02070441d4401e03488980a00c01640c4c501400c0b61000c0c01c003004641069885c510030400108815040091603042c0000c5960600c500c6030b00840b00c4141d082084c456a0001c0d0007103d04136680300c800c043c1d80344101584800b0b907005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 376481348 1250 376480098 376480103
    0x112080a200309181b0a02100c020d080a050906040b0601030f0203090c030c010804030509060a030207020303070c0e0c0406021b1c12140a1b0516090608010605040209101b 75
    0x40380340407500006400030142c0038101048403030500c41c103400c03282400c01a6040b9807003a4000d0300010354003a03041300040103000c0301d46284180c4d001d039030720851070038150359161020000607400040ca0000c2251706c030350902d0f000700c540b01081c007103030601061983e039580313015001800a43e84100410550f03030081d07209400c0080001c00035900c900d0310107003180e141c094001c05e0303078020300070f07280c80305e440d503219004061049500d500e519003000041c0d0103101207504011844801c1c9582044040d0260b6000c1010380b40d850300c40c20f400084241029901080000043c01003441c0c403805110a214554010513018242a0a801c01010140510000540395403203009000e42d0b010342804111f0600c07260604201c00f1010039196010120b001600c0d286840c0f194468900001d01104c0482c11041020151f01d03059a000384102d900400e00320492680c0d007200c40d8004083c4607030324241080580e500380100f40050104440440c00c100e50000811803000c510303c103440400040707103030f0f000343c4200462240403480d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 376482598 1250 376481348 376481387
    0x11a014406040b03030702060d0e0a20030c0402040b0d1e0507080717040f0321050106090303110703020f091308040311180405100c0203040e0c040e07080112080a 71
    0x44404002000d14101654039a0059040103100216401d000085860003a8081e190524042a410392100240810800711500c1e00401008402160310f0740903000802502014000200003850b0800d8900803600c2c8500d40684c1c0140420440b0245410546070396007084c14011480c2070a64a50060700ca00c514141d0030303850310300350910203150760043c0c9680c42041503468240c400a243c1408aa40743c9044600400e004a00d254490001c2d1081c0c04030124441c8501e0380c810106001d002402c2a14004d1308400d002600d03038402003092552050003591910521000381c040a81580c01041d4901000080b03103000c0c10380740c004260448800c4c011529240d411143c502d44070750320b0345084001e40c621003040034800e0701d03040d9500d00c09103000300109014642c0f1000411640403580e40c0c0700040e05105040d001507002c02e11002a8000b240b040c503510032825003103850340d9039040400d644403020020706071034100000c40c8014003811b64010411400f05070422495501e650080c002243d0751202e00d5442040d06 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 376483848 1250 376482598 376482707
    0x6050a0c1a070909020702220219020c0a060302040e070809070305060a0204030308060f09011a0403050703050604030305090616030207020a0b07060615020a080f0702010e0a030506010602011a01 85
    0x35480d1005103008182583c0d0f103e41d199078800c0120180d010724803010754000c0c03400a02e441e008650381451240540c200101500300981e80c80c2da20080c1c0b240841500c090703085141d00d050340d0303d001400c64002c1d2100d030804500b01410542144150740e8010020424000c181e0040351040100700101c03c002c540c002c0031101285000f08004010350011720040300421510400b0070054074000b00303401c1c080400a49945401c0e0703c2d01400c140700310310181d0390490304403040101201007071041c05010084c5015100400303860409140040440c0d00c0104a00c4880c0c01030001d20450400807100350504049914025803104154000070300c080c5080c2e0b020703533101b41c0001031120810005400140803900407001c40318526180e98402d07030315440c1d0200002c2041008005c0901e10000070805443d08900603d4909407000505000c1b511140a0790811b440c036a01103001007091540c24044c0d0a8070b401160103c2503040d00c03240020f410f00c0c0000c0d02c021a10a0f030b0000e110582c01d50603461041130130345480d20580c0d0307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 376485098 1250 376483848 376483883
    0x90f020f180907050405010b04081504060f0e01050612010b0a1401090e07020a1103011a090406020409090311010c0207050f090403360e0f13050c090a050105010806090105060406050a0c 81
    0x3d03071a1a10506014034180350000410321031140a4908440040f4058109280318840f84461410024022540c980d0b0b00d00301642c204140d482140760060120000080c1ea04221041142c840030307502c1c03c3c00d1144c3c1094280c01d91502c40024000071207034404d401844001a45c1c006965490343c40d004190300d10394a000300004c00d94000790075806507006004132091000c1c0311042c54280d0340b003101e500700300750303001600b180f51030902002096005001d610010300b8661561050020780d000c8410640000f03840100c44140c4038802e00c18003401101c58001041070a103040c020440195114903c284074240400c0000c0500d80148e0000003040b2030302a52440340510030740ca2003004440300c1245100301c040d104001c141c1110358500280a480d5800c4006d40035962480150b180015000c1300329042d010b503008004c100d440d040213050143c12000d40103d03a070742c1010001040c000703004007914421086c40004003c540c45003021602a95803510340983d98a1301d680e0309494184e1300410041c08250881c44070f41c103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 376486348 1250 376485098 376485103
    0x70e030a03030912080403081512010204030b041a01050a030609080706060f08101817070501060f0312030902010f1b080403060218120c01081315150504090f020f1809 73
    0x1070f4144101401e0682c900c900ca811a02000120741c001c0c04078500101103000c040041c1030202c03440b00c00034003a40c4000400c400319426030700681e00442c1d5010044c0d050104100710801968041c404515041e071441d03141ca80040e00002c07030b42c400034200d96a02d007280300500c040d580482d041030350040e0041c044130ba41d0b028038455240103071143d44d034580100c00c2e6003900070701e05001d82a05412003402c4a440c607111354440c1c0315502c1d8840d250b80c900800400051000030400c1c0641401401a400b04230305181c0b0718246109900c0d81540c245040601d081035110041c0e800000002e0459010310f850405501b000c41070fa6960303509440c0181070460080390020402940e41c0041642288105451491000481c10300003c4142510304140940240000e0251940308a036040d9009048218482100380c10b0f80b1580e1169625018030041036488100001480481c4c9180c43c0042c85c05603010400100b0b240c80300002d491b2003c20091241107a240c010302d180d82c1d003c003c1440e6031074400005020782048680607a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 376487598 1250 376486348 376486361
    0x303041707062918060f0a0f15030c09051c0503090d050303040606090b03030d091a07021e0d12050a0b062101060c020d080c01061a070c050406080c0603070e030a0303 73
    0x10048400c0d2844103d034200020014080702003c84903541640b505010400300311007605900340c200360010400698034004c5443d10740100404050441110001c210060985100003001c0c4207016482e2420005622904c045810803407819440f4002e50b086882c1c850305602c00c40200c40d5000701d0407450714003071000100086018038410103042144940d15074440c000e4800c5412032950641003480480a0f06c2c0d0306402014620340b081d510b1800b0b1203d501c00100241c00300743d80f00001640a0350741607003030280004c502c0740480c58100003041c0f05110003034000c00754040c441d03d00c8100c948900110703210b5003142c4c01a94002100030621520303886030310014803482e85401c113441c0429407460b00008026004080c0c03002c0722a000b030052640102c80b40c841c050650f01c00b161402d510340d80c440000400d5000700700c007010b5000d03100350196075804242c240044000080d800052003145071840400488000182c0046400350589102c3d13143d9440a00c02c0e5024010181500d1b0140140d1000c00105a410760061 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 376488848 1250 376487598 376487651
    0x405010f140d1d01051e13020307032a0e0c0f070b0c21040209070c0f0b0108010203091002160609031b0c030218070e040e03040306060e27030304170706 67
    0x10f89140f40c0e140041c00d94006403280902c000c45600e20b00c85d010524200c440c0c2c071002d440105010800184c1c0031920300001a401070b501040d0010118217480c0700340c9a0b424414144410054400b030074070300c02c40c503030703403005000350000740c10002d030a1780340c10484019a6451a005850405140b620654050280d0310000c030310745401129554250100d040c10707449600070b036006042d1101c030780c0e9824002d44601001c004162030100b08040d000d40015040140140038142d080009a1a03060440310149040d0115074403025140c0144260301084428000c0c0b03855207034014202199082c241e00b0103681018036414042d01c41c01c00c2003454414001000115402c0380c0c42514103600c412a2480c1150050b2800e90b80e4000007004924100d001c2d2a1a800c0350f50300071800001c2c2c030b1a09641c2c0e1b44450032035486510240d02032881500b0848030140b06001c0008480444541c40c07103141404a80940b03e03c0000c00003012100b40801c0c407100a400f41023500d110ba40d01a10411440c0e0882855424042105101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 376490098 1250 376488848 376488881
    0x1e130f090b010f020f030a0e041803020d110f150c0c0a080a08100b070f0512070b06030120041707031e060f06080a03030902040f09140f010c050405010f140d 69
    0x52003c1c1d82c030001d043c9412004050145042814000e011148001d2040c0c020740d0203521000a4810780312280e40740480315200b03400600b21680382110140070040c003203504180c1a001200c40b41c200240200e04a4aa90b07000d28043e02076a0700d820b14488140200c400d408a6846a422848200242003009000c94015600d401100d581c9005880c9036980843c0240406280240902e07030008070000d5003800080d2140096900182d08500301c00140c1c3c1103001e0940700c0844040501c45641020b204590850700700440100b880750101d140c0e002244102d1007103080481c080c41070f00d100d0080910144e40555805101907940c4030b00311003030000c112086401980c9007031801c15810b400d03041c6482150300b2a00c0d5100a003c844209403810b8008003554882a038016480d44268003040c189481030300c80007441525800c1c192640000d14515000101d2038140080e850003084151907a00201520100c3e0000d180c00302304c0140c8010708984405d252403200c09080c0b00803500b82d204480c103030006680c0384104c268 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 376491348 1250 376490098 376490117
    0x91a0c010c171b07030e0a09020313060b0301050601141308100501090515130f060506030a05092503120e030106180b0117010e0709031a061002031e130f090b01 70
    0x80440082d10800c1108060740c20400b00300028018030725050786c0e003001401c1ca4000f42c0d5400c122001d9a104450b1214482001150102004043d04c6403001002c000c2e0000c1120703107442c600291400025690b884001031021550a245140205490010300707041c1054900b1000c00a4029020f00020701039100d50750305140c0065032548240055060000004144407048a8000040001068810030a0314000c1d00c1d40d50104158640400840c0071312400c107400540c80c40d0500100e8184180c25582d10a1a0701d03104036544100341041901060300d8011030b603c0f000c00e0340400161103890390160465059402e08400049034045001c50940302a0401010301090640c6001101c19400a1481c00780800408006001e4420003c080c1d5a000e009420444906a140d4586100c1402406204800c1c421104100071341c40c00c00ca9442c1c02e00541c113000450070b000780d51310455407610b0442040003a40c2c3d40480e904100401e42c1ea030350001001528607003841e8a480310084e1004d002181c3c0607601042c000c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 376492598 1250 376491348 376491361
    0x2120f0a0b0907050310260607230310030506040f0c1a120702010603050f0c040c1d012102121008030403170d0f021812010507091a0c010c17 62
    0x140401c8100080121420360b81d140002d94194101605101ca0910100d00108440740c0d070700156980e0324140390300c206100c0e04486003c0c1c54018014210700800103040c88040d00c0c01c009084020500030080444d640303030303510446000c2c844011984007610f2480380c0002c0c0001c0c04088100107810300d024a80a101650f114102e00b100541d400707072141d4400d202045204e16142e407846030709810400c0b0744004510241c0c1c0c1d0b20b44030700d0000440240b088580002c8229800e52400303104900180b4400d0a120340d003009400b12103682c407004c00c1e0700c0368188601590071903507184420f0f620790b610303400f003441c00c5403200410f400348150950100c901e200f41c4418188007103001d081c0001641e048a030b011140000100031501e00c180f8a400220302003907001c1c0c4650403814441114000390030b000c5042d00d101c0a10003004420812529551828141c1d04e9140c003007070184030355028240c42c0c10303114002005507840c82c6103c40c1c2c036038520415001c0b4859510386031410081a5000090840801c070743c81c0c46541c240c9501c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 376493848 1250 376492598 376492601
    0x5280b01060e0607031101090f0b10080d0e010302031b0f090406050603092e05011401020c041b0e0a09020406030605030f01051e06030f06100503010f1506081902120f0a 74
    0xc0000e9000300f00b030164100003440740c0399040030713000d0300b40010030031403801e40ea032020303d21540300e040f194641070204004081ca0300c2c006110040c114500107002000d0000400741c1042030708074045040540000001d0100341703100c401c5404800e40601560740d03884108000354025005141014400c0d410101d000a01d46000f82c1030707134010f24400380a011040e12280180100040c0203942aa08440c1401c4105240002d8801c142c0206107091102d22500c454030002400c0007840b84016101e00c0c540810000e0825010f04490b040304001c1c00c0050342c60340e608000a28401d450340c03100c0c503001d00015001c1585545230b00404122107041e8200c3e821172811811503401c0c2d502c125042c0c503141c02c491401070050303040c0b103100580081024082d10320140da940c08460401e201111a00c4a811214804014030300703091041840b144030700001080782c100000d001c407007520581c4c440d0300100200040400e80b403c81203055101640c03c07091046642c0c0603c9014521280d40441e5240080354000c4002520614030303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 376495098 1250 376493848 376493867
    0x604110f0604050a05190e0c07060e0a0312150b0c010906060b0c0c1e030303270d0e0d06020427050f060f12031608070210020c01080103060905280b0106 67
    0x4080f4135099040c00c003804a180700004c68140c0514450b8800200b074203010340306501840c0100800d44d80c500117401d052098036015080103116510805c14080400d074003032030b100300140203441c010902c0d03980200e22a2240701c0c00d8200284c111000144000d01e10303415400308104070320039074041c010b103a500d8600080b14014810385481540100b075400d4404e11f04000a610140d10f104400000440560007103891600120f0b10301070044249a02c42c046034860080d84000034511400425807a00e102c000241100c08220b0000e000340a2031003604204241501a10040e01c02d40c20441d4042c681c03c2d078051065140000c070100050b00e0000400d100340f60483e072191103501c0151603108207488d80000e00c03561390b001003180d8129020500c00300514030104149000114081e140d40380c0c80d50b015004001c600403482c00131400395844045030707060030707604414824116600507500283c800030314201541800c55609101c2244190314a500700c00b0750700340c0503560f182d90284c45205003903030721703407000390b900021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 376496348 1250 376495098 376495109
    0x1030c06180b07052a030a03030e210a1e0c120c0606080304030506060909060c030405100f2c0601050f0406080102040e04032723030604110f0604 64
    0x41040c04514065104204482480c0114001c503903030358901c8107125000044229103075084000300c0002070075190b490300540c1c641503d24030850301c032000000c0d9480400a0380142455220b094408002d8814881d50f0040858240800d80c107034403000081d506540445503440c04a03074a8421145041540914aa000002900e4802d800702403500c03900356292995045201f000011188100055080c0c020603000340181d80c01140c40307a003980f03885800e01200402c0d081c02a06018100030b041c00b0700141580c1c00404d1880115038a0b2554144181003407010701d0300ba13689609140f0440c0c1004c3e216401411190f10441404d081040d0300c5450164031042e082c2c2e01a413a912002c010700007031034080710702c0d00701007001840000da441d40e90b06001e0030fa030496440484100c3d0480100301c10b041e049403100b00b0740f0083c0050800d5201030a40583c42c00030a0f03000b07550003144031014410f2410541d883d02100c80c8001012124540f03018940b40d01e003160043d08172801000b0800e00c044060914205035401d0b181d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 376497598 1250 376496348 376496363
    0xf06030607050c190302011e050f070f05190801140d0302120c01020d330806070507030e18011703160213090219081c0c03080621060109140103 63
    0x22070340141190075810143d500c007010b000c3c19400c1c0310f2102014090400161280c0c001050b00704a0300315240d04522070400c1c840c0004e0505003040b200325208c042180c0e211486003090221001492800c5520340207464540c3c5001e022848000b21454002da2558100c07500ca05500c03c5a2161005020328401c150100401517480303e4807110071101c0d00c1010742134414491000605060704203c80340c054441d0740c0c181c0c40104800440c185201000d044030741103204142160090940e180112260752540024109000c101d000700d00002054850b00c1c0360458440b0061051110445548002401200038800d500009400c0c460424098a0120a0b550402d2211071102064015a002d01a4a2014280003520745985a00c032100580d0740802e607001e03600384a0041c039646030074031014600d4290084c0003800e042c52030490440020ba440f460300c4131400c0e03040c07400b2450307505d8002c082901005162800c0c2c0c00248440728841602400103200e0f4101c4603000814842c03408061441540341200703000141009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 376498848 1250 376497598 376497601
    0xf08060d020f2107090905030a0305071404140102010c0306061d120105011203091a04030305090301090206031e22020d05030f0d091103062404020d020a03060e0f060306 74
    0x514051103040c003030500162807115030200450014662100d1020403e03458942c01d800d030310791108104014009400003d108005800003a1143c1e55640240c02c41103040513240c400094045126001410001d02d003000015200c41c2c940d024521880e106201050042d86883c48400c61a842030046600302c0c3c0498403082d8240040041c9401803820300700c50940c00043e05042c9203d42e0200340710310b60003058046980340e0150801c0c50001c5c104c2c2603650022911190a11a6004610381b250442d02142d034141051742e900d150560110703015017081503010b503002001004004414484008145030a18000110345080e6200d0460031641c14840c2c50801c0e006004401a1006080c100c5610842074080c02c00c5a0030a110340f809168103a0080c6041c0125035115031404040009c0c85034814210274007180940158a42594100c2c2d5020b10a1042541070441c0c10346040e0300c4c3c5070b6604030752040352000820341d940d0030f11410140c0682070350b114205041d01c1c0d80b800581c505a42000281c06050002c0c043c0006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 376500098 1250 376498848 376498861
    0x209061c0b180c09011710051005070b07050d1d03030109290934080919020114090301090807020319050307030305060a0806040302010c02120f090621130b01060f08 72
    0x3d9070081c040c2c150602c4420b441c1c0c0c125201200030f0042c4a0005a5529030880d801d02c4188402610703d0700b5088203000c02840072400180c450303052150b11140d240b4040c1e4845181002c440c01030041c403070b46400341c011511070741c507140038000c40114123990303560b60b00307001d850401d28580f0101d22a107036000710844805580c0340010315000101d00c2d0085180b040c100d010100e90452444a0440072400c04082d0004e03004004200e60030584040d40071045a01424041c182d580d441c0500310b2069030000c4c10001c1c0340100c5103d200c04002502c132100b8000d4003c01c05608645400c10003076002500a900c02d204030101248003410782554600d015030300002079801c0070240d40c0c064000e00b0000e000d1661082c0311460210b10140104400c0b03118901940c008221411048001303802c00607030020001400307a04025200a501442c0210b41d034160040d148036a882502c001074200390203241003150340c003004500a00120010b01ca00800810340110b1108445036038401c2d059441d24002c5110002003070040740003030321 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 376501348 1250 376500098 376500121
    0x8030f0a03090203060a020a1701051e06040f08060103020f0316031401141e1005010903080c12041203020c06120f1504020a03140906040807080c010209061c0b18 71
    0x51010351400d02003003500d0280c0c0060305062080390380802c003e6000c038410490640c04648111485403a0701071a1b800d50400700403403c0e03000d2100010580c0c01030b104080e1000d841d144100c6000348020702d0801170180d1155a400e8455000384030683c4a140c60030403d248030b14021401c2c111800e48018003e04039455680da582c0c0c0441558107240e0107542c2c8560510140c0080b6051030303c2420f294211a090f2034000c101151140c2c4050041180110603000c203008a9800c6220b510540741c008400d0740e115100d604c11540f407c403070a600002da60030080350000e805034000f18400c920307500c42c1d000d49072100424020b0110a004000b0700d07060313610345100414464a81180410741040c0c002080b8003012a046002c54241d0340b2401b00d500009036540303001080c01e000700a9a54221a502c0c02a0810381413688030851940035001c406082104001085200103c09504884140c01c0107400c81c1e850b4151000e4859000007190010640c0760304240132064640781483c0f18070f1070740c85000500c2485485820655a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 376502598 1250 376501348 376501357
    0x606170f06090a06030b0406020307111204050d0602040f0e19050c0901030c0c06050403051803010911090915090304140102030a1d0607060609091403070b0103020409031704061a0a08030f 82
    0x14503544e0720004404946841c040611941c041c00c00541d9904108034000c20221007888040403c2d0000b5000e00903200f94541100c04680d001c4a280704130741414200032000744035950188007443d20b00c2c1000a040030305038404c00c0c0300f00d083c03036081e01900c0e0038004803034141c58048400807850707041000000810741c080d41c0702141105e00d0f0f1900100c010011381e5600704440c0d040d0740c02e401040005c81ea04100c20090f01c2c400080d464290021300020076255900d2200d80603051020740309450300400a5070042c010480c500c501b1900d03654a40032800d00500c0a5203e0340b05003d4510070b1052418000f0035540000105c0b00c0c0059140d03107000c5240340c00141c24121198400340141d100034104603c00c003044660081c000a0001d0302c1000030b08801c14a48140c0c00d1449501c104c0031031b00f007400103101145010020740c1c1102c0c0c054501155502291604407000c43c1c42101801d0000c0042c024402032200c1e90780305941c10102055501c0700c00107500c040000844552050480d15441005908a42c451100c00f91 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 376503848 1250 376502598 376502611
    0xe0904030c0b07140a120b0a030b0c030c0705341206200a03060f12230a06050f0601021605030d1218051624050901110d02010606170f0609 61
    0x30f450200c0c44450f42003285e4015803400d400107101420070781c20100948680130f6102003c482c568400c0e407541d555200c003018010008040301ca40440040c05200c07444003201e00c92035000d41692404622a0001c000500400764150094020300400e00c4410b4410300c201c0d803c1d00e00701000500740b0542651124050f110383c43d42c2c0c1c400d40040c4020714042c4450b40015094202103070b1004a007060401c41c03031064a54056001c103036a603d000c0b001202203039045078400f00700800f4403c11207048a202c0010b40c542101c030680105828900010050b594020002a038003030f130001d900303a40740e0800440d030b004801800c5004d0603030305030800d0100042440c05000380c50203d103407020012800180e40038030f0001c44628401e060700e203a040385080360036800d0054610790107002d00c260400c09040c80400c68048074001d021002d014818005a1031580380e0081c50b1440301c150200048403e48076550304002e019220303034401c502c049500502d5151104011060543c440c0d5210946024180d03522070401502e0480901503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 376505098 1250 376503848 376503857
    0x201060e09030901230a11030915040509060111030d0b0a0f030f0b0903070503070209070e150a0f1e03051902030405210a020606010e01030e03190e0904030c0b07 71
    0x240d200500d88680d00c2603950348050750303d80d10321000141840315280400b0340320340001039200c20041d5495043d603000c05c80e01e1411844000340c1d88a40351440c425992907541c0140c0c4011141c203451101c1005000b42c030415500880d054903520015038000880c4c1410000a80082c40100360050300c0c0e03400115054401401c0d02c0c05181e590b50f241d490304030550000d58405002c034034588107000343d2084581c0c010080c4401589440b40325100c0315224010000024410a06480807640d403070704c81c00d03480b031044000034a03c001c030841400403031040c0d40c84000501c01161203c186a5002c44c0192403081040d4035820302010320482c401c0d02140104001410464103858440e150070764140644090b40c802ca1250000b44510240300e044000e10820800401181085c2001181d40d515808103003290017150a003400b00e0f03007808001c01600601450030190f03016120100310a503505d656602d26085004903920703005143e44c2d95000b0b0002020040300d014001c500250a00d100181c101c4130316550210003440c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 376506348 1250 376505098 376505111
    0xc0c060e040b130e011b0f08070908030a0f0f0c0305180409050a0f0c05151209120c060406050a051e070203130306050f0c191202040e100e010906060503040605070201 73
    0x80e402c04105000460050350f544403aa0402c138091003140e11022290003203600c0004c6060008000c2c0071954503031010801c414010400e080e0140c00710304040d11540b000daa4507005107103801040e00700000c0182000601da280a4108c0743e0184110690094059a802d490030012407019449007200302c0c8040c4d00b103a81c0b0111400411020b100010813640b0800c08080c4069007418901c0803142160840b500c603140d1140d0940c035100c1e10340111524441c054800607026504e0039030517402c003002d51340e856010b40f10000301403c05010100b072a0307110354410701c000c102c00e0301c8007814103048a0381183c03c0386041e00d240050444030b0140c03404540c0e00601510489203012001c04450071401c5080d4811242c542e16001031040300c0504804107503002d045c031000c1c0c80c1442e0440c2c1980c0c40a080070703c0000140400580512070f1440c440c0c0480700640030400010025003044400303000d4820b400d1180040d000c2c4c5110010441158900070b410032a8420b42e122815074071603448020052401070210002c0d51b40e102c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 376507598 1250 376506348 376506371
    0x70e01120609081306050408060105060405010834030204061404060203040614070c0f0e0f10050d020f090106090e0106020f0a06020f07050610080f060907060c0201020718020711010c0c060e04 84
    0x2d00110107484140e446e00e44491400c074101b46881030680004d84102da007840140180d9a1080c00b86070301040c01030b00b81181c0c00902d003890004005090020b40014110030401010980503002482203c1051f5143c1800b1211600850300714041d85c080c0da4011303003040104121280c460034919246c2204051720030300c4d024041e903d240815000e5071280d03420341c0c0111010411581404c10941c1e0085a0080d80c0d01d4a181110040c2e507826254022544178651042d145400d548482c02011031000340906280040e5131180005082d00c03046100d4510a0900d03500041201d61010407003071402d90300d580080c0814003a983d14a00070b50044540300001d540240310420100c0d404100076801804100250306049041c542d0203070074408000244829503000605000040c400000c00c1c6003141c50a180c9000110000d00c0100e0230994a84c1c405d409011a0000b11440010395a0040050b98800c0750195000306003400191500203000b2005044504241410082d0398000c4845d01d0304484000c0c0300040050000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 376508848 1250 376507598 376507627
    0x8220b070314041509033f020c0909010b04050c12040b0703271b0b070605040201031404061a01032c1c0c15090507151e05070302070e0112060908 64
    0x507440c0c900040d180c44010004d0098081402d80c12182c1d120481800c0c8010200d40d054102e64503150321fa00b004030300200550244207011a1181c0c0300020f100040b1420304892480c007034801c07603510038071542c074140c081101242003204680320171070550f02902c9140ea0f907860b503150704007000700b00380e00b859202d051032042c2e030344407400011228000b24201d0000280b0745c04c0440011a02040034451110141014400448000262160580d000f1004607265a0318070040300a000451300414100034000140020898940c01c560014400d40c0c10265200c010680110180d0708525030075500901510111508803c15404c0b8420720b0b28603200301c03a0400a281c0c45140c01c02144014000001c0404c60600200015122040030003013000a040c0b101001603190251101a54400c0e0078004c0f20b03403803103403691a000300680b0303034000e0b5441c121825091000070b0103800380d0f1215208400501441f40c0c0860f90310045444181a101c0d501c3e821a0100c1d507507034030381d4014503a00e407098403241c20510980300c801d04031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 376510098 1250 376508848 376508879
    0x7030b1603090c0e0417090307050d0501020f03011d0901050402010c031116080d030506030d0203030c0304110307030303051f0e160201421d130b0408220b07031404 72
    0x1da0800320405d103042c0c140b0150801041a500404e2201005504995030300042c00c40305440c003c883c0500c10a50915080d4028402e0162070703508031034040000a1440117170900d11001c0008a6079404032903441030031071401c03248121002030124414070280310200b88621500340d0064281e8084034424011740d54558131100380c0d940004056400f2080120100b507040c0140c1d90048029001484500460100a5240c0c003005192842280c00400028240401011303030703c1040f60080c050f0351902d9202e0800502500c0100c1d00c10581604001c42140c0215200074900704030707403001600c0d092640750b0304101e00614414403509000c541d2034002c0c0000318910f8bc04000c10007000841c540d15200307007003c200750800d030505d0091000d040040004001d00300103100034100f8680d04052804180d82e9505071070000080c91040038003401c2e41202007004002c40b0780c0007091405c0981c0022060050942d142d9485441c281c0501c5040d14007d201140003e40516010950380208071003507400c02d5152640c06584091 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 376511348 1250 376510098 376510109
    0x602030717060907030e03071a070314060a09020f0f04140f01080c0901050a0c050109050604020103180804050402030a060314070603051005010503060f01020f01091b050307030b1603090c 82
    0x140041031100080e04041100c0001c44a80100030303403440c060002404040d0000d180e41e040c1900d542ca480e6080744107200300d0380365680c440740b0702d024079449401e075694401d002c4071300301d0100340f4040000700038400805100d0b20404000380921801424071136000040e4021001c4607012003018072155060020001c051f0002e46602080c030040c1340100000c00894070030340c03420141400303130301018810702c0840c94044403032002d4207003407603503850300240402c41c0c1104090030701070455441e00240d4001c01402003081d07030056000b41c0e4240b245900103206e0715480000004028441d140401c404c0015042c035030050342e401002e0f2503002032820740d251100200d1071805c1148000c40e40058100b07000301074041c4a01078220380c04000c640411818500041e2492002070241886601c1d500e49044490384204500048540300b64020b100e100c4592400c140000000c1c003400032036440c8802d0220b014180001d1501c1100e410031400105a118103e40344010404484403100305070b128264100418104280d6000500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 376512598 1250 376511348 376511351
    0x1020405061602131116020a091d120a0c030c06020d0903050c010c0e0f0f030703050115090b060c030403081b06130201020609060c3414120901120e100906 68
    0x209070b1040203131040d28804034003819840e02810780f840d000400c0640d20300d0100000740f404205e140c2d00005c2e012080d00e900046009090000c480414080101800d046607070100071540d0170250324807804560700a03c1054400151005560404079116101c0e500c1c00070301030640103141280d003500c00c009175001c07404242c001c44e00004503100001320074414034142c2d50003407a101060054400006000d480c0c0890014071800f4285c81c90055a1b409001d014001e69008008103c5c9071650f801d04481c1c7c11f0f0f1072080641d01890035400c114079091000844007800749070000ba502e01821543c4074000d64001d91700c00b2081e1981d0201d081c02912082203500e001e0400c40ca110140c8091174800249404802011090b154104c1828000d4007404001910702d080615049c0c1c2c2004481107400341e8046501c110700d401c050881031000c20501c028042d000183d03c3c1c0404c155011150b094041040c544140c000035400555000001013034025154841e1040340d20480644071068604000381d01a928100e070309072000ca = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 376513848 1250 376512598 376512637
    0x81b0c1e06010e01230102031201091e06140910080304030303050a11130501120e01050c1209060106210204050910090b040606020606060c0a0b040302060901060501140a110102040506 80
    0x41010003800c0e00400250f401d10340c4540c180b035159021641c0c98240045480251103506050b07030b001340306450440341d01c1c040141701580d542c1d40030000307040d4112201440c074100c02d43c0d81c440400540161426144410051b5400e0115030013030103130103900246200016502d407100400da44078140000c03c0254000d03540420241080d14855086819006d03800c2014001001010040201c41c2240b90031180700f401c2c0540b40c03001c034482d03540141c1104045500654600000c20003480b403c540500b402085000007841700382d88510000b5a14102800385e500407503103105100e0903030030b0101002d03880c0800c0c0f82c00250801e50b40d200032807100030302581c0d00600341504c04010b01c00c00d0824400c455040e2000c403000c0c403a10b450500003035201c68014051a000d40310000d0b106c0705104041244c0085c40354401d000800c1c62801e400d00944403002030340c01d0716041d4241580010b40350b1003000394481030425001910b1505000382c00650308280ea03108031200d02e5400b80400101569004050020b1888480089040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 376515098 1250 376513848 376513903
    0xc0306070e01030605120c0409020103020405031009050607020303060307290f09030f0105010b040b07050304170a06050a140a05090c0a06031a15030c030a14040303020408160501081b0c 81
    0x160340e2180c00c85e034041c804075101a5210440042c80c4001c2e01410341d0000f407640c8075800120042e2049400040d0103100d11110f009000a00e80e000c940c03498012004e55615031034480b070480e00d070b02c015140030354941d11140050182040d1007012482c41c0c083d0170340c0402c0b0b600c03181012035200c0d0000c00788090400404110b9040e141400d00030943c4600802c4020402903040c05550007140c0518010003010a5000c01c90008100c007c2045501802c44c00380020900402a03408039641c00348030100301c40503401c1c40046000b4807098040c0191500c0d0401c110750300c0d652580c9806008010040c000c08151140e0000c4070f0654880c0103141c4e000e00541c0d60080313240002e51090091001e8500042805010b0000503071114012082c02e41740c20116a51005940352600c0c54071a010341100000000c410100c0c4090004244d0598003d200316203800082e680311050514031001001e505200d018041051040010581043c3c81d0b070b1a01e1135500007044504240e800b0f240949403040d00854020005030a029040381c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 376516348 1250 376515098 376515101
    0x150f020c0316030b1003031b0204090204181b060e040902130c12060e090c0f12061f06020105240a0f17120a020d0305062e0905010c081602030c0306070e0103 69
    0xa1212103080140e440c141b031558001d00790700d5112484c0702e8800c40d000f41e540c04c40d529a00a40c68080c1c00a20a2003a078400400304100c1c6030410004075600c07e603036001c001c002c4889417110000c455054840304000080c140c10301014000212040303900101240d2a900c2180d0305101e900d00034142d9582e030b1071501004003244c80131603249801c001040c1c0f0503202005568080040c5c0c0e15134086040d2180320920b2000c1b00421410720740c40020740000d0203104c04100020f0903901c203031192341c0c0d000d2826038101555a00242d00725078081c0d8401c00d24001400e1540d1510340350000305584010f010b000013410344d0307440301540c00803039840e04056607241c482080080519010003524000c0301c1c0411007285000429100603588041d42000242030580b1980002c0b4280d680803821310454010700c09080591744000465421416a4420480812845240481c40303510402c5402d1009910500203403510f43e188201070410000741c501241c1c1881070425440168805101c00c034001c841d162100718914034013400140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 376517598 1250 376516348 376516351
    0x180f0302010606031d06010317040312030b0a050d020603040f0c05040204090b03010c0e01080708040318031202250302060705010914030d06060206040f1506080102040f1d01150f020c0316030b 84
    0xf0030345e101c4400340348003010041546411650301240c4910301c1101d04410740a14003032540054404100e88510b080101d800d40c20026100340c003143c03c050b0041d12030703040107200341b081400030350070210a00024002541401c48001510b00071071011074180d5075500040c081c0d9200b80c00c25148151a0780000b08642024010044542424101900c40f02241300008000c1c42c0003c000703004110f607103400308080c140545001d5061f8020b0070001c1c500c0e280c680c00d151403013011103141c0c200113208a5690401c252030401c15800041a0b416002c00600c4c03940e001c110941c0c0040505070381a558a60b2010002119031552000304c4a50a01450310303110901c91107012900164800d40c19900035004100008a0040d100d000c0954031850100500703905c0e580071070040440c0e80054040d0b61001502103000b80302d4010160442d2011100c00b501c1ca00f6403044140d4010080c071621112261030002c403e025400340c90421404905441150540005680028a0501e10000e0086418032118050080c400f03000400c0b0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 376518848 1250 376517598 376517621
    0x306060809010b1005070c0806010e090d020120070201120216050d020705011205070e032e02161101180e1b0c070512030d060b0406022806180f030201060603 69
    0x1c010400c046008101c02013940300205081000001300700302046580d082a8001d0451707001126150341e1141c507602c100c4c40041da0301000c24810f80e010819903e10501403450a480b14401e0001041140c880703418841e001084224140080d01c40c0c040204016480034041d03044018070503140820842c1403403400d048007044c01c2002c6401040080c40740ba600005900c580c0070100c0030006041e503521104a80701d401c001c031081c1d850f00030300e883c1030780c4641400c01070b0160b0012542d51420554403011940b00302e00c00c500082d281400c0c007400345e001040051064407003440f01810024401689040500c000741c41e140c10114807100e2280c1840502c0c04a01c07180c00040c60591012441c00c14000d1486035100003074030800e480340401d010a88560f82c1c043c4252801002c7e82c00092041d00d0700c5400710031080e0000d0096074018400c1c4540c001c0b0f11460700c60506d5030f608001240301600c82d0540c448c08007810100f031052254120b0005003100069041603044907141c0290300000d5041c0c01e001008040d1010110300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 376520098 1250 376518848 376518851
    0x60e07140a140613090515090a0b03060612010e03030c0a0815220f0c020f0c0316061101091a07030b0a08030f07110a0f0e06030d0909020c1606030606080901 69
    0x9000d000807610a41c051440e0480f10103444000300c0e130910681c4e64582d084010200d060500f4001e4020703903051714100802044900082503640c00ca2000e003140c002540c01c03035255204c88045940c41c144017080383e102c148000e001007540c0e036021032a6031643e80b050740c07030040c4814000303041c040d91a4080c6209802c0145610030030001100200000c0c01c08602140d000e4040b204407208081030341007580901e070920114081804984460b4802a44994280401e8242c030700401c84028014a40400d00b200c039000750300c4400d010241828411916481c0c81c40040440790b42c0c0d8040718001c00c400c40c1c1c0807401c0048811000c01c007032400000050582721148107440c0142d040200600407002c3c007000780c0304040072000d142d0707407181c60314107005440341841d06600380c2201c46841c0c0403540c4003901c04545d003a41d18103041c5204e191500014581d540c10903a201000284011005005401b401e800a00640c4900c40848001000280c002501c0304c445601100c0400c0d9240003c000341500000e22540c0302091000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 376521348 1250 376520098 376520119
    0x406020d05040f180b04151809030503160903081b0c0307061d03120d05100b0f071202031c050106140906070b0601090305010906020d0e0c01020a02060d020403060e0714 74
    0xa040800c0c0c502d00507003956905021462203545070f585e000042d0124000c00134054959840a4840803600c1801001140042d585100b07003690f40c9030141d03800da6a85a0386961540d950100c88040c2c0c1d20003201e0b50320404c501418004041482030001c2c20a100300b0728059400c440d0b6144000d45070040c00090f19000b500f0518080024a0f00b241d5650300b040c0f07460300c40e00141c2e0a40c1000a040010758031708030f002c0301000300304683c0700081507201a1203032040018071481c040d15001da6035441d01a011401640e418200446000140d80f0820000034202c24011a801c11980100c44030041e04240c201d110210360390401000103580c00004c056525840031002d0345000408001305100b403160020160004150801285060340300c0c003a024019900a4004c0140d10014500540654000da6032181000c0c104030303440c00e0305c0f900451208040d40f0144c000300004a4154280003082e0811052004103070350a201c00030205103203004818080300b00c1000b405150303043c0307541c00403111884490b0034094210f00c03a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 376522598 1250 376521348 376521359
    0x80604061416020a080d060b03040606050f150913020705100f11090d0605071e050702010e06250212010603030309050f03040326190c02010e041b08040c05150406020d0504 75
    0x10304d802e5154000c0e10907550f891181314444094502e50307010455541c40041000b06010140d0f200b0b005035130040b0751107480d4452600820001840440c60303600088800c21941c200e618242c07280200098078160054180129501e8543c14064002d104614864507440c102100784864411241c0301540d10030b00d40d0030051900041351110321412001000555510045020745001c4d48400384411407800756000030650460f4000e1183e000184103e01280041d11503424078507028043d142036109040c000803042c403601c442e10781d09508000e03050382c2140e040000100c5402d001c1c0100c5010307502a86010440140914083d45841c044020200c2c3c150000c0c403080c0b00086d5400c3e5a0603440600ba82d2a0205e150005103003040d5108075103900348a140000d0003c1e0b2a070741c0260126055038000d0702c1d61610b10640801344000d8520040a01340700c400e07002c65041798240550342c8550006e008400701c94581d038403180030070710320000c480d0400c4210078003140c108840380e41004001d540c80500e00d00907041c00d1821 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 376523848 1250 376522598 376522603
    0x4020703170714070b220f1403041d071814030c0402070b06010c050f0a060b040510050102030307050f0417010509060c041202120f0d03050a0c0c020a1e08060406141602 74
    0x9140050040c50500041b070b0507040e000014101c100e1004100c8540101e1a01d410003a1451144084401c4c0c070381b41c464841000c202005440481c0c04a07c000300c0000b0603a114000d0300003000b042c410510850780d0210501c10301f4504144090440131071440e0855806208251800801010040c801c6004000003030000d00b161400c541c00c41000e007021100381c940c1d464500e00341120042c1c64007003442408440320600429401c074822400c01603404210907110060b40c040203800d1801500c1c050382c020404600e0440c4a04010302103400205070340303401c181c0c40e6041362150404604600c2c02e00d03910369041c00300340310f010310103150040c000013a50343c5880d06d0f100249070406001c41e4060b100d07600c03031700c030301000d4181c1070104031903c1080809a80c4003a041c02000340007070505482ca50952031804080b241041e0145900c2c8000396001490108928540400895150041b0a2006107004100c400103040201000701d0341c06075215660100301c1c0309841c40040600e0308001c000d00440024240c1100d01d0079000f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 376525098 1250 376523848 376523857
    0x8030a09091808070510090f350904020f0408030c0d110a0201031d0d030501030506070309150b03120f210106050d050705090a0b21010503120c010b04020703170714 72
    0x2c0380f0a03403500758500b070050500300c40d0510b00b4400c0f800c00314210100610500d800d00c070607128054241c101989081070244003a110b404c2c1040711046220400788800d908405403401d1100208050b180006194201c55150460341c00a00c1c00e90000c076407152550028812076603810850f00d805144d04683c04802980c69074075020190605948050b10486416116444030400302480100e50044400f0707000203000f050b003480b00350790324061078021948040c883e000c0e040440d900304000000010b40588010010012000401d0b4140310b500300c09020607101c500601722480361440070649803101c1004c2203a01c2c07565008112505446e41e001488102c0d00142a00d210a0400d040014580c0d1801c005036500c2c81554819940701c042e40c080000c0584080000340050140c0a206400d54281800d003508140c00030b0190a5264010100b500c00448001c005050381e0b000b09000401e1030814940841e040368007114041c0e00103100c0e080d03000b002182c56001150060b91910341034495813a041d424440301d014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 376526348 1250 376525098 376525103
    0x501050705250f020418030f02030a0c0314160c1404110f0d0f05100504110a0219060227100801030222020c070801020901020f0a020907030c031508030a090918 70
    0x42c03003406509001c80b0120001143d640030700200300c4d1281d10008095000740040c0c046000a4074642944905480481621400c940781e440b0401035039202c0d40c1c01d03030b00743d0901c8402c5814408188110f903481c40c80e035100000024010301d20220b21034148080c041150b620310306440c0c041d500f40220540130103011004c0701c49101281d55074949801c1040c0c1410083d107004804419031506080c1070180030201048030700c1c12100102c4040060359031414907034019000f60f04046001d038101c001d40032112000e041400002900c1060014036021202e00d030030380b4a14665201c00340c2c6c0300501c00b0301c1100c1e003048401c0740c0f10244242408135441d80b42d070b0700140007507040030b0700520340481280e251071403010a60140d40002c0a03400c103842046480d10728040c003d4000e1505c00f4014030810144503651079002c502c540e2000d801600312912036690100c16005810b040c00c0d810100b41e6120400512050500c100c040035001030400b85907070f507041c0c110003041003120741c0105400300c1c50b003e81c078110703d904100b0300c514065 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 376527598 1250 376526348 376526407
    0x80604031e1107030503090f12060f04020d0501090c050a0801021c0c02030f0301080d0315080a020f0a091803030e0c060702130212010e0108060f04020306040b0604110706090501050705 81
    0x300301c00821200c00c50000c0d850003451042102c04020040040054001c1c90b1069604000403200c2104211030380d04620610000c94000c1c00120340c00a00415030039a100340041c042c0001e00d00710741e981500716004940180c400c2446500705214a01d4030344a40002442418005e60070500c0c4e180022806103050034030b00d00481e580e640005402402402a01c100807000580c1036260760392815040e4585040629410019241800115551010b0004541980c0440d80102000c00d00c503403d01c40c0e2040524807a590015600c000000d01110320f00540c040300c0c0910120f8a055040343c60003405030307203035002415096080980ea40c92561104010b80d801c5640486290298107042503101d00242b080200c10b10121001d400082854400140340e241213070455421101240c0c1d401204000f50305050790000d5158002e0b0b0007090104440703403050341c0c000400030310000d406101003025030050343c01407030111400d540350f071002002e1000c00e1181c551312940600b4440e00d040481c6000b0a500d4241111078100036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 376528848 1250 376527598 376527647
    0x90c1602030c0622060207080a170d0c1710120206160b0705040807060c030f050325030b0a082d07050918160302153009060108060403 59
    0x40d078040103609881600548101d80c1c904c8050b0031030701149907402010b4210b030403460b00010038910026500701101c2080000e0b050b0089903a44403029040c50f400d141002c05424088032400603080d1082a5240c425a02c03100f0800d5030500d074480c0041802046684051030310305040040a09601c000003075558103c42c0c281d5905401c1e40071a0806440d804054070101031141000303013194215004006440407942101e4440340c0c0c40c00b080710700c40c41d1400000c0c0025002e5000780d802d640220b0145801c0100040307105c041030101c0c840400d040c02d14203200300000751144955078150a001103410b010b0310170390700034101500d041c070030001490303108100c03034460110b07054152008944103010300350191800a042c4070007410083d0355a0b298240c2140564098001d03400c1000062698058101c22260b0203003140200c8420041091126044105080c04480c004007601c4510031044410160000c11700a8002287c02e00d2030002c5e1424405030810a007950000b4140000300f5080b01a06080720414810074054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 376530098 1250 376528848 376528853
    0x6070e0a0512100212010305060c030903160501140907050f04050f1605161101091d0403120212010306060f0e0910020d0e030c07030605100317091504030605010e06090c16 75
    0x40c40c810741c04402c0703000d20204119061a000c0755105e4102e034000d10444140d034907400080c101c1d9110503030f80650340d984208914120340c2d0b02075020448140c001e00c000a1484451807403011442011101c414507504064010310444c030b4811640c01e860340040c0c1d000c008514108602c078884200281a540403014403480d282441842102101d03a5106000700c440e8195906240100010010b104d44501180301190007081c542c1110b0392044a800c01c0910150440d2542e45090300c1108a9a00f583c2485408001100c010801c2c218018003e5115040010b4094946140c0020401c115080209032120740c0040c00001e000001b24661440e200000060707940030b4100c0c03c42c0081c00c40b07010b8050f00340004251008143c1c00030607500d048034001c4806009594800903500207404a5000c020000d1101c0b143c411035810300000a0400280c0141905030031081c0d0701100030442c0c2003035008458103621440107000c580480303070398150000b106682d00402800c0c500c03490082d60184030740d540680400364800605 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 376531348 1250 376530098 376530103
    0x609030f060209040b06070312050f060d03180b1c06050904021e190303030506040b030f0d031e0608030409111206040506030a17040e0606070201020303010b0c01060312030c0206070e0a0512 83
    0x45c00c04c0020b00061b540c03107061801070300102000d060707110034610f0314000030408940441090b200c0d4000500c403c1c0300c09220754050303441c18201580b081c02d00048280104140c1680c20050143d440c20205150701c0c0c0c84403440041c241e075408e030891805003020382d00f4000141c6031402e0364500745002c0303145071b010711002070042a07149054420b02c040d2107108000010038580c155006a0044105031010300409502809043c0d8403c41441e0000c1154071040d15214880d10980c04102018000c0403400022142180c4002c20380b600358210685a4200140800c1100390610075070307801090900625081c0352204440d00009800142940d0081c2c1d21500000d05569003886984211035019114a035000c859004480761604540190303c0d03881c0c10600861079510b400f030140c407081d81d4141d00035841c41c0c1c2080c250300d4103070300200c081c0007956490b00c2010000a001d43d406121492a545c1c1c0003504a006840c001d2520320003402007000e00c034011065011039201d05554030f05a03401038600c02c6c0c4016410b5001031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 376532598 1250 376531348 376531361
    0xc051002010b0301060e06040b0307150507061803050a0f11030a050c0309030a08030a0e01270c03150906110c1002160804080a020f090903040909080d14060a0609030f06020904 77
    0xf03078154a09003000c80d01c04184a4200d0003550207490400403054500145a035441d1a07001e007503400c03410070910004841c4903a0090140078843c0c880400c1e103a1600e0343d0ba8004074005c06084000c11008920180d1590b40002c89081d5404146000741510190440143d1248107406100080040029008940c1c400c00c104445203800007808840860820f070800604980080d40c015008600303200c1c07622403158050054001c1d00000001d104c02c2e0342c4001c00040c40507900c0c0f030f400329070031194414004040b91503616204050012074801043e81151445c16408859500b02c03a0421040144000070b05010001050808240154001030760b4842c24600e204014104110051034054000341c04940201c01043e10802c0030301c00e407100001000307a40100419a0310450744001964428001001100c2c5aa0800b1107194050504c0c54501680c0c0e2000d482513849400040401c520060705218050408444010003040603140148415046a171159604100c8000103410581c01298102155a4660112 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 376533848 1250 376532598 376532621
    0x10206041e0c030b070f120b0117040f0203030703020c042304061d030a26010506030408030411090a05040c050f18091006030c0303021015030f051c0c0506060303070c05100201 77
    0x10400d07142c00c20004040d0486d00100ca80042c1100001904000e800d001d81d00081b0416110408440300c48029902a0113004006070399110004c50700f100961014001802442d000b640a03100000303010050100340c0715110109002100e00c07000e00c00410000764640340c0c0150780464045280e6440950b107800c00c10702d440624165000020702100d40ca44c01840040c50070a159203e40b13800c88600ea2540d2030401c00b482103030b030004c108000207800100c5280085620920481c94821642c0180001c213010000c201d035140403582d43c0b02c2c2800b06010845030748030000e10044411459508682c40801c0700002019484c040ba45840070104a4805c4c040c48003c44004032072108000c82550b90a0409514206100c2900540102d48030ba0071000303801d00514011032001d1410002c03561847c2d4541803142c1d000305c82a9120701461010414a00c080010203c0418440d962440703909003508103141084000307880c1074442d41c420014000018101c225040c02c880049070410f80a00711800c060b809081140042c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 376535098 1250 376533848 376533863
    0x2010c05250b040501090b0c100c0504051f0e060d0b120619050c091c0b0a0507020f0c0a0603050712050106200c0f28080102030103020f010206041e0c03 67
    0x36038000004003000740c80080c156901810a07a4542d00c812583c0f2a60144070f0010b0320400c0140f000038003c100600b1285105000c640c41c246060141c4c0048850b41c1b2203c00020300c00041c10000c81c40c200c4146020342d0b018201011008011090180020341003503000d40c000d2202007800b03814200c641d8044002002d02400305100941e208580c10744544044a0500900d944071281045400d910310032644505c1d03400081918007801582041003410480c45c51446100c107038208200003c1082413424011440380501044a0030541e0b4040d0401003110950015503114242d07542480d9a0305000004503980342c10300142ca512015800c441868035080024500d0b030600300000f5002d984900321074114080c0ba90244c003003403884500e464a900421a01e0b40c1e02c45554500140c5a1500c50305292038044644984070304004a503483e1442c69070554010300060350b020004100b0360500010b003401c12a401d1010b00258a040d0b9102c0c0301c1c1d000340201c41034000e680e503060b02003002140803100003e0354000d0070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 376536348 1250 376535098 376535113
    0xe06031501030f140a1407080702060402090c0c0f011e020f0d0b0a08030a090e010b0c210d1103040510020708040306020706090204060e270c1212070803150f091302010c05 75
    0x4640c060007100c411a15581121b40025a80b94400c4040a010760059400303030005440300c0d020441403070b0b005081400110740401400008802c2041004d07c83d8490342c00104900701c90700281c400aa5500c1c082c620348900420581c1040e03010320003156210301d200704000071101c0d030040200d05107441075044101e0360701c000209c010490b900600c902c8106d40e90143d04616580c0c80d0a0300402c540107a844800c101c0d4002c00054409540704450700400d021847c02007818003421450306c0040d204600c2c2aa603a00350000107200912100303120403005044442c10075441c1001c1645c8600c19441948005030080340d021490f0410842d0a030450800b030b44d0001e00a114968440780e42003003003101900c280c09040001d079555400507800000880c800a1400301034400c22903d40c05200307141940011141c1140510900501424448406010280e028410f81520f0b03251580500c03805040c40d441c464032840500500c0c0449580342d854190f40066040403d00110b42a840142c0b50f1401d0110020514020502c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 376537598 1250 376536348 376536361
    0x5030706060308120105030714240a0f170408040612091506060305070c1e020310050702030901120e1914071403010b2d0d120c02010e06031501030f14 66
    0x10f4090044c0d040d0090080d030341e803401090364800d40d5114200b41400c034440c01400929040e02d00342e060a811045a1002e29061504005203510020540011442e40150304140c0e99111403030f810b40c030750101c950720200d0400351950b401c50300861041000308400310b014124050402d4000502c9984e2102c114048640a216072201801090207440d0000b442e1000041c1402c0c4079007110001d064004078102400d0441c1c2c88640010800d01c1010307030f0180301e0030307040343c00740c03005445514440d0000303601130740c1c0b2000303c071000601c941d90000c014801e003030400c9144254008081030504100000040f04107056a41d03241801031440012907880e4035000d2420001034000d0200140100418210300030040d202c911400c100c01210b42880a40038414600d810342c95a00c186a02d001c20300000405540c07445240c1c0d40c0c0c0c2020301d40054007050003d825880c4400455802c06800000850f0440d442d030b09500c0c00320840c450a41c8180c031071504054941461000c040340b00d610540b5500800c031515074140ca41103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 376538848 1250 376537598 376537613
    0x80a0e014104030203040608060405060a03020f0109030f051c0504060906080601110f0d0f050c1207030e09010909030e040225020109081002210c1c020405040507020f01050c0315010309050307060603 87
    0x1c1c1f048034040784020380003038554503081c42511720644006218907942800d40d001d0008400c40b85000c60305110318400f011000c0360206110341c40c010311030b80c01850380a608203004807540740101070322024040700b88410700c132260300044e42c81c0540d812845d08014556600300100c0c3c00d181d600780c0b081c000c1d015440b00c440111902240d00041c0348030f1612050401450395004603600c1c414038841c000c0d82d400400e0341ca00903610000c01041158082c1c5131400061214200280052170281d0060350001d85e5088d05400f0160072032800c3d11000000c032411420301340c4c0f80224080b08044440300000b80280110072208682c0254080000703009010201d03000d00c00e803c415034009522400c0600b01c0c001806042500c442c00c0d4030407442c8901260b420700340c00c043e1200500c072400c07408003881d0070519070248000f08071500c4601c241c030300c501032a9008100c7d0007101c952407030031102c0190141050050401c1007021403490f080c0d00c100c03945820300e000502070344d850420600314094400300402a50130711100009010740c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 376540098 1250 376538848 376538857
    0xc1509020a0b030711030408030f0d110f04030b010b210417030c090a050d1106070f05010903050d0b121b062a100c02070608040809040c080a0e014104030203 69
    0x541c985c24507145514130140e0b41d9020790312514403a94020005c00f000000e60202401034161080404105601c85c11050019908a07540d0030400003408079081041c0500244114011b021480c0400c1c6001c4584103c460440d0300c0c3c81805c22800d42103404502006070500845131802c615080540c1c49050040342a00a5030181c81c2d810b106420b11070740800d40345050410191016071185c1000341c2c056a000038403205811000040d14070b42c14500409001c9203080c001c482d40c0620175980d95594401d1420340c80121000c1d15500340c001d449075034014100c07140003d000e0603401c2031690b013856003000b41e500003480340c85804482243e040c4100415010050303040f003641084211502902c814410a4140400300c4800380f40040069000c0c1c030f801c0110901654046801030b0203104000d180004841c0804e0903103100024200c0064181c1d4100000c03901d5a00c2200c0060403500024000c009040d104a5864624007101812036107000a0707c8113040f0504411151022406584c09400d00c4c060a010303499412 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 376541348 1250 376540098 376540111
    0xe09070e0907020303100e0c12130602040b030717040b06121204080106151404151b03020604060f0218040c09030209010f030b07080606030a090503090303070609050705010f0c1509020a0b03 83
    0x2c00c0b40b0302007a000d5007e901c10307216a200d03488a5003043c1d880c1404071171112020f001503207203908455040c40483c04a00051001d050303850186503590808210060883c034041140c11003401e141001c1c00700045c1a410149c3e00904121201989100f00300215424410020000d000c00d13013000400290f4400c040d005442100c810781ca00c0240100c002d070f000c0e200513042c15258660504208010320440c900d19103604024207062404004a14141d9441107590719010710a4000d40d0040c02080b040092900a500004002200550800c2c21000d80e44002e020012100e6100b542c4034012410810300c1111240d0081d86c000b000c140c4907503034610308151600c209000948043e180100010b00a07401742d200c25010740c20103400760b49503584140c00d03200144050041203030a40020424000155000c101a0054500070100010000d049240a5142c00095440281804907480c0395806594110186a80070783c0c100d802d0503045900021181d0040c240010000d50003d075000c0081600b26850019511410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 376542598 1250 376541348 376541371
    0x190608100c0c0f0311031b16080d021b040b102c09040201180b0307030606091d13060906060909030e030615100e0406090c1b02010e09070e0907020303 66
    0x4080341412035044038002c6018241e803603840d04000002c0e1145884d2941c450141c0183c9040c40038000c0161001188041c0307010311a44003240b203000c021103030022000288507000042c84202c480140280d20303400158645403504071002e243d022980c803180c1020020b50001084070900c441000300c0641401c8195440d04c81d40880341030350142e801ca016800c03019004004211482698440d401100d00700d1070003900c600c003540440c00004118482001542c01000141c401040c95410451700900201c415800030301c6400741c551500c541100302e2011a500305c1202d000b240d180f90795030f041801c0030300280040141002d01c0c04000060f40d024a0344500d980c94441c0e41c0b0310402038010420159692010f40e828100c224540705459103030b1810302c1100500012506208540c1c0600ac00003908490050f44900501500c1e242c4400c211540f248120183ca42118401d940091440c0c00090415103a200c0c041e0158080364082080240504030049104100400c8040b03541f030700040c025243d410a81c0c5912815 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 376543848 1250 376542598 376542611
    0x501030b070c05070b3001291b030c03070b071b020102060c030a14010e0609100608150a0b21061203030604020a11070f08100903020a0b19060810 64
    0x503100750b06042c003158026008141040c2845840e41d50340e0710445401e01030810002204403108545009606001600b4401500c1c0c0d41c5496130030b10b6811101032806020032210300581109958480940d0758070341c5510903115480c50340100491552080e0070301103145120121b200800c0003010400144101c009907243ea030b00c40b1070900a40450446510300a0240c1c004c400010b20002c0000080c40c0e026844600105101e2030f03000e4002e106c5042038100b0176500d4400c5040003007500b0444900340e007082d0400040c040007443d108000301024006401c1c1d44440400d800400080e42d515103203440075005016580d95642c401007a410b00109c07040c404074048091050008005181003051003042808410180d0300c0c550703030a0708000081d4040451241440280446d025007900100461000781c04501c80103084a42090b0a0601e44101803446042c441d0401e83c05800199001c00c03100d205c65801203010002d0380315013a40b00c036054074800401480501d002c2001414032000a514151103251002c2084807 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 376545098 1250 376543848 376543861
    0x60207090b030c190504020a020a060b010804050d08100306020309010902040c03021303171207110606090709090911030303070f0806030a020f1504090c030e0d020f0d110c130501030b 80
    0x1500d103007500c034950641000d18082c1540c28000400c210f0480001110409030f615100003504a0300030001c0d44d00140c1c000031402042240601c10341d080e074602400c2a12710f51405035195039942903124070030403c00c030a60380800c8044003080f4460000d540e01c0b0400350744900c0d003924464000c100140d01648102e090480e43c694081c000e1080700c001c07441ea1182c8070301450440e02d840c0c1031003070b000340c68080c182010025115803412101c01280900a03a41e00c400c2105140305101c1d1420030003401d803621682d05a001d01c09005d0b0050319080072180114400f03d603000003402c24111042c165811560140400420025660340c8245901300081d070580f9540d1068460000b4507076210006800290801c0000c54101028901040c0141d40d880400392030628003a02e0f40307400403d40310b0040900e00030070348400e24902c28041c180070a4a14204910041c0120340402906039540d0943d0b4000030240f1546c000d4004d80326105004030424088040c1c07007449034028800c0100010301092009880e1401c161011541 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 376546348 1250 376545098 376545101
    0x201200406050a3f110d02070f02040e031e040506070b06120106140a081c0318050a11180f070f02150903031e0c040501180e0a0e060106032304020d0b0109050106020709 74
    0x144411152051806c001c024a42c001c000c0d0300028080d1684200c15000b400183c0d140d015100300204904050740c1c40d501070440c03181c2880e5002c003d810340c1c8002404280426220403040d00d44460b008071088582e5240c82e40400c0300c0401300301d106441c03035080c500c0c08101104000d0510b00c003400151141035030aa1342e002c40e1604d40c1240982103003484681445c518040b4482d400c100304000700050400307400c000a50b141494000601c42c111445086290300d14890720702100740903203100e108400340b40d035407070005891031802c03c0040c56202071003c10b0040d4038034544200301d113840301c10845140d40b1303041c2025a00e880e680e400450320003664100c5d02403da00c00e0b1180601d624013505000d105203042500340001521043ca10f03950310a40241805400a0710180b28200540100030440c80041c1d44150b98541609100050300000c06242c2000c404035000166400d185118841d9410078082c02d858510005145003079200d005003e040e40c0000205000005a10440c1245c802d80c00710307030785240d50740700c0e440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 376547598 1250 376546348 376546361
    0xd02060901060e1302010201110a0801180504020d140c0a03031d0103060605070305071a0103060e010510060912050c04050408300a05060111010c0f0201200406050a3f 73
    0x100c002c003401103103a07000a85040c10300d045c8140008a00d016940d60503002507000141c4000c0060020001040f12142c001148150621000c105011a16141d000710b030040400790310041c0601c007074110811880005000c924181c42d00141005402540d0f0b00780103241903100c000540e5201e441031103030401076000384140c0c01182c4d6a43c0302c0c6800c00440d0344040d1059005004180c900310100204840420048540d07035019500c1143c0000b690032102d101b80d400c507072008101d86007855041005000f210f4102200e04200c0381c2600000e01542d9062600504180c030840703801e41c0050400c0184810480b012029006400042903c00070819181c003611080c1020346800b60001543c09004c103000300219000681e201a041c18012580030740001210b0854200900b2a00002e40500e107040080758207000d1070702c103a64020420305040000082d1190b552140c0d104400601900246014220b80640000d000458080280c00d501c40307040d800103003641410b40d107110a5840350111211942d6241d11602d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 376548848 1250 376547598 376547609
    0xb0301031a040804030215190905010909020c07050a240e010815031504081902120d0209030a30081302040e070302031b090106090e070e0a03140d0206090106 69
    0x1400041c194034031070800000040d1040e24424410800840503031034260a00304940307200401d141e556000323040000f21803044886400f040080d9403004002a0b079010741480207030398140200680d10700c080c1040c60300c0c0c0492544003980082001c0b000145403c007a05074007925884004241c286c039550450304480445506040a000c585000042112080c2c4600050007041e4081d0413500c22140010300134901c0c00c41110700b218000d02c00654402d450b51200c62888110886d4001804031803030500d404410ba00a24aa80c40e5055012903038200c00d035020410421407913007001c0c940380030105500c41017082d01c1d001040340ca00010074040b84913450f0300c10300140d8070940c840e841000000e9495401c210142c076030f40da102109480358002c084056501031116225a4032000320801c41c502000d020b210310750070164044410b1000d9054104510003042c00707a6544a807a501d404910220300310005803088480d0b400140059007809040303030155100003001c4035000f0541e0201c903d981d5031880040d00b44ca010f401907 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 376550098 1250 376548848 376548863
    0x106141203030f0a02031306090b1801060302010c020618060309100627050c1b071d01030201090303030f0219031e0203150d14152505091201060f0b0a08010b030103 72
    0x207800c11380940d026581080340401c03408101101d9460750801e83d500440c00f51016540f490a2003100d4100b00403980110b02110001e101091954001170b103144001440030380202800100005141a07410060080d100001e1099860b4204009059500d4608034110300465242150118450a2907003271460720380303140b10740e1240c0c0d0008402e80101500d80a054944500410702a145003242d030170800842c1d1001340b030001d0080d103107000d41c60710310b50610103c1214441401c400620250342e0145c0501c007541e402d0b08002c500340460041800003403043c42c120b2100342d41d070924020100350341604181c00d800405071241c01d0240f43c040c449401ca05c800d80303266112018148205e2a5410b0640d2060b0b0b82074083c0340764001d400d04100d9001c1c2080d9000341417500501a0a04020142076032450014900010030307460032000c0e444070700207003a030303c0703541e00c094410203003080080d501c0030003500a24042d2142020052026036102c8030000c0c65004101e6845c0418500f000101e00b609203031b42602d0480b9005001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 376551348 1250 376550098 376550101
    0x201021215030a02061b0c0406150809160306050117121815030c030708011406041a0904060605030711031c0207020d0c030b0f06030102091503090304080106141203030f 74
    0x1d00d600100e050311034503030180070306040180035a4a120107052420616200604010760b4128418104201c810b04c05106e28585030003072204140c43c00096500c0c0780380e41016402a142c0c40886854401d101203131003040b41c00f04101204101040d0440d90484680842c42c4080440c038442540c0c540030040b03504486030005214400689032580e90519401d40080e120141c45106200c0380d10f690742c0100d615400c409000400d211025a1102e0211b0040242c8000407110480402c0014a40d22623031259180d1510706058441b41c1e500500304460402e40010410420700d41c0d200c3d000740c1590411100780000c50054030058801d03400200480350070100c000e01d20200e0500c40ea8920000790030848081c2e8002d402806024001001c0f214680060340c01140441168a84600c065aa10740010946800f9900610003600e441e200c0602c081c40e41d0000c803440359165030303406058070314500032075010700c1d0300c3e43c2400f20001c3c020b68100e0310b0014862050f51008500000300100381d560f44019155601410079200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 376552598 1250 376551348 376551361
    0x41a07020309210d0f0e04020d090519030c020f0402041203020601030611070507260a05030705071706070305060f42161a0702100b1507061a030f071502010212 70
    0x10021902d180e170074202580101c640c0c1300440c040307030000c6503601c4c440d540c0e0381e1781c0e102403041c100520124120041b594040d1100c075035600420000520303900034051000d80b003242e8115990740d010703540a04051000c002030140c5500303000355615820720044e1a414a030480c8880340010340c00031101d02d2500100240681c0b4075000000e0104408011420118045084003109940082c00034004481c010300085841e40b0740d030f090160500140b58404144000b04c81220000c0ea50041071486e40407069003030008880e510742c1f02180c402d10320724a9080d03103d80d0040c14040a10800c044965420b4290103900002c54481c100200241c0c00e80242e40c40d10910502c11080c80744200c08150015034803c61096601007043c800100c1d10250036640140541c028866a000f40c03100c0703200351500e1800450b04040040d000294414161140803005041079032039181114410365104d010003c20710300982260a0741c90400d0156460f030042c0c0c0a210350300c02010f403a0314a114070500039114007026580c0002c40584408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 376553848 1250 376552598 376552607
    0x1504060c0b0a090819020105090a0f02010c0312050a02071103150112052b020c030a021302090a180603021206010e132f0301062c041a07020309210d 65
    0x100394140380c0f619400060005400100506040441d0b07440c4d24003114124800039081d520020481c902d2a0f01c14074541010400342c402c0e01107019020308001d002580141000c0710b481c0c42d805c81c00c48515042c5400e2200170380d80355000b040036078014802c00c610044010101503c0d40b100c080c0540b511412100140000c0c0750074500c030fa810741d110f0800c550702c0c207845850010311038401090004444a010303840d01e5036140c061000a40031031003203015061554141e400581000c5e200c0c00761001e0290302042c1080d00e03031a00b446078070183c03548480581801301034011901c003600c804d000884c02001307050300006546000103807103416a012031254280d59560001c2c5c0d0303084c181a0030400c1e40c0c0d10501c03030240c803079003c508411020404803405440000400752414142540c0a5910404961100c40c00d030503841c0300c034039546400380c01601100d18a145c03100d00b0842986200b403080300001001090500031860340010081c01028811707030f540c448001194410302d00301e45010b54040c4140d041612480074041c881c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 376555098 1250 376553848 376553851
    0x2f1014150307030f0b060f0d02030607032c0a0302010c08090304061416060e0d1107090b0604030507090b040b2b02120a050f010e06190f0b040212061504060c0b 70
    0x7904031410641e0741e8a514540d51a900d00690701c10010b50240101410446030400c401001035802d10240c042e03c1c0c0c04241c3d43c900042c920000c155603112459104402c01d03080017110660349c1a4054006000001a0b44403c04481e04802561810300400e5085000d481e01034440e00005001d03504051401409652650f502d1440030b84002040100030880340c0c2140552082c50b005c1c0000050840310250364034684128601c0020a015449030103100600c00054010250343c403010000c50004556070208055000301e4100a1a1b4010031202260030422940626454541100d00b48a00900b800038084480351000c042a0340c1e420b10800c050005507080078a194051020f01071300d68100d0000340050400054039000c94654010f95008160309200b4040e0761148920078029004609240700d40c1e5400300102d1a100b0000358640c4284081003103075900c0301102201c0a00195510300e84a05112030504044901500c540040d1404510351307110a02a18143ca215071561840d0814944401006860 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 376556348 1250 376555098 376555141
    0x30102070f12020601140634080c0c04060b09040207020d02030303091b0901060f1101060305071401230d110405031213060309020a05102f1014 63
    0x4003001014000340e0006031000c0340a000e41014040032000e814000c0c240001a800350000e4130440d041c1d00d1040d9602012a420101c02d080d0000d10f5842c403501c000e0f19440d44400c00400e402d01244403c00303104c6060002c140f290001d1044e0f41d2081c0e02c02e400c11007203807640d01441c0c4d03a101d401d00c454002d60406500405080380020101c2c0760b148090350000389590700407903641c1000e82090f0310f180b810861030420700d01c050030700321808005581054401000337903100d28002c4042041c2c0d241c000300385c04401c0d07010401035a000344c2a2002a902c901c0400c4104520500790fa00140c03076512203101401100050505441e4480507540c603017a41c881c5014041c01d0800c488980034403042100003416942003041403541001d00040507260381c46020744856140460340301e1014035050940010041e40c6444490f0140c40046030401c0100300000d4007280d00030f200000c400d101480034043c0d20941580c0a80103128644440300329003e00c1a80c0180c2010b0f1340d1203044040017401e403000444c60a802c5e030502180e2004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 376557598 1250 376556348 376556351
    0x506011101060807180b06070816080406020703140102031006110309120d1b080715140403020c0a060203131802070503030705220501050d1a03070603061d010602070e060301 76
    0x18410300c1070300b1626598810402688020001c003c40d942c00308082c103c00c21840020030008400c034002c00c601d03104504000b09507410018402d012680b1020755400f80c50b400c00caa481c1c40f070703072181d2001c3d540c0c1c0814001aa200c0154407241101d084050080381d1049078500102800d040c5800c4040d81c45070844100022140400e1021101c140c54030140303081d0050b92140200040100c400002d42032401d1500288602c04417982e42e0340104421504880b400b42c4e101425220382d940001e406001410b0070500144140515420322040c15400100c080c2002400c8605000310395841600b03a0790391007005400311540110300c10410540101c00341c0d040c0400448500949013181641d90203095510444000300464004201c02c81040074803002c3c80b10000f01012050505400c01c00040c000c0e00440018403442ca0b1294007100076101e00801c1044c0608015084541d0381e41c40b00d5010b03018003002d0040d05800142d0b0400340180807103c0300880d040754001e0300500b404c581080481e8001c584010000c1d03030190f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 376558848 1250 376557598 376557617
    0x7050d180504020d021201090c05030f0a0b040c050901031d070303111608031815041202040626061501080708040c0f030c060e10090909020a12050d02070f030510050601 74
    0x10303121400205503000e050710f00180c1d10f1b646050b20700c1c05248180c0044200e00c0c90f098001c181a41c215046071b4101c505c0c07038010311103a56482100000780403400c10340f0382c0090a0103008200310380c03c50301078000031000362000d00544c50034004000340501c1720b52805100d0b42c807805017000807038001e41c82c1c0d02d2940031010a59041081c9240310240a41540d400601c05900000c2c800e404c00542034090340c2e50200440f001120319450100c2416580990f010304007503409420454805c55072181c0c4850000d050541012445240c0510040c40c0d00c008110040002c3c00356400103803110440e00c0700520000d00503102e40c9a66284d0080072103942c40014000c898220300340e000440c2108034151003100543c8990008420700d030400c2801881d01c07803103908040c0205007900c05041d16030781150034401602c080c3e0000007015402800043c154003400d034802d6030f401d034a844071807007404400304001110390955021145100d54408404801418a10028120ba00050181c1a42e5070300b0b5001075030054030514040c0351741c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 376560098 1250 376558848 376558859
    0x616050c03070f03020a0e10141c0b07031a031c1101051f08030306090103060c09121b0b03090d03051302101d1005070f0c1205010204030b060607050d18 67
    0x9009280d000912000c9000f5001c10440c9030840345400a00040c14901d0103d046c41c82488100c9001405106020854510906100c3e01c1d0b000c0025899a405982c00c56014450708042c0c0f641c0c5416955840024204240f41d2a0090f00e0403000030940c5015000304003448807490b507101c08110742a0b0060400010499240200a00b4000c85001e110303083c01c0354001103800100c040e4031000d41e6010407030750b17081030041200c00c1c4d490a401d03038116604035001142ca400d038140c01b200c81c40703442e801000d000130804486c41d040c0b01416250107c60084075a5400000381c442e08141d400c1c0c041100d400400340d00c08148000c0240c8681c0000350040c04140c00845041402c0d0b000a400144210703e5800041940040031a050b0820079203048240094440e0481950148001025440b511601802c446100803803c4e04111480381444000e029204d00ca12110410b0300d00076001c0c0d840341c0710030356090344a0b4020034034500d0558110364000d68806c2c020304144840d0701c1c0640380c2204070f80103c2860400c08034000390 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 376561348 1250 376560098 376560103
    0x1609051021020a0318120c02060c07060305010305070815040303020c03070f0302060a05060901060f0503041104061205060c030601050714010f0c020a02011404081e070b040906061d0616050c03 84
    0x24601d081025031110f01d900c0e401411070320490310700c50079a80840740641c040784d550441c00d000b500c441e151503e1110725034008110f141c4206200000b152007407000006d01035a05600040c1038030310980958040560341c0c84129640c0b41c503140d0181c0e20446410105000078020307401001003c000704142c170f0502985e40c880102c2074141080950160b0010010001032049910840e03038030001c00c4401c00b43c1941824001000c0264124500c0b06125000020400f44810401d070355028540040c42442004c4e00d5903140410b107502d54030202ca0398420900829041c45110080d40c0c465401a529207003804800d80360807030800300c0441c4440c0295640e034002c402c80d0240303008603959090301d5001002540518070005000302442481c254004070140014811584042038069250448010050302901103c000505024440d8046040c111000500080390701c440d0700407200311242901e840c400e041c5078100700300d2805000c05080b030740a00304020f400614501410303100e14150041003101c021a0040c0d010a2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 376562598 1250 376561348 376561397
    0x1b0f2613150f020306040e0610120c0e1e15060a0c030318060506030f06040807030804020328120216061202120109140108160317070203010203041a16090510 69
    0x20b0342c1640000401405081600540d521005030300700600140c984622442280d081c240140c001340d52003504081d0900000c0040040a04103041206286040c010a001d62071500d601f60a50302080250008a845140c0380039410301a401500e81c0b450040e1559040391341d803040100407401c0c140e40b40040100f00c429004841d00c118030440340042c3c41d0400004140c90301e4803140d500c070a0350780004e0401001400550540c1d03802c03641030070070680d01c0c2c40364400241048155030040b4081114001c81d41d034041074403580110040d0007944142e0300c1115881341281c413815a180310713061040c101041000301611074007130b1885c5000a4800103040100341500d4408000c002e911100e9001e4480240c20603460030000c51600514444c801800030407400c05100ca10340c48140310107080307803038070b4200c020007803c40c0b008580c10780364010002c5650749000c1c0f504020003100d034426500c5944000300096507000c41c000d030700c81c4510440c0d00c1c3c80224a2405080040c0314040145000411006088410303000402c4070100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 376563848 1250 376562598 376562621
    0x23010605030714191b020105070f050f031c0b01030911090901021b1c05070b010e07020c0603040605040606060e0a21051c0e04020f0405010302070302011b0f261315 72
    0x100c1a44c6000385000b050f4500041e00c6885481441640500507a00042141d030100d9100c11902d01c807941c0750410a003050601c110043c2203001c00140507115014a1103551390111101c101084012071600045086076500381000701040c5070003d0200042c80c101c0c041950002407100054906015400c41103020703a01d070b58070400d1641c0800c84c015009451082035040906484c03601c241481c80390b488410b030803041072244c40c00c0000c0c1c80c0082800c40b4404c2c048203c0e5600f0180c0784564900b428503100000300f0040b1010b031102881e081c00070407414803810607102054002816545404d06105002c0821405c840794601140850f42010000500520040d200802d8818215040809403c400340012140e443c0d100d2090303104000d100d8001d001403081d034041d40e10a190050b2079410510303099004095030805030611540903500001003a45c0088480307160501559a0101e184820405180312540b100c1c460103088500000600d0261b100c0b40301885480c003591a01e41e042440a100c0030454106100e034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 376565098 1250 376563848 376563877
    0x20f100908100507020a0f08090a064e20040f0e0c0f09030c0a03120f0c0b0a11070606030b0708130512091815030123010605030714 58
    0x410100d1002e0049510b15402d207003040c001ca10f0300840080d190304494100070301501c8609500303c280840c090a440714400c001e4043d0b550306464020280500e80300c5c440501c8800e071441700158981200c10100b400480d510060b41c242d992031801100ea00381c0d008070120046c5036480005c41c58840f20781d04401002c2c50040109540ca070304140e95000b0070304040e04180e051003046814008084d64101c102d13202c821a14684c00d4036007885e000060700302011004025807102c0d084501005104800d414001c0002c080d8981000c050300300c2c44c0540d1010030540010300b90342c413207000180c0002e4203a0403816400c0884e0b801107144ca8000d2799104215800380d0000e0703a802007840100300c0c095402a1003503401c2000148082c5080b05103903150341e594581e10b001403211113804a01300c00f041e101c0d061040580440d02300e5000300c5190a040c105192501032204078401e6082031138680700303101521a058004070003c901c005440e070801030151810f81c8040e007090708000c24015540240956400980700001041340d9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 376566348 1250 376565098 376565117
    0x3070e090d090e0601030f02090d060c0e01030b0d11040605090a05010e0c030c0d2d0b130b03070909030c02062703070b0d1a090405070608090309060702040504020f10 73
    0x4441ca04400349100740248811000709100860480040a601680910707011955405a0240c00041e01400200c241c010b4407217480a4100030481d04002c0c40c40300c9941e14040e145601d00011415100a00b55080d040841e840c040c0c40401c40c03180c8464100b440281001c01c0003036030f620105401c0b03c0100c400343c400170740c0c4400520049142c20945da8100b5003c0b40c00740d040d41072019000100b44111110304049503034030b08030342d10040103480416045421400c41400084507400309100501142d54070903205c2c0d5030794040700c2c189a0b80b0b4442da2201003005030040c908141010800001402c80000a07014880c00c13981c2e20005a6840c0c000781300c0300002240f48040000000b40f243d01e82c00721101102c0c400c5d00045000c2c44020841002d552403000521000b15078010b0507890928000760081c0d019801080d04000c0000340540081c1000444501d41d0f039003941d650703030700c0c0c2c0c2c0585038081c11800f40d51002041085c0809880c240d0840fa411900040906544a80100000e03400340c00741030040b00461103048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 376567598 1250 376566348 376566361
    0x305030405060c2701031b031a09040f02010c0804120819030c02280b0c030702100606090b09130617010f090c15051902030403020a060309020f040203090a0203070e 72
    0x700241d00f2002103400d183c02c0c541031498082c606003002e820003550300b02c0c202200d0301c01e0f032083d041184002c0200342d002e0100c3d410301c1d2004000d8504200a0400e044040c9000d581508081c66800d100b01d03000203100c58540c1e0f0560044500b2035558206403502c00c0284000f16080300c85520001ca500e12a2569540d210495052604100c91082000301450300d0080130f0f201e081c1d00401c001c07a0b19258031f19020001c681c1c444184094560115000e404810400104102003020324010740c0545015000c44010480d8103d804d01900d60794080d410000703107002020828440000091700c00c00c0343c0104090f1610b517070010381d9012500194401c41000030849040b28400e5030038407818000c0040648140907180c090f4845480c516118815903041007040d03202d040c54284100c0c245c0305200d07240101d0f10b9811041e0b04000790f4076086800140e1080a44110002e5514042e10a040e103050340905100d00705450720040000a40009084200c10700598642c80b00690342401280b02428480000c2e410605048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 376568848 1250 376567598 376567603
    0xf04060f0f0201021e0f041206050402180403120c03060b070605010614090a05060703050c0f060f06220908040807080a140d0206150f0904030819110d0b06040e01030305030405 77
    0x1d80400c41035901c100b01120a2000210840c00083d10740b40580341d40b40ca0010100c0e007207110319408881d0000780c1d00d805000b01300f2142c0041d40a240210380300c3e07031104500049880350032401e890040108040c090340300040e01c0f85401112040c480c504001424035130350302090415600030501110115601c40060001e1500080030714046455002903034104034091022901e06030700d40c0a858403c09000c41c58004140c070071011a0500001c41c41030f070305085d02c2441200d41d114001d43e504400b1451010000f070040c240201a030143c941424024400c45a00e0641640106113490059540280030000882c100c1420401c0f800184040c030b00900c50f2919508082d03044402921130b46040d50410381600c5059540022a603806c902d000000e003481c07000200c002809100020340d6a0380002c0d145003000280f603041000c00e8030881c83d101448005d4801c030a591000c4401c4607207407200c001070a1042d01e900c1d801a03070001c0d22012000e4181407500c5c0e10303481d1384d4030074680991040703000480c000304000c00c1044c01e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 376570098 1250 376568848 376568867
    0x1710112712010f0c030b150c121219090305030402220e070e090309030601031e0209010b07030f02060609011214032a011a09060607061a0102012d020f0f04060f 70
    0x1600c3d0400a803400d140c0044d01d44045400ca07076402e07001c04507034641200c08c10302c8401d07503c0d1981e00c2130715a1203100d0907616108102c125a900d01d0000385c540d0034217010f40140100304800350f26a03103551031035680b907007040803403140780710b03002603d4004040c00202c00405108031840d1a10038401003500c3e9140c004180304540004111909030380040c00b01200a40300060140d06480c0e012480c1180f081003031102030400044800b01942c048544c20001406a9406004002c03031406581c4694000d1250f80050b40d640d10151502500030074000c00400c646d2003e8807a01804c0c500ca03030f1500ca09181d00100700c901e9070700900720441060326a03182800d0110382560807a10b50722041301c020700110b403034071505612042610b110180a90120b00000d221681c4910890728180c2d8451402c200b4540340807031011124181003030381400741d0710344450fa4480382020703a0000700c05103ca00743d01c481560784180705c901a400c0b510b0401c1c2070b00c50038008050b400b1281e9014001410182d0396131002c1c038000002c001d18900c103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 376571348 1250 376570098 376570121
    0x7081b1b040b1207060e030a06060b04050907052d0c070f050901080610091e0c020c09010b0711040c0314040803060a15020d0e0a0b041710112712010f 66
    0x24505030400091004144ca40c00c071012420100440c0d032000b0b0201e4100090424014416480c181d8041041c240010261041d26400e4441c81141e58810030251203034461440194400052284a1688440c010542c6200b1f00ba5003c070082c2800c2c03c180a907498445142c014195982d00e40da070a0009041140c550750062842400800650409002001d8030038000d000e007004254486440048030105a9410110800380328010450304030b114000a4840c480c4411540c4100103046c000201c080108044d80d2145401210a02809901c40c3c1000000d0000405800526031501010041001031282c864820390095020a649261681c10090400780c0d50b0818040d607170714a600b00715a0f6500040c0940d0075003150030a03422803610040040c0c0041410b500c10341c1c42d10b200040104030a07400c0f05403008000d00200880f43c20719048114542a0f43c00c4001c00714261400784542243c0007811901d1510030001c1d1003151190554920100314501c2d040030100246a44801c2c290894044c1d610a0301d10110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 376572598 1250 376571348 376571359
    0x4090608030d050606090d14030405060a0809010e0f190c0510091d2401020708011d011b0c031d0402030a05041104050c2212050703020a150507081b1b040b 68
    0x4480b0700107002c80b400014094061605541230a04081c3c0c02c104450103460f005000350703110520040010300e03030b4400300c610611035405e1a81c0417401d10000201c04030004a0031010700130304024107140072107014681d01d06884010f10752400003050b8881015002e90612340c0e50b100d10740c02c0e082c659880e00174044410b10358000d004807404c1021840810206143c0c0d0100354198415003000180101d252450540004600f0b51804c09000b212007140004681c9420f000402804040d101c9204c01907501030322100d04010072054404000041d1040341a858160f040d20455a205084140131030300700d030005c80740b035a81540c0d544144020b0100c044d00c01e80c0480812202030159107003079a01c101442c000e5070b9508101507101c02c05103279050880d240f10000b901c5000034000707002c1001d0030019642c1b0312512090b4010101d040c40070442042180f02100c0301000c584400b403030b00703010344d03188030080d400402c00110800c0691250400d4100512114950200590040481d02c05900800084804002105c1d00c0341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 376573848 1250 376572598 376572607
    0x503060604050d081b010c170c0901080417120a06080619020a02010e1606030e07120f0c05040c120506010905010806040902030a0b0f071407050a02100504090608030d050606 76
    0x994603401260180ea80030f6030a10030072121031600c550325004000ea00310205021017650380001205500220f5040084d0783c03507c08100d2012005801c1e510142c4680100740e2042107401020350007001c0054025102d40e5540403130101c101c07214086600a20181040d08100006014008003d4050032000d00f03012005801142004030702d4042c152000d94061001c582c0216106414900070740c0400d03602c0c3c0000c025161310080b080300d155980d2055010340008203103402001584004000b441c04181c85103400d42000c1082d86494072000340094107404c0f101c000c0d10180100b01c688076801200f440400c039442c0c04140c154035030008015590000d1220381004018001002a682c9c029403554016400f51070000d071503001070002c2f03400d03d04c03102406000c58401c00c0c240504090a01c4010f0310807419640c1d40b49100709494406005807064880251071035200051a8000d40b4062407040012001420305900c0d09544405e61403d072415580005c1450f000417070100c400d5600c1e401419446a0116038040c0741 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 376575098 1250 376573848 376573861
    0x13050304121407210308180d0e120a030f18270b010201020a0203090f0409060203010312121406060a020f0f0a06050a06051f090504050c0c0d0905060a050a180303050909070503 77
    0x10400035000c00b8003041001c00110f03682e6001998100342c2e01f480c8800742d8594039205000948007106500d45d01d4000c62415484a41040001c42c80390089036265540841c1c561210200711802251003444903440d000c15040000c010a0007030800d01c50840070703440e00000c584807644410881c0c140888a60659004001d002c071010780c0403080390700c40401102c90f6400c0808100c042401020405401005648000000300034005502d060020307134651a514035007142908404002a10005d50b040890000000c001c20303040d242070800b40c600350540d4070448406440b41d1042500d481d005450011490700038141010a014060044540c411420041484507900d0800400d848040c2c10442d06074a100c00740000020034401e400d224024000103006001c2c41c100221904215403000d00e6090f001d10501c801183d850b80204204003c45a0007004242444000c1d00250380e290301402c0c58008202564071078594120049078410040c50003030781e846031280d030000c0c00e2005020014100000b480b0050040081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 376576348 1250 376575098 376575149
    0x10030b090a0803160201090606030515100608010b0c1504110406170c0d020a080d0e090112170309011104030f030e1c08071e11010305011202010813050304121407 71
    0xb040780804d0fa00e004c3d0f0381203c0340b00300d0042189541c02001181041c40000038040700003400c40586039401107030012a01c40c02c02c460303028041841058080780c081c1004101c165000c1000c0c00c1d842080c803058816031040c042e000c10600a04440803641360f03102c904421841d04041c0f040202400e14030040c042034413002d00000e582d03000441003440c451041c2035070481c11500c4142d40c01c070051000c07134226008410419400362019440045442c080c1c200b400000500c0000e0007010000c0325006002c1e00001411045188400d0b400104009041d640318030740c004100110074000c1c40158020f900c0c540f41e0480c14600203015211030401640b045035400280c2d841c00080680d466031296002450039950085403030312004140742c1e0300e4010144549801c0c8101488130000303a18402038000d076001c00c4141c0e220248401c1c06080c0031806400508d4120018019424145906c00f08030701960440381441d54500c030b600d0840303c012a0450b40300840c40d08000f00300b40c041001c403024010034640d01209403c0c0442220 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 376577598 1250 376576348 376576351
    0x2060103110d050708010c0e090606030a0f0209030703050c1924030f230604110f090d08031303170c031f05040606050c070e0405033010030b090a0803 66
    0x600c1c840054803904441e40e41c042081d01c0c1250300100b0350b6034040e560b40035135008001c3d100e0080007182002490045a140c8109030718444e0030001c02660854030781540900c000e2484101cac484009508211107d8150b80c01c200b040300452292004003450f0000c01c052098624007174020500e0340001ca40c060003811110324214242c8540480f02c52038201104508802070115119582c480600d806600032000300c1040851341840000354a42403e0f803940c0d41444105d4030501c00500004030144003190740840d801000380501c800050010080c0340064688425580c4240d4803251541c404100c600c0426030043d482c4462040e040c0148a01440c03e00000c1c0c90741e200c0106100344190160b60500241541580130070003801c00940100003454541790090000d511118840c9818481e603500051140461002d007031103594460b01031818a5132001034901180c28144206c405410f800141508022171403410500c42c2403d05c045803209440c5007040120240054a01c0425801c800c200402292944040300d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 376578848 1250 376577598 376577603
    0xa0b0103030f020c0a06110d080c0d150306050c28021009061d0303390f1c0b27040b09070902031806160804030507150e1e0106030302060103 62
    0x402c0065000b00d81281440c00640115501411000300402c000b60b00c501040a900040701c1110081c545d0000169048072080b6549080b09000f04600c1210000c142c00c1a491023039240c0308489140e0f12036441b4000da580441d8481c205010124018043c2c44425031840104480b28416881709800b410b4004c4d2034496401c2403540c0d507502c0344240c00401001d6400940c060440d0030480d03000c40c0c214107601d1344030752080c3c0782015800501140382c170702c140301c244c0844103c840007108004104540480c0710030a4000a0603108415414400e10110504001c0140e5000c519540b0004400e04400704000800b220300c101203030f0000341c004108890843d880c0320b460300250000e8001c4141c2d500c0d442070034640651a00305c60081790000c8184603010624032000d060009900b8282d401c9680c945030038500380e0740c8103081d08000918800205005c03d008400600115008414110480042454101c1074400c0c0d010001c0c1705d43e0004154036040d000354a114200202030700028443c10b031550300c00035511742e41800302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 376580098 1250 376578848 376578857
    0x20303010e0c21070908153d090c0906050d27050601051c02010914030304050409080a0306050a050d060b060c0114070f0906140a0c0602040b0711030a0b010303 70
    0x200d2071002c40c14060302d1110255144083c0b016500d00c4141c1c510381015203c070350100d2060070300840e41c2d10012400d00483c4050300c070940300503a00c1c424450002071440c0103407900c3c02560302c0516114042014000c8406d04400080151507142070300c08021241e140107000100181010280641e0798007008a1301064003001003c1211001255111080001d8851020100440802003400c2020205039075048407c21110154040c458100d00c031200001030700028001446804107011880d50840c03060880342024040b40e0600d500d6501040881d002540c00760b503001e10200e11400c800c1c1d03140c000d0704050102590540c800c00d16010114446414884008080705d8841d0f440040f2034032120152003090107c00000d00c200e403000e42a9904565003910243d00068a1109a9906030b000d94802e500b00e411f1583e070140782410640642c842a0041e021030002c00031100c0300700c40071402e40c0c009000a0113a0207040ca40e0303080303145040c5400c0360900c10003078000e0f002601840301003070300c2a43d1241101d8041c00c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 376581348 1250 376580098 376580101
    0x5040c0e03240a0b030619090203030a0c140a0809040c05090a1512050c1207050c011d0705030c0625060504050105011701020c0d0e040e01050903030a0605090106020303010e 76
    0x2980c1000c4a0585a40c051040c0d52440385180d0298880e10034400c111089464581c881c07020503020f80300c04150050b0076900c44400701c0d00c0720080c0c4441100c41c0c0703c00000002c40c1d510a030700080c210b91086100100151100311440140150300701c0c542a550015001132810011a596007007075801030701c004911a0356a0402401e006001c2d008503520324000038030350280c0720f441780040c08505c0d084214a000080c1050748420350804280b085500983c002030800b428446103104030314000000030440400c00c60180152045018240074400320558009401955089174508562601c845c592082d8420740c01020b40c8080c0ea1512011602c1d0000c02610051030550b000e81c500c00c0e01c0c0b64100004081a1521301004180302041d449903050710200600c45a40d604814806400d034040c1094034507040d04621101d200e400c6c052006000740b1000900301141d80c828403c000c908581048070301e406035800c00810000d041d45184155008bc200803140c00900e9414000020b5a80c0414020640d04106110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 376582598 1250 376581348 376581371
    0x30504031d0d0b07030e0610091104060813060f0e0706020c030718020a020c0d03030207060c0306031a0603010b0a091a060f0f0309030403080304061e23130b0708012309010504 77
    0x200400c10b80d146c002d080f5a1f4500b010042c1c1ea400d01001c1c81401949032900ea095151546401e045a0844a0b295144d030304031b0721841400c4982d583c5a00b402c6458a9880030840c480010b1801050400c44604014001c840d1406902a00705042003140a02c2a00300803000e011030b0b0a10401882010384c0503000517220a5001800c2e0b00c0e107040320620310743c402c08114003401055803540081c01024814001440035003003900341642981c226000003000c00c81580071080c14026810802a80120010008134079200b58001248080d03106030030525005881c3d110004806007c50840a640c003426101289060222a01d82286020b41c10109204034400030201d44289010403c2d58082c540000072641e5908051038081300500a22660390003400d07145030080a0325038548109580d00c00b0030401c3c2140780d4100283c5400520004000003050400c00c0302000100b40107481c0c2d680f00d040c690301c98004650400411881c05591800070120400400d9507640e8181c40d0504114112442510046251031814 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 376583848 1250 376582598 376582601
    0x30703120b120a03030b01030209010512060d140309030705061206150408070b0c0d020718110c070f030203150403020d0807231b06090304030215040f06030504031d0d0b0703 76
    0x70440c1d640c800d2a8464024803440003142d0f02602030300c40d440c1000000342020040d0103074007811880501040c2c041c000b2440110481030b4440d40700f00020728410280e46541e036035144150482e540500190f101281c0301b03106040400603980900320850b8200d041c107008080201003401e006160500a064040e104402104030405130f4015150013420703651426101d10001c0d4041e0850781e44040c0074840c0340c00258000c0d00109440007581d07081d009040d0880c41e4880000054507207955103c02038001040191034082003440901c0c05800300c40340182c2000c5c617500405d07284c14842899026452100002d002c0000d400180888460515040407004e07659551015103161161007030901400b901d40c4d00d1003900350395101c020620000805c0641440150a0014541c0c0da50111707030202040c1d204000a02c0036240c4080e0740d000d02803021382c6140c82c154072441201d00b06044e44c0c1c030541c0402d03103c0341032004041d089910443c07061680900d0f46466103c54000030899a207078503024011115030001b00352118840e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 376585098 1250 376583848 376583861
    0x23041802041d1005160c02100f0e130c080117060402010e01030e0109032727090516061b0317100918210807050a12060308090a0b0c03070312 62
    0x10b200030703a840c464400520401501c0708a6120b2620100ba40c851200180105214810b0a4000d841118034015002054500d0031241000200340820101e0070381c1d0b640d4495205024034031030004086401c0c811004068103051040e0489010440003610704014210700142c00c80d8040d0302440c100204802e414016401002c0104c2e44440d99403c200001040c507401c40007049500094201014501e074410100e00000c3d0014014200d181d107002000c91099500b85a0700e588940d0b5160740000c4222903503507082e2030400703e500b5113500f5107048242005025080071580600340461001444807000c55640101049408400d14040302015404113414030401c1031200c02421030303210104245250500c042400c01d006040480340f004980441c010045810040d500450f205d68031080400d031074219003074030301e40c1051510000f0010543e1441c0580050780c0100401140606442660344d5825400d00c540154079822504d15290f042019030360110000040740c281c25010b181000340d1600c4000e00780050100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 376586348 1250 376585098 376585151
    0x60c030f0212091b011b2102060a0531061104062d02060f0c12010b0408100b130b031c050306011206050a09050c132304180204 56
    0x40494180da10700158142d0324050755424003120801840c01c8516003d001600ca1181c1c0000c000443c005040c006034080412124454090f251a1440d00b982108041e8051a045001640300000340b250301d10252160b913410002d01030700c545c141307110307050721105034180018030440702910410007c00744075180c1d1001800a4000d008140e8590390384c4801032080c540c0383c50113118200b800c951840d0907945c45282080305c0200f900908020f0b924104908104c0000404c41c04011b60108101c55880041c3c0000d14080c0c00d00388a007603107603400e09110307170b1400184500c080740551034004440ca0b19942c0d01502d40640c1c01c0c030500443e02c09401d001090404090983c14000c40b4071448854100701e82100256100d0030b001c1c1d9410158602d1703000b0503400d65085214085d0044034500d82070207460400d0b00040d0b8000b0401000a02d052150080a0300c4000c450344182085480c0c02d4101080800b4442004041d10045400303005002c1c6d2685024011111003000034400e40c0e403482c1040310315212541144400740b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 376587598 1250 376586348 376586351
    0x708130515090f1203060429100c080a020607080a0905070e060a0306020d05010608060a0317070f120c020a090e100b040e0a060509150f16030b0a061e030b0d060c030f 73
    0x9400e40500c14a13410a03a00d0350721030ba0500004041516400c080c02d2002c0740c542c000c11700040012000d1209d10f10010b401181040b0100900001080d240b000030000700304603500070546440d0442c0018130ba4400a09080e001c039040c03054560100d40000303044405d58a01c8041c00c2c49031346414000070964141e603440107000707178000704894070304e0b510552016040f1041ca0711758510a5440508200792000e95000c0280401c0900c075051000b9082003024000c1139200b590b00c4c242c0c501c00350325100300c4692818908400a4900740c403a0b800c50030310054450081019441c05d202c02c081820199803504014290340d08803940c3c9100e50b00031a40c0f10b13000b0050603180b2505459401c4034908126000e00411241408903208000b088641d00065441a42c4074419039100e0343d10340c2c0c036011000300c03040340c2c1107244104064651820741285d1b07541858000042080b610750100074181050680403400c1c100034040c0515140000303030302d061f4452000d41409070340d200100140300e000c141000e400500340e081d10180c580c3e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 376588848 1250 376587598 376587613
    0x1812030c120903080105120f0d05160f0b0a0b0a0617060a031227060c02120109021201090c0f0501020309090403140d0b1f090b071e08030708130515090f 67
    0x254101044d82d060f01d4007070707800c51600c0311402110f80d41e034400740d070f03a40b0710369800001106c4019208001070003c11003048401c107070030050358480040d440c0c005881600d00003000030510220b94070350312032140f01600c01da0b91007505500d440340183c0101d45402000c03c0c5e00792480009542a9980b241c010041c44c0d0202c487c060702d1604c0b20f0020301c2031403034500711050380745108144e40030580e2108410301212165510b1020100030b5909120500c5400c0500030740940d21540b82030300594540824500c1d4180082c000203051040c0d0a0842802200354800301181c10342200611103640c0c04002c07100d4941c0140e503030400e00d44891030704072461352440c5c40348003d0380e5021800020351112074003c4a448041225140111815405146200c155070916070000c10f101041c10000d246148010f800b80c1801031240c030380700501c400504040311081040894803003400008104982d80c1010003181c21007182c501d910100400c0346c0d21142e5408143c0320070700b0341040070000216409020040c00640c4030383e080540b443c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 376590098 1250 376588848 376588853
    0x30b1201060909150218100513031b0b040e0604090f050f1006150f0f03150306050f01170307030302130323010c0212041403030702120c041812030c1209 67
    0x8040b1100f00300c807000540360075510803c0c014003d80b00e1440020815500841c007035001c1211580350b081e50b076130070320100388010000c0d81c0440b145000110700172a110b01c000c951030112004604d1040d00a081c4442e8180000c0c01800400160558880f000f910006690704141c2000200c0c00c00303901000340280300300300141c1601c3c80701180074460410380c01d400b03104094442c4644900d46181090403000106c0015000004078441d24070489045443c1c14002092802c84041c000001d800e074005442441d221414000005250003c060040003082c030005144002c131850706443e03200303012010b000c06d0380101c0c070200316641d011203000080d90310005050440d982d50100802c201516030003020254a0007101001460010602004105400301118a0282043e160b5243c242110800d2501480103100c518016111904041a40d010040040210b50040c504000958030701c8403c010313102d6403580c60760700010750200a5924030070031410049214411840304035035003500e90851010309402c0c80982000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 376591348 1250 376590098 376590101
    0x206011511030703051806090d0b06150f03010311040501030b01090b0604050901231f1107150c290103020906010c05060a060512030f03010b0a0905030a12120e030a030b12010609 78
    0xb407880040380402c6c08503400c0401170280a100e102030b82211030380c1d040c0c000150100d0181030f403020000b410081404c03004c02c45200284c002c400302082c0c0c244000700510500c4580400c480745030804940601056042d6030f1890940481032041d840e015032142c1428078103581c2c0c07400780c401030140584188180d60307507803e031030981c041c00180c0f40c1206e5416030745000840c10300885405410b07140340c5020196004008044034060703140c03040101d4a0045481c0402c01c298000490724420200385d0729504094824104002c02c1c1a400d18801062444009441141c3e042035030607504403074041700c1200c66641c40d900181d411628403070006110b4001c0c0420485004141d038403e0040d20310580303402c0c03003460b200c020650b901d10440600c92501030701400104a1103160800400072480c09107418207511381d8803000f0900d4211541811034504011007103e507681540142240900306100f1401c0c4010740b0401c60a6442e485420304080401d52205030a01242d01c40f84000e81340b00310310700001c101c0c0d44da8a655000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 376592598 1250 376591348 376591357
    0x70504020720100504151205070207080f011407030207020d0c061d060c0c09040f0f0302100f2306031509010b0f060a050412021f080702120a020601151103070305 71
    0x1803140c4002c10100065090043c1e03001040030043d02c2c0d0714505400c0030b00003480c0140e030341c88102c100308510304000c41f0780308240500703170003020103400a0011604001100e410301c01c4490161469030f2401b01a14100c8003143c071010340201140c14010390f00d120301e0002c100101041031010307006217100800007c43c1075000c001011714600707840d001d13103008a8410401c4520b0ac0313000e801103640da001203c031201074a0b0101000360040d10541036501c5603040c030703659507100c03003880803041c0c0150304020900d50a40c00c250003922181502840104850000401a00b00e0039034004140402c1e105078200207003080c2c500b0049401a1003c2d8a40366401d0b05d41002d03181c2c088e00c18404903602803c071540c2003d1050400c602035450304551a102d00e411b041c18103800c60f20346601d803441030381e000140c100000461030002c041101c031051103582d8040d5070b141942c0064134104d1000303160607450034100500c00415501003400b505590f107401100c44c030042d90030000c503020481240c102c0c0340e0340800102242015040720003003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 376593848 1250 376592598 376592633
    0x717060d082a19061505100e030c0108040317150411090a080a020a0b0f120406020904060e06060f0c0f0106120b060a03080313050a0b100501140307140c0705040207 72
    0x81042d6841070203507685481141104030004084180300b0000030b400e64009160100ea1089401e480035541c80c00605c5d0700750a650344001103107112482c4489030406100d010302c588000e0802d600582010350300140f00b0380e40d000012820000e4035000c9403070194100c2e01c0000d81207009205204d200102d508107042c0717a20030000304d4030502100c580041c0345078001c201c0028241c0c0040003400c040d441c0c505c1c0340b01654811221407038901e108110820000700144410341c010741c000d0702c00584072007200040c00300300d403443c0c1c1000c440c2441c15010003103103035a80c60440321001e45403600e65072100500c00307050340b40404210a200841d402d140002c9503040c80e2440c100c0c0040d000c1c92251200b80c0b0380000340550401e050201800c1024104001840260020000007017540301e1000c66500d4030302074944203412602070310041404075401e1340c20051076034445201c0c0e5004500101483c91803c01000142400c0b1103060150030507100030441e500c0005043c020f440003000b01607c01c4d552400c0d01d141004810162400a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 376595098 1250 376593848 376593907
    0x6010e0604021605071502151b07030210090308061905090604021b0303090a0c09020307020a030c030e12070807060503090d08060109090203040c15030b0a05011b140f0c01080717060d08 81
    0x112289400c104c482c0d240a44224120f800c209c030300e04043c2000036032191005600798414190007041d1410907200b509001c500903540c47c003e03800c6c28004c014038400006115407090800140601003956108400e40d04a43e080f0781c0140d80f040c00c010545d43c0d0440c20759120601d404084100103114402142a2803120310403102045143e445044202c2240000e42c0d01000580c8070304071203000640610884980d4038000d0074039240c030b880744000199140d400c082d9071000b15001490200507290040140c503000e071126080907820f51600301101d03981c94100c03401140402c00501d0110380f440e4010301d2014054001a2419903880c54542803002010714503126004400340500c85503003015209118048450400500e04071900385400c3c01141d00f00803030103601076004c000c1e42c0488002150400d1001c003000c104c02c040c15005da04c03031540608045022080c141806000800c100c200d175403200d440758404114100790b01040e2a00c0c000b06d5a0901030307075001040e038800003502d500e504da0f10000c00102c4544c003210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 376596348 1250 376595098 376595113
    0x21303050a1a180703030309080d090609030806220507110d09050a0608010b070b060112020a180609030b010b0f07080a1806091a3f060306010e0604021605071502 71
    0x200300c03e0000c02006100b5400164091000030721903041188041c1c081c0003450b00304640e1202d400216a5240c0040380c440d5070764000c003001c268101e0391003540680e04580e1a450070a050640c8204081080c60520071180e940000481740c0c0d01901180c2e1113941c1c2031048030b030303890740f50040944908010300620b4811800383c0c40019119106182441c16103904840c41c909140c103503500c1072004400642140d060110b00e010060510000d440540000092a0740c1d21050b80c1c1c0d145170b0002450403540000040180d562001d002042108441c281140c0c0752001150b03450138005450311036402607600c01042c0c4d4000107004120302d50701101c0ca40003100c61040745044903903a41d00c10344903190f02c3d00c160b00701070440d16856141241c4200150000b52280c98a2500070400c130714901c8040d1441d9040741403035402035801c0c1040c0b480b207009000e074000b8069000380500d50600400e280ca032180240341c4c9108580000c0c110303160040c2006252511a40201150041074607038005610340000710240900610030980d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 376597598 1250 376596348 376596361
    0x5010b0c0f030a1b0f140d0806090402010507170906030a09110f030c15090603010801020a0f2622030806030f03070b0115020708030d061701020304030e04021303050a1a 74
    0xc032003012080e81c956810b42c01620302e042c00c1c281d0340c0410554510b02c0f4a503080010401e0810414125120100580204000031f80c010703148145c050110380c011004c8604100060740c00008460346550424905084016803d01011b201c0c402c0320320306900301201105111001d190740d0440d0060390721420303103680882e00c0c00041c002442c2c0040b01590703041c0c3c080444400141801c020320f6520070380c9403009030300d00001030700030807000e40c000c1e80002103903940010040d1150350320040818103074907a4640000044012503240c1b04030140c03041f40e0a110020072010418095803000c0f81c1c0810306c0b613004000c1c5083c8050402400d070500442e40e0714040e005244083e100d03200040100c42c8007075072105541d100c80c0d003030504200108066030320250030351269070008201c8000401c090301c4855280d071000f1070094102004040111051140d4010b03a0380107005001c0000e0304585000034904013034400680f0395040d03403503000d03a02c0709540c00580380c3d020700c0d410b040502484400d20810135281e55920301c250b03110754 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 376598848 1250 376597598 376597603
    0x20a110603070e0f1305040803010321230c010c020a0201030f0b1c06020708030f04021c0302030a0c020f040c020114010803040f06030b0102070504110901090602010b03071806080105010b0c0f 84
    0xc468030302c002401e030300340b030412498088061020300401803d8441031240e101c11420803180146c805444048001c4010010401740304816441d01da280142c03400c0785205020050044c0098003c403101400510001d200705c81c450350107880103441c2d410b0080c410b4a49244010f512102014416400a420407520303016005e15402000d0510101500d030701149440d05682100d4800700031000c9a40580030020040840d0301c020140d4015081c960800e140c40c00c0c00e10400803c030942d0f07011211300d20b1500c90392030046a0040240c03401604203007440020443c01d44001104081d450100315031091a2501c2205c010781d0541c40050211818200702c4100c0c0d0300c0c4c41c1b181f55a805248543c044024031050144003440c8030742c018109030072045c01200d2105894500040c01d0b60720a0400c01d464510204102d040c0f9030707121038000c0080c01c460008100101c6200042030301c8003151302031310304040407400c2c0c1010500d6640e4400d8004000c042d0080010356101d2400d1440c13a440700411a02c2880382c2e012107105620003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 376600098 1250 376598848 376598851
    0x110d0f060c2a08091801030b0a0c02150f130b0a0c1209080915040f15020c04060602070b1606020a080115051305280b030a0608070b0708071b06020a110603 68
    0x26007249000d9018036900c03011144c0c00401c50f1030700050344e00500d5441e00155200c0c507010f5881382c0da0b051a145060140c08040310300b4240d0407001c65101440804038034924001181c4c00880301c06c14071025580c1c1c0b50705048052903400008090300206020055840070030b0b4020001840c1729035684034910400c090410a50f403a10002400c4500100a42c200c40d240c800844440c01040803410350405650307840381109517070305170703c44107100000008900c00c45905000c0355003481780c103c804210703950a04200a50301d103401c1c05200b1401400142e02407080070847e903200101da903c400c0656440c0da0014004010301c40070301c191000da0f0003520810103024060001e036003a080b9248a1842e04a2800e03080200c44410854001011200c08010a101034000c04036007001e801000c6403941e6908010b20040d00300d50060307020006542084405001c0802100211240d0710341145d0b0107070319a810b41c1041160202d0740f070b5018401050b445000100941c012078452201405910001c3d0150b42c46002d02005110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 376601348 1250 376600098 376600157
    0xa14130603050714041404050f16050f0c06011d0708040b060105090a0302190303140c070e070e031f1104080d1d040f2007020904110d0f060c 62
    0x58048050110500c0380d0302c4281d101e0881c1c0f502011141000c020021564099005030080b031140440c00f8100f402c00d0300845820081418000c0c555190040154503481c04241c3d011041100010f01a084450003c055030000c0079980150385d0340e565100342000481e100a851410446070307110008070240c1c001d04605100ea600465404020343d41d0000460b050fa01c06043e1a50020b1015000f00243c0c807a4100c1540300c601c1d0283c0c0605442c1181070152114000060020001e0380030042031540f8400465580219400c10543c0100c43d201c090080c0c6a8410380c2406c6a0103105da0a400c203060300348126906682000c90404101c0a00300400c0c0c1092403040d8015054107520240020b10001e10070340d628048031a81c2409440b207642c42c1c0c0c0019040c3d4641e452100e102c0364984400716404d4404840400c4e90300c28050406181c42c500e0380c0441d84c503600c01480078010002c0c2400008072912a40c0c00c0c1d85440c1e50006010131044e69601d0840c000b0103450b000c0d10f0000301c0d0203074220042d1813444200d50303c003030703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 376602598 1250 376601348 376601377
    0xf05130b0117042405060301060803040501050708030a0608010509030301030312091a070c0c081b0402030628050406150f0206010609050607050106051207180c090e0402011e02030a14 80
    0x1d03008421149050380c007802c00c031a5003100481848050852018131a0008100100454582044000c05094810756007004240d50400c00c800c00c15680c100044641203640301d03000396102d95824200000410490b4400c05503542000d00304081120044001d5059a1090f1940000980403200030000c581040c84010100c5103010000540841c00d222240d512800d00d02e00200b01035911750340c084248190b64004002980700001081e2690904c5841d40780080080c0c4085055292904c0010541104e006003d484101d0700a049408084591800b5014000240081c40075603510f0159000b0709107203440203400223a9081c990342c4014030105009040b55100d45e25000c1d080e080c1070400c0030300c1d032083c2000c461a650300c10001849880e1840c0e440100e031410406810054030f003034080350082e06041010007489203840841038984d50010300f0001501d9040c0c0b10391410355281d20058442080710f1080000c81c68240b00100c80c187d0780003005008200840c1e80395041d000c58982404014020800011100e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 376603848 1250 376602598 376602617
    0x60803090a1a0f0d0906090303060510051c0c050d0e07090b0d020901090b0f1f0201110a02060705130803030f010315140f06010e060313060b0d050307030c05030f040f05130b01 77
    0x10803c0c10013600d4201c2421000280405640e551503049800f4014224082074075540d040045107010130300300c654400306041883c50507021054030303110070080680000d412640c4100b009500c600c40c1e4251141c640059900b007181900c052001070303403111544a07005129040c5146484e80c2c0c00c1202800d40039a9015000c1d041c6642040844409000c6000509801004204907480e080d07403501c00c00009200c03801403588420050030402802c1d941700b42c0144440c5002006910712042d070001c0c80a901484918101d5203401c0c10070341c00101c00703115601078582440044188500c9410703014150781207038880c15005000c131500b219040d055035402e54011050018079000514482d032203000f0242d100605141803004c4242080002e4240d40054555901c01d1080d07091620400205119040b02040704403003004134000d059940a07074a00c41e03984020100b0956141400800c0f10030000d0303800c0035130017018290700ca42d1103121002c0b8503a100e11516114041040c0314108000203840744142d1004e040c1c0d80e40820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 376605098 1250 376603848 376603867
    0x150f0b09040b062502130612030f02031215010f0315030b090a0c060206090601090902060a030e0f1c03182303090d0308010e0907060206011a07020301060803090a1a 72
    0xa000e042402a0030810401040070314024120b01c8020140c600b18200d5110313409030044c0034003007040319403150050b4641360060001e10303110300302c404406034145414580e03064001000c81c218014001d03622000f08021050003440940c81042c5050802c0030391300d03444030080006084081d0b4006500900190100c500309102140d11105650b80c82882e110444000300e49951360000c40784580e5000c0b5006030001818400041d4080c0840750042031001014000d1501640004040c2d1081a90394803c0c181d481c00101c0d4003000030f001d481200d80c542020f80b40d00c4200715140c240708209141c00640064505650307603260651044003c2c41244e08071000070b5a492001400d0020341c845d02d5445411403106001c51042960384040550b80640b09585080d859450500b214006180c094161a41600148030038452641e00068140c1110120408082d11a0954603103c49511840f40d001c0d40550900d200441c81000010003820050f400340c510318031142da81d403c0d140b0010500800e00e24a00c00401c60801c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 376606348 1250 376605098 376605101
    0x40c050f010203040803040801150f0b0f0304050c10050a090f0f03080f04030510020403020a0503060613180c1508090f0c010c1502030406050a0e03070b041b0803030a150f0b0904 78
    0x1030302006004891409888204207461a0405d510a85440c1c7d1582460340c02d441c071010001005106002c028103083d4180840c0b0350107402106080ca102d1140840090140b040c00c000c8000c840d00082c00b585141d600c200320040c080d03445100d207480407400c1c1840c0010400746006041e821500c0400340c41c884c00b400d65880007007944c028415400b5205040c040071022940c04d001c0000709210081c0016503552a602c1440701c01c0104d40c1c4030b544241c02000410030180c90b9512103100b11804088001160203480f03201040041d0700d003074094100880d102011640c1c1c210801d5040c402081910f480060342d0310420059581d0107031207841e102d01c5e00813901003c1c0f154060200449a00d10850034082640410020742080381c000b100c0c15500180c944080c4071003c0042e11568504408030b1028510b00100340c0c44520f49030001401c000c14914250958000c1c0c08641f8420078043d141071410b4036600c3c20a00f03030382c5c00903000720301007490341240082e0b00080115104112104880c080500d460610404008020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 376607598 1250 376606348 376606369
    0x140309060a111303020f01110303010605030103050709021206041d1f1512141504030c03080703061d10120305040e010807030209071101110a0302122406070f06050403080105031005040c05 82
    0x20b051003a1234000e40e2400e0010b0014501038a0507030380710390300c1e980f65003441c916000e00b40d40800740051041001d08100c00004ac40d8952002054501040840c0c0003400101c10113a20300c8000c038070b8020a008492001268407603c0313942c0c1000f803000c0c00030f03c1d41160340e001d6061082c41003241c02d05220380354500290041008011401c000016140101d0f88003452000318a0200e03012400604000f82d880c00300764006001a822a03224074041203001d080c480200e040800c05501d6400c6c2c2c04c00000020f00c02d0b281d000713505015180000c864981188149009000307508140503c0109440400002c102c41c0c02c0014220101ca80052107202d00d07031203124095490781b0021000440e50354907002490044005200184820740059400503900d500b0000307801008480501140380c848504401c1e800d8980c1000c0d4522003d9a00300d0f03403540d440c4024900018101f1000b00020f2205080100b00030038182c120603464101d81096040e00c29601c046850303035044410032980204240541001405181030142194 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 376608848 1250 376607598 376607629
    0x150519020304150f020d090609180e1006050a060203030420010315150f0e130b2206030308090f07031101090306090c050f12030f030403140309060a11130302 69
    0x4a160984441d1103d104105080e00040812001d000901c42c3c1503040040c9407441d038082c541100d40900b4254010852461440780d8024004252404080741c0704a0707103c4400f03089418111040503868071244ca010300024030803a07100340403c0c440000c01c0750002c41220b10599225125505101272502546032030440d8002079810550345e0019111030284441701c1c000034140708d8100912208003800024400d10b843c00b044000c128584505152740e4940701040c0850251000d03002c62480044e102103001614000c034601541c40da10184410038407010360103142660b020765030b03000c402e03900c01801d5030355095005082009540001c0d801c01c041841c8c1508180c00350380500d80030248a0b0340380c4644054a41c02079082d100082d141c00e08120b14600700324448504032050b140c40041e0711021840945901a1039004640410700000050806120b41e00148902000980d810f40382e08041807540d90b80d1a00b26005041140780c8010841030b40840350a0b030f91a028102d500d8140c06003141c1c2800400d41010600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 376610098 1250 376608848 376608853
    0x909050a06050405090c04200d0c0302130902040602071d040b0423030c0606190e221b1a04061407020612160804150b0f040509070e0115051902 63
    0x4200c903600c500402c4e000300c000c5c034000c10b0310002c008100401c076040724031419101f00100c0180c034800c0c2c103e00d05891005038405000519491a240c0940c0a8425211034146600ca1031a0205004295034058029210560308450000382c5500740c5c1d0294101550f214061b032000240001d001071212591304d6803141c440c00c030660701e01f4240a0109461924090030700d90503000030403000d490500420615034805402c694104040c4804100700344000494000c03402d0b260364000c0003600489d012100d0044c9441c9a1990304030f81c01e150300344111055800015000c2262200c1800648803008000942e003d0a10f089100d1500e4603040c4199000d030011a03007040310240074131007580540d4a840c00303418140c031204281403080c545283d02040055201c450700c1c0038400a0001e020201c2c915850082c4055042003000a10349405c1d0700281007112400d03052503006082c442080100040815110704644d6511003054840e604c98019018080b02030707040305c00045043c4000750103c00343e202010400c0f201c9005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 376611348 1250 376610098 376610111
    0x90e070c0f050c040f0605030f0a020108040f0f0b040f0308090c011b020f0607060606110f030703031e0504050706110a0f021c0804090207170a080c0c030c030d0902030d020d0909050a 80
    0x4613040d101c41c560460105580c5070703c2040141003d02c04004429005400340a0000490b030010340031780d5025001501c64030b650315000702002078048202c404141c00034283c401c03074501403401c8a003048100300e04a0000f1000008184034071400a80c122403503105840e1f10b14203001e0315015107900c0f21580000d9078810a0425813481589548004000d25802803501140d09800c05030054040c401d503070318085103a80310408114960b640801924009545841c0100ba8090040910a441e0181050003148145004107020170014005120000c0301e40036150170301040076030b0007495150400b004000c1e00b07094144100074018980020f04036681800011155200c000301e8540b1101900590040000d9903400100b00080c455909003442d1524030440f00c980c545580090002c1a400021340344544510780400d0406c0c040030705105480c0e40c10202c6044a4070f03801281111409000000c100f80e00901815a0910003035201150001c18050755440d00c2a12034138101100c0018070000340300120441c2da550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 376612598 1250 376611348 376611373
    0x2060f0a020909131106070309090f24030506060307050604033002030301080105060a2402030904020a03150b030108030a121b020a03092c1e0f0403090e070c0f05 71
    0x51842d4000c0c0c4c400807202c540180c00e0302d846500300c50356410036846a00c0c00c3c081c10000079401030446007074400003100480c400610000840241100141400311001c0d046003100280c0701680c2204100d81c0104c007141c03800d8655030700313043d103a4119000741508018200800d00118140c00a80244d0460100c80d030703040b0b2041020308280c1c0b03490f000b0b00000140c000200400c10f07181e00340541c540061048407505c444a10788000041044c04840b040c040c0904800d4107442c1c0135000303106130ba0000c000600155541c9100100040080040310751001c0d18581c850300106120000d0b0081d40e058684c1c0c00021032a1172904401070300c04411005104480c40c0e12191000d00c200f0562100300f1541409800420a901c598600980b00c001103420106c1d0703e02c51110604444e01454140c03c010520381c0504004540707802c641e20462428041c00c0808540289051101c02c501c00c0150500c158029a01c080aa94949030765810845041d43d8000000342200c00c001b0100344c820000f0300b91248250b04035107002c1406c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 376613848 1250 376612598 376612609
    0x1b0e040e0a0f0c0e06100f110a080c0f011b02030306120c0a0b0d18080307120b0307030b0906070c11060d09140c0f03010b15030910020f03060f0102060702060f0a0209 73
    0x40b142128154030601c03003001102c01418005410160482d206105442c52a00040022400c000c103401007007842804a0b10707040041c0b00280c0300740e82002c25560383c1d0910b01c4040740d40f00300b034002e0040b02d03602c0c00b03200802c00f94048000390a5220f107940550700d15110b030360820008003110046a4018010710381020266610034400c2030003050404640c0e078681481420040444616500542085c1590003506002401c0f02046075408107150801e5441c4400c148540002090704455040d018440c03684c02006000560120a124002d681c04503982e50b50b801c45e04403402400301700c000f0051a50744004a200346000c1004d400b851507489800038008005d070b04c0d000407003620360607410901d400111b800c203400d052100070f181c8000e0068009000320250072000c282d00c030701009900e4603507007000b0010a000c04014440c0c4003000243c1081503403111981d200307a5003254000d5802902c500e6041e001103005d9400030452030311503842c54002d46095560544440a0154020041c5001643c20408240d240d61007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 376615098 1250 376613848 376613873
    0x507020304081c030501140d03110705040f050105031612080a03020904021603080a09080d020306040608030a05030f130305090405041401091505090304150c020a050a030f02041b0e040e0a 82
    0x290f060700070110010340e80103003c8510680081c4492070028003015070342d0315030804040849074146043d40c421041104600d043c02c18907008a0350060804001d400b0008080d00014165070040f42501c61800d00010044c2241c022480340008151156141501090106d8007804c0003100c03905025260540d100001800c991200d01d084440d04074a50110342415032100c3e0341030740140365034804c2148044a840f079252074050200c030360741504c0e00000026482d84480c0c000b10300030040941141d071507009090300030b00650021509069641903d000180000d000030752800c0c2640e41644032240361100c04814000038200003842541c081d0b01c51851800c0044007440740401d403030702400c0c0907203140d034030b10039480700359007003d00300c00b055038002e01c0280a0b128019807031044040d01403c104071941c070a840400c3c5400e0080e0f00c542c0e80545403000001c103001e5042001114948219020001c04141861104401c80c0345120340b4000ba262001c1d07082503040542c84006201e04080454401d080281d42e05c8000b4100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 376616348 1250 376615098 376615123
    0xa0b0c07050a1502011109010e0f03070902030108030d0b0303070f030f030b030304060f140a0207120303090b190c030515010c051504050a03080109060503060a02180d0501060f0b0702090604050702030408 89
    0x90320405960f100d542840b03105800760207010154500003400d0002440c81e980420564400c890142221000fa031701001080c000b01b4180d84250740380e41e0349101c0f25840e03800c031040300340300c0c0c41c01d207006602a880d0104c115100c05500203100e0070040501c0d20704680039400041d2000c185541c601000e01036640c20406040200456039620f440a103900e03000500c015901d0392214250780d002c1c400c0c8004950085040300039103031440081d03042c040c1c0c03a0900b01c0241803a4013001e080c096240003800740307840c030003400f846401a03440418451004406004c07011944115100280005c22146010082d1311071100045158041c0013280c0d1034410982048074a40c505031801c40e481e9000e40322040425401c04480c900421941d001004000e1418003c01c0d01c640300180842c1c801640083d29641440c0b903180c001ca03035050060640c0d1400c0105140c06402404240150101481d0303414000400043d07010403a00d10541c00303821000e5503140ea009110181c400503180d20154007080c0070108804000b0041102c00f0072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 376617598 1250 376616348 376616369
    0x20c010f0e1c050f0304030f0c21090602060405060c0a110f0601030209240d02060c010c0806093403090209070e0406060311090f190306020403060c020a020a0b0c07050a 74
    0x10b420692540c000002c106088042c080c040c0103a0542800d01c6050340d03031040c1c01d402e04501c802140101240c900c1d000312001880e0f0b041d0b100803608851101c0d003c0900400f040d80712220f060342c40303036020b980c0c584088500132b000ba4010400107c80c0d10b6540050301c010402d904000141c0b103001144103080502414101e40694400c100410940c03030403520391a002001761a950060320b481050300f80103060914140b500642ea1040310340c0031034030350008613044a0b0303c1000822511000b074400508141041e184644a840b100012403401024940c0e03c14020052542d48801d4000c83da20403401d103100c4405500c1419074404080b005030300c2d03100e0860f208103241c1e07442d001002c00304e0040000315046500020101858280c1d6034802e60043c01c11100e281c24112603260900d011100002d11000e60b985245030381c40d84c80314000007000410380140c02540c0c40340106110111000304201da58408401002e54441c0221604000503040c100042180d40507441c15281179548034408194102c070190701060258 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 376618705 1107 376617598 376617613
    0x24060c020a1a181e011809051003050d05180d02030a08040902131d0609311a1504020a0207030f060b01110d0210020c010f0e 55
    0x41003500c00400a154441400002a4112103c4052103040c07030710300b400d943d103010a03e13540440407020f0003035054048400111410700d4811034019144036074140100305580c0b6809020311440c1071880c404c00d8541740d4034003245011582200481044414482c032400c424000f0003140a901089403216100c440d2400000e0600f81d00e0b41d0700a210300c0e00041c00187c9044550040d0170000e13529040c40303c0e415903580c81b139400040203140d00120764100c40000340480c680804c1c03072038102c1040601c101210700c2411a00030100d84201e2a01c0c103c110b0045120200a9a40310040a469840d01700721076a00384802c20390341d007451607800f051003142c01040c0454264820071002000b190030812241e6010528100040180b0b40494010700140800e407001d511020001145246041c043d0300070010031158041000007900024121240da5481d0b000780342d00310308070307006801c1080265400750a41 = true := by decide +kernel

theorem cover : BRFrame.Cov 376438848 376618705 := by
  have h0 := BRFrame.cov_init 376438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 376438848 ≤ n) (h2 : n < 376618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
