-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5345
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:33:57.140535+00:00
-- url     : https://prove2.me/submissions/826a6779-f742-42d4-a78e-a46001fc3a4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 961151079 ≤ n < 961330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 961152329 1250 961151079 961151101
    0x50f2a130e0717070f080405011b020c03010b0405010b2a01020f0403030813080f0f0405190302090c0f070b060d02040903050c07050a120b0c0c0d0903031106041505180601030602040e 80
    0x104c4460005c61001e100b0040114480d44841d87d015125800009041c4800c5800c4d15441500c040c01d01d00580c0626000000b40c1000e0150b030070221003d031740c140003d5060140802c0c40d8001c4040100d024a1282014502d00c810001c00000103072001000f1503403004000030000e0644e01501003580420000760220310240f81190440131103d402101c071031300f41408014406010750043c0a1460f401405000101e4559a54500301205412480701c0c900007a1031031040c048012802802843c14101c01d1019020000700700086a0941d544900c004c032056582c0c00026401c4d405100c0b000e0b410070314028401d41095004001400c840e56108111498a40ea510070000510b0750f500504000703002410003580020700060890341c01403000900c160504a07069034641c80c000c0c1041c450300020768910400c00506810880903841c4030010342c0a010a860180c80d500c1c425544030420110403940d80000a1600c031560f80084d100400d24020341d11f4559403400c00e44040d40150065440400422003c50751039060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 961153579 1250 961152329 961152331
    0x30103170310030602090103020403020a0f030b0f01140405040c08031c0b12030f09062502040b01030b060a1413170705040902031002030c1303080c01050f2a130e0717 73
    0x12402002c5201402c40e619800607400c12021079040c036030244008801681c0b805007400c05860460740c82004903140d4240508140800f0b80000c0b41110030100601115180050a440302c082c16200842d103510380b0319008000400e182c2c800403036404041102c0d010004601a903540320142500705005030900c030340401541085d280b520341903581c41042841c0400b203417030010380071034203004000d81c0c10090714041540a030460303c040c02d510120704900c1101185401e104142168100307107000c02200c0a494007050b480d1088a01030320900c190101e2a0400780e03015805c03200002c40c0883c04070229513551022805c0728414840c0741117640100f10380070410341410321920440680040003081c159000b08040c41c02588080c01c40030a03074034100281013001000c140a80011446105507a43d05d26004090130308461000d0020f50b0f0b49011f041c18800f940b07003102c5a0a02034003038015084076100d0b28848401951040c220007100d030b8103d41c40c0002d000f080054406126890b10b0300c07205595034000201400c5244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 961154829 1250 961153579 961153591
    0x3030c170108030a23070312050c0708071b4403040b1b011a091003020f0f01030f1a1206011a0307020a050a081b0105061c15060b0301031703 62
    0x1c0180599000d151154102c01d076002d0021489900424103032400b85c8050380b14000503000f1404184c03c01c48200300784d12905501032141032006007480c2c001e039030ba05036034810048060440c03503086003150711800c0b142c081c403c0140801d50706121940e00c1e0012400c05070221402c0703a000440f110101480d070061440c00c1c0c1c0f40e00000750010b907241c503040010802c4550000103880b2404420b5201f4507840030424030410490500402200c403d422000040210301d4100400801c0c52003504a410001038a40d200a495242004c88103a24082c00d0074004030001c02898003813400312030511800404125400d6011680c1b0302d801e075040c407171104542281c0c5507100420700c0703081042c40000360f501e85400ba000d005550858150710568400c86050303110b9510f8068229429900380000003038201c0928096070701003070310741a400028050307460201c0009411030001480c000c0c19405066010341003080c0300c4101c042c0f40b9100c02d0f08020090300c0e4210a0380c02d4009000840e60507802c001040c216590080640744945 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 961156079 1250 961154829 961154833
    0x150f0904052d0d02030d0507020c10050906090d150506030a030c0b07090909030207050901080f03181801031113020403020918011b110d050406051803030d0903030c170108 75
    0x506281070030942c0004032000e0001207164015100390704050020715040d20701c690082d40c5078104006008110756004e0100000e541c0b2400c18a84643c440e0142d495009100d4100682ca98880d10089410b40c46000302c5a91701c0100c1d20401020000707062500d0b660b0205040e02002195982003d241c0e03903d0480e5000350204402050f003a00003280403918560000d41c81c50a00d20855583c008403058841a01d400c4026800c4240180414140203035040d00400d224401410801c0107181d44680f40e12270406000010f50100900a18948410440310040341600c8082e561941c0d407828809100c0d411580442d1040384c1d141000d104030310b824000e40342500d400400080c09a00c400503ca01604840c0c0746018980d502c5004030a00c0005080c0c040c5000842615582902111410164280340345a40c203881400b8051005110044d0301905032a1006407080300e000c050103c080c0060304c1c6000344010106114100546e140c10585d060308403001c169070710b40f50400c0300e000003550382d40c40344000d000b030748030507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 961157329 1250 961156079 961156093
    0x302031215011b0609020409054b0705220b0a1809050132060301020c0c09090106080105190b0328061506021c0f02030a050d0e06150f090405 62
    0x591510754030100c101d4444c000000b00d050081c2d02140649680303020076585904a10405410340d0000a010b80440c80303a200c58844048140701100c107400286402200c01e490160303400300c0000d00400c03d0101500c3d00404c000c0c0d1160030342055041180c41a04a000c095041c905660303164100805410181c1d40082c16050411442030141d800504011409490715900c9015070300c4080c44507003011440072001d4004046034030841821680741140502158001d84c810010300b129808042400600c2c2034044038040f01c1a1182000c2902401ca107821006240d46402c080c0030000d00721040c000d900042414082c4200940d4104154445020030420b1700d1106203111844030360024264589a1540705a200160261a0100c02c03043d0300d07616006600585c0c400c1c05000b0081c081e50402102e229428a081d001390300b80c40100079100d0190300c2c190414080040307441e00440c80c40340c002c00226204041182d04c2da180c5010140d11615084102500070042c824050b074003420126143e510981e0800010806 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 961158579 1250 961157329 961157357
    0x1909080d0b180c0a020f0c09010920041d060105120c0a090f0b03180609151801050f0601030e0c010503040f020f09010603020c07050f100f050d0207030203121501 71
    0x2034048808034960100c40d561089252200b42480180141e00754409640ca40080703040c007034078080c001960b08a945d0322100701014140c1d146c01c030b52410b5521401d0042114030865800703034118270030314501c14640b00002c24007252070070050502d0740c3d00c5010b54000f81155102c010055541c0d1040d000c020800e02a034100050b803400e03540c4001d20000c9854a00022516a41c101c250803000054000150400001050001c0c2800001c010341e44006500e002e8001400c090560756a2680d00e11407520020a0345000152450702e210f0603504e241d0f9102c002880b0f240741100310002d103000100d4006000c280f07801c102100b07801c07000903c181b2020041c0c444a203552115280c030140e4006610040340d0007440f8400d03580980c0c03550f000441c000c00e8030fa1070240e00d610071180060300b40000750b080359000d2400700700309608580d80c0a1318400c041d0101d0a2080700e900582784100e841d44184100070524a000043c0c00b000c156002000b4601304000500d402030588880021740f00f003200319078a550010b4228121080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 961159829 1250 961158579 961158581
    0x8130b06010912060e01060b0c0d0e1507050a02032a01081801140403080912030a24260d020a02120705031902040c020c031207020d080f031909080d 65
    0x6000340c0141041202c250b903402c4088003942814100b12400c1e526000e00004034031090248101419849607102d0030401c9242d044e950318440841082e0070080d24171b1000b14251154203500c1c840008000c072955070740f0f12a080c00c50f6a250301220880c0a0722410581840301e1010580e88624a003851865850382c0103010011030380c000000d003400790b00000116202c41216024825420000d010001b2008140b0b030030704000c0d0041c2001004618590841210784115a030110700b12a80002d40300e1001031000c881113408900401c204280d5040e043c103410380403609051001c000c4400101042c0380350760350f1107126240b9403150a076000000269120300c080c440180703002c48101f003001001c80225401076a903800040c0c500b030403941502c1805041a0080f03c02c1d4106400740105d0564030340000c180940340f0002182c0d0712504402d000e403100b4404201c6404642e0380450350032074a50080c00c001d813255140020b020030341d030094038141c0b1220f8442165003032810f00390103020303035583c0c00180041c14514401c0d6454 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 961161079 1250 961159829 961159831
    0x30c0509151204050d080112030e220510150302120403050c0f011e0c0206040c09050910020c03031518040f03050c190507081609020915160203010c08130b 68
    0x22031075509001d2418144410303201c0a12075401074004191038811010050401c41e01a0802c0300c00804801860020903040088800010b01c19103041c143d4441c68069035046040c040a48859076040c581407112041444070310350b00f5038624031202641c2242804041e0200c2c40780d901e40141c0e40710498000340100c3e0140e0007030424128a8019201d001414034629800c5599110342851042c448a024000d0b040b85489902190441c0c0c0c00107242e141010303103840300450000c0c811180c1040d01c0c0c000080e40d11106011f140440407860f0019900c0d03800000c0644d8603900b0445000b14002c1000174101d031246000303101d040107046038075014520364a907522a84040349400e041a0b081c42001c000c640701d040b004003c614580d5420580400503080c840c9041402e181c01640b1102c8640c3c8405e40350803045031408008070071038101c240c006a649101e01d010a02c0c513591030754540c4d9041ea000c1450041c00301c041e001d0b06403451080b0020080825480402c4c2c031102010356020182c090300300305101c00228846005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 961162329 1250 961161079 961161109
    0xb04032a03060e070812120103112806020705010306180b033d05071725111b0102191a3405120406090b07050c12070321020405041803020d030c0509 65
    0x48564620400c00030bc0080b1440040480d00051005040000a6040c032440d405010240390501280346440c0c1102458080320008024459844a8520107540c007009040440807102c44820240450418401c4050300038034a00b07000484010704800d034010541c801c2e284210141e0700c8021640c0980c40b403000c61850010f05540d6070030b90100305541002c0704c009510138009425903c100d8001000c528040c02c105d0103500318900633414840401c0203a80129180c07008a060504080400d082d500740a8104c4410351099803240c52648240030945116520425900b034a001d910705541c0b25040c814000001c4600c4443c0c00250180076420214514000300e5804c140140c2022816240603104e21010700e000769410004282d00103400d4181c0c0c40306009202008503000151808c2c202c00342c5000c1c000f0004403245582c1034001010311b4010204c16810341e4040c0c103000d4010050400301c0540303041c002003030351019030140c070682d4220100c0a03ca802000c80d00c1c1101e988031414100c0301e10034098903114030805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 961163579 1250 961162329 961162339
    0xe0a0b04030c0803040b2217210f090d0503060d02040506131b032921030c0a0c090c1e030e010212100b04032a03060e07081212010311 59
    0x401003c142800060341c01240901003800340d0b41884442c01c609003c524501002c10342110201501103040715159800701c601d0b004801e50340303ca018061b1940350000da2250000324546005100e2400405910035210b001c8400c102c1b4071480105005a40b580811690340e580106109100c50050815421040d0808000780409a10480b641b580350b098528030740c640384110903025100d03160341d5814000c1d0000c2243c0003000c0c150450403502c410100740b084030243c40c082c080c862801c0c1840e2841c4003007607110240003000c1da42c444a54000403030f241c54158109403103902400001003500103552040380c0c00c0ca103583c0c9a0142c1c5116194000448418001245050513901c1d481040661400e00041c03030310000c0980007d2161610031f52003045104150070000030329805010500000e4002076a951001c03c0c03400f0004a40031040d80c0f515640d0290703070170040c10541012075410090a0008000c400e4541c10307402c2e100b0ba00160380140c0b150b80569540000050803a0004201240c410042d0070b80c0034002801e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 961164829 1250 961163579 961163597
    0xb1c0903030e012414060d180506070216060e1e04020c0106030b01090c0f0f2304060210050c03160e032103040501140c09190f06020309030708010e0a0b0403 69
    0x1411400c54044d01644040c43c4800e101c02020141c03090400005003110301c03024026400e00c2008141d41c4d00038008006e00e0b45541d00803916111020144c191200d917441412541d4070714100e000203440e5a600c820742c00c00b1280d0580e012034a40c0c05101c4511030510050311044242a400d0511b25503c10261b103140d0300254200000d50b4901c0084c041c1501030750141c8000201c952404008104550702c10360b080040080031800c00c5485584070100c0c00a140c00c17407800c088440440c110407420740c0c03044544c05103901800900054241c0d004100c06801800d00c8070700b00000e0342c50b00b05260542c0700032141c500543d8980014110f296004182c0a000581e0150881b60003078000d0542c06c5401d5685150f065400001100f0030007088400d000708030b64400c00060804d51407d02000c40c200c00e00070110003e1040036019080002c025450b04503900030194001900b445542d01d9801035200d0f40702c003902c103010780078011010461090501071003080c801311000038091110070703403a081040e90f40640100c0030002454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 961166079 1250 961164829 961164851
    0x1c121107092a02070e100b040608040303050612060c1e0403061b180909140a11101e030209060f0c1c030b0a05120a020a080c03070b1c090303 62
    0x325520140066003000036142400c4070492660420b42c00003800464a5040d161200ea540801c0780c0048511110b9000540d80b070b480002c0061140d81d8022041c02c000100d4000341e0180e0107080c4d05c8c001d0b8001e441c1004641c82c1c0c2006e01c62042e508141444403540b00c6030119010440501c0140511001c09058401603040e0b811201c0c180d511640c8191092600d640c448500e500d403819020855103820b0030444104101c1140726a00803049100c2d000c281c566030002a000d01410061a400041c000301c182c809058071840c26440f00341006e48254020031344c80ea14002d41038050080c102807030a4003145070840045162040700079520480d175890304011b052002c40c0000b86881c01905104058401404d52030a000a9030500c81060b1028030041600340100445948c0760180700c0801c1d140e050310318104a01e41030744c20782c0c075180300180005e4000503000000685c1c1c95000c00c3c2009545c004406496100360703103070f104880fa8084c7d5400c1c04030314030000800702400d4950342d1090b8070b002c1c031900b00419464290 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 961167329 1250 961166079 961166083
    0x3040218090316150e030a090b0d0204030203032710050306120106031a01080c1c03030903030618020d0605010c0c0e07021e03030603060105100c0215070203030703120b1c1211 77
    0x116030031904092a55401003480510b40101d90170749005600860809010a000628480e00e512424055400c00501141c081d0480e0301110702541c0c01404496690080c2c03680c107902106c2d0401103640c6088400016161032404071045580850700c0c2d0f442600790788800c000c0208403110307000c802c2025981c0b518000002480f01c0d0f00c5010b001101a060b203283d45c034000c004e40c10700302c000e058588506e4094103440001740c40c030418000c07600d805240c00a83c60402c0c3c50250000c0c40560400c3d1243e00042d01101904482900107010307100211404ac0000c0b640c03000152000c012486004289549216050000414100089620648902c1254089908000100c3c000080c41164001e590000001c00845042c100125401800c082e10a550071503500280100050760b0510003d102c1c01498448064010448080d20001d135001030a0f01e41e11986450302a00d0159103004031002c0c0c43c1000940e45861070050300300d03840410f0501103040c031041141e45040185884680c202c0601c0b1520b40201e15400742 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 961168579 1250 961167329 961167367
    0xf03080309010603170c010b010807051903141005010e04140f040f0b16020d020703081902160902030103230607052a06071101091a040203030c030706050105090c030402180903 77
    0x1024901e0707555000c580055502351802204928103125102c010300c402d166000c0126603500e10180c1c8034204510b82620220060070310159070038111a0144103000e400c00700c2c0c16540e001c0b907400362074640641c400e840038070042c2d42c03644054810b48408040050508a00d201159500130720900c0c1c1c2c141c02140030b03682c1d0314442030281c0f01504003540700c1b002c1104894041003000f001b80c009000501d046807556841c80c06611407c4043c041ca41d0409000c004018000c2041e401c40418140e1314144154541040c10001c1d0401d1000391001010080600c0036031141c600656450300808003c0c00150f503940e102034841360702400a80c0101e0103840c51844445c0c0d10b0a40003d0011070800c080c100504160000800f1162280071500a81e40741000940014403400e0103400c2015980020041507a2a400007a00f140140c2d80c02c0c503001e000005a0004105c25644014180d4030101c50804658655403143c2c402400116802034100c002d645a5054003540030003402d03440000f0703404903071411130400001c5002c042d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 961169829 1250 961168579 961168613
    0xc050d1103010f170604030f1107080114071b02010c0206040905040c050406090209090f060a1802090a271104050d03020c1003090c0e06031002040e100b040f03080309010603 76
    0x800440180f0a1002c003040000081040c1301c4031070650401c0c2c1c0724458403064090401070501a030700c400b00b919140100c1180c400d007079094050ba054a50385000c041d010300000340340220b51052040010324914020f90002010180159034400518015401981c00210540f8103030303442032041c0000034a105141c00380c140701c1c80c4140c03095203500345403805001c151211074112180043c01848940c00645030307065191f50000040d135204920740c41d80c1c001725002d41401d0304241e9580c078080052400200d6071b5002001c02590a07581440410360b601100391404208480e507001140240c00d03107000d07041e411b4002011015054510b5881c0c5070366000061011092128102c025802c815070500040c54109514001000d603403c080c00048642d41c0c034000103841d10f0080780018142d56010810540f800c1002e50840b41c1c0c210740071996a5200c0e03c50030760203003040b10145010609114042018000401030360200d82980c031000c544503055a860b548541c1000b007a2b011650f41e04d903400000b19403d58008003c0da0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 961171079 1250 961169829 961169861
    0x5040c02030a02301602041107050d050a0c03030c11030c0c0a0506090d080d0e1e100908162405100f06120b042319050c0d0c050d 57
    0x10a04100280c10240c0d02e403000907259884a410713200140000c180c0c100480c0c080300800c0c2d80c0e40644000d01c2050100c04502035003152074a000d020b0001d51480060079401e000b04112003c4403034000c000c407014810740c000000010704501c140800640a40c000c3d003400909801d1048150720b54030701242c91130704484c26061281d0b100c8000030b10581400c0c1003003401382100380c40003481d0680c5440880c11070b5212450050960f84e0010307604000621a6000788000f088050590701c480008510341541c2d221681c400c1c00329802407250380144484244960380e44194001c00342d506001003982c2d1204502c0d001c441c00da944d40d440c501d044001c980b601c080d100d2540c58050700080e0b076040c240711910294620360411081c0c040011740500c60f080d080a1000d00300000d454012801e6a0b00201150140c1004d8924204101640300b10810f0b0050010700ea07846980444541b40520900724032000c1a01c805541307002111400b04003c90120f08580c010561141c20750130210710300180c6e5140401202c0700058020000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 961172329 1250 961171079 961171087
    0xd05130506160f09080a2a0e04030306170705150c011e0c02070602030d0f020403061404020f03010207030c08070305120108010207150b221b0c0b0f01030b0103061505040c0203 77
    0x3500b0980342880610340b031801c241c4117810220303100c2d540e56524102400401507401034581d401c41001124003020700700143c1000f0310b55034800b012075554050710224046424000b0104004d0071401c4000c40c40740402e401003111030301d81814001e0704e034101011844501010055800b09076400d00418020030803008023081000300b04c0000200312003200da4003a0454000131405c110103580003055031444960780a00203075041c08561400000d10807070f400101020b00344100401060f2a200d0401e20441c02685d11103060344240c1d040600701d200317540b00100410009071140d000b141c000400381510b00c4c8a03040c001d1904010000d1014001c030240d0002040d42e400240c28003c001c00e00544200390300c680e0106008030420100081e04070750380c00c610a80e03c00642d4441840102d055001a602e010513034901d03881c000c801c444000c201e6012008180c620360010030105415541000782d40b41260b4000d400d105041e400e55440340040c004040709520354162400c0041070319074452054080240e1960000c60391 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 961173579 1250 961172329 961172371
    0x1b030405041404020109180b0409080a2703031d0d0506070e010201061a070203010b0901060e090c040f05060d02040801060b0901020f011407031509060603141501050d05130506 77
    0x10390b65007541c034a885006100501005076049265030056400605107645540011841c100043c4805c072003490b805824800503e052020709401440150b1880e542c004071701d04041540c2c41d442a0001d05034800c8200386c1c0c3c041010a00c2002c2c1c0f0300d520000310400d045130b1541d2100042c0040034011058405401000510000d1034001c03100c0942c00f0b100380000c1c00014a886944c90404202c80155146120005045c50071507800b90303c061070352000140300c50310950316807400508859a01c0300c1d160003030070401d012940981c00c01054404035206107031585c6501d4100170034404181c02c400ea0740c01c10309400707110119200e2420300420f0080c02c80102400e455280c0031380020714040c20510b200441c0d900d400c40d8950000640c00ea038a07801001b508000c0380d0488c0035451507020402c540d0186020500d4000c010030b01d6641500505400b2001a0110209894045150b00c0070700c40894200d000c07400401c5854041105a0003159000b2008031045000346950389605043c458200c3c0d084444007264041840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 961174829 1250 961173579 961173581
    0x1d0a0e09071508070804110d050d030e0d0c0c0302060a05120903120c0a080f062d15030709120804120b060a0609080709110f040801061406030f13081b03040504 70
    0x654502d6914201d10b083c20030a0b0050721400d80900040d003015400c2c40e81d00c030f0a0b11080ea07076442a85e030042c12540c08911208004005040c030790102c01e00b41c016010420b665510030ad0203140300720b402a1121a51528541c02c20502d9444000034109110b400d10500e0525080c2c0000103101d41c40c5040951b40d5412100d0f01e125040400070110042100127000c025440760f4000410ba50290012003c10982d8451b00b0024403d0401d01905810103802c1e001d918284113980f00b402000104140e039401d5486404120b01e1041c4d000c1260204001194603004109001c0c1c0c4c80b030608100c81c000c8a5007881d040d11800d0343c0c071241403078a0068800880003418480141001c1d28104002c0115240000c1d4850030542c0403501d600a910918031000d440b8200d010048902608540c00ca18a818560390344035034400c0510302900442c8103d040000155100c560b0301d0038443c02300c80c45009022540f10013584c51100f008403e001140c420350f48080284600e45a9140107540400e070280300c034005545452034101084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 961176079 1250 961174829 961174859
    0x307060302071505090c030d020106410d0c080105040b1f051e032506051e0a09080118060510060804140109050312040b06101d0a0e0907 60
    0x902094070401441c80481c00001048010000c01c2070042456118140c4032807130803424060659040c02805424107010350158000000c84100107440d074410345c3d02e0b604501101842180b16445680c00c140040d205000d40c4003042013070724004040c0700351046039807103040004401d600071852aa6545041c007060041101445a000c100740c1c80e0003800401000e005014007200b84105401008000320410b90081001c1c000c0d1100036014003122194204018030120040300c094000d0540c020200d0b001c25001d10034811035020301e0003400c030b03001d41040703903200d45903243d2091480904008540d0000b0840e64002e0090664445032101035044000c0c02c0e090030812a0740180c207041e10658031800802c001504820f100346d110780c001c007032800c810300c1840403107001d0507000d4002407941c08001019051060703035010b82409036014540000d955600c04090003070210f5000403e9002c500916100600b080d040f00022072580070280000c14581d41e100000d52140f082500c0d8100c1c15040000c080c020b440340c680c0c0c62 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 961177329 1250 961176079 961176089
    0x131107030c141c200d03090609060908041703180904020301021c020d0b09150d020a170105180c03060a051b130828150207050a0f0b01080a080d050916080307020307 72
    0x5510300c0300c240b807a256683e17040301e10b0030f10515448142501c140080790b40040b00a80c0c104805009110081c50003031030340d602038003e000c0001076000c24240c06031400000d80e14003076200d840803d24940480200700982000a100300c1c0e05640800038030161300110700000300050118880961110400c400802c16100110300c000e000d007601004001d50b054002c00905421501a00c0440c0121118000325018412540002c0040c0e031401240c61181c0c481548100d1003003130410a10406040081c41094031a02440b6001c0c3e4558010720204141511a0744182c0d004000c0c03e00c0d4024038240101142800e4011034958a03101c42c0c180020041141d06004032070040c0e0304141c503264111b100c1d059209030f10180001c00b1301120854034041300c00b10402e504550b420b079044800c94040052625142d1601c000b504000ca90701d00358080002801d04001884441280d80711500500302006103c50200510006150040a1141e0506080d01d006509550805400304201a50f640c030011b005252a060b0b6a40c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 961178579 1250 961177329 961177367
    0x10f0902100f1d0102031b0a03140403150506011b11100509030a080c0312240f130e0a120210110703051b0c1509131107030c141c 57
    0x191490194030403074040c03800e00c400c80d0b5854a1201c3c180102e243d8013610701d004a83c48081c08140304a00030014414141c24440e6640d008040030928056419001c0c03480000c000c400c1c3c4070000070000314103800c416441030061404070148028110342c02c01110a443c0d040d2490360340124018010b051030581c0020000302400c09a19204220340030035503030500541d000c0c04e0104d020500707440301841441112047d0307107840003a0f001e60904014036080c20f8a4101741a0049502c6841910542131064500b0f85000004082c2c010140c9091412000761120500c40e204501844031804001080100c400301050700c2c903030061070011511350f495000c480b0144503000c8103242c00d01a181c0000d07401400c950200f6081c8803001c0c45072180f08241445c1c00010141c00303601460b200303841c8540f034513000c01030858410120303040760b104400041e04404a40b4240512884541d04105000101c0e001d98001c10b080e0348582070700548078001140b002c1c18410b045c2700e0303140c0044c003400c6001081603211a41c00800c1c0d4103005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 961179829 1250 961178579 961178597
    0x41409010303270b2b0608060612031204030513060804020a03150b030a2f0d020603040201140705030a0e0910181104120c06091406090d0203010f090210 67
    0x2006041050580610703058280f4042a1400ca41d50480030200100b610030320f0251106101c02140314030840b01e039441c99401103001442e110104807401360303004841f28040a050f00d42c45000602c0704500b4a071004403490b11080002c01c080000c0142c070544074500079543d05440c2d1101943d80e0b09800d80941c441c80800415809001c003590701c400c00c050440f54002c041e24240364440706d024000e880d00700321090349030040751007500c01d100511400360314803000258a80fa1010b41070755600100c190300200a42c01880c01c00c01c0b0303070050808000a4ac0c01c28014180304000359002c00c1c6000c450307030042d00112201d41021070380700405908501c0c2c008582d07008481150940c60860000c5854052a100701c0c40c24a030055100050b40340c640d030215908224a400c00341d595526095800c0340c0c608a40350849000d40018000145c40e0320034902e00c1c050300e6802058043c2041003004001190300030710002a4480360402800005176000d01c10013401a940110218900c2c0d5030780104540800d184032000c0034861281 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 961181079 1250 961179829 961179833
    0x30e070f0b030402120607020d14280203071203060302090f0c0315040e030c03040e0108190b06030c1c060f020903070911090d152007020402030622020414090103 71
    0x100604140c801c19012680c60740d881d40000703a25a01c41c0c00c142da8450241e10288061907601050544580314207840b4018150030821644d80284030701a1410910010311030f810710100c40c8920204c544250707a104903400e10a06854035440000b240c5c01a801182e5100d10810441c01e000d01026031098401c1c0d082c800c00c0c944101d0412141c8402003080c0480480f002c003d044550380d95001c16119101c84040b00d84a180c11a40c2607a01e0780540100b4010566034000010000000560f100a806003200e841407504825900d6051429010701807a5041c040c21008016036110080300d903140444c036030006203001d807032400e00070704a80140181d8041c2500421000040d40c17000a040301c1200c81d9030f400018440c1e034800e24050a4025000c0c503581c042154801402407003018145100d103211480820040c40c1c034000e170251b502d041803804c814050070702800104007501c0c00d680650b52010000c0c1c40c044d050103200c80c80e00f82060300ca0540888840e03002c02e05004014048400402c6040d0558a034010f1794110303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 961182329 1250 961181079 961181099
    0x209010c021306090f0209040b1c1203141e0703110301140d020306040305210f01090c12060b2715031b03100614072301060b0415030e07 60
    0x30860290081a5200091215602950003000141040f580420024044183c100701030f6000d6120039110780d0400018024928010410307401d880c12004e103007000001250b44011205103003800403001d065590070350f44802d00029108a120701d0301003141500040080c040384240400c040c00c548101407a140d505004507031104112070550b4441c50f008011810301c000001e0300852980d40086d01400340806101c20150080c0240c11006581e81c0020101f02074041d004a120308100c032410302044201c03004006103001c5900c1041225501d20709820b41060a203a504182c80280d88106019a80040d0384d480c000d080d0110309041c110031114480c1900c0003000058250300b5110780110094500102007040c5102451a00c90412800d03114a526840d0900003000c2950b202d200300030109084289040810007100704440c4e00590040d104204007041101c0720103207100420401c07402e90f44e12a408628082c030900600020082c54850811901c00900000d00b41c9007003c0a2220f40c2d8001e5205118045507 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 961183579 1250 961182329 961182347
    0x6010e0a0c08180a0507030f140d021005100302191e0602030f0c0a020901090f051501020a2003150612010209010903080904110315010f1e050f0f041e0603020901 71
    0x3000103c0d0704030303041214550b820603008940081c030a10a03000c0010400501d0642551202e008124004026520104040e00c3c0c2108410200040e00706070400d100e0710f5156031103075410122180300341d4102c0b0b031290302180652261a650700050500704408028041500c10b83d14010701000f1007940102d8980200a982d030300800c2c15840304060041104507910341c04101c00400c1580050140600c0d5954208070002010b840d114041d07070741e0815000852807407941d4180c000509041c1d000b85044076541d11048901e081000105030203060405102c4035950f400c214003411003003031401d5a101828400e040080000210000614990040c020740d8031aa8000e540c243c01c5a8109090340e945925110019000b0801200038040d075a40c04010702c40603d07403086c01e404202c4c0c400c1e02e4075001c0e06074010341075031110f4a00884058000031702000c00c0c1811310440c040c0401c1c06403200681e003440a21130891003641c00641281c00064268081400f200c0c4082c1008002801d035030404500e04040100020030601e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 961184829 1250 961183579 961183591
    0x501090c05011806030e1203280614040e100509070501090f0f030b15030102070312140c03180f0a0f0525050f060912010c11060c090f18010806010e0a0c08 68
    0x990f035610104d50042c00d0040a132148060006a40d8130f1400d031008a407045009e6070341000d900580109403040443c81d10444050314403100c50b40d01480300da402000050b02c04007482500b5800f902480a10b681d0040c0078441c020308010380a0035221b82842c1c00100380b000f050348503024900368001d0400c01000c1c4840700805680c2c1284c9602a40c3e9560340c0003451042002c20070641640c8001a40320034554405400c81005006101c14840710303501e81c0c0c4164022405032101260034000300b010509010b90303420002e250980c2c2409540c41c441c10141d00a04045820f002501d10840d00c007130140800109101c00b02c588072090644256681c400a13200c90481c103540602405030b004840c40854070b590300c10036140684e400410121740304400700f04045c0078004516050022130143d60310305000381e6001c00c011707105a81c520001402c00c2280010000380841454600350044918032480345e5030f2030394404490103440350a0040c003241d403610040c0e0300200350040010254a20f440d601d1061282d00001190b0040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 961186079 1250 961184829 961184831
    0x305040213050717040305040306060803030910020a020a06060f0906170a1209090c110c100503061309120207030b0c09090601080604060b0d0e0f030405030d030906090b040501090c0501180603 84
    0x140d15400180c40c12009008680504c3d400501000201036000c0000e0080c0e0384607401c20f000036540c62120740d6076070100b910303480f1140e04000700f400643e40b4558090101103200d881104c0104040352201d03011070740d03560406008500d0340d83c02071062610600840c0020103100005000c599001841e043d01c49800c06001042281e00c0154070858900c104101d102400c80b2140400c074801551001030582d40c4010721181e81809a2420303007a151418208941c032000709502c4007455503aa2134200200007081e018206c1d0300b0350f564458680072440501400180700d0494008100c01c0b03096041c010783e00540140803441242040005031007907104e50000d6a005242802d001816848039800039000d0700e000e4102c00f1207020301280c000c80543d110b401205a082031242a01e20a0030700a101907100d01c100e01a10390968050303a00507880e40e1082e07112409150045800046c80a06660340000b404829942901c02c1d84d1220142014401e0b041902d00c010042400d005c1700c01510000782c0f980c4050180b00d650181 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 961187329 1250 961186079 961186081
    0x6010501050d110d0c020105061002072715080a0b010e010518061513051908060c1c0c0e091003170a0c0b280203060f040207031803110f01030504021305 67
    0xb07003c14005685560b00280d4043c044d41c41d1046001f802130508481d0948074101d0300e4103010b072843c00071a260342a190410880342c2d0400d103030340b0810351543e01241201c44842d81d84c1003200041100e0038095001d85002c81c0504801c04082c01c1c440a8113806801003811804190010082603641c2c1e092a0014008802181e160b9038807036000510750540c215032508850400145605158041d008103400d4440840d18042e505020074031441c069503c41c0140c400036032120b404100300b0003068011b0007401c550500101c0d10340341402c910800340c4070643c075440045410840340c2c240780d1902d4082c86522880503400e40485518544a51000b800c6036000e40d1100407000486c1e0800c60300c101c2c0c41742c030420780080b454101390800d0b2000c0c415001045842c0704640d05401800076020506000712802102c0c018507501100c4071103000c2000a61010703808905101c070b045403400034100390400e440021030149134280c903003070010b07014000c00c80328001080741010310b048104030040e0341e02c0c091900c15140c4404001030b6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 961188579 1250 961187329 961187351
    0x60503090709090807020a09200f09091312050a03291302040b03011202040b19030b07031d0a0309140915190909020301180503070b04112e0206010501050d 68
    0x1305209000c8080d4120301c03050f1021500b2210394200c03c0c010000020400160b00300011503810f50301407076603e9503080314100440456440c00c9028207800c01c0c2500307510304800840e0381c1e43e103480c084000c444030080b6201080000140d86c05124140103468260540c010700d108034050300070360b003000e5460301d44074141c804180c1002958a60540d03001d440c205c60070300d90380d585a2140e1040c42d002904204d129608004414400c0d040075170140c4600d0540a000b1062142141d640039031300744000f41100b04141e550100f00f607042c0c2c080d4001c8a00030301e4880c00780022400500380201141e0094003c410100c0b095100c69040f611980d80d16a407110100110803040e000c41c800040313911704180030308448860030310310120728502c8130341c008040300d4801c400130820701c1803103102c0046428020001500542080c00103202050307821020a5020348038448101203105040002840c04100300401d961504204d01c00c030000c00c1503051480e9480480380002e10b4150f2500c00000c05a2250126035010980c50f0340306009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 961189829 1250 961188579 961188593
    0x30a0c0806090408121f080304030c1a190311070b0421020d030b060d09080a12090231050c070b0903180d050705150306031b1c03020705270106050309070909 69
    0x2c11b1001d440381c032400255200f54141d84c0741c02600080c2c410071082e10002940401d00740c1c210462448021520741454030341d0021a4002c200c1032085010325842c0d200022590b1642801411424456010804507003400e0405801810400c90140044c64181d2020712066400007071540302c82ca014034012881600c10030200d6440c0c0039040c08a040302c0c0c1400d1001e4204512640901801d035416aa0f0a00780051401d440b81a55140c2c01e0203034005910180b05200090032840354400c900410300032408a0f83c11020203070440b138045a42c2018030b00040303051803c0020b100b8206e5001582d42e00294202100410281d072707d90700c0c50890f10300c10040070702c866007004010720244d030040c0303801000e06900902d0a40d1400e000c1e4400c4440510034000c0c00460826464540c2911130040c07409040c000548800305501c1c4008183c2c1a0250705501c5030f41400205da41d9001242c003180e004071a502002c2041d000c03103164403240182c01c92000d108043c02008070324100002c0700c0c0211a451803010401c49040c0c20000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 961191079 1250 961189829 961189861
    0xc0e040c17160507080904020702090114030123010b09180a05101d01031b030525060804320a030207060822110a0b030a0c080609040812 60
    0x150054140440e080306160400e01c8480003201e0051005040d58a2942454100c00d101480c1c00209005128110101c0c84100c043c00b202403028000624124850300002d004650903444246c07414038a44202d422400c083c02040c404c294401010b264466200041250394a414020031291002c0840c2c0340560b03603201c007600c0c0e4243c0c0c1786002002c102e0420030414005480100d80280c0340f003071550b0700040d042c404144180764220550507102101e03400e5540e00d40780700d014104d10f20a40c0d0400c0340c011006c1003062180101025403880078249481040304080300710081544001c0c14080c0ea54204804182d0ba848100c40724480340e100600c03030390f05111300d00d8641481003110701e034a842103d42400c10190002040c0c03007a610203844515031587c80b090b40b410313291211031040c50f807282c5019841c00040c0141c0b40142903d080140001d12040c0c6070056103600c0e400c1111441c40258a880c0c091418507000741c2d58542001003510b000c2d115203000c4e11180203520494149601901032000014054a03183d0060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 961192329 1250 961191079 961191107
    0xf0f141801060309030f21110405030d0206040b010503030c12070305300a0b030a060e01021603120c0206130b060d0510060305010501120c03030f0302091f020f0a0b01090c 75
    0xc0322003540c40702001001441c130b080301140400c2402040484e0140180071a00034072407014080040c950304920903102070002016201010a0240b0011a030703a502030003501c0b41301e8401d40c010321082c80c0c1400c1402001d40c0c1a4025402604108070900d0302c0303203002c1350728444292505005507a42105180c00c43c2c3c0f034400e69581c4030440d0300000f42d103c3d0b030f81d500300741507561005a0f00b10150350340c03208035240084540ca01104d40e03040d4454503604001400d40e420000742c044403600010700302091002c1102c080f225100c2d04600003008407054020305c1c0302c2ea00c1901c2c882400c40c80101a03601c0c01024650710303400300d00005804810a40002812551000180100c0e1503020081c0d60400c4440d44092001d40114003044031a0b50a0000205421014031407480040780c200c0c3c8a203440e24656101910782c4840c0840d910300301a02004100380603264034450706098207086c5d005c1c0c1e0070300f002440000c2c2040761103009841c070b81e007200c943d010115120b032030302605442030b1080c00106104051802d4138620111840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 961193579 1250 961192329 961192369
    0x160c0806010603090b1609050d02040603140705010f02060708240301060320010e0907181a09040b0315040212010b18150105030c0301060e0d050f010608070f0f14 71
    0xc10700683c15001103e25a1003104107030403075210300c00900c584080d03800314880002c40e0210100b18074504101003010701343c000350000840c00d4882e1103050381d000e0307229047c0200f90300041c0104001d580c40981050601c00703e10203040c107402e082400611001d005804c043d0740300600140901c010703141c002d2071060300c24010001c1013195a01d182165546c00f041e00400064500090240025402080b620f80340e0f19005020600c15940e03214113031503034006401074440c401c0300701001182910000c19201d2410000c1c1d40e00945440c591805c000503a225000168002d402c141c018000c0b0050840a00da0800d90441e5001c0000206810203401071100582c10b5611000500c140071400c814000040d0041c454900b400e00c20580700401514503201c01d40b080402c800040004115507845032040440307090008100118030380e41901c950f45080e114981c000c80c182d43d03400342000041410821800244000040fa0004900c0d00d0500d444900d458442c0400d50488030201c080e07039030b884803a00c5804081d1520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 961194829 1250 961193579 961193581
    0x130504020a0e03010924020f030a09031b050601031b15030b04020f070812070e060d0510120308090706030c0f030906090c0f0312140d0e07050402041805011a160c0806 73
    0xa01c0d514040450081e115500c800703c1d41419009460f008131000500d548c0d2820380755455180c000c50090034020350a60401c4403528000000c48441645907020354080d4000b084e09504500f00300d11a000d01d11958008500340070820000380101f501d055000031004c0c24001210904a004180a882065054003400d007000450f0b908100214018201041092480040d00c1d033b180b0382c041c5c440c036080d00142503218000707000b16095041e55400090b40325100c00800c0300055035880704c0807a00824a10300302d011030703200c1040280b42d40041240c1c070300612031031a0038071108040d0000030f0001e00c441c075074144c205038640d00c2c00d00c18400700703070001c20f425039202c03900d24074403581d41e41000c46000c040e01048079009080003401004174170410b40404c0914960048602d440f200b480440001e01c00004040315074000d10100044a50700d92001d40001c00100c1a0405c91901400c562000c80c1c40507001102c0641e5600c0b180640458110140c0c1c841d40c00354007403030b4250352060410f42d810740c01c55400b8a00500c1080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 961196079 1250 961194829 961194833
    0x10f0207081c0e0301050603031b0a0203011107051b090a020f1303050106030c0b03070801270507050306040c0801080d05031f0f030201080c09090714090402030109090512130504020a0e030109 84
    0x4400c4180200407595910220f01c00c010802d0709072182507034842d41c1940240300b4002c5200602c82913521021980040315803840e0940d0101e401d5440c0300d0083c19a841c004201232007031220501400098240d6038414044207030b001c0000030b10b071280c094964803210354041801f00201d500b000c111100c41d070404894040f2280d89181c41806004503000c101c500c0c1d251070b40009003d6003241c0a0320300801d0344d0b8440c00030580c2031484481900a0051140400e1801740c0c03085003403a1514450b181c020506507642664902d099424071040d00d10894810007080f12503030041264003c04244c041668171140780903541e9840781080484804640351900d0407005d40035000254082403819510700301c038802c1e261610a070340c032070b00d003e1304038001c0c50798854005070303c000000d0420703214452a02a81750245042410180b00740f020038120382090b04066000c950b12207030b0505204040020580c29084030705114900103110781d110250b45200e21030140140d801044045c40940202040c1c80b0000c00a0000c00034030f0114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 961197329 1250 961196079 961196113
    0x1a04032a0b130501180e0f04060501080c0f060d27030905010903020117071214100503060705070303090206070f1a0901020a05042705070c12050301050f010f020708 72
    0x12200500380c14490280026410128100355840120001e003001c00c124034007001510241c0641850507080c082a0002107445000e1070921030180c0782c072070b018090514003890500b04813003041e0420081c541c800c00d24140940c1e038616080e0408002a03441540710800000f0140107011520010780c000400c2c0d0030112207580105803103802c2c035070182e42c40d11001640d540042d81c0b0000a0301010740000e03141c102d00052010301c40131080d0004180e14015010294441c810300446400c41e2105204000000921100e410a100c20601038102140900310303a04001201600920a400f00241415210107241066540d4601527440d0540c004d605810300c0301544c5880c03c50089490401c401d00d0b61048003284080105109542e021403440c0c48444c6040c0c280f00740070804110340d400e411b07005100c0f0901516030103198040c041c0542040e4850503c0803820303107403c803c03c42000704c09800700b00c402c2c0010089039441000c40320b0040800c2c240501d10448001c8100d00303281160b04010624810310781e60070902c2c0c0345 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 961198579 1250 961197329 961197383
    0x203070302010f1401090518010c050406080c040e1308070f030f17011503020904060513020a021b0d080901050c0d020c0109080105010315110c060a0b040b0402070b011a0403 76
    0x82a402080303165594003c0900f02e0f0041c2d16260614a403000050084c0c908552000d50032031005141d040190301d800044a0030b4072346081407803001880100c1c00304551078001190540001d00327404c0d594106401c0503640c070006c5000501d11803860101d1031f40b040a000818007211281038010441c030b50b18212508000c0c001d40b98080907140068014078940c058500032484543c107940041d80d040060008140c4201c02a4000d0315585ea40a603468400180703d6541d548100c85d42e0310f0103480540c071407038401806801c1054503103a041c20306c400380c060b41c60b5650b2181313041d1a490350f014461989a601150040b42c40d80540240082c030351003442c540010194000a076403103609404d0740c0d058100398480e91041d0980740284402000e400d08074610181c3d0b041c1c5504a00e01c140000d4500600303243d42c010101c1d107000350666003040e04c0340c0d803140c05500700c0c10306000d01d49034030005460542c41c0c401c296840b962a410305108220b00f440846039080040d40300e0b1000c0710002c54000c0300c41c4450040160382e680070310107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 961199829 1250 961198579 961198583
    0x60c09031a10081507031505180906091902090c0904090507050906030c13052206050a200d0c050c030a05031503161208040b0c06070207170d0e0409050607020307 71
    0x380d0700b10000fa20050015448803911248a0803c001e91103024041e40a030581036082e240c18010718901180c592034986c81400c1d003d1081c2c544050500381126514100b48010302044120b411407607241400c4180400614011035060300c0310042c40d0f480080050700c6000e280f071116801800c2142090070f001000406e5002d440341142e2155031900c81504059840060b200000d030401d441032180d0036004420b0348201d40c04140510540030240d020481c00f6000002550200d90b055501c4040c00309424843c0b06800342000d4680c1c0310000f141c2141f13000310181c000c00c40906c180c3e0b41c40300e07030a031840e501c11010380b10724841240890b501e0762803102001e080e0350400c980d2400510300d44081a8010700c0c0c001a1058100c2d140d6004603446d070b04000c401000302c408001301784c0714220100310000e0b245070020010300e00440f544001e860f80f424034100003030404a0f01e03403000d600b4800c581d40d5513000880101c0d100c0c4814000d030a01d059003079400e01c0450060030305040080e02070702a110400072510340110060a00368 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 961201079 1250 961199829 961199851
    0x1080f0601060315120804030f140111070b3601021e180616050607090302030c0a142b0807170a212a12020405060304060c09031a 57
    0x70303032241011000c44204c00d00040b01040b501e4000c00201c08400102040c183c096201203140c039860382c80d2000040e05c01c01085521051080004076140c100788210380b25543c0402020741f0b40318003901c0300080b602c0042d100d0440400048206211044204215403000b40310764800342c0021114407145000390060303110618940150501805500b849100f11514840140b850541e40c0f04021300740301d01604517410702c3c4040c0040f650314001041e410000203103c0e40007070f82e072450200c0c1148107050038488650340c118010700d2480b00c00e000801e482da039034000003001510707001795802c82c00040f0300d44c4003a440100d000080c0180c11410502c1901c4000b0300d00c103030142c108000000c60141e0405114852010088001028a410217840031484034194500c0380000b0702c00b280ca006c4480401ca111840c02003c37007075118004a0040c1c081c2c0c0c00c620041c107030940700c2500314141440c010116030304c0d204c000c20007400290351f12070084c1d0607401484c000c0003854011071070001c1580e06001541f05400c0603a00d603980c074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 961202329 1250 961201079 961201081
    0x90f0f0120030a180513020f1b01050714070f020415050a141c0f080a110f06060f191206060e090d0311070327090e03070c090c1b03051201080f06 64
    0x200e42c00d0144c0c1c0440704080c01180c0c41122294000b0002e42106940c176011040802004440022482c1614181c507041d000010305410b00000c06845241440e0310b059030f403202840368001003254602d5034034a40d50141d90101d0707814410710714070106a40c683c00041e4003c60340600032070081c06400360002e5049040c3d03109001e21904c9140c1c0511688004002005450010001400104a8000341081b42a07500301010001d91603601241445980700c801d481030b510400400c0000d241c204501d00c2d600c070b011385814950700b4450000f02106010b50280c07200300c510b0b800d040c204101455010000401c0c0036011a90142040c2d82c03070300d4407061113594060003e4204061046d204081001b16905030303515489502c40d02660051282c0500e560783d0f181515880054000908205240201c1c1c00b94002c000145d40d0710b4900c4c2c606401d200c54140c005d103103018a400300d111105070300168103038040d920014030111844c03018079048546216280724064183d104400000c0c4024000441c004542200b005490746 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 961203579 1250 961202329 961202357
    0x5160503060c03010b090a0b0d0516110c09180f0607080f0c0316180909061b0206040308090a0f1202100b090c070f02030102070c0305060705090f0f0120030a 69
    0x78400064460707140b082010801000300700c00b0380d0700030314903210041e180051980d0b8500c10107849030405906080c10644a800300301d2028422114001c065601e4248030040d5902c80c94190764400c21410128000c030b2a840101e0301144603480c4c0c00c94066096011a500c242440d0b444544a400980d01100450f10b40c1001c503c00c00c188841c00c41c455910340800d03078110b50350100564200c142100c2400f0038040030213016071180158044140c05000904c8000c0741d200c44500c0c01c0001c441903881159070364a60011680715550303011030000d81168040c54030311042d441e4240c1d864108071042c04000c20f9148802ea4413010050180c1001552078400c0d02904e140c00c042c148484156130030541c0165002d91000c00251200c4041c0025100940c0070702a07480c05900d003a07022a0880c1d00110701070f42c0f0311903001010030820900b0010154050a2840d2140c1072101007804514000041600c46100e1080e03000f03142641d074407850b000b5814054803d500399040c0d203c00001600c07a40955940f80c000b039810040001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 961204829 1250 961203579 961203583
    0x1514041703130e0c0306150903010f02091005120109150e04050706110321070c0c08340315020f0d05060f0f03060c13051002030421030509041104090905160503 70
    0x110502295001605d5030b07850104019443c514000342402d81d2030148070a10142c1c03401d01c030315248000040401a0b8031a125020001d01000d80c05c1d160007002000c121084030204d5411510b41110003460010072082c002485819244085c0c0e0030002240c9001c1c1c00b04420b03c500014840c044644030b450740318007047c0f49264180c0328452000a5880105c1c3d00d400c0c00c07461121260740303550005117842e20f00e2541a5580c0c410092616a42c0070302c800382e1225801010f803000c0f25004010b4030110100680c3c40c000d8000016040d03c0a5100c041c01030302c6200348040140b00640c04071554224000c2d402d903a68040798200703a0052030305440581c02202203040400030307420031031045603500788000c0c001c0805654034010300341241d00ca40303c807030041c81c015000000c81c1d4903070144000c8214200d80145884038200001030f82100303c0c0140d03003441004524008008684c21400300d84442000780e0740410554081c4154100601c034a2b4400158503283c1610441840000704442003885044105040c0c600e60b1882010303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 961206079 1250 961204829 961204831
    0x1a04050f04091a0c0d060e06030d02070305100e03090901030515010b0315120c0a0609090f0c0f0309020a0317041a09060306011b02060d060801050603071514041703130e 74
    0x10f128203c540c4801d080b15200c0d0b114164006040000503245c10319160705c08003a205903a000f03e0b10030341ca080510005140031b000c024072040c0184028042c6a1941e19950b03501c10480342c81c001580e66641803659400801d1044940020026210114a59407071500640e00c102c110600403c040d03620001103a0b0707078804c0003100d0048203090102a01816048104003103e02c200203a001240300380c04840c5e0068480d4090100148100c0e01c40d141d20925000c00002506c00c2c80b4015900c0c2e6281c4101492030700c0e0041c5000c642c0d207c881c81e000880b642a4804229540131680015014860400d1320342d03034402401009006550380004d04000400c5924003401660181100f8240d10010500000e0034651040000c20078003642160501c1a1002c55000300d03c2c1ca5020402c651145900d42d002403290b80401d005035038115000383c0040c044030f07240c50344440050030440c61210402146511596012110009503405488480141d0400ca0041d140702d0307030380e507012082e840520303031011200040040c40d0380c2520b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 961207329 1250 961206079 961206083
    0x40b0315100309050319030e06011d1807030305090103150f06020d090e0a0506150a020a06060608061f020f01020f090a0b0f031918050c09011a040e0705041a04050f0409 74
    0x207600f80345c1110011561980306c08100c03401c00d540c410a034000010100405402040c50301d81d41c40540d804507600d40d5495000400c00c20a01c2400b4404101040700000c00408030380e0103217003590f2580b00e5400100e0141080d048240040140100f000c035441440304c54040c1111256002c41d000c2c00075a13501943c03004600e10860741100b9001000408030380464100d1a0b0002009080040c01001c05200c0d503031a40014002000691183d032000c000c11401c0d00c0740001419036420042c80914041c40020802c00d4558030074661203666400044580d40200309848982c03003624000d54a078034507050201c3c03030358000e0182d451041d5018007000840450403000c40e0085004070021a145655141820a01c400c15041e8910f04550301d0411080c0c801e0300c0c0005014140c4074601510030041503804010003440c06030000101e00e1192801c1c0e0190000440c210b80031034003000d20303421241d80c46960546a5015581c8000e840c014100e240203c4154840c0003001640c404581740000e2918035030900c4100d035084500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 961208579 1250 961207329 961207333
    0x91009030e0f0406210b010504050105060702011d04061202090a20070f08040b1b0606060a1b0209010602030307080709050d020d0c18020702210601060f05040b031510030905 76
    0x1d90401d50418002d1920320400c09040840d05980d01e0b031051301403541251a85030351910006061080110428a560042004603400d114950604000500d28407070100001d043c48409c81d40000e200303181d01c0a5601001c0004e00c01c100059865400e08e0711911817040881c070500c02400001c2d06011680700f901c3c001d10880348203511500320420102200c4d40172a00c01e0382c061003000341c1600000e628000900240c100e50713a1040d110213140040401c1030320440740075074a980080003004a0342e10340c107040d6040c10500b4940700d0740c45004442504100804a40065002143c10002041c6190000001c50160145a8038003000e0380e0b0340c2c81e04840616690080d0381c5c1c411142c0d202c103005481c14222441d5640d005031640791405942c1d480c041440c40030200f001202c1a0041006d505500e0710b00b6008108c005200016046200c03080003094840405025110500000c41c104a11451048003514094251440300c00c0c0d903803c140d4030480080c0b40104400d031080c14400e130b00c160301520a0062040359070303000300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 961209829 1250 961208579 961208597
    0x1110313031a09150915130201020c240d0f020409020a1b0c03080708090a090e0f0102040f093204060615021b01050c011a040b0d0b01120816030809100903 68
    0x665411150409040405188107203042c9040c00301c0344c80040340c051004150b03008040300e01f0740f00182c01c1076110400d0038425040c8a1011200c0b0017031081c400315a81c5454100ea41e10025181210000c0180c240340c100100d1000c240800c100c800d035401809510768075120740c4c200310407a184403140c550802c0d0008088001e803800810002c1d08440240500c240300340b1000d8200030790742001c101001c0d1241d1200d14081e8442c1105402d100044c40841e00700c2540c48020361030607040507030618290f4000e205101c04a59030390a4054004c840e81d1492107a42c1150701020704161480007804401c003c1920143c0740a4504540010b8440651510780002d9a458001d80740305481c0c09100c081e409840b22690341444410028803011800c28802d01c400c1501809607100b46c0d42c000c0d420b02c0126550644810700919081c24100c020940c80385c1c0700d604550f00c404162241414616010003075020f90603500c0313486894820700c00304164000491038840c1c10443c1c11200c003d1042180441540c144000c09004a40d40003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 961211079 1250 961209829 961209853
    0x11120d03090f051501030308100e0c091516021e0d03200d080a11030403090e070309060207080a0809031312050c0d05030a0f09150e01110313031a09 65
    0x103040540103a0003050403802d2040c49888075800c01d03400100b0075421203d08030040c410180c002c0c414035000808000360401940c00d0500d11800c60750b0280802d0050f01e030224080e6917036665007181201c2c20195141c0d0703989a00007035240c1518840922404c0b0712901c1c516164942c0700c500c40c41440030042d00104103001c0341110b51030540c0c20082e10303018030b09682025100c840d1248401c10010802e111b00e9075400900d8541240c14804840d0808a0a1040c01d020021320001c254080d161b40705440d013040e0b00d02641c0d25600d00607002000c54000040545001085c010103000858014102d8000d450300c0e042d079245e0f81c0ca8029500e03441020f0b110708000c50b4494080c0409410010b010300300600c01d8045400c2120040001650304082e94411603450f07100156140d41540e01848c540c00300c0d1b000f405c00400840c10501c02c1002c0070703d16204001000903c0045039031076841030500c01040090442620b956070002d00f02c503042c43e000c030700090300c080240410b03160358842c03c0c1590500c92481c01e80038042c0a5409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 961212329 1250 961211079 961211081
    0x60606030613290108010f0501170a140a022101050a0b0d02040b030906090d1403070e030a0c060e0a0b0c070605070201020a06020307030912182702130311120d03 71
    0x41d40c5180c22662021108118030751019850f0740800c521469040501400d80018103021050704a92010b1010000804c10759800c80c2c010750408a1030200c500d42c90f560b420401e07000b041004e104d000d9a036400c41c00d12248480c65401042c03070300f00c680110a20801d000351030b03d90024080c8105600300e5020101005100701c2c041c0503208400200c803016290954403c100c510b0780e007050740c02044581050084c0a6101001c10440844403071504040c0300100001030000c205000040c50002800400c00c0340390b02a560a0121040c4a50700200c00c04d84036440d400002c01c0480031842c40360040d0038164011803a522502d00340d814014041000704101402d041048803207801024040381036101da0440c00300050311342c3c0040c0d03218001c0f941d40002c140c1094140588000145034207103081c002e000d134091020040f0302002d40191030017000c0201140c1e15070b54a1a511100c1c1003c400300d03061021503c4484981e5520f05841228015000440041e50a004225188046025046ca15400011020061402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961213579 1250 961212329 961212349
    0x90d030b030f150a06061d04020d060b0313030207090e070b0904110301080c310b01021e0609012304031209060603110102122a030408120d0b030606060306 68
    0x140546015692641d5550700e803100b0b10f403040d400c0902040400110a00c1d602c10800100800c0c0340910501d20041003290045400d80152030080b500020742d584001150b82045000307004d01c0c0700a0380d4901d81100c0c00d500b50b10300c1100440040c01444000981c0200b20301079503285040c1d81e005802d480c1d20305100610154028480319411a8841c5488041307558002c0142d402094524060700e01a106002000740c1402c1c00001c080c1c5030000b01e051000c0207156a0030b0300c0e44030107082c43e000a150b84518010303071070003926607160603142c54540196502e503080824564000c00b100d00c000d100c44903108620448020280a407075240741c1ea91400503010a110708947c1004413900100020311030726640780c8009980417a041940c070300e0f00300308944031075580c10000c0d40c6d03104000d841c0301400c00900101c0040d42440d0000c40d0070344003403040e4450850308002d1084500501b01c0b007003201e007550301100d0440c400b90031007141c00204500c3c01000003030f01d043c08204940300c0d0100a104a2844d42c4032000c100405203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 961214829 1250 961213579 961213601
    0x50303090618062a01020406120903030e1e1c0203120c0408011401031101141e0c030a0207081e1c030219080604060f080601030b04140604030f080c03090d03 69
    0x10000c520b403802511460020004c1c1c251224160465a2010004540790119070400340703066841040100700e0150701c21014041c4000c894030115012900b030408501034062480004064002c0041800e181c49203120b8203c4120b0064003a40e400300691425011611100800c6070056042009450f082132460b0030f2403680040e01c80710031820079440364081800c4520803688481c0899980d001403080c041102c8000200460074600200d484074151040c00443c01410b0700b40218484101c1c11080010221095801d0703c40c03403104580d261001e060000b50384640c944200100c034060344441001c500e040101482c00322850200810040520500681a80e61601c0c000c13400c25074240107841c102c2c00c440e4000301071041d89a132107103483d0800c1c0081008441c06a403202022881c002002c0004500106a044c112500888620000d84c0d940c1022404e245801c1c0c58142d11b030250104010825801500014000000d036907400765582d15004500300a1106031450f1500d50312003034604403200e119802108a480d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 961216079 1250 961214829 961214857
    0xc03050118021b0a05010203180a020a0603050a022101031e0b06010833100c0b0118061203080a110403021e131416030c090b03090a02060c01020a02060106090503030906 74
    0x401041c0849013801e6203010200e401c2e9400109116183e14003909034480000f0250162104000c0c84c1e0005002803050300c1060705140d01d030340008146070440d40c1079801d8002d980300c0c030702059503042203105106c0c942400121f80c095503e1207109000308185040030001d56101c0c100e48156102c800047d10100b10090040c1040a40c84c070b105c1a8250320b0105d00032601d071400461410310b41c492000c004074071250174401c03030401c9500b0450781e001ca88000700240c115052089041040740c0000351240107082c09800c00c001c0c17a110b0403110300c00c1541c81260070344904040c003401c110341c88880c40411818407942c40080d50150340c0c52841030600c0221071032000e81400080107075100c060080605c0d401c0e1081da034410b040c00c1c07818104110008441c100d41308000c204900c2e0820514100c64400341611640d03018a0015801c04400a60444000c2103242c20540d001402107032520703003254500e030203075110007a080e0041c02a0400003071000d0141655000b500e1000b00035505181c0f2a034240540c03600080c02e100741003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 961217329 1250 961216079 961216117
    0x30601290306150a181a0d0b030724090603020f04210606120c05040207080a0f0203040e0c030711060603070501050f070605070513081203070c020d1a06040c0305011802 74
    0x419040c00034100c0c03200a03104d903403038205080d482040090480d449103c0c0074408800310311001c0a00302c00c5410482c200c40c000188c0020a4000c20301e0941c80780c00840c102d1840c0c000f00b0040954010015000007082eaa801e11100d8a80380100c05034082c20b80140181807084c0814041e08541c1444000708642d030104590b10b642045d1607070001c0d40e07100e901c0b284a04451146030428425072800403030180800307a80079441d1104642d6003005600c0b8004000c800c016090b1500c7c1001e51091080703400500761101003002c28109004036081e01d5105880d0a0301244240d00c5014000f000815114400e140003009461581c0c505030040d0307030315444010038242c0484108400000a03096101d501d000e207480e5541d850701c9451640b802820401203400180d5150f000c28a15005108104101d80d030041d007918200711802094408140900d0307154100408042c600c443c07000c106c0c054403201c20303c0b1b44012602400b00444071002a0b00f1a00d0038080c03565005450441d900c1c82c034500ba001082d101200c04620950 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 961218579 1250 961217329 961217359
    0x604020c07332a110d1b060e030606150d020310050f030d140d020c0703080301090507172a1c0b0109030807080c030708041805010510050304030c030207090e030702030601290306 78
    0xb1548004500315420103039800d4010001e0504105403010346100d04048d00c4840d00765001a6650400402c010310505000782c411050f02c0b55601564240311080c0d100b9034680c213200c101101c50110300d0042e54040c0c5080c6c0043d070b11614001843c6003400030284c55510540600c0e10152800307600400320300c80c40039000c01c0010303c2c5120803c84440214001c16545440754182402c000c2a56800741800082009100b0000f14024102c441d480e0000c405008030200213108090181c0b140c8503500f83d2800114010030000381c58145174490398a1100210340270008681c0311b400540d44d80ca614000901038644c14048000000c031100028010140840d040320700b041c44a540e1150143d010303030030541100d00c40004210300d14400e401340c3d501400d42181c0c5180040560b01c2c00800c0c9010041c030180070400c416404900345130080c80f0007005041d1940301842507085036510603640c1d50101404074000d119100000488950304512000385195000490410800c03000300300d82c03940c10242105a2208001b11500d017 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 961219829 1250 961218579 961218589
    0x705060c0c1011030d0905100905010c080703050c04050105160804030507141e040506040e1903081f05130e03070b091b090604020c07332a11 62
    0x602110030310080203150760035014040c50380d895144480c02c0c40188041c1401d40a804020b4441c4000c80510000c1c0d01002c40c2440351030031a459041800b20b501c1c000b00c61081c0700040d080424503070400e4840305200d44800c01d0032000c644e822074404403a45014401400310358480c0c1d0041118004c00b481c1400304650640b504203507580554000c50b80b55100d0041044610500080e40e80248411a003040528030324921701c5031a0202410500d200d15903440001d110303540e86074846134100c032480003110700e00c01c1c06403030340400d502500201340c000c101c0300b500042e08030400d5032482c80c1c003103200c500c0c2d840c02740c2c80d24007880b00403488058a20318064a8403040641540e0401c05041301038000c050518090a00704d4070749040a0741c600b52001d181300400004501d90325450b400d0394210170166030060ba104038414a42c0d04008960708441003035070002256160b60284143c01c1241e924610700e03003070003124040f802540e00c00c50158a04400c00c4480c141001c1d5462000c1040c2d82460184030024100110180010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 961221079 1250 961219829 961219837
    0xc01031109130c110f060a0209060c1c020f010605240705250b0c0a2006030130150518101b02070f090203090a0803090102031b1218070506 61
    0x48010f40c0c440c00300340f0700355108071481c040482480161401c42d1804120a0f1541e02c001c0c8030154540c0c0000b90640c0300d13220003017103949400c1004141c030800092000301609100c0304808030fa00500c01c3c0403a8001514040c13144400f02c8100400c24242d0402c48403891074459a64504240d0303020082c424000030030400c0c04512002d00b500c410015540030507006c6001010710300c5c3c07c000d00444007404040b60f2004000f41c1400b400d034000303110080004040d600401040d440445072a085800400001800c5503c591110158542038401d0002c0c207901d40d4200c010005400b80c06401419200d11114400a15520884d04092501c91254a0f8100d00c400b0924040c5019048030f0002c2da50200c48108c80d0b030b000c2420f40c1e0039038144080c00f6840e02e80034800b0240c25242c0284e054943e07000010070752101040000e015680d03800724000b61a8901044198000d410403142c3c1d01ca92440504074401d04a00300c0c00322010001030302780b005030607141c00f041c946208800168008040c0300b2b090001c241565102e000d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 961222329 1250 961221079 961221109
    0x9130b01181e0f0806191b02012a0206160504260106060509010203042c070503010e01050402040e043c031707051e070204021612020c030c01031109 65
    0x7000741c41c0c80a1006802c0a00c80d400030340c2c644001d5205001c0c2d800c011a04c039400c0010700c0603503010360511204803c000d0505d00c00110051007251080b0080c5030b010340009219580c00c0b20842c840c04403800d006081120980c0e10000180c010000003195410b0908001034100154905241455118030040c40103a00e540c40302c5d658011080a0003041e10000d014080c06030040d4078140d41001c1c030740c0001030f6603030099003c0ca22009842d042044aa1034410071025208072001c0414111030410344e81c06425a8800e00486c4002803d200000c145401c1500840d01111280c00c1e0180544d0340e59140e03a03c030011070b030a0440e582da00c42c0d030580c50381b101a500300d41c0c69852001d186007111104d62501a11040781101c03d000c0b0310b82c04904001d001a02300d403d840b801c1000c1c0808113034951003c0808202445034900c000e501c01d10220340b008030a041141c03002d050f11710464201d2441c001014060365624040450640d15a2005540c0f0f08194820380007400880c01c080da04d02d0500090500194822040c0404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 961223579 1250 961222329 961222349
    0x708070c06060609080f07060813021207090605100201060303120e0309130f20090909030f0304030c2d1b090509030703020c19030b130609051b040209130b0118 70
    0x18170408005109145184001300024118a403038a203020b0400403004040b6180441500f480d030b0150740728034400c0581e6652210a8070019074480b03a5403402003d1500071079000301c0b162124001e407580144900d40580e5003545030000411040c0d1342180103442040b5148000380000d05c0105040d40b60030300a090a00500f140118906000c52203c100301c0744840c1c0b030348031000030101170381c10008440c0044030620744007919400c04a0b0346201c004c924511071134032200b0400741700104001c00c1c10b40c00640030560380c0c8214400362822451540600c4558511010041048590000d0340d0010392000a06504c1d094070b25400d4004541e8cc0c0c4001d0101d840031a11102c8640000030740700101503060003480100b0300e084508040b0600801003d410215090200815920850b008a2a108850048c202c105603110794248101d40b01490100e031181446581e034500c18071883c40f0800c803441c0038000c0c1c4084100c0640003228111084000340043d00b24802c000b0305104542c11728014243c0b8911000c0068419074030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 961224829 1250 961223579 961223597
    0x507051323040605090c1305070915020c0108010f083a03060e0c0423041119030e0d050706020f16080a0807140702120c030106091401051002060708070c060606 70
    0xf8180250382008040c4c607a04d4110390035801c0ea60b81e030040e0b40340c0d0b41c4440340703000500c55481d410150317540c40840e0490704001c1c0c11030006421180d4009944c0340c9682007a0b0340c41c08166650050225881c4c41d03801003400d141c001c3c00c0704007010000407036807540d0240040b0615090078192010b017040107298070740d11000a41c88120038030001d000d400d046a0050260a0a03910b0b052500b441ca41c612600e0a03030007910f0703107660000901c041c0c1d502d40000d094803900034031560351011080611006224031036045808603080141d0024441000315403840600c03003a4440c9498942c3d590307101c01c020750010030445400711042c080c0302810510340343c0c2d01c030391030f0f100d01c120b82d50318000c881028000e140010060020480b60611075a501d04801c800d440819134191034001640c00845205d03404d01d0122100e49805618049001030001d109401c4001d038800042c0000d00340e640ca4038144640c03466182c0300100568007840108405922803502140d004540d80f03800c040d090400d955460a4500340d81c8401300007604a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 961226079 1250 961224829 961224833
    0x5091602120a0e1c0b0c0c0102090301140601030c0905060f071b030602072006040302040b1309121d03070b1c110405100318030f0e03030c0a0c0f03050705132304 71
    0xc40814001032100c101341c1c2040241e500e00303920742c50091554030000b80104154403103880c25015215210750060090041211032100c120804504480d41800242408010078005001c0c00c1000e056030f4025082520300050b84100203140c1e40305810440e4100705184019421b04002205038000d54410000541d42c0c080c1810010114510a208110024107141314042e4565400c02101d04a0b541603501180c10600c0303000040300d80b1490b400510000781081008000c0040150f24951510384940341d404002c0849a9121511900c2c04880c40d00b5a0120001f400544480d0020300007900305011250321074401c0c410924142d0b101c004214800801c00304041c00305103405140d00b0300d8260340c0d280800c0782e0004d001e05a0210780c00c00a01030284032509000840880c8502261032402c0c00250440b5034400c01d0000c115654080480152031031041c081c2d003c1141d24440c0c9001045a0f00f00c00140006820b100c1080000d404105001400550f50101c40d02070b074642d600d4440c5a0741941030505414038041c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 961227329 1250 961226079 961226089
    0x9031009050309150408070603110d140402091005010804110d0503040b0a020606060307050d0e10140103050f120403062703020d030b1c110a03080c06041b05091602120a0e 75
    0x58000104c0d02d04144020310844000045a00444500340b90209040604500040b003d00c42c941c01c01804604008483c107070301030307489011406030f0302c00c0c0c0e420764040c0d4440765002401000350003164000b44103000410049004804110f200ca4801460310185142c0d03030b40d0f480e18580c004e41c03115408080108041000740d8040c4801c0d07038021016100c4520b10700d00000c6c024a648600200394514998900742c0410070a010082c0714840f40e80c4006c00c00c24540072802c040ba1024091108032120f1081c20705143e484200404c0c188291000d02e10118141030030f640d20300002e0b102402c0c206a00301c2c80c0405203110b941030005103103a194001c4d0080d048059500200806954a036034a8900515000320181603002c207070791009041a400605620701c91009400060002d000e50b031010b8403801001c40d0303140483c00d0101d2a20b0041c0d218846408411080b07851038190f035000e5115440d440b07201040020581020440e842007407241900c150380361810950424006500410342c884002403044812348098102 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 961228579 1250 961227329 961227349
    0x90709021e0327060708011e031b0924090c1b05010e0a110f030609030a03180c06030b090f010b0318010b0a08070602150c0d0e0304030c0308120a02130b09031009050309 74
    0x4c4c4c0308009123040709809203988c1000302c0d444001c002e100e50102c04400b030741400e030414020341820341050151646150300d031007013000990390203162002d0808000840d001580301d006060021f503101d80000c00700c85410410140003c58047d90195207130180c0c1d074001d40040c0144203443c4c2c42204060b0b4030400794018055046926a6418044d41c011400d00803e0314001082e0340b4041e2043c60042a001c0c0d11859842c9891290100200b15290f103802c00b0401c1501504400228041079851039842d9441c1d02891514007000e01c287e50340c0580c00c00200351209040f240c10070030007101400100ea05000b02002c501010400d80c0104100d40101001f8084607505008001c0c201c05032001a40c1c4130706000c1d00c00b1400e44109030103541ca2a9840a66041804c01070040d90010364100300b40c50704140e41d80c20710229983c0508042555030070301c9400580c1d004518402d4504680741c5049482655050841701d070f02c030b584002000d07a03061140303d80003484048140258901ca601c00e9028580b50740406081c0012909 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 961229829 1250 961228579 961228589
    0x12150d02180601020c0a0f080c0d12180e0405100c0c0816020a05031e010f1404020d020402090a08031c02040e1b1b06090709021e032706070801 63
    0x21501194001580d600c142a149401d44101c030080207032201d00060345420b40450a181d00302080742c0f00010b070300d070340074000d0000ca030040c9007641c000345d50304010420340b04900000204107650b10480c1411051243c03818844415910405c070800b45e4880b40c62451003001100e0442e1264420811014445064040d40b0700409040c01d00c660000303040e907114840c80c001d0f9003400305000000302c890025503842d00d1031403000703003005416184c7c40024141d005a0017014207030f00352120340c20045201d4406080c0d100b1001c0b460105540e0301c54644a0b64204041d40289130b400f41e0344243c0030f028800803a924008010010720244000396075542c2102003060080d48200800e15905106000400030307203840f91811a030201c250b0680211000da409903455403401450b5800010850300c82c90440c14410000b0024040e10417581240c1c110755588008100340d02c95200c425843c2122041d002c0d940c20340c410f0165810815689101c10020b10300754803101d4001c01c1c200590410340c4a5000e2001c855002000c1c0b501408e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 961231079 1250 961229829 961229839
    0x90f060b01091d22050703110603190b01110712060b0603130b090109291308090f010909051303080c070308040b060415080303070f2102090d081215 65
    0xa01e4020f0b40351200518040c90340d9402d04450019403981d02e00c1400010721008032464480d0940c0505100b990b521160104484074401c8a4031a50f0340d2802400380c2344110b0440216440504065070a1409003008101140c140000c1c2d4911003254841444081d014005010f203041c1c81200710700f003400c00e6030005200b03e030040c0c00c00c00a202030720820483d02d41905800c0044017072503840300c1c03801718014a0006000390801d00001c6006451144901c05604228403516010351035441c0d480094021048505005040344400c020b15059410b102c00140d42c1410141401018103584000d03040c161101107030540300e1060b5a40400c420140c00c81001070300250342d42c480ba070600c01c4690b4040d00203003010b040503201052240c00100140e640703801c4045501507000100c14290740d2030707038880d50f80d070000ea0390341c0003041c1c11420325081c00303108000c80b0001c1c180000306a103414003141e141400944c010300425404c0580c8040400200c2c203900018044004040d42007080303850076150140340855440300040c415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 961232329 1250 961231079 961231097
    0xf02100902031011070c090b090f06010e120a080c06010602160308030f040606031e060f09050a0f08040e09030705010b010906020a031815170703090201090e0a020904090f060b01 78
    0x942c4001800e00d401c45070314900000c414421060722420342c0a482e400800140341210041203444c010f811140c28200c0a40f035800254450b0307068494101e208407a064002903075403000b4019803602c2e4160f0f0480307035a0a4241c0301100c0b1035031105c1ca05640b1065001606a00000040001d41e5041204043c001c0000c042c072401c441c11980d5003d2540b002401c501548210000850705100c4d0320b5001030000d42c0d00c20704040d0700d0300c001c0c014040b40428903101a10820b10306942e00742c0e040700c1d500807101c0d00781c2d0107000380c1101ca09a0341c807840c0d00070380488283e4408000b40000300c0d8404541d001180206e40350701c02180c84400c9403030441d080d94520010541003100349001048400c0e000180103806540c90309000480350780742031450001840302d920541c0c0e404502100030346280d40007140d10844200c1c010000706c2c15910b0407030580549403002c100a0000789000340030481c4022000000d90400e00e0b240b0301500d0700d602013000406a600c2074100f40d410f806100f191104200f50791140c0341e440f600c01c1c00e10f0b00305 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 961233579 1250 961232329 961232333
    0xf0501210203070311041b0c0308150d02040f020c03131e03030905060c15100905010906060504170a17090907020607270f03030507021809030a11011401060f021009 72
    0x90f018a031100403c48080e8482c480e0a9a44640003064030010461003091500003140009240d130f0100314042e804180500c002c24096a0032403854103000708043c0070b11402410a0f424003000f44040c0000c1480160300784401ca072040c0c4144000c0034034400522803242c16500f800c0b10004a400c41d56840140c40105500410019030040a508112a8101d0700103031118009034030700d4245003400582400c0c02101034200a030038454805180c0503aa03814204000d56a01c0b080c0c0401281c1c0c45004a46c0803440902080084c50303d13100303c400c4005401c606981c1e004049650b03050b40032105821300e450000000c6400b03405800c10640d0a58042003500c02801d450030104006401c0c02c10848500b0003464810a56240540940e01c260b8000c2202c032181c0540c880d075030f0500401541003810102e02c1446400c1441842100b081c4110380154000300165152607140e60080c0c8483c9580102941195202c1100346061742c900d4038024002d0103d5140c154020800c111b0003402c0500450200318250f20340199100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 961234829 1250 961233579 961233583
    0x309191a0304030210110903011409010f061d06120607080601081e0105010f020114090f0f03030f0a09140a05010f0c02011a1017010306020702010e01030603021309080d0f0501210203 80
    0x17502022842c00000c0f09040c07107021107401d2154804480d0158201510340310162044981e9600c119000002086452a840300710800c0e6149807241e0741c1481e02d001503803520b00740b1903603410350490002801009000741c45200e90f828000d08840c0318010420820821046580100c900d591081d42d00100381100f038070882c8601481e05060158604100803800d000e4500c42c000d5000c4101d0060030f070080300305450400038155461110215202c01c80c0500c0f00040c41c40710303000080c0c901456110207440301a6175901c12480003080b0520050340d481c1510903d810b5105820b1181000307260040c00040703030364201665020291514106501304580c03503c4046102c0344108132107512101c00444001d1000300c4400310849003010204245d69010100d000000104001a802018014400e80312074030910244001501100c04500c0040c0d040858100b030f820310008564401004075201c1c0a00c0c80c00c003000c5100c0542207860303148201750030580d80c40051040a0030460031401c6080050f40da15030709069680465 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 961236079 1250 961234829 961234843
    0x10801030b0a0e1603051b030601030506160e090a020703032702010c0219080312010902121503010f0f150f050f01050313080324010908030a050702030309191a03040302 74
    0x1803455641e07045030032410b081800140e000742441928004c8041d12030611a44890740f9401180802400300740c140720030700b80401e810341205d8102003c0d200d155143c03a400200d1a114401c038000f089034002d00360041d50f84200c44d107030048010240040c1c4a0701d0740c0c038015088030908148880490360750910034101c1810081d189580c21ba0a10b000f1080c1840fa2000c00d200382c44010010003e020300f04c0012401050020150074440c08000a1400d41d0b680c441c912002ca208110100301c0595495000034812034001ca01c224282d10301400025107245a00f400380e040b035440701000c02005850b2107092076420000c0f03030301e40003800e5501071031a0341601d03003000240100b404601c281d06202010002410070300680c0341d001c607066044212250340e850105000c108007014094402c880700440e52000a2075440b4120b01c009039a1100010742c901809584c066840b074100d404200d900d4402004695121340b649155010100c0c089a42c041c2d420b404c050321007842414408904141c03600070700400c4013103a80040d02e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 961237329 1250 961236079 961236091
    0x507030b06040b130b030703090b0705070302070608190608010501170f0309040908040801060801140a0911040f020c010204090b010221070816020d140706020a15050720070f05010801030b 82
    0x1913a140218a08803540c3e010b6540700801480005c0f080201d0309405410440196205040c8042c80fa41c030804240c407140159900540168805807080c80814010b40303405800034000c0d100e06202c2c01e1880e009009541c000e80160040d40d46407001001564080841e03005d000d0382e00b002402580c01040c5c2543d5130380c05000181449a501c9007030b1903041c4080d16088801400040009101c041d840c0d000207030107000f05070a5440f024108a00244c07020010740306000926622900000e039140c844410480604030750f02d81c031140180e0800403058800c03001d100400c01400902c03004901240f017440060305142d106645682d821840d003258112040c000021101240e9101101589540f00f40196075940e98010744020341085801101809010186042d11103c2c0d0010080320542d58031014120b880e4482c61344001c2244803484880e100340b500ca0741220380e02c44031a1800c1031106889580e41125011140f1745006d058020034414400e80b0b0340c0c0c60003100a82801e08100207030b03515540e81c50800382801401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 961238579 1250 961237329 961237349
    0x140102030418090f08210a05060108060d0311190c1a0f130506040308120601050408100207060b060307080a24090b280501020118032c03010c050a02010507030b0604 72
    0x603002000103005180358059017054025449030300804501341d00142d41c103045c8411130040c10000380c10f44010f001c0c0d00d22415041c1e6401c910350302c1d54000e0040d0800403000403001e00c1420103150700340d0142002b00c2008451400b14501121400382004c60f41a00740703400c04081030003c401c4000c0245124000c03a200d00401c83c00c44d5076a00301d6a00d030b050103c50150071040d8001c02c002000424095084003030918110103c01c110f01c1a1180310054486224502c203640040c0c01001d14a0a0140141e0207400042d01801001c200b2074905000901c03654011150749022815060278841c410f00c1c944910001c00789403164043c40700045250b1640050020301c210260181c4a0361031101c03613115000406541d1040114044480c40000407003400030f0313158054280190318098402d05007004050301c095203141c141c0c450b00e030f10500b0032014a1507a01401c0c00e6900030700c908030346169152402d2003610b12200c82a03031034644880310010300909403080580b4071410507040c07404002d810b0347d4800442c0d04441c14090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 961239829 1250 961238579 961238591
    0xb120a020f1c24020f0d0e010b33120f01060903052e09080d0c140d0c0507052a010203030f0a0510080a0c030b0105060408071a22140102030418 63
    0x2c0303a0f25024101d65000a000303400440e602850b0488540508150707880200c041c0144000c000c04103080314880c6810035480031039400c903201200b0342d01108403400e8444969540c5103114910a00340759034800c1c1400c0440301c5c85c032810001070184040c18980980054034024000500c0d54445640d5000d184504100e1222040c5490440c40c09034503a1205518003200705003d0110a811b148200b600301080c0c0d0005142080000802c02d032041450724a0303900e03da00c0f56810030800e000000020201000c2a409101d000c00043c008035400b00a01d1015100302c071850446d4180f44c2d50094401d103000b600603415940240b051101000a60b20050380c841c00e0450001450350311491101d5038060301c0da0020041e406402c0c514000c0c02152024401500d014400c0f002c076030f90f42c3da030500200d4400d07441414107039002a1001e010414a1804082080c184040041e003088404c00c8295808480314055128000d4800d108120a40200391422003800090014508103443c0c4040c00910002a002c00c083c01c41d5a91 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 961241079 1250 961239829 961239863
    0xc03020906060403051b030607030e19020d021c20010507030807031b050c25030f020301060308030a0902030705190905041713091b0e01120b120a020f1c 67
    0x82628000c2d40c0041c206d03680305c2c0018204130848007032200654040d0040000081980b8041d0207048402101440105402001c140580b02e4108200204990140309070900c000541d0722003c001c015100b214505001c15080c6207400039404801903901d82c0390104040d003210b210783e003020549042e1505402c04c5c0203560307903944080f002459544241d03034610908105480300c02c1d42c0302014084000003082206c656580c4001e0300d00da0100c0c0d9080460300040003850600001e00100d0819041c00d1000d00042800c0f91030f03680e011a20b802c1190036646c15176270b44450718107614080116400401c810354000b1840180c8603000304406020303003e0010303091340710700c0820100038100801004605030a4031840d11496100144840c456040c880c0881c11414210b28400d408800e069105254059031030305a80c8400c00c0005544c0b0804d28044402080e0f5035100e642450345031103400e00c01480c1101c0180000d40040e10402240380100d8401d0303030065045e02c2800c0700f0800300030200051980c20045181c44400c030302c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 961242329 1250 961241079 961241089
    0x20f01030b0301060b180103050105240706290102060a15140d0f06060f0b2811010903050d0623150c011b110a030905060306060f040f031b030c03020906 67
    0x2e505c00da03000d03000052030507030015102088101e0b02c0400d076018000c40c0d90701c40801407081c842c14203140c207202c0d49201340503050180a001707140241c4198800700c6d014070380102d0160001d05548180f0004c40400004690969050004552003519104100001206030304545c03060106d5001e032142c40c06002c203c1d12959a200c00004c403d8613480a41d80c0601d64403850320002401d1544100791a2520080002c00c0004800083e02e51510301d00c902c2c4095040903003806010007548070444003d01c1103180c102024001c0030b010301c0702e0342402a204d82d9603640c41c034079011007213078100d40c446070b4048000b403c143e01c3c4550fa6030801d0340300c41c1c0448001a0028111502c00710900c1042c2201c07907a903281000060310310b41280c181551881407916004c0407600319502c0c06071a418880d50003000100f02030030a209a01d4410080c5401a40c041e05050500151600c45602d40e40660803000c0c03e490410402c1042064a01c0449124482c24140203a1107107503698240e0401000d000080c4104040000103070709480d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 961243579 1250 961242329 961242341
    0xd1209020a032603040b0f0a09050d0305190b0a05061e0c07051804021c03051605010f0b01020304050916140a031a0f0a030f0c17030a0318020f01030b0301 68
    0x4000c910300d15600c3c40e03d905000450016100f01c80152024070350128282c6056030b01c1a60424000402d56179007039480642050001c1c29804819507442d54100400c1042200707484940c0350342c800007040d01b001841040b1000741003003128421030a001140d01c3c191212104501255800c2c0c1e9002d4450174401e0703044050f4014502c1300c1c2c000150219052924040006420040312401c0d45e202c000e520842a070380400c401c4c21240a5000a40b040205042c1d40c0c03910140b0f14181e010b890440c0c28002d1211b42510b1401d41d4540648891303440c0c1c070b000001034082d40700d1054840024001145884e1516000c82d0840da801405900201392445070303903100d280984005103402d02e100200e165110314200c80035004041d003a02c0380000507116225201507051040703280c03100001c010000001c80e40395546461b00340d107400e8000c07600c0d0601228006030032a141040d251140c4044800382d0b0b00c1310542400201244c21039031202c0c85209070b884080001d030b12000784c0707010052000e207404140c80c08508003113030141031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 961244829 1250 961243579 961243583
    0x6070507090905030a1e090506030601020703230f06091e01021c060e0a140105042a030902090a1e11071406010f050402030c030c09031011030a05090f0d1209 69
    0xc2010503850401501100800b111700700d503110620503101d041052000ca46852508001061b21b2040621040c5002009075900c414144110723403180384c40c1c2d0b0751003055a680b03c41c1c0c2d60b520601480c000311881d000344480c4408048013002068070b440c2110440740c0e41e600046890b8a6420700100a0400000a40480e035100c00c40c5090042000c000c602264011301d128402e41d80ca00150802040c0300391028080c06041c008c1d1040315400716400d01301080000c140c2e41c48860121648108140405842140d045d2142d4015440000c0c1521705030051001103130000b032417400d002e8540040c1d0314041d910844000c00b510742f03002c3c000070350750354155441d41d040c8070780d42000d0059201c0700c0042d8500032002030103030f042e20001814103850b155204180720580c0820b0358407030040e0109000088101d280355000c0c1000c090000c0840740d03001d80c950358100c1201c00c07000380c072400e4210000800c84071241c24010300b40c10609400040401d94410042c00c1d0700c40c1c030015106400c21035045103601c5410700580050504c15 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 961246079 1250 961244829 961244831
    0x1a031e0402010c0807051e0a050d1409040921080712090c051810050d0203031c0b100306140904050a0330050105041a0d35030a05090d0e0607050709 65
    0x1d143c1e040c503d40c2e030124040c00c1807100070300860400480f47c01040d4804031030350000003400311800c6074800780c40303420600810400c182024800080e5581d110301541420078021089030815901008400c207029858001000c01d02001105010a66038001241e59000c4610040054004000c0c0f902e4001d44020b544000c0d13100c1e14034010f440c5090088051207005010071040c41000700da940b002c2c001000b40d07918000c0c3d40b41c1c10a00241080501c4840308060030060004006000404c0c41c0c009480b40e84501341190000341d4ac0d01c410300c08254044038424065600f2141a03600e884c6c1651940e54403e0302c408000d04200404030110120800300700c03840000c13a4040c08140c20591014480c1004003402d128051240d41803112000b03000e40207800504111101130a0506490b900e48c81c3d5240345015007003150140462008090309100d80001100e060509240026580742420880041620070140060b5401d80004000035070280c0c1281041c0703002c0c041036500d41d4655509017082801c115031503000c2c401075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 961247329 1250 961246079 961246087
    0xe042001120e0c09010807050a140a080a030c0b060904111c0b0a0c02120c03190207030605151206060303180a031a0103030f0806130b031c091a031e0402010c08 70
    0x4114049501182250f00b42d640c408281e030388880305aa1070006214242d000346c00d002080c408a081840001d0381b501e006080b03860388560b02c03d60240790001c66003080d00041c11141c180b10400107601409a044102155465101d0800d600da441a0841e03041d0b01d6407080007204001c04420061641004042d904000008501e1900c860103c0182c10981c10350001406000300170f43d10410702209942c005070016000758100080c42012026440f1000018415407013051030000015840e030144500c1060202d40c01c1c680c5040c424140021142c04108540d96900100d0030880140c40000035505d407441c0c580b07140212243c000d40854401501a000544400f2200d0303116010041e404580e18100e0303100b42d40d070000c3d540c0d1111084900040959034250301410301004a00202c0c500d400c00040c403003004065881d042000c962402c4210148d2002c0d03000300309a00410003d4420840c4001140c107c40b0346d045140d842d0034800e2a952040c0d07501024418001e60000c107003964414007801c0c1c3e0345540006581c0d91 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 961248579 1250 961247329 961247351
    0x10f06270806100e0c0406320a08010602010c0210051305010614180f01062f0106090c0c0203070515040803120609070f3002040f0503070e04200112 65
    0x1555412a8080d84030011400c3c00100320303a00c05002882040c208008608003070920004a03100000403060001069010303494541c0c3c000c404000d61621491035042603038815072540060028001603001d88250791510942064090300841e8203080020700590000e4165a5034045080642c40500013074a203628000000c41d424400c40002c1e00701035001c41d410600b0108204988000c0101100c0344030703c0d124000c0040100c1801229503403070341e890381c8110f0000d04401d002106c209021004484800360346070b440c100845006403084214000c1c40e880c00516120054000c41d903900b080e0301c1800c0c041c1360a104d060700d584280c8000d8402400c04817042d6581e075819111243c03003076103090366054460720003000031810090103100103592100c0309803141070b1000388082400001c86800ca03028096611001c6030042e048409200500140c034545110344012414030060500e40900d980099810502d68824440819054003820034080d0076107020058a0241d40c1c0102c80c131810248070300c1d942d9170810014410b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 961249829 1250 961248579 961248583
    0xe0312040e090c060c0a1101020a0614060a0902041a1b0106081e16090203060a0302190e2202060714060f0a0e010606120c180305010e0607020303010f062708 69
    0x40116200b008680501820004001070340c810031000e225250700001c61140042c4500c80d0007821843d05005403003060440c0d881d0001a42c07003046034151007001c2041040b0491404801d4900503090381c420450801c0d0800704c00320300940d25800e1980c480a80881c04001c1c00c110002c42101d00d20f0203000912065a8070700585554202c803010103121141c0031f2034180151303400044d8200b02d0883c11302c02081440d03e04000c4100030b600140000b904070018030320120140c3c54806441c8000992540c511081070710f0480640700c0c0303580c040c200350a2a1040c103c800c90490f218820f9084003a01101c4103030f590301003807901c200c00000507643e038550b6000d500d0800002c003180d02c031454880c4100b05410300c0710707030701808165003240c00501a10b0007007084030310000e008039050780c4460050801d9080240c0d4580d14242d0340040910746a00c11625030303440300524800b064041c0030071500b0140d07900045045504104502c45100c03828040d01040048902d680c900b42c101c0745041455804440200a10803500c40e08e00720303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 961251079 1250 961249829 961249831
    0x80403030206190c020c040b0105160b01060f0c050a03081312021e0c090c1318050a0b09040c0612020f0a0f020c151c1d0106141f0e0312040e 62
    0x1404040c0302030b4180c030808050380142142c000719a809000f80302c0e000010080140004074230181006010320105100c00d1680340801110350155003604025850444005d05540f03440d85d074002001250356050740000c1d800500c210711180c4c5070034042d10941c0d070104180007100300550043e00800002c5201c20a458001c250940d119100702c2c0c2c01d8030f4120760300e10013130b649860f00800e0700c1d080440000001d01e0880e402c0098242054031a0080e0310032540c9032082038940302c00b80b0190f051103998a0601924065600c11708184410685814106180545486240442174411541440403602510011404540c100c3d5030358110b90804580703c208421006003a00d48840c043e0b40544a041c079140c0030342c680f620001c44001c003000c00d024a8000c0c600020342d144c1c0c810800d018415a1103800c5c80e1105500d401c0000380c2ca025030310000800720301e00524406d541c00e0582256020744544e00c0c410200150341c20309040707800214203041c1c0e580740440c0d002c00d2401c507413648130324010326002c200030138441d0104c0c0c002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 961252329 1250 961251079 961251091
    0xd18032901171606020613060b04110d18020a15030204030f030c02010306080609100207050309041415010e01050304030c0c05122512120512010308071a101e03080403030206 76
    0x4640a811440b01c40450f07107154003507040541e00c02c0c0c00140c175814144200e515001e100348008114144004c010a0949204408920104030301240761210703551144150003004601034500c2e414814650085000040306010740c0000d0703034110448064990194040343c00865105c0000c02071403140f4100100900d41c80c10f41240000e081c000d001070402c0c40007941b1405454480c0150194114072030030640258040750084480f80001d2018401c10758980c882c1c000c02905004400645191142c5201c0504c00301c06040c03030510800b00b002903000e0b644002600c0e072040c1d16007880041100d8600b080007000803a81d000c1d5a1140404900c241c0f030100108020721007146c00159081c40b0080807031030f051160440d01882000b08000e500c00e5000c2160095030010601c441c0c01c01030f26000c440003c031041c465098005983c0e0001c00a40c00040000b80800c0380c0c10341c0721803501000e9605044100030180310741480381804005101c0b4004803080d0a82032036200440c1c1c03102c05182c0d1581d60f4031f00a501d0380021242 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 961253579 1250 961252329 961252333
    0x30e091905090606010806010c0203010e030f0712080705120c07060e01020c1509061b040801060b09090c0a120507050c0604060b010f140f0315061602030d1803290117 73
    0x102c2c0e01070350009075060003540c0c140c49550199417054011038540c6132444051341c1c19925010420302c1048288010070701817103982034040e6a035446003025010305900c0011901048200c5003000a13460313001050303940410704901000b0717071a01ca05c10308104900820b50064a41351030404c0101d001c0380e055000f0f01081c4203510565440703103840104528020b804450450f8241c014000060f001541c820140313481d450500300c140e0600e03440e002240c0c2103811542004140100000e48102d2520706a061a40e00000c4420014944049030b5801001543c0d4441c5003801a5190360200d007a250207503042d141c441804804540441c600384c01d120f00903060310040c45004c240f070725420000e124400d003281d032004501035280c03d03c0c181000d864440640e100070072507032420200c0d207081002c680c1c94000400d00b89000b0207525104105500405042c0342250034494140200d40041e02600c12243c26440c0440c1d810081103241402c0c2c82d070202d44c040b80c00c6030303418a40780b07071007000419004082800b01d525180d0040c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 961254829 1250 961253579 961253581
    0x306051003140a03200106030b040c091433030a060b04200a050307031107080304061103070912111503010812031e040f06050c04050319120c030e091905 67
    0x50294454610b43d0003d00041c000c40505a840840300c003680d00200304030000095810f550b070f11180083d410a8808842403080100304100001c1d160080e80e441c20301200d202405810a50030040c200007000d203202b81201c0048124407418101040508004880502130341c0600200b482e0041c010030304034880700d104038078251000000b8042c41c0305403210700c1141540c191622446520645264100a11450405840b41c10032804280b58401803c440380c4541c982d181c0301d04052400805552284a022465400c14000c001e4a203600c0074840b4200c590381c0680300c1c001901400c251040032507860001e070304144000d00c0c0c0265101c2c5280214120340103d82510400d80070494414074910090307031052041002d9404004201030031356501c07500a03101c5d103070000d006005552100260b49046603244540c8078041010441414180201c00c0b0070642e0341003420301c05180e55180c908001e21820000e0802c03c640e50000105805a500443d00c40401000300c440e81c80d0000c00200344c0034000c910300c002507007808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 961256079 1250 961254829 961254863
    0xc020d12032c03041206020f04060c02030c010c0c0b1e040605040f091404062a08070906110d0f050c0f07091d0c1c0b1326120604060306051003 63
    0x20480c0544142d1030014516003450300400601d1036122203426507900f0703820840401502c081800400007802143c0b00d5174041c001da401017500302501388480c941401042900040007403000982c0a003641c140901c0039450702d561070507560f003000e800802c00701280c070001404a41c20760440098030803a40c1082c600305c85103480d03400c1901a2101c41d85c1920000300100007180c0041c030140c004448443c0c22501514141d91078402da0710a040e4403001501c0480c031400180400e00307500180400162911b0304100c0b410100000000e0f994116140c3c0740020411340c2c94054500600c54011940d6095a110444002d480387c41070203921110188203090890307182402c0300c1c0000d04c0c0c02c1c01e44110078170030310081e05000e0018014824011692a6140358500040e076011b00060300a1001d01d01844800c03e07204003200091506000c04080d4840030281c1446e03006441508848640880d0007044880711080b0b016110000841d02421054000900315402c1a0400c101e500f10441164120b138050455405400649 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 961257329 1250 961256079 961256141
    0x604061505090607080706091511040503100c14191b02031c0e4c14040509010308190306080a030e060403080304050a11010215070c020d1203 62
    0xc0021010a4041c0320250203464214003401030305003d4600d80f440e1141941e21001220261074044a07034490f440c0c0e40b00d820036914840e84e00290550713074a880c0f400d4205000a5a200451a50a0466500c98400180d802d00c03903000c5425548001a13503070784400c1064920401d0410f004050000030701406880089440b03e90320800d080ca0300074000e800b503c207840780c50000300300300c005a0030107100d041010190280c841c010003d5a22b5141c1600c800c508001d6104803040b0000070080010074055031005640366030303060802e1501c0c5807480c10111b000c0700380600d40d81018059072780041da0180c0d81200000c24805c2c00d50003801104090300401c0900300122000b0380c1203134003901558a4940c0201541d03400030307000d03050250703400c14000c0c5050300300b980e80c0c0c2c0c0301c43c10348e07000720b80865494105166440400c40b03151a003d00e03240003400074252030000060401c2e45404000c1c81202049440751000b019911044c50800c0d102d0703048001700c14015a0300c03030302402130180802800702c0f254041082c101d06042c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 961258579 1250 961257329 961257359
    0x60c0c111905040c17090d021011030610230301030605062e0c050706020309030d050306090c0d0f0614010e0328170a0e150306030d26040803060406 65
    0x181840c00da40508003000d003c010403001c0100303004e1090a0b03100105008441261510078600a801003034003400800c002800d294001c24021405400e01c4822918036208900fa654000f0042d96980c1c1d0000007044110b0b0141946808490131800700303445c26604400c18001541030303034099403041c4103540f078490070b1040d094445070075007001d0903100003101a05440801d91854520040c070340080c0309041c1e034849905010840d804000035910000d90600341d81010310601f580740840d410801e0440c174000b00410803202e001441ea01201c0c2000843d89551442c13680110000c0c0351100c3d08002c5107850314030002ca0800300c204458045501d000c684041351400250656070f407291448012009106080303040010400090112404602d240042c80010000303000340040402d50354512141c1c40454051103001542084800c0001100f00100600c03038400081c071542c61841c52a01c08802e48003403c0c1c0105013416251040b90609a210a01c0f0074480b0b031601850290800b264108480d603601c1c1484208054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 961259829 1250 961258579 961258609
    0x30303090a030e0a270516020c0d060f090f0606081902120f060a06051c02062a011e14011a13151101150b0706020304020d060c0c11 58
    0x840700d410140002d114001c0f0030b0510001034044c030b841c1c68031000ca40c03840c082c0700c21640c00d2100e0b012020705c1c84d18983c1d001c0c082e085102030035a0040f040100c20000e40741c0304905101c0b401340004803c080c08010b81b5600c001e14659442200f005641002d2410317140c18240044161052428104c000c81c11020224050760a14810118070000700c04960030322001018813844215140500c4080c17200104042c41642d101e284024000100c1c10300b407208102c4c0c1554a144800400801c418440005844100484120b60340c0402e075440796040e50912000720700740c4042811940e500b032501542c0007030b5507101c200c1e80b0388500a80600c402102c40d0060400c0c858248034000c5841c00024800315404000e00041541031941d00008009545070a4421000311001000000081c40e0101c401c09145007171007030203c81c00d40c6024010f4940d2402d9003240035070103a000302420880e40040030408540c0c4461034a05040c1e072044040c400203600c030702c4c0a030442d50491010b884140640706403003d5031914000b41840b4423 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 961261079 1250 961259829 961259833
    0xa090b070303150b132c102309071808100b01030609090c030213020c2a040e0705011d040e0115080105040f060c0c140715081003121812060b03030309 66
    0x80e141402000200301d012a00e006d1042034042c500100d9203803210801d20410007840890f0a891a1000680e4400501c1c0e884c81288501c401204c1465961100002d8208500b032a20103100c2c101d50b0303000400c82c5840c0c3e0004e0500d200b1a017148803201101e41002d00145000d80b820400c2e2a0b0301c401034000d41c3d4882c80d00601d80e42044000707000525100688581034542c9920050502c070b00d11015526041094058050000c0c00340502002000345802d0903100c8032050740c0034015400b0b1500400d5032900540141418000314480d954241e8a03c60b582c0003000c20014414071800d4101c0030918020700b00c1c408040e55500501c280807508500500405005680c4806004400807554403898000e000041240041001081c07101e008a80985030651424440c40050443c40345004070b00542142d4584d00f64086c000d01000300000c40d070380d44d00074408980d04040662071000038082c003120080086000c0b41c08202d541000864030111010700c20003850320500b0b04002c020007200815030707640811544001706d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 961262329 1250 961261079 961261117
    0x24120f070617011415070c03051005070c2102160e01060e0d0b040b06120318040b01030c020601030f0f081b070b0c0606220204080102190c0305030a020a090b070303150b 74
    0x5003800d428500095207042c0707178142030503440d5490341660061503105507142c0d40120000a00d2085910400750002040e082501c0c2038101e990b03802140200540c00440f4065018a821085074004d018000141c0c1c0c50340310900000e41c07504c1d803003825010b0071300510740040c80d2848002c06900704940ea0050141e00004103501c81e83d100d582d4440d03000402800f150b001a0343d0303502d002246000300041e068400100c05200e00c060b41c0c01061104803420000b0083c1003608195641007000e4001c1030541c1546d17080b0314078107800c50550409500e094100a0004c15401d0300085140c1451191075008400e02a4501035500c0103036103040d6821540516031001c0c03926085000031541c289450601c0008286410040190322414000040d0498100e40d209282c81c2e50001000c80e5843c00d401070488142c0d6031070811184024094400508038040248030042c0b840c0e00091007203001c2c2c041c1142400900030b0140b101d070340303019a15008014080d00013800c03007a107040150205108040f4015075000c000c40305815845 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 961263579 1250 961262329 961262369
    0x4020d060f0608062d180f0a1a0d022803050706140a0e310e0303100b1617070614061c0201031b05040510050324120f07061701 56
    0x11440c034141003600ca21700417102e14843d403580184000e101e803020841494901d490142c3c3c00ea1a10f00505100da91071038a14041c505850714911003030354203400e40340789842203018800b14040058080c851a41007400d860f0400c01d01c9074900044e400e40341700b20103485203039955000641d619003180351b05201c03000051000000152055022441c001002040c2010310516001b0342514641e5a5401c82070341080403402020f40d000501074a036000c031000e00118a10324000ca00d41446000b2401054007002c40060442c829218107481011a503821100c518010340d0304040caa05990b00410040b42c10b20b0a101c1caa0025070741c02d80550744611009809000050520030140080c072901c4082241415a40e100c441e507184440e0381c0b5180151701e542c4550350b540341004200003070010b44c4912001000400c004000c0b030b030402e42c21002181d28455484040200c001130008500d0000910070030590b00c43c02c400507801e008002800c030100e400e030791140c01c2c030301c0707441c058042009900f40201024480602d40b0604 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 961264829 1250 961263579 961263619
    0x1209010c080c010c02190503180105071a0610021c030c050408060108060f09011a01120906020412020f091614091c0b130c030212120c03070c0902071e08040504020d060f060806 77
    0x621109c052400501c0c0c0240b45d85c1c2d030012000b080e2031100c2c4103040340e402c01c402414140f154186180942c0014008071032010710b40400002d03400c034800105600c900500034424003500540e409884040c05035900f81d80c540010030354800c1c0884e062440403000c000070038400c41040c030810040ba10411130b6040e940c1008801507485050b42c003602000d440e81ca2000781c011070f040d0b102401c080d1840ca044201014158010801d00d04000321407580f050380c7c0641032041400c1803804090700e1894606081c08000502c00c8901454011505800c1c4c201007095101400540098032040081744076901644c0d00d07844942c114142c2c5030035400024680c0419030f4052025180c04410300c0c4070510120100c5001d182041d40303030045a000310b0300d07501c40d0758800f180040801c0301030030082c00a00110b50703007103040c0031083e11400301e4040c04540310400090a191000180308004c411107010780400b601c2076544001c9224a14000c02c4c0901c503001c02c030400f6400215a09200d06203040c0030f03400c000c0c983c008200548000071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 961266079 1250 961264829 961264867
    0x606011d09040809040c0206180d020d030917030f27070303084611070305090f1e04060e0408310306051e04051209010c080c010c02190503 61
    0x40c0703018805208513101a40e460003070792100503c903070142540341420008006021040084005940c10404208450550000e801500314245290105000c449420076880c501c0815a55400c000400002c100150403e9105c66001e00b21a119a21744487c1c1c1c88440b41d44c0f400c1071842c0190303503044a2803c001080c0310f1088d240c2c000040101e20b5891031090440c80303110700c0111000240e000c80580e2510240780a9899558805a50346000e20024038920129001c07031084000090a10402048240307258842c8000000c2211010301a940031b480109443c0003141d004010107880346060140200e400050700d070702d03103000b26405100c4904083c40840c081d0369404050b622140e22a45d00700141c80f091100c50321400040d4080e9a00150714109a01562100c143d40740b9400d03c49100c0c0e03001e00c0001040001c41001c421010034499440350f0000004803026000c1c160060142540421001503100b010b60004e0540354954084600368031280f5420924a04d1104002d0003e030411300507181e01c40c02c003e0b100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 961267329 1250 961266079 961266083
    0x190303020f0a02011b18181d060105030c04021303030c240906050f0402010e01110f030c030405010201060617040b0402040e01020c0d020c06040f090b03070f0608090606011d0904 78
    0x5424540800c00e15916900b102003401d005130346032600c0340048090700703100e1160002c90b0724110440c590b04035982000d01d030301c0b842481e16070650003026240d0a40303554007071103090f180c0d520401d5aa0301c082c1c042e1981c3d010203008042c400c3c010019580840e10385442126412034181e61501c0c1c3c141d265031002d0310008241141a58250301142c801c5d1040413101c104020031042c00500000c0c1c00b0400d040c01003c03900002c2040b224014260b0a00c800740c1c0e0002d000000242c400d00c2c240390785201c80c4030707101c1c2451040c003e40c0c3c0c01403201240502e01c00101101034000e0b5a001e90080000580d6600100d803054050902c16411070180008900451007c0001360340c091700180020500c620030000031400caa00035025040385130403d0544c1400c2d1039040c45002100e0404454260529003007182d469078007109442a42c0159076030b070003070303e80a4400340a030320020408003006c0f100103a030b242806001c0480481e00b40c60103000b00c00000740d940d03015030600c0c0d801c18218402448070035140d074240091a440a801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 961268579 1250 961267329 961267331
    0x31505061b060106180518150402040f060c121713050a0803070e090f070e2403160801050409150f0609020d060f08120702191e06080603010608190303 66
    0x40c080340d40808100c50343c0280120b0782c8042c4544c441101c1c00d540130b80c860700320912030103c6401c1a98014180811260000b140c030411078400599100060001d215a501c1b000e01400540e000250a48d0403118040180e8000c0d080100800407803501161849002030f001d5108415482c0407510707800e841407000350898814005ca07201140140c8400006403c02c40b0030100050090b0b0b841c005609040500035000244009091107a0810540c090041c00c01c00c4040c0340614092481408085804111028080c0c0302101090352410590364112034001e8203d00680401c02e01c00000849080c58407502c05c129810200100d80003484000240160031105404072042d6241c0b0404920909144001c0c081042c2d20400054481d1500c600c2040403d80b650050f509500000074044446040f001210744559048801800d680c0500e0580c921400290f000030070f8854001b0072904039181c1ca42040c40584225850b000364070b50b0f96504141c2a00c880f0f0080f400141c000d00403a0a40280c1c0c0895035080c035210303040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 961269829 1250 961268579 961268617
    0x40b09030403170c0f0d0f05090a030606060f110f060c0705010f0501090b1003020906030105240c15180d110a140106096e0703150506 59
    0x1565070107010360421031110504005540b40c400340040000201100140d001707015030f912500005400c09411f00060002e1100c0003c02c09c14035501c07160014055a8801c204120013921407c0040102400b200c202020407410100c0100d00d41c00000c2c0d4030300f40400c00d03006242d61366400c40e4007401074000c40701c216419900c8880d41030704001d4034024180a407400000014038940701d1010020602156544042031510410510301e95880707003c101c905640c400d031501e051451071110b0181c10b0003030304890f03925400004201020141c1011079054580388050f20841c01b00e071a500440d510103545a58409103650056102004140c001c3c9421860508140203803030070030081781c6800881125a150700b00c0c160755070300300c28000b8407541c0c03107005455540320f6052203c0c1c003034104921456408200d4009a450790803107860901c200c03d5100c1131120b1200341a0740d844a9082d042d502d011443c2c0c64201600741a50380002118036100b441403401180903074000c2c0c000ca41ca0401400900e500c020180c0e00c0b11103000c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 961271079 1250 961269829 961269833
    0x1b030a05101d1b03160b04030807050a0b040c08010606050424030e1509010f052404090204020f031504020f040504091401050f070305280b0f130c11010b09040b09030403 74
    0x2014444907100c0030003c071810a10000300305401e000c0108425208400c840b2414000398a041058500352540300b410a561204503090180c50071041410080a101d401c1041104000c0103041c64402c40314084000d020352030720343c0c07000d482d1406103014444406040c2210307164400030494514080d401c0702e0800160304104800740500b0b107042a5440341840c0030410900171044400d124a40901035408820412030800e4003084075100d800c070400306100a02e65604000e16038403075104421899000b8011590f82c040c541010480d50011035180c01321b8441056a91400d06140c021692014001070010f07203400d00348402c01009105241c0107803000e4240c1d580342401400248610f50080500c10030014a030300c1c1210f0000d040d144010030154001010a4620300300c2c039045194807540c965103060118002d280301001c00c055180d190724103035010136005603020320300c0243d61005e104406641c1e55800c4902140e54100d099981c4e00502c0f0303030030405050005020070002083d1540000320318041d20325040e669 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 961272329 1250 961271079 961271083
    0x209060a0f080d021c0207032402040612140c041a04051206010812130b0307030f06060906030f09020f040c020a06050a050f01050301090314090a0302121b030a05101d 73
    0x180e0000b01d11503201212280074690108060601c81000600f1440024844d40000303454086a1100900107809100c1c11402c100c28407502028a4164850854459980f14401812188607807a41c503034492500d80c2c40c80c079014034001304a114030600401d0710301d8185420242d96070346200740d15600e1052400d02c8040303050b40e600d644000000a04c000204000d504040240d81411031003031951428660402411482c0d91000f500c2074111841d65002989a03036960b0400d8010b0b00300c4422550007189800000324140f07800c0201c28056501c269020401040403c030801d0466884403c007135444038481c6400c490528254000c12140c441900c15191a0348455884100b960020798248d14032684810800148402c041d2840e03005207000c5000340700e95001620040c052035452400c1d13407030201001400401a0301c61080c540000c0d94003602c2054020351140d009501e0728100c40a0a02415008401904500c1c0000d1030428240d0014094042d1000882c4d000300207200400302c140501c0f07003078a0003040c01700007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 961273579 1250 961272329 961272359
    0x40c0b0c0a11030a1e210f0513241101020a1b02010504180b090a0903360b0301090c030209100302092403150307061d0d0c080703210c0209060a 63
    0x5140c07140c1c420503190703280101c4c1d6081c0300c50030b24601e00e03c0f891002d1007540d84071b604401b4007c0b41d824080d5807504174890703c02500031190002014a19202100030140110000f00d01c20100c5030350710762800b00304041c5000e080c0c0c0700c1c07240004006400c0c00100c00030a083e845840380403070b1050414a00d420b503249449074200030b21120300e24946995480561880c1044414554081046002000560b43c103683c090200044c00c07550701d17001040b08188120701c07805030044203404c558a00d80e030780d402641c0c5c03130000c3d103258024000d81e000e0a050410140407a4000c0c026207480700c1009181c00d42174401144114003d4000040259103c2d40702003c120210415070302d21010003070302e450710554900d0000d1055101c090704070002802a03006080400046501003165450000d0303402903400d21000010014040d000c040d14084e060a03643c1c1c00010b581c040008007841201d00c54a03c40b51141d0003800007000c110380000c0c86601040101201800600e8000c0100390720a0300100300115244e1508145001101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 961274829 1250 961273579 961273613
    0x30d0f05211906050118090e0a0b090f160f06050c0118210806060301060e030a122001090b15032a011b02030709020304140d08040c0b0c0a11030a 64
    0x70850101c00804040e0b400f40f90b015000a09080f105541c51002080c0500e00d103116207041c05980d41c091428855081c41540880c0b03400152184090502d5100303140c8500300700e500a801e43c03207850101c002c00b104000d20302c012505140c01440c811807070104252429400550381c1c2107075540c0d3b0100542c1090130021503c50b8113000d0105a400045003804075603101020030401d500b400000c60401881e070b5210303004c81c1c0c10748080d0310b4651989446080446d00e008506003009042100c503241c40c1a2580d449103010344183d44c0c5000101075022448441e508a130008000a0000744540001641c040030303400007003d071404054120345507400310454001a4080da180012001c1d070740280b0075142e541e07000d1013003c9900f2a010214100c030300035900080d41e0300b1a0384107680445401000050500511600301040c2e04680d0042e41d21003140700c44001c101d4042210110b4000f2000c00300407034501e400b141074501c140340b90801807280c0b40e45a154dc45000c000d840c1590341c14070507000c00e08005000100381600b119 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 961276079 1250 961274829 961274851
    0x1602031c020102130506090d1401020702090c090306130c0510140a18140102150a0204150816030536070e0402040b090c07030305060a030b091b030d0f0521 68
    0x340304c0c000789140040555002ca4414181804440b08035940d8100c41d001e1035a200807518001d41030800e02034068001e946d0042e44c054030030402c0005084040006104a8a0840584806544d03c180c0749030916620480585460382e4000c09100c00c3c00e0011410400b00358504090b40c0c3c440b000d8400701007030381c03050704207400180d07405c01100c01080c58680500090801c103010462843d000f0b1000075a42c0940b215882d11182c2541c0205494819590440340a00800c0c5064114a01c200f800a0a001c03400d66114a13000810701040302154031030b104040c020100d08180c1100281100085150500e0050600501e003115a18589c2090700400c03081c0c0003480e84d10708200d000d207000d004101c21144140c9050f03001700c1c5a241084441d5820344115810f03d0740c1070a001419454440c0440c0ca804642d030401882c0208010a001040000284034140542100d4585552460034400d1546800300c00cc8094040303011752525420583c000c00c058801074150301078801c41407042c03491104a445080d44d40940c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 961277329 1250 961276079 961276087
    0x9110904050c03060d080f0708070c0f0e1e090c030f070611070f0608090f0123090a0209070c051011030f01081605060f0c1b1908031602031c020102 65
    0x1410140149580800900300d05411132421030f000c103646103610040200000d40014030a006d0304000400c0d248400d40003482151103d80500d000d881c220700314007441844000c1c61000050903040c65125900c0351382581e8030030b030904400081d038001e00200a17004071711600a014441449480800c104612407040c10010326071280b410340081c00c10341c10702051600c19041400c051203182e80f80c07004142140e003d0f1400c3c800548d00d0100031410281f408078100c40ca03508145021500c04074010b54030540d528043e0382952507071118600c5c550746150188000350040700d1140052030007070182c00034205190181c403d070307a089040341b1454021a0f401c8028180011400f00620a29210415265015110a41c02000781c001440c00c114031401261280303500c10100010829a070b846554117580a0002e20401c95019003407404526040c8100740001601512002c041c44402100040d550001c403041d07003010314075090300c0000804e6181c50700141660184078980c2604c0711810b4000800d554481300790300050311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 961278579 1250 961277329 961277347
    0x1d06060a090b2808030f130b07030c02040b0105070803040b01150503091203070302190905012601120807051b040b0d0203191407060509031203070903080d060911 71
    0x100c02904000c01d014607040c808a180e44803003080042d0b00f180c1c04540491080714491030048150103400150141c0030100d007103c44203180300040c103410303501c3c0e1608034002034030383c1100e503a40d006d140c001600084200749244098145a400420010410701d001e070715095a503240c001d451343c0240d908860f54820b07400104041e5922202c032400c2091240b40181c91800c10a504594030038020604022401d400070200d080340e40241c0c1190901c1100d9100b46110b282d00300400f405840350344c0300b098041031112241000011a10260704000003900200c2c0f0910703400c0c02e1589010111840080741da068040141c403020540070015900b80c030613604461120000c140052100790740c28070350300c2400340d030180070f442c0016940842c403203403225403405402d044030126003005000c500b161a502d0801d07000e607203000325070f0561110080134004000d500b1a40e00300040c1120401030b11007210443c000075040f0005000280c081c17401001c0c40e200007d404103400383c840d0748127402c462070218000e100d618001a00c0403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 961279829 1250 961278579 961278589
    0x30504030b1503030403060b030309041a090703110f030901090f2604030c030210090e0702031210060903120509092706010303052d031f15140901031d0606 68
    0xa40026644500042e089002c00030a91328019408028442034640b40014800d4408100b92040504020310034015840301c014048407503400c0943e0280100f8070880052980f0340a402a00040c00c0c7d40480d281c5442c1c4802c07540a515040a4401c0940355242c1c40482c000c51080d06d03840b8561401080d0b0080c3e80c1c81c3c0007600c00c078080444030540c0d080400600003040400c000b0521102125019640803407d41c603003030400c46446403190413803d06019403209002005500002a0041100c14004d00555446000548070707210b40500c200030014244c8441400090031b4071f00d98058601e12401c1541c00c04d04060b0001d0100541180d81d5079207000703102d800010458402c7c4000c051b0380b05170b40140c40154110386002b003042c0324071b80512418401c2c0c440011480656081c0050030303800c111440343e8a03030402242403a00c0101c0300d410000303443d0362881d000c1400002c00701d000030041850344850850319841c100952464100410560516030748483c25000036a0b80c0712000c1000c6c8034100500014900303642003103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 961281079 1250 961279829 961279831
    0xc18090b36010801180206070305120c031f080607390c050405161b150c020705030d0c17090d03020f0609010c1209020409140d1b030819020c0307030504030b 69
    0x1c06a0410761801000c001241a405806406a03540756568a82782400d441d80c1c458480421305c4620070804002c5022502030145000b0048000b11076406e0019000300a4285d0075401020740c0782d000840401c800c5030180c500c407050004c4d844017100c00f01c442101c0340868100a19460001d03d940441c03030300208480a0b84407405000210740400c02030400040e400904401d108014060004d089440000792521054206400d64000320031200329202440301e2000d058000707501400f62044240c0442c00d031a011a03480c10700d8415a5642503403007980d44a004050020700700501f0a4035040040c4c80c4642c455002c2c0704800c1b4040d40090100c05e818403585881c00d20b0080680c00183d140c00909127001d54010360106000600f01004a2400113500006005012540c0d0082040942c0e80c00202e0a540200e00c14004100d90741f24404c4242c406001c2075110584450700070001442e500002d00c200c0e0346c0f402c400c0040e904a160060030201c0c60680c2520350f074080b5000758042840407d04000300001c612000b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 961282329 1250 961281079 961281089
    0xa03020a0512072a0803180405150303031302060415050a140a09061103250b09010504021c0c081207050115080a0305071e0c0503010c18090b3601 64
    0x20610f000c10685404010780c4580f4140031120401c1183c00381051000088680644107403030075290342e107280350120728002201c0c49505004604000008290011000c00b5000543e030290255203141d13070b44102941c24031403420040ba406001404085480031040724682031710b520a40701e10b980c500c40040c000d4484c001c10046035030340c042d08000050540364445818003c448a90422604040800788103a046014003555509805100c880030b203600058034070300c011071034007c0d82440c0b000e0700c5211000e800e0300d1084030701a400417071044143d964409216141e0070018001c5424407000c58842181c1420070501c40301146502c140455a6028050b0a00c42e00c900682a2032a50030100c5c50031342c0c001d8407001070302c138041e00b4081c3c04210107007030241c00001003500c40000c88841d00c16480b20b01d048440e415450140501941c03809202d142d0160203411841d03403000303581000040780381c6400c1401d405091000c0c036058008440c4904071301240340c2000054040b69604034500c510300200040480789100513840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 961283579 1250 961282329 961282363
    0x4181e0e062512020409050c1b0f0a0f020609040e03180108010302030d050c070e09100f05040b04120311210903040e010b090105070f05011b030b130218030a03020a05 73
    0x10b0001d860b24050410714403000c0c14030880c2c1c41c5050740140002e000d01d600480c046410302d010060040d0280d8001c0c5005c451007100c1000ca1680c0e81600c2e40d0b9807800f0304d4130401540c0300308051008201c8480100d00090310040c0440d20b0001803002207420b4415404e5017490340d03480070891251604070302100d4aa03a19003031801000d55895034002954a002c0bd00c1982c0902400045c101704545007030050b200600508450501581015103c41d95920f1003c607107030001510f8880c00e00003049250142500545c1c12050000b003a44070703911110030b00948442d80d04181036172801d040c0e10905000300a4403031a01c141c070300c40c841c07140402c0d100e11070410002c00301c0741190000c0000340080e4041d805041d056445c0ca0808a071103040320001a9210301c40c0c21400f40a4500e41405002001b605411100c04200c2903034452070340e18104813007a001d941c1c02c07680840d0300080c200c150807072988071a806403c1c4400c80e645d25000c102a02000319080c40000103064005802540030a403c1c01402c00ca024100510120303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 961284829 1250 961283579 961283611
    0x11401080c0f041107050a080a030f0209010e131b031401060203091e030a0f080c1c0c02010809030d060e150d12110c150406080a06050604181e0e06 65
    0x10000b1006070740c080c02540314680d40c28445100d10b0324801605d20603503115040326000b1102c0e09003d201a0041d052030340019041c0f02c040014003002c1e00a0f145c640a0684620704256100f00801c000c0c002400f18007401655110f03403e040820300f0030889500401c441e00c000031084040002c40700300030016000341d0b0642d40304100c000250f4503020034031007840c2030fa07082c07429121a00000080c14108452070240200071907508100c1481050002482680a4a0300f22046402000782c0e003000c00c1445107004002c21840d0640d00c001d54082c4a51582c4607070170f00292803610324060384c5602244d9090700185605c050b04001c000e01c101d1460f68001c0170100485004203131801c90f5864000c1a2034181d00c240c20040c4034880c41210440400c074101c807a40f401000580c907501074500505c3c4540103032080000040c4500301155041070103220f020262900904002e19043c103003250754104103400c400c54600d442e9100100c54000c45100d1804079841c1040c1d80208841c00c2024002c0e250100140095a241030245 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 961286079 1250 961284829 961284853
    0x60c02011b0305160c08120d0b010903170c03041a1201090204030803150d0b0f1509010506030117030d090c05151603030c140310031406100b13050d0501140108 70
    0x1400e80300a1400b03501000e44c18455483c00102c50103070b55020310506c1c402d4407040c0b02540388000207400341c040c0842003002100c2d440401152201190b04c4060172610075100743c69440340b82c40004100e81c050690071030740f500d03594641621f5100c0d0920380300001d140e004500d210520345104035031401050003200a5052a0330340d12aa0703110300c8041d10f400c180c016483c1402c039031600c071400042c110541040c41e211161401c0f0050020840044840310b1003c0c05800140c5090700d4018104c030f069520280415040d80c0c00d10010160f44100c498828150f0b2109100c1e1021502d00c8d0302400728090b1007000072565079450074043c010502ca400c440c1c1c0c030030b010f020300c100c0c2c2440b181c0d5008038010580510300030810411560056031302d0260b40d041d050916000204100c455090280b0510032640b01d100b6400c4604403442685840300419255100307940c0a1030020455545c1000c06130100c1401d502030640c405603184000742d524000124216100d035120724600640001c040c98160040039140060407800f2170380 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 961287329 1250 961286079 961286087
    0xb1b0d0504050f04240905010f08030702060d0e0d0314060409150b130e030415142209050a0e10150519210b0a021305060d0e010501060c02011b03 64
    0x103400742ca8024090848060741595807900101c2094043c1d0400d01001985100c2049024949000c0d11610900b010000680d003030391800040c0496604034059403d2a00030b90030803009602208070580e000d51504800241c1440c144007402803944035480005810b02c4641e030300d0103140c030001d2007070380700b1440c091005000c50200c1c2c52080110302c43c500300084542c58440090350034111042940380b8030f4540940044040400001082a0b80c003843c1070038030400c0b520b0411181010394410421800b41c05100c0081200004208548181c2045204030003254651807040122042119252a42c5880351500c02007000c040c0304648068460328018403100088540000c481011886007a000303405803403900c00c040e0b8544040b080640754150050680ca02a92840b010360b14600b40d0035100d0b24008c0000c118082d40d10703c200c40076450340c4c1e003c030801c05103044200315440d007084c1d210300e941603150400211000020311030f1501800254442c84003054542c000140301400ca8600a0844070714001c500c0b000c6a08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 961288579 1250 961287329 961287337
    0x10e07030c020718060509010503011107020d0807060504060c0f0f0915020f0a03020303011d0405060714090d03181e050f0307090c0206072d0e18010b1b0d05 69
    0x8030308000c901911104001c0b841c0c41107983c001000424080041904900c1a07040030088500446117411141d80b03880c01c0600325090720440801c4110200b081c1401418203000c801031407801030707660703038200038a43c1c486e48140d0700203c40440c4d080d50b4900004420680007098800548460320341420030302c0e03c610010301050340034001ca160003194410045480d520800c00f41d202080f014081d102c4880851a01a540e0740080c09180c4501254a500c140401d400d14446072040d0340000c000c052a45a80c08280c07940320400120030103a9034100700d00e0303c1d16100c1c05d403007400580c440e585482c400151407444140308106d0ba0442c0e64048075011b1300c060518111003002c416030310704a403c0400c451a01e0300003407500c5519071105400c00d04003091b100b520341d0046040c0744a1822522052880500c1407008491101442070003012101040c01e01003559200b643c03031107813030b04000d0240822200e1203584603011440980c0407689602c000550b2030440c071130032821141003800714401041c50000c0c1d0b100c09011401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 961289829 1250 961288579 961288591
    0x1b030a02100b0d0f080c07080a1e0305070602191b150e2a010e1203031906051203041a03070c030c020105040e15011419181a180108010e 60
    0xa1a02a1002c06940f0925000940c03a40f010074144101060f140c22071664201e80e0b01c2c032140b0300a9040008900001040403103030f2503840080081180d00981101072005421002a0100b0500b4451003000990520081c01c003000200041307a030001404000901c000185400080100c0c5030401c144006140481850f0315904040c2000c2242d5451607645460116241c400303d8455405011400034800e11420f910038110342aa601c81101c64044280078402c242c8030f070000802d07401000001d211104040d844407120001d2500071412070781c2d4070f0019003404c005c01d9580c141504001070401c101e1002a402800c00c84610040d14154504040d001d007005c1003008006d0280486030170820110383c42a01250050808140340140b64108445101190900c1c503180c1c901041c0c100c011580202c10b550b050700ca0340340e081030300c0b103584d030481c004211b8100e10003103140102d07250b030444040b80b0310b021003c0711000f502102541f65111260410400c00181059a10f1410709c039507a0b0040c401040c13044141035200d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 961291079 1250 961289829 961289831
    0x40f0504020c15101d0403140351030c01050d0f05240102070b1c0609090803100b030f01060f17010806061219110d0c0603021b030a0210 60
    0x82c0341d89000604019000e0207114000000714104904454403829400c2a10502189008010303040490b0441112090380e003e00804d515410fa10b005851400045510036040c0c98211180122070b40c068418000c0300d4104810080b02000300e485c2c0002c006200102d541c084100c0358803507001c001c08a61101e5142c000c05041203000600154050020f41003001c2c4000202c00402c5189401e0184030708440311082241003001c3d5540c4644901e41c40052220141e4128440d140d00e040590340e1894811707600d801c20041c403c3d44810000030404618451100c400f4040d01c3c0d0107a80c0e01d00b40d4092000150309400009055038144240300c80c0310440c62610341943c8603401c0c2600c0075502007400f0741d03448410410300a503030800030740041018030004c580140201001c1d2202035860b000d103800d9507141c410112003000c0c01740307941f4210030119400f90201c1184e100058101c1c1200d40050f2541c0701e825982e6040300d001309030001040c0380200c2552201106141c00940a107050001240c0025210005000b01240709 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 961292329 1250 961291079 961291087
    0x2180402150f04140402091305060d2406051008041203060e070f14070f02060d0e1c020d091220040c0e130504030504292b02040f050402 60
    0x15200e10101c4005421100d5006459510b441d00e8003109501500a4079072840e50200e001c1803d0815000369402c01c030005000340c0889031021040001001c0040c4146c0d44404c0c00e106c0180483ca0b03095041031841c1035070780ea0f2698254000d10b4081581d200c0c2e4003140c061060207180300340003640100d690303070081e03445070b6100000307001504124058405a00903900c2801c10400307001e4030303039080480b060880e107164444410009840307005081c0390040000241041c6c8056a820300107240070707070040c58003601c0c08000082c01d480c6d200aa904d0301c000d840d2000c0b40c009128001c0c8842c980c041001395580d15452405058190801055200c2d140f4047d0009011803400d034441c400d4805c0c0c6c0c104404210002502c00c100d0b506d048003005084071664080a40201114000144c104402e4003c9a103c0e54141c0c4420307207001c0c07500e1941c1c0920201143d101c00c00500444548021491000050a00c41d1480a9904010130039002c003580310440071014600c050310402c07040208126543c030302c804a0300120784c0180c44e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 961293579 1250 961292329 961292333
    0xa030f09180c020606090603030d0b120a0f0c0806150103090c031b1a030c0f03090106030b0c0406031b08130203030903010609021306020606130f090506180d0c021804 73
    0x1151050700445039039180351000140980c00c0c0d0380300b041c012000b90b0032a54a130300d882c4140300080c3c0c01a20480e0309078004000d4821100032940018000301405440c1002d10610030981e603082803907034001180c1010492803001c00340300600c02400301406558002d418a0300b080321081100024810f9028103040d120303591581032200b0703e05184011500b020a4481054490f16181440c00942c091103110100c0403620005404440050b05d1160041c01001490140d401c001181e46070030040003000159240d140100001c0d2039114010700506204544036140d50800034094181c4d440d0741003041000e50400f40466407183e00c68030140c0c000c68100f4039000030380c41030300209086104101d041c540560810000043c0e108242d4000c0c06400101000c0c850f01c1910f8080882e201c80c0c0c1991240e50110f40926004c62901c81c590101e80e14858001c8009035079001c69842d6420301104940030354480800c2d200c003008094044c002002106007510345118520b103079a00240c400c03542c0301c1141b40364030004000581 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 961294829 1250 961293579 961293587
    0x3060d0b04020d060e010f060f08060a0914010e1b010201021813091e0507170a111f0c05070f05010c122c0f0f0f10120c0915080601020a030f 62
    0x18141d0840024407020305000741c05c9001c1c16903148081c07103203407800c0b000040f4072543c284004203807042040500b000c0c0d00d0320350b1004013074841410151410081100d5840c0d040e4000d10a21081034184c4000c3d01407200d0741c640700f4500300294040b55055900401c0680e04491541d82c1e101905401210701544001554540305c3c01801c00c90030050200f0b04100422071100e13841002c4142c04ea00c100100c0d0303083c0d44c0320041e02454140103100c20246501010305400000c403c2c81c6d800326100006050650009152541403003111a08401040411542c9048009010080c003c80b00501101c00c0c3c2c00740303000e1605000801400da0010068401e8220200c10904603114002c0140701030004200d40d1005111400d51030102e0504c01c2d144c91181d0100e9a882c04541402d100912940d00e0042601c004681c401041c040400311040c0c0607010060222640d800300c466602ca02030056101c0d03034038230000a091005101c0005686280701081c001d160003081126070340000c9442c24540c1c145440700d80d0345221142030b6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 961296079 1250 961294829 961294849
    0x902060d05041403070f1101050c060f071715040e07050a03060f060e0702060a0609110a030b0d02100315080102040311120f120c1c140f070b15090c03060d0b0402 71
    0x580f0780c0000990b002c10300801800340c1200900a20104211542c3da000558662003007000f0b4040581015000611403004101107551000303035400c000385403d07003207900c9018034401150000716110080b2004070300e50802303100700c242121701c44000740406420000000d0740904941700040203144c0700d2010240f041c080d84c2152000340400645c0c1441400c04c500040d48509080701c01085291070600c0004400c0d18a0081c071414423600e5051628050b02210114050010f40c540140c00c0b807a40180d150050700c60040344201c003642c0d0b039000145d0170040d9030714100c02c55031030740560850b038014842400070414140a44130790714011116881d0304000c5941c040e0070000d154a1035403107800b80d40c00740104400d489006001600741c450a0361003103a180c0c0884180800c44003006070004101f030440c400290728031002802d42e44031910341c242c01d0081c01c0e940c0181d00c4c0d108907909034060081600c01805400c200000c40e4100516140080c203500d44003000c00c0c0c00d80512a030180400c4105070115095488006940c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 961297329 1250 961296079 961296113
    0x20703140403060501051203210622050a0609050105030c061e0c060a0b0111151512160803030114060a091d06100c0803010306021b030d0c0e040902060d0504 69
    0x3241e01c46540e820440001c0200340306140c025200c02c0011040a0710100480361503811000700881c04010800c1c039100c094000422450f0003545c5403c4c070040c20001c44240030940c0000e1000809c040c0f07060036004094403100d40c4133500d854107010050005a42c0419400200001a04c0711507ca128196055482c41c40c640702a8440d400c0016010b044490f0200e001c9124140311082440700030a094011641d00d11000180e01c260f401c215490341e07003880c4198105400180668010141421080c0041d000c08440d0164801c6a030028540d03d4100c41c00710800d038014103d00340618103543c9004090340e2200e900080d200c1c420400003074480a00303030040070000090285c3c0042801d1002d040d1901071107205080e90010700c510480310590740391038821010b031100968440d804a0441c1d107142e484d10041c0d0070024206503568102d40c0c52082c4000208041e041400e0450004206500400b602810072405100308030f00550515180304003503200c11007245c1016065510005090340c1d02c0c207000b4445036041d606 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 961298579 1250 961297329 961297367
    0x708031c0c052101050a050a051e010207090e0a061b020a0f02061201170610060210020c1c02030a0f03090f110a0902040b1b1c0c030203090301060e150f010909020703 73
    0x119907000f140018289042e258203030b400a03452520b07078003001189480ba2146030341c0040880480030252218900e0f9840c4d000040c0101c0c3c1541b511a600d51003520102800740146238070416010702804128090041c0c00300503203400048020700303564000e4541044500c003405156510400c01c0443d03d500d0200e071001c00001000240c996101d030260110022144140c02d030a1180d68081030700d403661035100344101c40c00b81e0014002c0700d00044034075010390002c802c860f00c5802070b4081550b501403641410001c086441d03014543e1028030038405000a501c008620041516064412000070b0034038840c0da03843e9400100b80414052120005541c0030b450750404015980049000100040400c007e07000e6102c1c085002c9200c070070170321040c60b55228000100c0311030410222009000328000c0c2800c0100900030301c1038914011950b00802d0a54202e035109200002d419030404c140e10711103105051440d2001c03110364052078000d0000800406240c001e06d65500e0b0f000855508060041d2a0410307401c81c6541 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 961299829 1250 961298579 961298617
    0x903082a210a0606180b09010c02120d050702011b0f030804061e0b010e0301111b03070f0c0f05030613150b0a030b04060b062803020d0f0e0708031c0c05 67
    0xb640e8054841ca100f00e070042660100213078a6890200700640946500501850401899200466207644e01e42e40a0341c0005062114090000c001d0068070900030360342c3ca495503140144e1000525a60400325401040d801000d450310004141442c90003155825285c020000c0d00c0301d080c200003c0c003414854450440c112803051000d49032039008090400ca00744ca48800c0e40c0100c2060500341c43c005411f202d951141000a006040c0c4202203034070164081c1d0003100d080c558581c0e146641c21602c800305130b40b0f60900c40300401c03440d0354003040c1c180034040680203007000c0d0600804a100d21118604024460b000000718040045007560001302e060748010500d40e1069079030305281808000954069820a042ca400110076060041c1240d898642c0020016101d4100300100c04445205900c90001c05400300802814020107008040a90402c42c60010f109814481d00a140501d1a4003460240c1c0040c800b04e4010304460306c00303420b2010700c1c400c0880c00059116040326544142c42c9608540034000c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 961301079 1250 961299829 961299841
    0x30604020a0e180a060b0906220f0e0a20190e10030f0609090f0b15090a15060e03030a03090c05040507090807060309080306010e220903082a21 63
    0xb004601504038513500f0043c090312132032519030354414070483e181c0020041111080c0c4000c02c0034800c40c040007142e008040b998030742100684000031540032955031540746041c0b0000c1c4c039080c0b00b0350350340a2070303401d00b000c00403401c01c0300801c2801082401c1e40141d14140101c4401801000580034952000b4012104091401406401084000c7c1140c007407600c1c220001c52800d0180c0f05800041360042d4400015440b00e0b42c0d00b070340800f0b00904000820062440141c80d0b501c80005403405054108004a00300201070a80d0300c40701007681c08401006180d600c800c0042d03c0c00700490b80d842d191450301150360f92640c00c110302482c00070b5000540041c5042c0422403140c0d8010480025a01000c0a42d20702a51300d610443c240c80f1450700c054204101000414059070140d1075901c0c2201000d480200c8010b415007902d010301c90340302c045040d0b00ea16842244105075001000c0342d40500340e02c103c0c1400d0200c0d40d43e0319003c00e000c80a10820307924001240007903202407000e5140d0305c803080144100d1901d009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 961302329 1250 961301079 961301119
    0x601150e040e0111181207050904060f05010b0c0105060405040309050d05030c0f030c070f060f050a0c051203070e06040b03010303030209150301030c0512030a0e1021061d040305030604020a0e 84
    0x4031802c140e0b05003521171755070051900600645540340b41e0303002441043c0c144002c00a07128000f0348101c602aa50b940c0740c0c00e030302c1550b004960083c0719811007180c0754602c84480c0b90a4032002000140f00700d1a0004200009800001c2c0e1016100c1c141c412031000c6c0440e02e85030b880c42c81810b40621951040c4007981c0440c5000100900301c1454840c180c5208654450100003034944070300801d004a07508280004c90144650040d05240e41c05183c200403082c40d0f41c481b0f03828450560603030b0180c81c0e000410000800c0e04040058003040007039841c4d503d0589410f240002e43c1c0070600008040640020b0707002740c0c03542d41426107204503051000c255501d5a40b0b01c4d0038001043d1a100e03da014140640f204901d40d203012050342c80440f4207882d2440024052020800d41527400b05c1c04006001e05a807101100b8050803a0310701000020b1000000d0003414a1503c044541010707000d00320002c201000c1000003035110f82601d40180e8152009a1500600d400c1500d5540380500c195802c004100c8a40710450a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 961303579 1250 961302329 961302337
    0x1101020d02210403080703150b031e10080c0f0102030f0c01060513020306030a1101020f010c09050310150b09010c08030a09030e091b030604141906080601150e040e0111 74
    0x1e01034012540d40c940d01d4981c2c000c00d40846024001c103041d02d00207100305000350899803460070b001e4607240c40181c0340e101c0140c85400c01d49a4200d003d000703200107030f14400700b1100c9a4000d905111a62589441c0c10b201681d213200184455008010740b001c4040564020401d42e40001d10501180e80c480400300d0f90341f8020b059070f11400b8440e8403505402c6100200d00e01c202c034028a0082d001c2c05504642d5141c600402c280900e00504512400c035113440c00034428850304000d07602030398648205510f004c013050b1614459036941c0c90010700d029600c032640a08402c4550880c3ea454081545480000d03006950755600074001038401c0000100f0801c0074440c07903205044542c420f45804003c44800c10611860181c00c80d04143c90088203180d800820099801955000000030400b150b200042070b400414044240c801c0c181c48015015003e80c40401c50281d44090210f40c4001e104962510a007203006d80005503002c01400112515000b554645030424810021614020300159054040030104d40d80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 961304829 1250 961303579 961303597
    0x20403050d120c120c1707030905060f1608130501091110030e061305010b030d02011e020c070e180a0b010603151a1b0a0b0403030f0524011101020d02 66
    0x2e40505404085a09845900480581581ca9501601d50061114020010b07201800c05001d07400651a2207007a03030708045403103040240d034045600c0d403030351408510b40203000d8040c41a80444008020007000a0107084140d6012803500a0981d00d42d007252041c0270081200260965090501d0030080c04604c4100c1e042c102800d40344c0741050280094100d040741c8540c140b5502640280c0b000c9050710301d01a0341800254010400080c001042c1d50000340f410350030303040c0d140250351241900b900034080340c0704d8498040c04c1c500c411752030300003030061707460301c5039014003d8031040d44106012030b6203107405a224802140c1004111a005032060a007002070490074031030080045d00346451250680750451080d011204481c04040004e0240303000d810064214840000c000390400d40451b042040030800810504d002d0101c80d00c940c02c0904004059840701717038140c1d1069042805000c40141040803820155080341c0d45104004560700048848091b44011010300f9070022400206464541d802450281 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 961306079 1250 961304829 961304837
    0xc04060801090504030207051003060b0d0c030b030d0912030c0204020d2007020d0605060d0f03090509060907022d1203180114010623030108030306041505130e0f01020403050d 77
    0x60b03624810380c0e040d500202c41c002d0040c2c00c0f20400300700714200b10756814107488440c01e0118900351224a90305894001d03010007030340b0386d0b2250896012940c041c80360399403c050540107014440d64581001c7c02c082d1240c8902c205005c4a00c403e074051500c541f203080c03c2140e00030b02c00d65480b40c00c0304800000c0c008a544503440e001c10000745c0748410621408483c2016400352a1100c070151076107802000308402801c5903007185401d1081d00010b09100c0c01203000714425103410002500b4070091000d2154010030702409090040c1c02d02040580000f5000c8450800d100042c0c0048903101e0561400f1820100c0041144144c0b111000d10084000185210f00c0021140f0005082c003058074509075800c0d0001c0c0c000070760900006202491103046120082030700c592051000130740d14032043c00c25902c2640301116030303080801805113618140c0100e4904400e00050b0348905820200003c04c040c94250305400b140d51303540c803085034100c4c2c1401486400c40f850b83c0215115a40c81c01c0850b120342001800c0c2c0005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 961307329 1250 961306079 961306081
    0x20307061112090303090330070f08090301090c060f2d0c0507030506070324030507090e010b030d1e050a02060114280504060905190b0a030b0c040608 66
    0x1a4460005004514810002404038400c0e00d40030118640c00411030f0740c0c241c0420081301b07031541c0f02000b401000644814160303628500400c1000c2c034500c02844600000c0b9010440345c004202802e1107000f5041c0c205440982d601144030001c0d00410300414000c2085040100000301d81e50030100300011000d198652891000d0039403d04504a1084c102803c1c00e130610303000e203e0f511171280c507103d100503108404946006440e0380f0703403d14240045604030002902c0b5074480a9107048080c1791001d0a201042c4c60303030503501b140c5c7c50303d845240720b02803050300301c0e0b071403583c6582e080c02508200c414a40c042c3c00d0300d1142c50361a000401c840d2034070b20b449803408000d100d8007551610503021036288100c958003411880c1d00346401000744800c2c03500790a80c402c244903404e41d016050070f10000c120250900605070100d14020a203c2500d4450380711105041c581400c0116400000d0445080607140c00000070316038034948001010040c007908050600c4d130b01c9008010040042c01d000300706031070f17554039071140d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 961308579 1250 961307329 961307339
    0x60406051c030305060102030408060f060f011b0201120b0a0f051c0c030f0f21030e071202060310030b01030305030403020c040b1f0302040b0c07090e060103170f0405060a02030304020307 82
    0x8801d0304140384071100d50030500840400d20a502c1213411400c1403051760701d031a580e0100307030307103007800980f10303821b07690200400e0020600c0c00315a0114541030a0918814585044681a4892241c800041e045c031a800701e25040d02d01d00303644459500280100454115a1256008405107a0500400c0d0040c4812680c0c44026044403455203000c6500518803045681565100c4405071051a0b0894400612100120008200c490803a2a00004400c1101c0300311000c1c2009082d24800c580c2c1d1442c42d089035000b40403441c2c0c0240c4052080c1e8044c4c1300d41da682e881d503010b40031800c7c0365a44041e0032500300340c0000c030070107034050700079030140c0c1c020303401c80c0d40301d008002c10441150f05507402c01c0e900a1100740d1400d1034a52030b04221b164201c56040040c00d05a8075001d1107995417002d510f145007900080010320002c88a03204400032500c008009011a6040d03a55506500c0c03110340440c004000c001c110506501445821a0042c0030050605a2a0080910065900e07002540d0480c400d004880d00810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 961309829 1250 961308579 961308589
    0x90c0613051503040b0403030b2e0210020a0906051803010e0a03030501080316023c090a05100b0d0204081603290604020703020f06040b0f0c19050904090209090606040605 75
    0x80245d07000751480ea079940301c0e81d03800d40003410b030343c8082d5402045810340402000603000c0c1d00e01c00200c100b5102c04000001103002070605071015400c0c04001d02c1845101003403a030105800059802a050003070f9501145103518140780b4505001690540c03c0640b0b01e0a101000300d000c55006209880c10f01c03880c1d8039904455201e020340395140d0b00c4101c0a1444802619003a68202983c070941c040820541020f03a402030080585a1664054183d901c0381c1d0307520300e0801c00602d6038031080450003044075080489103072506003614810320800c180c000c140f0b0b2040ca42e040e4102e60003006800300f20340c1d9400d4440100d40801c451031000303441c81d1614402c610441003405030720003c110b0140c0584d074420b603034010800000303401001c0309804601c505510030801601c1006030502035400391100d4581440c10052550b00e0a10040080c801284284031080c06c0324491552605244801c0c28515202c01056011900603c030300340011390b0204241060094234140440c481e409a00c0c2078805000e81922102401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 961311079 1250 961309829 961309831
    0xf070e460603060b0f0d020909040308091e0c06090102030d0f0c030606020a0f1709030118110a060504061d03010f060812120103080306120a050705040b0a050303070605090c0613051503 81
    0x8a400d1404001801d0a40031510007044046c400d40301c010b080c00400c001245a00380200c600318081980d6105107c41020f00b0400c00034040d150b00d01303a040b550468601036441e000040002806140f02241d4180c0e10b0380288140c4e81e40c4240d44008001c8800c42c0540c0ca40905011a104000301e4500b1102141d01480400e0a81c00c907604214450212442940c03081d4401e90071980c40003044005101d500007640d030038021902c030000054401401c4c010b41d070400000980070340048506c1807410b20010854990420103903800c880c40341c02c02171a100100b4a00d40fa03500c0d03815403240e50651900328061415011507002178140c440180444035000207814805d14035214204014041502d54001000013a59220003190f0194000c1c0000541703c1c0c81c1800580380c031006510032070302c58010880500c20346c14584603407030169804441e034602482c5428003203502c910034960060100c80e100c100042052104000c45d541184010702829078494611680c160400003034080c8a01c910a4081c0302858411010252 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 961312329 1250 961311079 961311089
    0x19170403260708060d02060409240503010e060114030a0b0103030507120f090504020d020708040e040b0a060b1602150a0f1b03021f0b270f070e46060306 67
    0x103526102c200c05c10860180001080364040420000804e59100ea80a55410102c1100c0c0904400d00c0364442d07103031040015007290740260315241e00800c100e000000d0380c904560034140f140c418104007002180c18606074020150141c21510000001c1607481001030440d11b005030040110f8112031030b0704480030300386149a80c00007501c6080500c0186404d900800c3c59161721703c1c1c018900455a5903403101500903030b200300d030b000031020100028000c0c084180350b44030142c80e208001e03887c00c164180a0f1801784807080d90341400342d5141e2400b15140c461075a800109003c02094803001140f030300a100c3c41c02c01c5180b0000402048202e0056801c2141a007032203030381500a8003868080b4154105a40a416884a100754490440c0300c01d680b902411421148042800c200c1c6144030003c1004040300b014000d41e41e01c09450041013040d07070384200e82d0340150800300c50013280380101d1251440120b915210100d00520b083d004080441401c50454004101c401d110000701139032003805400b141c0c15407180c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 961313579 1250 961312329 961312337
    0x70c0b27150a1e090329040609020f090412092301140f070807020a120b0408032e0302030105060a2d03060905150615191704032607 58
    0x1000e0000e20244090a000c814900e48105070750214510f800c0021102000003000c20090801441031202c030395440f9001c03070300b0305210700c203800c1510404542010700200041c1005035541914800c641e58108a0141e00c800148240c45d9401c00f800d003480d510280007902c40c08940038210000c0c1c00d01601007808052254170740c16540d076a0103840199941c083c62100a55038880030000c0500601d984005031005a0040100d251a0300c441c0c8140203410302c250304131036543c81c0c403c44100000f4136104644c43c0d02507844444651030b0307102c640c180341c04000004900c40c414240603109406620380070491b4001c6074001c400a0015496120501000c01c03440d000e0b500c40e84000d6034005000c1840d904181c40500101507950b102140d072501c83c0c608880d10fa1a080390300390840303040ca1054880d803188980d00802c044031080c0c0721000940030344d4424803980c0c200c01e003507038000e200306004c0501410080000704894000c1040074502441e00600308280310700b01c4102180ea014080f12250422084c0602c04d15160326 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 961314829 1250 961313579 961313599
    0x120c03030304080d021b0f212b0c05090a0501030203010501120c1b050318040509280b010803030108010609050403050d05060f061c05011712070602070c0b27 69
    0x241c10406912412081c541c46400701b0100d0001d0103040b84464030256130300c2c003922542000c00c902c6401c01101032681c1c549400707140310007200c070002241160703101d000034000000d450404a00000522501d18103100802c1e280c2886600c0c40344d0003034010034030114115800120345442d0001501203000a0261030b00090104207408501000e43d40410100803036410410604d00404001c0040010040c07021140c642011401e840c28030f070030401c19020010225014407a902e0121280d0360344003104c4041c142c5540c0401d50300002c851b049109460b0140c0c000303060404560311a00c0e8255240e00a20480000750b10f404000221a803203446007034050396040d910b180c40d1000207080708001e440041c00503a40241131200180d5140e507007000500a260301103000070103081000d901c20307084a82c142c0c800496102019404080340340f0200d40030802c01f9074642c55075201c0c484c074240180280604030b03004045403845240802d00c0e0350000068412132030722071645440b0354921604a002240c915030417581024440c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 961316079 1250 961314829 961314833
    0x3030e1206060d1401050703021822090819200a02090a0c02010e011d0d020c150a050d02070b0105090718063509072301120b0d0b06120c03030304 64
    0x10f94010302c12405140b0440a100781c008001d030071108259100c1011990000d41851020f0a0500100c41044100d4800b10b4240000c00809042c4441514001c01c01d80c0d201c1d08181001b00301030030fa9172580114001080030000a8001810030b007044440565071717540c085040e0703410040026860360260360180c40f110060321118402005000d864540e1002e6540780c0200f900388150034461080d000707603907a240c0c466941400c1d0100b8140650343c11b080007150040855a44039440b07000b0350b0782d1080313100008070f070740d030140e04608481d1717400345083e00c500c2c0500005040c0309004540d6941030585e0401c17111f0f450300b915814000c3e5280f280300303420b0000b0f8454103042000780e1405054074603445200782064041909451504c0001d44e0502002c0115900c40c4c0070921100850401644016000b005044101032826203100200c201c21290901d0421503808418071049007150001c0400310f0016101400040103803601a900000448a480c02102c04500004842400245044010b0303030180c095480c0d603c40d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 961317329 1250 961316079 961316089
    0x40b09030c1015050907120f020a02061f031202070f170d110115030b041403070201021005090705150903010c09060c020d1b0806040308060a050108071803170403030e120606 76
    0x100543c0059a1244000600d81d111a41031500c10b0a41e6611104542c00c2c1200d40710441e018914600161171040c440006482d400041d0944c0024110b030000d0101c00300006c4888a400c82a0801400c01ca240c0d18003600e03203138001610400b03480341d600901c2141e584405000c015080c2d0740718000200d51084040744d0009008101210a14100c18004a030126151400070269501075000b1a000003051081005200a2140c00c001e14204e01c0e02071850840c464000075501c4c00800d070600d0388070b60b864021606800b010009070006060151450880b04140440e80701190003e4207030f103010f1b5091002c94050140325071001d105841c01c9403500f07070010900d0780a109030703600b0020702140d200c0f00d0221301800480c21201c661000708a1180144541c3c6003500e00102600710162105014543c5080217024903070f00481104d40c80340162505410a180509220781050a540d00240886507003910032402d03410700340000c3c010380340640c031b40980c090500400e010082d9054198172426410107800f0481d60310b82 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 961318579 1250 961317329 961317341
    0x8120405010f020c040c05310b03180a08030103020301180c18090501110702030709020f070f020616050c18270a1203020304060b0306251704050303040b09030c10 71
    0x8548104e480040c15080890100c5070f00e401040003094000c11090000b0602c6524210f1085001440194140a070908031030ba00d2000c1c0501403d0200101c0000d85075400300e61b9101401c407500003200d607010201d08180710594401e00081c0d00950a100e11201020b4510704003008169102c00c52003403040c0781649400b0760000020a010740360303449401c1c07a80844c03c01d0055840d200c10070881a82d4621a41c03040614001c2c0c10350107040d490b80140a0b400006681506032002e085e000702503520501d04502c0010514403640000c04a4a061001c800082c400c000490301c1c03a840c416030f0350070039110042c1403407002910125107452201c002c2014a400720420000c100f950034440c8001c6500c0c10815a0f224440c0f02400c01d0158006540801080107001143c0601c100481003503029005078102085c00500790351288ac020f54817107130400541161a4031032901c11021035040c2c86001c4041c00c051130801c0d1640e20032303038007a80c540c070322680408c004400c0801107611000c00640240100a0b41c0b01c0b2000203000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 961319829 1250 961318579 961318607
    0x18020a0b2b090f0606060801050d0804061803060509010603060c0c0818150301350c190b040e0105091f06080c040e0711011d030405040209030109060603050d0305010812040501 77
    0x340b02c2100c0700028207030804a0b05010310610000c226281000d10003070940005038480c5109692a160f12008180034a080f04c060b00c1a030318206122408a03d05416000c050368401000d8a2414003000300c00001988500c065922034101032102a00d0340720112081280d0b004041c00090003000307821104200d0200342d01101d000613145041e80c1c0401c2c54a01e100307400c00d03800b100c0d030381d092049903190b05004401c1d21030b080c0091a00c84460f0646024419030784a1038040315902842d102000f0014080400c0070880c010001980c12070740e01c1ea00c1c1c0c1e910315032a810a200d450701030b0480701c0120f074840c2012442031206004054004090501d031002c201e86410000e864120b001d5400c10011803152905290345d4450301d4142c035130815689150601c0707821a4411640c1003030046541c1d83d0035202ca20040704a8040f04d40440b00580c0390310320000002d00404c44608000e20003450400c0000401001180704016809151400c0107242e90300c401c070342e449180841071080c028a08010070301907903000700d0241d00018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 961321079 1250 961319829 961319831
    0x50412060b09160206010b0f030a0b0f060c0c030c04061a070807020a09050601020d03110d09060b0307060c1703010f030b0a0b0d0c080f0f07060c1518020a0b2b 70
    0x81e00240200740408400d5949010002c14070903401c80443d010400c050040c03000301c0f4564504454001400e0241c0000341480307984175280e4901c441c460707a8610030824400d6006240c541d841c4244520165a030800d0300350176000303025003004243d40785003600c1000308845c040b108003004410316880b404015070103a002150000c0007403105c900541c0310001d41e01c010384102680061a820400000fa182034281403042042500f0401d00805c003140f4201500d690304000c800100d1558614500300d4060101d079001903405109607080010071076888422000c501c1d00444041451440d011120221407000340208a40f4200e11442080020a010401680010351500000d0b03045007010006141800404042c0c2d1488041502406500030a002541440300d03180000c00108078a44045510f6280620a20040c000384900071028814140c001c080400910340c802c114203005054250544a00c80303501364011088864040b5031000381c4421982400c504500d20302d00405035030010407401082e60f50a5500c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 961322329 1250 961321079 961321091
    0x21908060102120c070603050c0910111002190e03070e191b08070216050906060304030c0b0c040315050c1611060705060a0b03060105061e0f0d0f0c0201020a05041206 73
    0xc43c1d02806814190039107409803403440e140440c028181c2e10081d00714504079a04003c1c010707640e95902158810b82c8950f082c5070400d51517241c4401d08200c07a080a20620500001c2e0495030408121a03080c0034035000e444030411a00d03030005055490900d40034016415a00c2c1000c1800440c10521101122080c0e00021410222461807003000051500400020134810014070011980608c400d188100c4d61506002c0c07802d10b0000010f41c86c400250480f4021140000428141481450b1062000381c1009000d03203a800c091001241c203a1180c4000c0d44c2c400480182e14100075a84d0044a0140080000c2603050064a03841c006c20f545100904643e030500b150012140d540743c40002d4140940950064501031800039031f6807054a1001c2e000f20700c42e0f00183c006100e00e07038400307058420000f21040c0f5056000e200e80e80080d4180300d0b004898003c00d001007504041a8216000100307050148041400489a6a10140d00b030b0702420356a4804202c060000744010030908986800040c0038420204503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 961323579 1250 961322329 961322353
    0x411030c060406020a0b0f060f060f220e0a140106200d020102040e060d034a03010c210b03120a08010f170a020906190801061503021908060102 63
    0x1d00d52041d40301d40c016803c01080d00c8240581105401d502484c01c1c0141540d13031410310001003003040c0c040d44040c880c0f0004036205070783c1c05080b0140d541c00542811102c4035402e07030301001c40022005104103070540c801c5a001450003403a034080c054203e1000e0002c401645d08080040e14458603060300c80204045000031840104802c100880e802c4c4041d800060782c807411704101035a625030003007006008a4880e400803000a91040855115041c0b0007100d240c0000178541114940c0c5000c01d0b0640060000e040d00c42d41240c0b04214000e9509048008200b440c18260007659005a00000c10781c2e820022a04080280c1e00d9400204050400030107444403241c1d00324007c009030b0006020303840090320b13040040c400c0c4038039085a02c0207030400031411500040500c00950b0354002d2002d0003402882d00d0750214045071a90004c20f4401d1004000003100c40380c41d103102138020600d078030900e90748440b24034081c2007080c024406c4642d01d1400d03180802854850000907183d1180142c1000d0441c4036000720079034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 961324829 1250 961323579 961323589
    0x3030406092603100b070b070c1401050f071101050f1609030b010f15320f0a03090326040209090309060d381917101d060411030c 57
    0x10182c0340700380d00140c4a080564100c01e016526801003101e0380d00810251000c2072480340300c0e070b520003100e280c00520800c00b4078090060283c00b0460036420340c05c20080c00020075034055444c0c0700341680d98804c06003420050319a82600d80a0f5a050340c2a002030780480c232100ea050a00d00704d1500642132000d0245c2d1780f030303550894481c07003644220341810b5042403d10240000110350080c08881c1c2c60941d0101c403550b04040700209500d0340400300c0307021040c803110700c1000d60f10a07581d0041d00c407440952200b000d410301501070078244104900213114803034642c051003a61294030f81128890404080ca5540b5a403d000c911040901a50100d00c01030103152000e82d1400000d01134603110542c00b056004510748031001860f0712144900615410300b8116400110454440104140444801d01481c140d50300d0030403034107117680103400340082c02e250246114800154041411152820402c0061500d1464500a0600005105543d0080c0c404a0702085c81e8841200143d04018148c614606511001a03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 961326079 1250 961324829 961324883
    0x201050603151911160c05030c09041a0603070506040603050f090304080d0804111c03030c03270c0b040f18020403051c1413030308180c04180c030506160309050303040609 75
    0xd0704840c2592040c803c5080610012780e080000340d40740026808c05076501d50034219444281904129804000381540d5400c20903100180805085d6a50310f03030f111140240a001c1c1124410200c402c18000706000300400402c5034125581d00b400b030000284103072403c41f40100b025009540140f03042c5808115555400b00f003242620300d21503c205840c5041c0340c058196070300fa07408142071500e0452550854000414518200040504494071088261410111103d03282d0403c80e00f0b8900420046103a51880e00d908040d0b80902907000d2026070051141d00507485140401480c0f90040010841041d400da03c09842040c0c840c1000410349100c0d180421190b081403502e81e081c5038002c40104103040d0030018040d0802909042d83c0690380d00300c000329a540c01071417080c6000b1135803440d00e58a114491542a180c865024000020711990303810701c550754080641340c0b02d0b80c40940c074200301ca4240c0a489040e11080c6c1c0300f4040c50440d503998440b03030000d113150441900c1c80102d80141084540d440400c070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 961327329 1250 961326079 961326083
    0xf090118060e1c0308040b040311070608100e0408090609031f0506090a0c09031b05030f0703140703170f0d090303060317040602250312020105060315191116 69
    0x242402c648104200400500454104500782c0c100c02c0c01a00070a80c400a181d5016030072200e09080e60b100c80c54103c07101d8100c00668002806003102c01304401e54441800380c0217140d1140000e00083c5c0754140300526081c10307203000b0034803002040100e20604140c8041c1080c0f0b0700c001c05641e811241ca60b0b03241104149a07440c016441d079610704121041c0ba020051030f400607110981008005101d110151520545000140403100611a88601d0300c0e55100e515000e000081c0946401041051500d5070f103001e54081260b0b20b0054a1400d098071800080d1101104d40000c407290b81106000b405215552107441004481c2c402000103a030981d4480c01001e48003482542c002900c58950704104442003492100000750b4001000308000182c0d00092910b492405221070302c0c00c80c503a10f142200c0c09009a8402404804964031901000e80c040d44400d02c2800183c0c00e0301c511050740c0300a020b034520f00300c910341000300d01c001d5980d4990900c1c2e0301425083c040d4880040c600b801c1c5030303001c24202d030b41000300b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 961328579 1250 961327329 961327337
    0xa0e06100c050f0105071701032f0406060917030906071103010b1c060501090513140a0c06021509010c050a03020c01091b080f1c0f0504050a06090608060f060f09011806 74
    0x51100c40c03540003010501f11702c4601441a00b0f1b50459460750b100c3d62030307502c0150f00e4500f030240c0102c44685610004801c1d5000034810400c0310790300d800150a640c0350388240100a00c01d9802ca5158002c04000c40d081180c000385014940710720381d82c0b800c0008408080e4030381c0640d83e0380001c1c9995220183c0100c4000c10f1441f800c05501041d00e0300d80c0685005030000c00300c26040ca030900200048039841c1507849544a01c0c43c1849409035440c041c40e06252100141003148000b6001403100c0e000315140f40000308141c0c00001e19500c401d042401e80e580200e041001480401650740c0c1c40e4865409050751010075000440d0402450300c1ea400340c018241910700d4007014482040012800400c141c00740003003000058070325100c0c2000c80e1400085201c001d8000e0180600380c481c1030a00c108202c40241a00600341000c2c0750300c913103004140c00b0841c050b400103d089030010540f6403411141c05c6031020001020249400300c4a002031500c0e81010903198148a0480c10344101e100da0031107035901500d42d50703072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 961329829 1250 961328579 961328581
    0x20708010c110c0307080d051e04030803060a090b060a03020f0c060412090e04020a170f0609030a0809060f012114010207120c050606040c0c0515090601050a0e06100c050f0105 77
    0x5550341005010750446100740d100b8401003054090203d0fa2400c01e40160619585278500a203020403441310f4036010301c61030394001034040100040c109c05540114001c2d1100c0d00241c0c0c03900803c208948040082550141c0140146000c05204e60001c2a102c1258221282004800c3c200f4900c0c04031700f03450849004c0502c02d41d00c800180d004400e20f004041215010340c0b1402c09402103000d5860320f000741c1d00c5110030411034640700881001850505681c0c40c00f1541d041c078000009a03140c0d0080310222002440c0b0001050000400142c400c2c09407040303190805144c1d10f070110b40380110902c400d0003910b140e40e880c28600400c529405031031884005000240c0c1e140c1d09850311500c85d1002e5199174041c070401003002c501054002408607070140068500081c9800b80881c155001c28141400604134418090f811180000500f42180a04004012603400e42d0300e8a04008600f00075004141d48209841c000030500d06d04010100d05000d0300342480d000e4003c09846072400c0555a912030986691030340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 961330935 1106 961329829 961329857
    0x30a091403011112040209060d1a04031404030803011a04030f03030b0d020406030609021f1b15050c031618050d06060e07021f0902150a020708010c 65
    0x2400c1c41d44c5a04010044000c50902107408a0159043c040414414100b180404542d0741c3d109c042c00d41c00001c802021005500010b1041c0e0401416100900000d059040244051801071034010342e01e60600040703280000c0c07005079007925000308200810228900200e09000c1992600d17001c02c10032032150001d0000580b601d00654031910701040001048a42e901204030184203480340d0404002605005549088520340070300410451507011800504100e03180180612503920401514856217a2004840c2d049035151024030307001083c09515240f80304000c40701c2c9003030b04d400c550a0b0f000c050f9036640b04006102d114050042c44480b03500300b200c0380e00311002904010700d8600d00c510705450001e47c0c520020385500060f00303510180184201c07107401842441500135008071800303140300034041600d6001002030700460040e402c1c0402c0114080c002c2110361280c03aa62007200d00004 = true := by decide +kernel

theorem cover : BRFrame.Cov 961151079 961330935 := by
  have h0 := BRFrame.cov_init 961151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 961151079 ≤ n) (h2 : n < 961330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
