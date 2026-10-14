-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3258
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:11.564113+00:00
-- url     : https://prove2.me/submissions/853f4d54-730e-48ec-bd94-13bb6a2dff23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 585791366 ≤ n < 585971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 585792616 1250 585791366 585791369
    0x1b090b0a080916060e0f030f150a02071a06120d230403080d05090c01020109020607080306030106330c120c060b0a0305241e04020310020f090405180304 67
    0x5140066050b0358500c401030810390a1100100c0c003814441002450a030b0181490000900c2115040303c41c4080354101a0340d82121124202d45030007400c9840005160285196400382c0091805413501c1d81c03d82c1c40f0038401600c0c0045850400a402c107001644c18036076505a911140c440013000d20824894018005480b41800003454040071650751440e44112001d44c2d00640e4491211a1107014005010340544000c030740c2d04000344202e2100494540c414040d00806070b030050300070303482c0c04219281e40b5040c0e40700030040c036010740d01c5103070005501d032075804d48144c0410050000020303031015800d0b4203440d540041d01c0100f0040711001c910007007040c4017000c64040405051064039200f442c54254007806040012070760020321235000105008010402001c40e00c1601400368a000e105048101003071419034404031518208071012080c80c414525140e0014002401c5400600d90a1500c1c01680d0104040f000e2000c0c010901074003070f0800d030042c10b401071401050582800c0c884809690b40780104d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 585793866 1250 585792616 585792637
    0x210f15180803090615011d031006090203070e0901061b06020f0f0a0f08150d0c1a12013003110a0609021f050a140c12030f0a090b010e04150e011b090b 66
    0x7c2204030070071903238100408800461405d03800c0c09481d5684070400002e400440700c1c2c0001c540e05414103e844c0ca40340500320b060700e20545401e50403440f000e020800c4180402003c803001c42d42048080313400601440581400c15a4001c80b0303940d40c081010041c03001381c03001c001e0000d000c151018001401e003035503801d44040f0001d44410500350410f00300307000b2500f001e84c03200e2400107034480750914a0030b58400500c1000501146001244d07030355076910325520012414031004420219003040d01103d200d070141410344c040d1610350780307060001d0205070608410340c1088500720794030b0702c5040440c1012450b440c0c2e0440f001c5540a01003201c408054a21b10495540a04000e440c1382101701800303900c02544d514a60f07030811a00104c80c168580710242d407081c0d0b0340c0a4102256400141901c0030f50240800b07556120303891b96030591070040202101000548102c032a0243d82c441480032240c03038483d551000400c640003140740f003003800c40e003d10a0318001400c000c01c1030094040c007542580c881161200e055 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 585795116 1250 585793866 585793907
    0x160f0b040e0f07120c080108070e01140d2405041e030c0b1f0801140117030d1509020d06030b061504050d1713210f1518080309061501 59
    0x8030f810301142c0c0700c40c12070310080b10580340c4200b561459a000e03507014140c6110408403500030392039101c400802c540034441c071b0782509111181641035081c182c100c2d140640c800c0c11281660010f90520040c6602c1010b00d55601d16521070801060040381082c2e82c0c1c42401d9492415a6020a0f48008100340889140501f441004c0c0c0049a9207403040081200030b000310641c400b504d5a207c0d42964041e10b8400e2260450254100c008600310142000c42c5031071348409001507150a115904440c0503000e05401c0108003042c0c04c0002420b07800500090a1143d08840005034050840c0362048071200080c054a00a01c0408150034031902050115003e41b0f00031508080e141c42d1a00d4440b2800501000030803e4a0300451300a082078900d11001c4180d0368113511114801c00c0980003500c40352400c1c0c001600c8d5001e81200b400225258442e2401d1000442001080300140b41c1e00140040b030440b041250004000420080030f0306003413003820b8105284604000513082c070030000800c03120b04503891b11801035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 585796366 1250 585795116 585795121
    0xf090f0604051309020405150a0e09030f0a0f1707050708090a0503030a0207140603060603070e19060e01030609020c0705060c250302090f22060e160f0b040e0f 70
    0x10344440649008090040c8121860f1003420320076005000011030407400341c1e00340004140310300b90030402e2408030440039041d240c04c149060380c0381080000103402004a07000800c885d03600341151a0040203c11200c0d00e401541106c40c08000700481002000c2c00525580001403000c3c8503444004c0b03484003508241465140d01c1c86000040900c44507510041d030610002030b044440b1038000c02d41c582203565826070065046200c106000491000311220b5a10110400000340c0560107544005007000b800307010b6501124509a22907540809070f0000b10218088810301c041e04e603810f0103800701411711010f040d401c00b6250b04005545004500880388220130101d240c60326000e0400c001c5010342c40014070103000340b101024005481c4540d00060380a0030010340003c800c408808440d6024003030740001c0303d540064144a2421003000310311308860242e00d42010745090407003000b40f560450103141d100840c00f0320303001c1c007002c0301c06295101591810301403108110081600c081e00398013201c0020f840000c1d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 585797616 1250 585796366 585796369
    0x5010e010c02030c040218180c0f0c1e031b0f03040302090c120109020a140a0905010f020a050304031505070c080d1a03030d09111806060706110408030715020f090f 72
    0x1140641042e41140c80070407c4503000102509181d000c100542d00c546602c55029509240203000b00c4441c01001010410341c0481c6e0190002010240790300815180454900105a44103c40d00e40300040c081c3e0000c070b8a241c081341401d0400b2131085056001b03007410518070703244070340f2406648406442510940001150380034608100c0e9400454413064100c29a142c61800c402500506814400a10345484515405017030800302c850029603074842c00f050900d4a4011540c41c14105402021400f030f21001400040c0100041e102461280d90b100c0301c3c2c56a424982802c41e00b009100b0400c20098140400c08580342d002259442c400e0428041000c41040485e0f00c81080741e00182c0c0e80603c4006528510000d469000c50b042e06e115031341d0705420521480c10010303c041e079048042c89240c1082d02040507031170144001d050081c0b0407800030411003903400102c0041c0e006070b40502c01d560000070750705040050000341a41c03080408079045040045001c1d00304014011485404d00960b020710052105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 585798866 1250 585797616 585797623
    0xe0406080c01170a0b0d03030c08130228083004031203111309090201030b1504060302070f0b0f0708010803211816180603020102030307050a0c12080402031605010e010c0203 76
    0x49170009040084502441d1800900901402c401140010011804600709002400068440701d800070714049284424a441c0c82c480d50134030861a10707038a244100042e000c1001d00c94446014802104140b03180020000514945c0000d000040c9808003000f081c4002008800c400e0b01412062800151082c248a94612076200f804000c602c20025540c0028100c0c03020b4002180703062007a82c003801021000418441c11100c0130717914111004060209210b6103110360302821016000d0150840c05c0c03142c50300e03070784248401070300d050108842d00f2081201c3c140c0c1041070207004021130310040d4604400e40490420364021412101310004401c40860703aa0250440c0000400d40084145c03130801d00140303a0169040041d1041003940c564442040044080740d21a0714222901a00554650355500000716003651054078940b06000c0007517424804103804100381c0e05119600e807908145401c4c140101407800c0d0404d040604d546240c0340046c44540d81c0132840712405a02030034020b02060081c4000381c00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 585800116 1250 585798866 585798881
    0xf010c030f020f33040206180a0e040605010602151012020d0210120c020c0303030703020915030901060306050c0a0e011103251704080327030d0e0406080c01170a 71
    0x1035101c0c0c420a2400720b5404c00d0384403480c03000703018044000c0c0d8102c0000b0a070003200701d6021b580414284008444400140a110340b4000c0080440c100c00b41c0790002c0c00b021000c1980d003900c5590b070310401801352980401420100c0d80443c082c0f24401d14000c1030f0f07204668910300800b09000c6a10700718000b19114440d08410640d80240303001440707580f140c4010b0800720380c201506038590500310502c5540f4004690341201c410060003861440e5a01e01c8103901960216002e1030f0000b02040628101c1c42c2c5c0f01c0040e6010340c3c07030312002054091941c01c9c01015036001a14400390504100101d02610340c201c2c4440700c84071428206129055481051242107008030b1287c0f00e0100d08080e10a104041d458800d4240c1501c0340c5802c2c0b040b0f00d50392034402881d024a001d528100d5000b00103c1502928548580502a141c07000740003c900150021034200044400c07840c0114144503a1000c440c074041c052100a03100c0c0c1070040c4010400d001c0000d05c52880c000300d103505540010081340c1c1004a6401202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 585801366 1250 585800116 585800143
    0x3090a0c061b02132711010504030201020a06050c0c070303020d0f0801081c0e1201140c040b04140f0a060c0233160614040302060702031215010e19050f0f010c030f02 73
    0x4030801744000c000b002004055811143e007500c02510000640c00380c0b09a5007581e030180d008006088203507a41c10001c160180c0040500c450501150008080400c11007000e14429800340c151901003a2000d00424550000d510a03c0581001071041210000e007100215456150b030850b01a1144800d0701c0603000b41044941103998040900e40711107054000d07400043c10300802001a07550f4400021007401680294009941d04110410900000c41c40c00b43c007460004009259201c0600300049045505901c48000b0900394036000080d0b140c1010442d6440201500100c9203800030300707041c041c3d6000081441015200840c043c1440c01d40c2c5051500115880b581c204204500c0c1c0e00084400c00c1c007118200c00500c144000600203d2011050380c941c0c09244107650040c0d124210b00c5801c002d452401641008120248070360380341c0c0d030b044c580c403c00bd041d0140448520b080000f440901c0a241e21400e0281036106920030407a43d000d42002410f0350586420240c0120084003242040d600c1c80020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 585802616 1250 585801366 585801401
    0x61e030b15071703010b0703090e060d1202100204060f0e031b0409080705030a03050105030d1d10050705070b0301090c030917031911030a180210030f020d0203090a0c061b0213 77
    0x1081c039003e1b1000604100e4043c2e22042c03e2165107503042c6d00c600c4401c0b0b5407a0780160b0800041000a280054050765151380ba0060b645480d02200680301243c129074440c0e0000742c4280d4140540da03400959108907440207501400c020075140e208240a0010010890700844c1c0c1d0f1030070781c1d0a1001c86811b075214140c0c00400c1d2a601d40880380d004026102c01c2c052a4824021050281401c80c0a0408184509001614140c1001c1c0c040100490b481c0d0f4524200d00f800340c204100e100182041c41840080c1c214030308a01e07280e5061240003400c488180e005182494034103960341300851080074000001c107520800c22990303a50303203c4e00d501000185980c0c03504624107001d150b9510740c042901075441282000c00800c4004504c1c1d18005032880540000307900860800151940315100f0b400482001012513009480c02083c45503000403680300b140d1030381d907507000720001d5420800034500110080c502d0307140a4034003482c11030050003070203d0a04002c1c460842c1c140707501d0302446190496414034854001d01c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 585803866 1250 585802616 585802619
    0x901090504060e0106030510080715030b04050f100503160e0a0e0615040f020306100e120a0f150b1f1b1b060219080304050a0c061e030b1507170301 65
    0x20b61400f01c1080c0600000709052100144c12101402e4081c801c560041d401403604034070f02940c0b990810074250305901010f40712010b400443e103460240b140181011401d868075813900c04034860341011a600658802d030000000003990007001400103003600c400300c3d98a182602d920000c10001c1488441052050184c102001103081103851181e04407c42a1030620031a038200c0d8401c002c0b07110403a0450352007400385a84e003045612851042050100141005801010400302c0030b240105102c000c40c0c00082c402045401c00001d0941c40c512025881c41c18000c6006500005d40102d031901750300785052588602d07860540b0b01c10480c1d240e008008001901d84a5440d081c184000310041c80300000300c01207600c0000700f40d403000903008040a5004171421414000d5969110340b9813014106490398402e04901c000840d810021100081c4055121000c6071016022844900d690a000303810a1500d0034050032101d44130041d007203640e03420b01c484d41591401245424051039140c2e00d00c00900d110301100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 585805116 1250 585803866 585803879
    0x1201081c020703150903030e030301090f0b090103050601150207030c09020301061d01050922050a0903170403050f032214010b03031c15030f050a11030c15090109050406 74
    0x20614240021003030304010305280090140d03912a103900c8000d0070f45445080002c507412050303002030700d0700d440392a01107480c850310040305165400a8001c08151a81e0b40700c03034100c40a0b01c0c4a070038060314059a083c05903625540b28651106014402c980c0040e280d191003442c450310134821580510745c08000045d0b09900d031551480250000d00441c001b16200381501c40f91120b40080001003000140e40d413a00d0218800280f102c014690f224144c0c174502c40401c011200071040c01498441c1c4005140090352146505000f0a031a500b190120240b01c0d91100303100220354003c08844041110071081070f6a529034800c00c1c01c2e807201d54800b0324a03c1100c41204070030000c880c400038414a4111000f4880303490103408040e141d1007103083d200c81c0054031b44c850600e8a0340613001900702280c09014404003555035150324410410b914400c403903540103e65000304000b00100014001c140550050404440810101e00303060306188034500c100b480481c80c109960300c141c040d000600805001488165650b04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 585806366 1250 585805116 585805123
    0xc070608070809210f0405030316030915021b0609120c030f0106231c060906050a050f0f15030d0804110d03023c031201050316030215120108 62
    0x39001c600154141002c5180500005010340b160807070320511001390001524807408590100c0000b01c82001e00380000102c5a40c1403026000c96a01d8181942506491345401041c1c0021a00b004109911307074103170b580e4107035030008003c80c00c6200051180d81000b00c03600040d8050048060007540000392081118940d600402d00e11183d444c264125000c8142a100c201d0030381c2c0c0540141c0d240007040311102059000c004600d01d40074a4003511500802d030020400e04807100d034402c8241c07017440d02c680d403140c03c20056109555009141400070066400c141010a0411f040a041c0545218041c1d000c2135141036108a06604000c00508480800c842c03054040c10b900c0301100c090b922000c015100a4039410088028240c00f03038103078040c102d1110100c26a454035807070718040132030884050b04442507a40d4400000e04861f1081e200440c4c8a040d02d5030f05200e04d442c160403080c0241c00c0382d00580c0300c000e88000c6402c13b0300e0b811a40c850381c010044401c1c0c0340b00e0058000900c3c22610030000040c4181022 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 585807616 1250 585806366 585806371
    0x807060813021c120f2a08032505070c12021207080f0105010504050708010e040512070819090f170109060f020a14120708220501061d0c0d0905030c070608 68
    0x3a030b0149030b090f540d1300041d540700900d4001790b0041408090540b2481c0e101217500d101e00c5c1c106001882c0c01e101640c0707174003180380c00031511061540b40811000c0c0c080c4c40c500c0d00944d000700c1245410740c604101641c0e8041e100c0424421f43c0011003500c00860b04540d205c040d45059003007500c1c00c890510746c1d95030903a030f503035001100c2c00c1e03195502e404004201410319010b103521a204603285e04009900e44900780008000042068076140034122082000f00e06100003400107600400d00c1a4484003514201a08542c04040d00002e12900709001c11000d943c01c48a54222240c80d01c0c07108030000c00b000d43e68013400d410940145010300d03041590507a030403542d01605001035159a4600c03100100601d0941d90306c1018064404081c1b81c00024035410f02c18070000b54000c0b03410b061404041d01c0c000381c66003002c000c00d90880c3d890351216024000c448c00d01c1c41303414994005240341ea5007800c0004031003480e84501d0100e80800c1d603d420307044c014000b04008403100e0303080301e0701224505940c0c0d9500500d0760206 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 585808866 1250 585807616 585807623
    0x1031116030f23031506070506090a031119062021070f140706060803120a0c0306122901030f060531021c03020304080c0a0807060813021c 61
    0x1114000f2501d014416804036070b8080042d034903031641d141d1107454085410202003e80d4040000c000c204000f03007044c00a41d0050380000b0042809080d00c2c038015004100b0031003480b016a0007c04840744410b440c04c00703010520342250001030113908081c001685c0d1751006080d0300d85e1100008910a81001c0d401e00c80c1c980001c040c10000c0c00e9180d10354200c855a8685120710006211000c144180c0341c0700500520580d0702c90b040c005a45682e9505050640c0c00c4111440320007a07141042200032007007401180103010b05e501d000c01c4a60b00745060030101e40300c0c00d4800780c0074040b040100024980041080f01c07011010703081100c401d694a20300074410441c02d0302c044840343c1c10100030811445184210071039031460012481e19406060b000300d05003002a44e8140d03800300804c050014608001d101c0920f030103009601956031181000f20080c6411503481000c2d005009886007004405000300f8100c06031109460700d07103c16206c2d030a03512540b220001c4003951104804030078441b54207004204a00f106d21 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 585810116 1250 585808866 585808877
    0xc040b1f03110c0c0a0618090e0a0f1401060602010c050f07151812050715021c020a030605030705090f18010609110a180e0105120a0c0f06120606050901031116030f 72
    0xc0b20f50b01296404189052031101410071003091043c0500e5030001409100034004650362240d16490311046680e80ca001034540909900e11512100028001d3b4000740000340001e00c585046000020400c6c8107018104650100c08a96001000040d40340b01c20020745c0d00d48284000c1c09112881c5542e1600302c901129a82349140e03201011a00401c15240101d4000034a5100742403184500c0340a580302c180040c000510010011010140602c0030344008031f407e0380d0009007107060005161400d00150081c901c00c910803010015031200f0002115804025440d08220035212010b101780508010340040c3e07581802c180703141c0450b840c6907014181904150340c03180c420401320312000b046110940110240450210014041414500c151485100800046800c406003e40b80c00b20f400074180c011012440c41807404111465102c0b10304294185020820004286400c001514621910100a06158507048109a04000c49003038610804d030080c4140c4101b24203181c000d285a210301d240201049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 585811366 1250 585810116 585810119
    0x11120f100e10020a03150b0408010e0606090a02070215040801020a1b0f02042f030a0b01081e0606071a0709090b0901091a150901020c040b1f03110c0c0a 67
    0x10303164020760300e140d1910006007041c1c1c014415504080d500542c801c4c4107258503410020459444111070384010b10050003001e44070707410302d507000c0c4c2034402070740026821758000f0040c08104d6440c0f1130290f81002c034040006903101d410348042400d0103a031402c0d270f10145102203000502d80006400500c14191030303a42d440203200d01d0340404118020980c02c080c1c02c920509108100504255000040060003c0a142418440c20406419030016000b07491400701c000710900c43e04d1540c500440c41075001c24201415185009200407040000202c070342a0b079000074401142007900d8050407100c020b5000071828828020501100c0215541a280325000034449400002c1118040c8103031f4182200040840e81143d18040c1540042c08141c1907544100e0345170070039040740b1b50381c6050f4090030306a03902c0b40d961640100000603081c06011106a8000d81c20845e10500d00d03076504200c1c4d1b20b017034003034035590101101442044008121801441c442c0c00800100100d0140d00002c4509a9803000c42d04440540d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 585812616 1250 585811366 585811393
    0x30d0506010f050901120b06040f050306010b0f0f0a09122307050a030323040e0115090f03030f0c0501150f081518010b06030403030203041109010605090d11120f 71
    0x15240c00b20500024005110524480d031081150a40125158402040f400956400101154030075031040d19000d05440003042507060901c6014018403600ca000b45c02c0c404d0700ac1c2e00c4500b40c440d40948580305000014840c01480c01603154001074180c084480c0301903180da02c1d00c0260b80722603070b100c1001c800d201100b09220750f50000c0c4241c1559009403058900f07074556501911000d4500b54007900040201403068141c507280400741c0024010341441000f19494100d0100402000400322405c108106806100e40040f20200e001201e91514084041e02d6090b80c0c00c42c1c0b040d81d0304c10002c0c483c0d42000c0c40380c441190307011700c06000da07485480d011100503622149940e41c0c240c00407070400d1071710710f040c0094106004108038040d003804c084c0002c950503c4140004032250301c201c0c0c1c01c40210740e0106c00c0c0170920280c240c0c01b619000040c3c58039030345941442000303051401803200305441607280700d02c000200503000b40030a840400203054420302e584d0074402e59484003400000d02d001c40c4201001074610 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 585813866 1250 585812616 585812627
    0x60207020918030d02070c05120105040308010905041725060c110105130b06060c0708031201050111060604110714030304110d030915090810050a151a070f050609030d050601 76
    0x3410000c1c03000f545040c0507540340754069080300006481052008100003803a403a401403924002002d08000501450715240250105406070000500d50303107000100800074400c20403140c20142c00089030f130303280c8060f40000b51442541d0041043c044014415030001c024540c0c1001011841c903446007000c4d4081960301c1401ca5508582d1126043c6030038400102141d404c90100350002400b511051600300c0c0030502d54034051180d800880719910020340030380416507041c107850140170709181000c64281c1c0c045049540d410f000c0c1500e40304a90711000740090340001411501c80c940c0c0003200c00449103a2000690700c80c0c1080b101030b54402d100481c0c0040384d1a082c1c1c00800d02540c99100c450b450390a180c083c004071000c905465080c0548510003040b06841001907030031040034154081040d16040c803c850503180c0301d05014080d104442400d01103925102e106051881c00048850380b1034805003480004500313085c0e0054528000c600030b10000400110051034203048901c0103000030b80316500115007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 585815116 1250 585813866 585813901
    0x609010209131503080f19300e0714030105011a0d05090a201201020309120d0b0a0e01060815010504030b060f030f03041701062d0e040602070209 64
    0x1e005404802c08100352145500c20f0b000800040000c10302c0315143d90380d4421079070021541010101c408901e5503054544600000e41e030503c14644840c0074010b009064814944482300306000d100303410301c2100094071607403013442140c0c07000044800f1a07554080300380d00e20b0300d1405200e000303500740340001c038985000e03641035803440d8070390105a854402054031341001400060800c1040d030085400c2c000204400c0010306152202c0441c800c20710042e80070400402080203644041c159006008015a00402240e42c00a5030840aa00f0786d1f201c2d1000c41c40d10007482c1400d469540080d945902042d006248242207050b100d481d00d5030205502c0c4d00c01400030031075a07001a18005601013100348002401800c03800d422a001070f1940d40648500e00010341400c40010460205a1010504000d414805101500070901c1e130002080b4140c00d0550078100000c0102101c0c0030140e10510590702814441a118000e2250140010b40c0342840d1401c04043c0d400f00105a1180400e20302045404400307822400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 585816366 1250 585815116 585815119
    0x2010501050406060e19091d0d020c031b130911030d050c0309300d0215010311062109010605040b0f13050a0b0405041401230c0d0e0f0c030609010209 66
    0xc4c100b14055003000905084504c4500340b0740b1b0403100000d00a042c5008101004030304600e04002090402c0825103060788034040c0c001150b1214510710300684022840031859a4600e003030100c0c000f40c00f8003107905008808000310b00c0c1e924009200e01401400081503a0103e0200e00380c070114800fa090884090260311b101c401c541d00200300c903240c2d6190909140c00180d000307941004100c40c4040d66414030ba100d400c88000d080c0c0080356190700d00e585c10701001110020382440c0301402e50450b124814200d80075914a0b005907000500d170402c0340714001450410040f000c900c8051480d040b2100d601030700d41e0740b25803030065003442c3e800b441501d41620384040e1010058204014001c0400029010b41405014800025030320403005c281078071140990361266014a003006151100c1802d92400c40d1800c44000c5140750508542d19031495143c0340e016048404118402d403100f07000c180c2c040061aa200030b002a0303201d034150700100c01c2e00204101100742400c07030a4070103607070311900c0b040c1c280d10809110a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 585817616 1250 585816366 585816377
    0x103230c0306120f07031506260f1006031109070206130201030219051309020405060409050a27020a08072117040e04050601050a0302090703390201050105040606 71
    0x80ca09410034405142d0108000340385001010441044a0500344034404401141c0c010075001e0080c0404a21200700c1b40320510000c00040740f03011001c00300c20300c48044440201044082001c40c404c0d082200c44c59080c2ca403800d03510561840340444c8002d0601d44411500510000c00341541c500d090f00201d84614000d80240c1195aa00500c903000344524010032414141c1c00d00400c1c401c0401c1404a0319038119640f240c0c1c0e50b0380542d055003080482d4551280003d640108024455500c900c0d0588044035a022001700f00f0351103c1103440081d1807062007058110a00c80b00c41002051078100c8230a4a6000307890007401030b51690324607500c940030390044100d6005020804911030340c16a10300b80c2c2d42800f86804080c0c5811741c024614003640558003215850340802c0c103001c14000d007400325600401e000c94007031402629640c045508644000e090606040d0740d4243d4440f41c52420403616220b01d030041c60341c14405940a188a010f40a4810702001136282c000041044c0c2410301c5404c043d5210742e29030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 585818866 1250 585817616 585817621
    0xa080706120b090f060112020a050d18050a0b1e040804050f1008060d05031e0304050d0507171b0609030a090602010506090105330a120b130513020d050a02010323 71
    0x14104c090202034141030420900c1d140e12240202188042c2442440139070b14583d490107050480c40582d56440c845e022240c051002e00e5000a40014004071419801400136503e0780d10618000e54001c0200b280c3e44210b21060704100811030180c0040c0162441140c40703001d0701400e10f003480400225203001b803022031840004101e192504030850141180300310300f10ba1814804065460340c9124003014807d280d034011061104100d0306000d1032042c1502c62401d1810114103031106801c1c030085400403002d0720000910b09001700d80c401100784020a00760200c407600d04001e11201d6807940015a0040090f1840d0700200d43c1502c180146406054000c040f4009a402c1030200051100f41c01d01c100c003140c1d00c01c40f400c1c8030744d80032101d406d24480d407803112540c941101400c040d11a407440300c1c001000b20310303283c40040d00d652543e40f107100c000d15816000a4660300c0c011a00f6040c1a04500a076110810f045200304000001980c82459403003a6020705c0f038103100c000011500c2505810b40031402050400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 585820116 1250 585818866 585818881
    0x180201050c0f03040815130c140d02090702060f150306061e180402011d090411030f03161109071b020a0e04031815021203090102090a080706120b09 65
    0x98011580c0460a66000064202c0b070a031541d40264010740c0c00c1d40218586111160b803500c07042d42e004401580075a0072180c59514194250141d000782d40820081c0d403004441601e89825103003685e80d000d0701107203441c18071200c06592520100c5004a0314000180007845003041580040b41c60103001e8000c0000742c507280100110f42ca80a040c2c07800121031b80d200c065281d6200c0341c080c5100c0f56040c0a81056080a0000600c40c0341d90820480d101c24204043d140151594084280d016401c80407218038003114000103401c1483c1064229103501c00410704400e400f100c041c50440c0345118400882c149900384041c00350a01048624002003001d01010600c4002d0401c0b02101292008001c440c8568644030b66803035860040d101900040e10740036002c1000c03a0200306c410041c101500082084c00d809020003965503c0201014201800201c00300c0c0c0900c0c001d406843c4c45150040003012210b80ba14525a42c1e15554862200062951403400094000ca846030b818201800fa0440400369103032074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 585821366 1250 585820116 585820127
    0x6110705040e100506040b0402160b07020102090a03030c02030a0b0106030c0905030105091e0a051005060414060307060f030605061b1c0507060905030d0c080a2304030f020a050d080f0a180201 84
    0x900e101d42160b11461f4403074403070355248010148004101b51001c2c01c01c7c0103051000c40c0f0340c00100711105580c810041c21000342d485910500450b6414507083e03003800c000b440843c3c1407010380c070700c001c00642540c80041650b90f01038100482c0d04400743d44038203040f50707524101801d80d202070f00c540c55541c01c40343c2c08100e00d0b842c0c5440390280001107802c554000c1e546a50741c601e4207460300c1003400202d075124188001882c0c540220010040c00c6503045450703090040009842e00c5a42c4505c0e0144650110300070115070198200e0700003071a00420a07a10f602110b00240c030359100100b00646130307001d1104810807002e0394031201a440b803003960f525801c01c24180d6400d4000e240d0031009603082e2105000c00c41010302c0500a11145c0440e96031400c1035410010204403e64120a242a03000700840300c1042a03040e01040d0503502540525250016041300300041c0d042c403899070320207881402032111003911650460312b024043d92220912000307075074030014983e00303c424080c082a0401400e41440e000f40d8802c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 585822616 1250 585821366 585821371
    0xa0e0703050912040602060618090601051905040e0c030d0518130204090207030309020a1706061018030f12140d05100513140c0304030f0f0504030b0106110705040e1005 74
    0x11012107020b040c0c0701021060b44e0300700b68861401130384204100702a600300120344203c640050092001d80381040402c250b140c01c01405000e004407400000038500841c804104802084042c20822105000104441d101e20410503654041d00c1a00b80600c0910300c94400c4801c0b0051003d0316611190201c03040000618100400e41040345d0240300c082460600c92001300395031803081c2c800151101c03c5105001644529034070200203188540c12450b2201c60115440b50f029404842c0350600e0740c0d002100b039030200040d15804a80000181000c81007248802c01264042d016028914200480c81402c80d581041d5070941800780d003003488050554036240d040103801200c080342d540074040d10385001c0f4142503400386000701510780f100c0061131000d01c03171840c054100382500c0c011891071a00f80c402401c420780140980c010022554130f11240c9500c6001520090b650184401c843c07540e4491004110f004400e1a03c046070051083c001190f1806228100d480b4003d9000351040c00d844198900080800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 585823866 1250 585822616 585822631
    0x804021503040f06050a020309011422020604170f0106090c0c02010315090f0c1407020a0b0d180f02120a0b15030f0106080708060112020d0809010c050a0b090c0a0e070305 75
    0x180b0080710020b2103500815102c1d06e2440e80050300c92510020003820b481400e00c4103403844004100703000c0520003c0211403034134400c004980320040454404603c041c4204e50107000304100115401c1903100c0c01164042e0080110802480500d403103011101c01c480b0344036030b402e01103011050350303600650080e08078860422900d060382d580d466413190560103a40d203460001400d255101485001306801a80d03410188040440d52810110300b540492002c0d04240601201c240c40465184200d0788190813484d44130345d90b000c02030b041418601c0e003180810032862040744203602c0318241c0300c0702c510005544034403182c018102040e00d84426000d540d802d01c2400303803184c00d0f0140d01420a1040024000c0c90010680d0100a28403240b0b00301c0820b0174000180c0002c10400e040c0c0c141c440242c1d8460220741c100c03603006500705c0e0342c0722880c41c0113a400e180007003002041809001011410320545d928034910843c5c07180240c070f0700f00c0c018604200301500c03c0d028440d4216100000318904620039441203a00030071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 585825116 1250 585823866 585823883
    0x1903090b090d0303111e190e0603071103251403270d02030616020f0d050f030703240603050106030c0207140f0d06020d060504020708070b070e0d06051501080402150304 74
    0x1210006c0e8088040d8000c0c840c454600004640c0202c540c20500500c007a203962810005c80348512002503030350b120260015040182c1d114038034946c00070920440d800748000c910340c82c0030742c3d907080c207c101e017142c04903002e58505041c0c0700c0d0342c1760300300c0c001c07040354411200c4207034034002d64040715840d00d07801035030b04115a00518185042c10050700e042100b0f500486642007600d04034445080024030b0420720101c0c441c800d801c03556151260030780001c1611090006a41440d0316030303a03110001c4004000c1010181d0390349514010082440c0b104c40800e20507208159010b01c0140e8071044264190740941584100581c41084108505401001c4032215982c00525503019100018006900501e9000054504540c000f030510007454072403282c200180801c5d5000c1d401c0402e645c0300ca181c10f02641401030544c04840000032102403090f411420803641c0140000c10749422814010003c2100701e546d000701c0d10300055954403560044022a1003154024030004007500044145809a00050401c1700d8018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 585826366 1250 585825116 585825127
    0x50307200307032a080d021c052a09060f0304020a03050616030506030c1f0c051002130504060f0b0a05070507170c100e0d141903090b090d030311 64
    0x80c81030004040c50782c081d03a01c154207821000313942001406042c2e103001540f0a64107801002808001c256030821041240c0182c4074250b05009101440c011060f01d40840d01d041d04122071201c174001c03a940c03c2d5040c0101120300700704801c900c070210310807500300a41c03015080c000560401000001541d0081c400b501000b2500c2c0c3e2a0350300b600e410815104ca01c000e00038041088903140d03052241690120086005003141c524070004500c2230a422881d46100e01c0201c00e40390f584d036005032440d110580d8031108031400e62642c4035042000350003508003000340894802c40003c0910301030242c1420744030f10181e408800d0340341540c500c10380d0b400070600d20180401400000d001c2181802004000c014103a1007204206403400e2080c01d11514804592151584858096606134031074184c180100060380c4403030001500e8103109648103692840d80086100302d44945840941404040c0e5116119480d001d941c0360b21805034103118011481a250030034401004030004c37078466084a403003501c07a8003540d480d01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 585827616 1250 585826366 585826427
    0xe030f0301060e030d0f1b0201020c0310020a0201061217090109090603081c0507080109150305010e010c0e010207080a0f0606030209070e0312090102150c040f060924050307 76
    0x260002d034070090204000300c1004140d414248110ba0300710303a1a00c0c0c003980d800c4e10007070050080b20b03c82c4100c090720b4a40000c4001164000c01525024120090403a041300382641d40c0d100181d440b20041c40010b500301100090540c840710661008243d00401d0088090514400b81800d5001034030000e0402c860b105001444d03401034814180614040c030107859445075813089241542c2007071a18060601e10740010803001c55405400541076802070344021580399050000301010441a420144c40c4e94a86144d21602da2415405022111282d072104111054940d005a03190700c1c03103100f1020b013608800806000030342204043c004103480f0b80d038000340c010703142c0d000305180300411a00c0c500495100d5400d41904d1400300300384c0780004820b41e18a403a1450b40c2c07000030b4030b41c00e40c841e45080e94070040740480c07843c00e00c1d082074601914140682607801603542070010910314a500c640806520388000c1d50781c94500d411032410044215841c1e051441d120242d00b141c100042c100d0381ca00350700b03068540e0300b0034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 585828866 1250 585827616 585827647
    0x80307080d2009010e09040b16020309060a02060a060f0b22170f150c120408070503071a07030c05040b0a0306180b0405060303090a030f03120c110d0e0609040e03 71
    0x10b00540b5282c0c8806950380050254450303040070318803e0189908000009010101c4150b2081c050031807603041c04000300059146014178914a58401004142c0706001580014003030f00c111203070f940910444d65a41c2e9030f034040845501450072228001c200d07101c00340d2001c1000003980b092100b494141a03070340d05651003443e801101c3c0305150b40c0045440a009690410178007210300d10321940101c19081c4680454031a224100e1103c2062502c44001010300140c14150b41c0007541020581e940d51505140c040d140300b6080038520b1b007400c190f00115206030710a114000c48090030f80c41d02460b0500300b161081d000d07000092400704250f15903002062021031049090080340d40c401c00405d414103248108000e4a4008002c1402944203004514a540d5102418401c41c2c0d04814500c000c1c40e0681002c48290382d440401102140c2400e000003e8140d0204864004090301c800f078072911046031100f103035403800410055a00201c00d10203111149070035800103100d500c0141c03c9a00e07112010241c12070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 585830116 1250 585828866 585828911
    0x1206091a0907260711070609120201031104031103070b070b01090b03031b06060a08031905070c0b030f070e0907020c0f04020c010e07060201060806090d030504060f0e10060906080307080d 82
    0x180c0c83c000c800303100e480b40d041111603200200d054054011641080b01c002d240340281d10440089901041804007964000c1d0b01038468607404c500b40b00d940700d031642004482c00c080302483c94028411210b00003120f03e9150141d0314140e500282c025110b900c0c015415024009001181e641408200080182d10000c240c44410f82c03854800540388a1406004010b054483ca82c84881c554104100c031003203031040301d80d800c101200d250400c5a1903003164100701110500580042a0218000090007001109044918444e82c81580c6054540d0360354004d204201106880400251307005040a00c4203140c030a03c01101c50f100a0001424010521f001a080d58800000d9113a43e800082c0c02b071141503030a0084030064140702d0003c01c800c3c02e0a915240d40e99003070016a03c2016600c502003801c0100740e803c0075603220b01c150740a1200031213119050f40c855205150b00110a40f030000300042488c502e002d01c0c0c0803945810090340c200071541e150504030b035111141d500b02044c2d0300da507400d0312080c0200c0c4805 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 585831366 1250 585830116 585830177
    0x409030309060b0a05010c170f0a020f0c01260411060406030e1203040b15030309040c0e0109051c080903030408060f0702010e010b10050c070f061206091a0907 70
    0xa828403480c1409002c44400d240044e00070100820141711a9030099001c984261340000c3c0c16290b4012943e0340e04050060190900e21407500003000c480c815030003e5840226480700090b2790f182900800151a500d101d0b0ba101ea15032204450b201c56120001070035260320500800300d10300c0c018601c03000103403142d00641010380866951800710b541e07800304020051180d01c03c10545843d5040540f60400b40e0040240603405038a45002404419101401500d902c04400341052100359440000036160520911845000421002001907546821038001034058407284c4143d4060b00d15490740b85e01580b000d01090307090b03c82004009001e4000308042d611483c001032a500e42410241c070000d094410003826950300d03a04005080d100c5036185505003030f45840a0400a944246a600441c104403540d031000c2c02441c505200021010b07040481c90b2003402c00e03090204041d0341c0f2910345404075500f241525076169990701e0012400e04222046a4110410b800c0a030300b0990300300c00310842c0250440780b60 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 585832616 1250 585831366 585831371
    0x903040303020606102015010e0612010c1407020d0210021507020d09060e131e0c0302030c0f1e0a05070b090f0a0b1e040f0c0b0f091e04090303 63
    0x100309269061051607007000c01210300700418010528006c11052040700200c1218000820b4200d00940412102e0304000513654240c4c0151f83d00d5007020107a4170211010703402561041d189203116481031080104100543e120041c001c0782c80d10050700f068006500498204a510100001582d101a11582d1028481d030080400c04c01c2480503000c1407002521040940d4083c1e60341d0300809811101340c20a0369903900c1c0418034000d1400003c3ea04880e0503130315003145c9241c00450880c0345d1510503504440440d101050201102901048040344012110205489428420102c010f28400004c04480c0c4200c0c401c0f0785e020240520380a0590711941555011900003c1c910082061405080f9804051540a0b001100c4044520f5488401c02c100050116510000068418801210303a280b00340c81125900003a28152900c5c500c003105e40f10040d2544404813100080a146000854403514003461005041004640502509034a9802c0034082009545042900ca44461041c825520701aa402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 585833866 1250 585832616 585832619
    0x215030c072411041401050a2f060106020a080f1b030307020304050a0b0403050307030e03070f1701060f0f290f070209090303070e0d0f0c06021b0103150905040507030605090304 78
    0x842c044a01c00c3c0d8014803a0002400204014544040307003402c0000300782001c1d562149036a07001c1b10840380710104590303074200c0c02c45030700ca00b1007011400040403a41c4400302c94159032100c1042e80c1e03800d90848006e0150504100d20481d4084040c054074405d0100f100c0c40030103602110003581190011149040141d0001c1010083d501d01440a500100346003d030444c07078241103403907540c2c8a118480001c4c2c01d101007200031030200d840410407039005084030721047d025240c503280c00c04164900608180030540c00d0685c04581c0c0e103404c94081c011135001072040d125007840c1035040720845210a001d20b030460307000d078240d40c000d68565005003050510f0103540c4e980ca80051042103410180640305241c40d5206100b0002c0c425000007040fa20b0340c0c0200c850916420303417817510441040f4003500080c488003105e440040c2d50354000031103d00280d840c1134520400c43c6154011011504110078100e106102c820040144a9940e40302d075410900075825120600e840341c66407402d4450942d0f07000d40907800002e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 585835116 1250 585833866 585833933
    0x7060e0d0f03080f0c18040213030203010c031a0f0a15020f15011502060f0a0207080c15061c0b040f030e0a0609050f01022b2a031106040215030c07 65
    0x85580445c805d08514200000c250080d0341c0d07403000d81581ca008660000d1003020300d0b050508804000d5070300400900003034400c0c110040140014420507130301100c100300485003d10789008100b0795114003814072000c45107849010140c0c12400c904180941c0100d4210034201142030000314070380032030004021042c0d4549000115191402400d460440d0800030600c80c00110302e4a503640c01c000444405a12404941000701c5284203003620340c1c0681c41540b00c0c1541040b86e022805208030720844218244000b80440c051413010500741c001d1002034000c0000d400252044400d48117940a0314091a40789110f0300131440041458004c440880d8110000700400e1900238000064002d013031010700300c1d004400300d0800600d1080900030b442011855010395403281301368040c0e0070089030000c0c0034405848121101102c0c01301050140c00144030f41640d80c203100d0000038400e004071b5000d000d103e18010a42a070b03500c0c80d00054451001c8850400888001c254404004551000c00210403102c0312003601c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 585836366 1250 585835116 585835141
    0x317040c170a0c181112060f03030406050d053102040515060301150e0306070801140108010803071203110d0204080c09391602090a020c07060e0d0f0308 67
    0x20300300311103940810904000100892440c03030407158420080c480a80c0304c40d1468024050351489000e02030070202c0c100004840c1083c080c1d0017100140c40b40d202805c041c0c414181c4034407440c050000458001c000300d41c8400c41a920686d449410240030245210948807038000f100b980781c240c54110380817200140d0a52174584100b5400c10071100c403500f0740c1201000466002d004c144900500184429031854000b4001c14854409440050030798200d4904104054140902800740084034030744140403a4540d40500c03011130594110740011801c04203141d0b05e0710030411004030032104040e01c400d035540200c400b10014254500e0040c10142c1c44604000703c40c1d18004401451500c0f80c0703658010300444515040800d588020b030000c3e80c1b100e05902207010b040c4405031100b041c1681c45c00092007018040b030907664104040c8211000422a281d21000809901617040e216503281c108450810a540c05403510000100c0042c14410300660079445424800d040b040003039010491241c1089280c08101c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 585837616 1250 585836366 585836399
    0x80406110405010f11011b0915020c0603040b0a0603050303070201020a0e10170c0c0706031a040903080a1505090703050106181a03092a040606170609040317040c 71
    0x8825003070a09207441c000800e440c0b611144441442507820200e02d0088003074002c980ca2a4031141001324403846910014481c013010307c20b080b103046400c44030390460340c800719030004c502c0e00051160b810350b100da890300c60ba250406810107002d2580c3d4040000050814405180302c0c4c80280c000603254882c92001801104601120a114100c040c02c0c22140c9600b00020542110841000007259a00d203401c3c8015032040e56000300b168400c2010020340c066068104900a9682c0c01c240fa0640c0c10120038402500e148680080115407041c0005005040a911914442500316400003420341c0d5040891080392040c2d40c80e500107504c0301d005002040d08a010030005500e84154000301e80d00d000503c6031401c941d003040b0805c001c00040410b13642e51080080381c6403030f00d8813100c20322500503040c0c1d40c0b03c803954000c1e41c0e03e000b1410b200000400501840303410300d9940c500041445030340d40d107904000032044000c00403000d02075112400c80d1107045114039075200c0c51207030703022062140c20030b00000040c00c0170 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 585838866 1250 585837616 585837641
    0x80304051503130803041a0f1602010e07030327090b1c1101030f0e0d02010e06013f0c09020405150304110d081c02093307020d12080406 60
    0x108140500b140c43c2008400c0e0301c0707410074109602c03600c451031310103152100e880d145610650440b00f40030032142a1070915024508100d60b01e40740c0102c0310002e03030030389010380c0800707180d6008a83c080010030b026140064285860030b00c44040c180300701e0013050000c0c240c0c0c0c0040c01d003241e880c2c64085c0c00d400c1255003132520312243c0314150b1036140079945d803034030318002c2c02405810541c0340c0a01c2c8010700040c6e003003040d01d240c03541c003600d01424407044000c0c0240880c1c50700c03003102e105070f100001d26400c1000034541d071461500500f0708081e003180702909041d00418200d11402020451000c00f142914002101605c0c2000c4c0150b9683e00c0e04d020031078079200694500c20502010401d10002640350210388200c5a0180c40310402100c580c10002e41d1170040fa0401d100f850340f103c01c0c401e91210194014003c01504a07aa0015261080c1c010120203915142408258452842d122459640003025000f4184002e2202e440115155104c640c2c940411806101051091091104000e20f602400006246 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 585840116 1250 585838866 585838909
    0x16020a0b101d0402031513082203050a1104110d091424070212070605040c05060d06030228171f0e010b01080f01050d050a061401060206010902030c040e07051308030405 74
    0x2000446480c02d0350342d00c403009100110010f109c01c2003184003481602c5903e038a407400024140e690900c65120311505c4070484040c035641e94100e0346031500b0300c201401e1407904461241403004450a4000824101906503900401040740f0300d0a000100880c22000346025004412008581c5401403024005861b01040d9081840c2b1180c2071b0300564140c450050304014089100d44640c10029202440c54110b00d03040760000880103640340c400d400c050b04580c803d40311409281018491401003000071a50415030404650040008003440585609003511176070584a4400444084200400d6418443c04503591030f5014920b44000a03c16070503040c40a0a00d0642407414603c00201c0d100305018107841454840e01d008107200081000c1d1014a510280401140c581000c6022100000740b046000520030340c000130480c5d0000c0d0007507034000c040310300c406400d20703040c40e81c003014a02000344461304000e0180421504180701100510081c03c0980c003460341c0354113010612030700040e101c8141d00b4421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 585841366 1250 585840116 585840121
    0x140601081b011b12031b02120901081b030106090f080a24150b0c0601051906030515061308011802060d020702062206030516020a0b101d04020315 64
    0x4084185103070228070900e0100302059204901c81d40c200c815610190482c00d90601c110b86680d010b901114030700e0109440600c440c2d070b0b4204202d85c1c0e40340000203050f080e10284040d00103075005d0304030719030003075030300005002c0108064140003d1034000341e00100000d00021401c1203c4451442950090021040503011441140c1c4400802c40074924110485c000c4070310020003280d5003640300041c03540f000c00c1080d111a0740d0320212142e58025030600d00e414010400001241c0c41d2403083c1c0088031404c003a114050320301d404019801003500811b00f0203410035221030302806594403401000345e960740080c01200e182c00c00701c0c05400c545003100000d007903a05007040c2d036025950303940907244400507044000d41c0e5030041d440030a205014070070021841040b1442c03d402b04480308505c0300150b80e2590340c00c0040b07035107881d04103400500c15122030015800c40805200800c80d21a0400d41c4810003500d44000640c0e51035100048000b10076520207042d043c00180411490144840305141e0508100001c450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 585842616 1250 585841366 585841393
    0xd0b060414131a130b190e01060504060b030601120209061b1506090606040b030604110f0403031716030203060f09102612031306050f0a14040b0a110c010914060108 72
    0x2030000d50014101881505c0080c0410f0b201c0072408529140c407003c1845500d00c6500c046010b000b950080b244142d05000000c12460051402d4034811b60f0305944108480302900403c0c0025407000e0a1f0350381001d0204812104c014507113040003440b071101001080c1c0040700b00504e100340a00600320700d20980d17000061106a0740d0b040255400d03901207404442d9680c0303541c4002402807039070b03519201d801d00c0042211324040700d201026100b164080d840c0e0030404416502613210f030007011036070382059442d44600131420070721a41c007540c0d0061010700604800c0812100046545e4002c80d540d0640123011403040c455801907941011071000d50b24400f04602407141c0c250307516400b208640100f030f17880110020303501c91003c8140340c0503290010303803c00890602c03046182e03115504803881d0303100a0074481000c04421084c68680d10498001e5400b04c000d4580c8180e03800509842c180c01c054249c030900404c4c1c4081c0d000e202e16448144601180d02c50b45540420841c10070714141d10501080d0070020211094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 585843866 1250 585842616 585842641
    0x801050f0a052a0a0c0b090a0b01060903330501030b0711122d03090622030c0209060402040f0e01030311030a09050d03110114011802090d0b060414131a 67
    0x101010600f51529682c1c07840701100c80144105004d0113441d4000140060b090002c520214100d009400303800c603580e02c0700001d5940030724070b11000384080d80c40003005154100300900d2a65190010b43e100783d0b140310a600d20340a55100303070000e41d40000c103441401038454001812240f810b00700c501a0000c1c42000080785401d000341080040b2088400d900c00700300394410310b16042451980c240741500d0b4180810001d544001c02c9454480620200c40f107220044036030055082c90743d5140e036409000705081da090050000c4080c0205400030b400b40303c08103107032035018050b102130240000007407881e6145050041001500c11140c8616400400034282880d80c0400b1036403d58030260349881c5e1040031131504480100d035030b64003480301c0d5192595a00c10341d803241c1d6880341214501782c02401050130006d49001240300d00d13102c03958032a240d210018002085080129840b210040c0006030001004d82390100d601c9080f2110100e411120029008210b2203d040050410b0700303600d400402e2500340c0c001c110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 585845116 1250 585843866 585843931
    0x105030c0d060b1c060b040c0908100c0e0d051c08040209010e04110a0947040204030b040302160806070509091302040c171f0501180801050f0a05 64
    0x70760b0303290030b0708550316180c500762084000c04200490840307964a085c00c10003881650a450b22aa0400c1e01c0c2d4100c443c0308006040944807050040d0074140c2080c0c0c201801003003504d114030184080c500400c15296070380c0d465a10018040c0d4050a007070503e5603035945010210364404402d001d0900140405a04c0e012a0356040d0ba038941c030240b42545460514000c5c0103064904682d1050f2980c4010600c4003a0307400ca000f070304000c20b00f1040c080c114280c412003050311000d01d60240e4042614a648640c000c410102d000c020080d000524254407a05d0740051040110f90a802582c0880d07039110061603903070000c00040c141c1070003800650a1546d03004000744611449144181c128001107510001424000642d40c0d60050003009407841100b400b070304080f00c845004081820790000502072a11400401d4500e207800d2800706400303800c01c0c005480c0c070f1021074501c039181c41c80c007503001c1100c410901c2224000c5824501114003031501d5000582038030002070087c00b41d02d401152507080009908000d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 585846366 1250 585845116 585845123
    0x30c030a1103040902210604090519140a03020f100e0a0f080903060123010c050c01050f0c010501140f06070c0b0c0f030d050702071e0504050421090e0105030c0d 71
    0x107080c0d01c40554680386005503084102403510001d41740c034105203405c1c1420701440b2030300181300395560740d0030400040700d224082c003428642001001030043e80300c2c14040c281651003400358400300d41c01e45001c1886c0031040340c03040300036a2000100d041005401c122004c1d0020800d1020701c01d040b02d910700360351140180300c40100a6200e01c4040f10405c203c1c00292048a1000750440b4800d43c0e640f0700d480d080e00901c81104038003080c5106040110b503c5038503125600c940260007003a54405500044805034810302404031500002e000340c0f11441000c0c06041e00a05819024201e560300319810048910802100e40303128aa01b00210000102c03046481030464000b001d549896911048005040c03001c2c607402d511140c00009a0740d0081c1815500ca01e018441030b908841c180c80c0c4031780301d0340301600d98000d680c0b1030404105c2042110340f8040d04483d034864801c072030b010010000e4203409001040d541d103c85000c41d02c0d164051001080d1031003c240104030403001001c14803410030115994040468024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 585847616 1250 585846366 585846377
    0x41703040302030403171b1c09050337030206040b0606070302190309080a0302070f1e15030b04060608060102010e0319050f09030a080d1b0503130311060115030608030c030a 76
    0x845900d503c00050b981e4000c5117000101d07018080447c52a1295080c0c80320b003030344000141c0c204049a101c1c0c1d041d0801e640028008000d880208043c040441d04400347c601845859010181000308802400c20115440b0f034005180301d08081ca0115804000100868080c41c410302c000000b01e580000d29031040c04c9100c280102c503684c04c0c1022180a06981c1154541d44595110001019400148681200d640030883e102c0180c903134080c24861191040300500b03030a000c810a10070700520800180071071f03455040000d1540c0001d80400e0950b0850340c0b21001145140c001c00c10315507028040c0d11150b03e0740a014502e001e940d19030028200b1191089402040004900c180312244400b08648040304010122020301c0790602d0101902c0d4008181308488034240b504089041040c01a96810048503441b118250f54500485203014001c0c100103030100020800302800c007001c107200240c0a000c84400c501c140d42da48c420080c5c25144e003544019015401001480a000404025030f1490b001c1c501d0003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 585848866 1250 585847616 585847643
    0x19150f0507120f360f0b07020907120c1e03050702281a010305100221280b0a0609030c051009090218090a092102120c06041703040302030403 62
    0x11240004036418915010500322071510340d0b60400c82840484803121350703c0094840d150548241030440300e00c40d01c07284400c00d106010044c030704013204590120b41490b0007010090482c1980043d1644201311001256240c8070313481c4aa100c40003000140901400c0600c000c0c205240029039503d840d00510417410048680201c60003e886170f03001020303401640000e0076291400503440568000c1c40221801d1103001100c212010032802514401d800c18004003400790020103008050403001048a202101c21a00e00d1002e84c050a1030003007c52040d090000b8081000418000908090f8000e0010310516079001c000003803031480c01038284c800554081e64005a400c01c00c2e1000b46854120b50700041c0042185010000ca0042099009800300d94001c804d465218000c0c00b2183c9a20002d040d07025522061024646502242d0300080280e10403903068044013000051140c00c0301c043c0d0b04040c1c1208041c03009020160104085150002890610707605065402940e2440f4902c8004c0182c44441d20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 585850116 1250 585848866 585848897
    0x705030f0106051c1b090e0403020709091a33090a021809070225061d01090b07060504170316080405070b03130b16091419150f050712 59
    0x11003040043c403040c24040c0b030303a82140c491072021a05c00c001c4002001b6800c0000d08942015404d8016900360f005040b22506003005a000760003800700540710782100d030b90701c02805a403400c00301e4450482c230b203a945c0700c6805810200e840031014985014000c408a90f090380260b132807081250300200c4100e00140e9450104003541d2020101c000c000f135101c801d038070800440765001b0420200d140c0f205a4103a030b040304061040304910009005810000750815501400c48481501d5820003010506002c0181603403541c1c844420340c002e500447c0d07450b85500c240300400c200444c0f4290040c4101c2c10840c1140303032801001864003110642c003410041c0d60400700c0c041c440d0038401d00015028401480e5900d14090a40202903d2a640200c03050030b0341e500080c107502c4012404038000300305583c5440d1418600424160411500c2e00d546034800e460303070300803003a054445408a000300060b110112081020040c0902a40c8440107981c0c00d001c420020440002c0c01c00c5001c004c0b82d0958101b0741d03841d110015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 585851366 1250 585850116 585850147
    0x10c050d15030b190b04181e0501110c1501060c0b1009090812060405010503060624040303030902132c030c06150a0b0f1812031306080705030f010605 66
    0x1407024151283e03680911400384295595000440090103081c00382040040520041700c1465140754a42c0d100c0001c00d4000600310f0311160311100182041c13a034014444d861740350845440d00301e0201c0c07180e4005480001d00c401401030010800d038610380000c0d17a41c50b00380e01501c07a2880d880d0040218030f450001980000902d0749800241003405410011802d26282602d0f05500089491003101c0e0110002a1640f9040c0562030680f0405170180c0482d40316038082c030106135803569007841003185001c942c00d00e0440c080094001580039503008120440c19005110f011900706018081980c20800c9021030340c40c1040300700d295600c482d08491200b40c03640d607549045001d1410382c40905e00038101840001d542e401013806d03d4080c22110300352020341e541c228500d244580e503c105d030a00c0c018081000c458400d0100815100d2001e426922902c0402141c0c0342141c0c400f40424000d0001c0440520556500140c100ea00000c1e80c10218a541855280854824414403c1d60104080005c511340390541c501c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 585852616 1250 585851366 585851369
    0x1321020c0a1d190e0c0405160c020906030309040e0c0405090312060613120c0e0702011a06130e0a0e10090f11040237020d08010924030b060111010c050d15 68
    0xf04001c00c80d5021001ca0740e40c0720301c0341d401e59a203d1820032020884c1c203c1d081207910010000764407a00ca21040036030a21085140c000d08055040c00180070100c060b0711280954082e08011385d0161030107030390034070401c001c842c000350801d6495841401056100c00c0020031180d0481401c440340e80d110016116400d4589040d41c200c22a180605d21a050400c800702c0d07116015101c20740901800382d51282d10481c02c0307900d854100d03121750141d041c1c0d40c091070030701c0c900800d44c0681d049848044603403102000c4007a441c0940c0d043d0803035580c400250300054002e0002c44501c842900041c0002e000c56107964007641d400580190400103601140002560340d0b9040300c0800c1d0b88185510340c2200001d1030b059080d1803100c084072400e03200c20b5441d09124408100721000390300544840580e83d0800e40480c0c0200314078901e01542d0502000c0a20003180d2618003000190700c549420649460400d00041c280745103100740c101503078103010001840c00d030842d05a9031841b42e10100021102d01200c1c20700c1203071055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 585853866 1250 585852616 585852661
    0xe0319050d020f12070e120c0d0503070501110a0e04090804060807030e01050c04080f0304030b041e201905011d03031606050115180605031321020c0a1d 67
    0x3a00300344c54452030b54002d00c0b440041d103412211281c0581031000320680c00c500c2100d590032054071040280f0705989440d8003035010740700301c80c109420b6503140e83c2115031030700c0d5440c41c04034041000d22142d40d0000030301c00051000d03103007409665072660b1211810f01460080c0b009200c18100041c00c541d2107644443e00356a4240001d00070382c10b21002d14801903200d4010003801e80640e0341ca10360760000c000103c40480340e000c03a0b0305105a50715100da001d9a9501030b15004401e902511107800b0403400d036550998004c00900c0b00c0f042c040e0740c404000309140c00750854140e8402080017000755070f80040c0300d0062603a42c6024803905e032503801e0009003140f00e60002c05c0c100129100700c05003805020750140e41a01d4400d120890b401c8021081660404090284200d02100c0400c00340000780c80784002d550080c02c6071031000d02028184d542d21006c0345019800240503a003030f244090707106504120b890390142060f00d2840c1c0460408408901940b40e1400c0c8211144034078011a00611300030310f0380034a00c00c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 585855116 1250 585853866 585853897
    0x1140c060408090a0e011a0912030d150e07020d08090f100f0e0a0c03260c0d1b03020a0620040603020309070b0a020d03090309080109030504090e0319050d02 69
    0x307080c90000115002080744501500c6641004a2480c4414071350038180d844409030814500050762809805a0110600b01d4000361185540c2d10181800c1001e000011910100400c204c004c000d5251901500e6a0080340e111180005012015401040466280ca06441d2001140d61800701803840c00c0503000004100d842f400241c814580f81c44d9021038190458140188024034500720102d6596010410191000a000c0c2c01000081c03001c1e40d0548003490045e4080741c03102000c07000504175030451080018940c00500007215995440800f942d605900410f4692000d03c458030b000323650740d24811008016075a2070b03c034040d402d4400701807001c40b07049409645035500e8071a60018007941065030142c049100b015008500350103054155101000c290740100a16509034800714060415000700f6424404422000b041101c800c1c010710105034040e448440c0d0340c5140c8010301d411148001000d83c996041400b4445c04a982403413a61082103152800325250361001c071031503000b480761101c1400c00301c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 585856366 1250 585855116 585855121
    0x320030f16110d081902010b12010f110423040b12101103010509040b0a0b10030207171204032d080402030c0315060607060f020706240e010501140c06 66
    0x9420450341d80a84102d070280520030b0310405102c0b02403181d0740001c0508400b03000d4840b400d84007103070080300d21500d440041a9000781d0030102d9500301c40e4084500059440d81d0604003103511038041c0782c01100c296503900d0b251a11700080100030311709401c024014003259426214050740c0b01e40000a103030071700034600720b50402009000c40d990304914450b15502403c245800d00c0f14140c1b2801d0364100c0d200130301840103a9940b40c0d201d0b00306840050015035025510b007140340094a6107400e10000c0c0e43c0645005a9500e0a030602c01c0810608600d8450080801c108902c008403408000c10703003007981410542d030006050700c6806135170025284003542e2070040140c12481c55034400c030468001c1e4029419034100c60710344001e06489540c0e0403c0e800310344450038045042814079100524005029400c001f42c80704c0c1924095060781e20400c0c00b61030040c0c80f40e111250000413100d40355407003400d07404130135200c5140110400c2c04201c14481c841c14040300c481c01c1c030580310f0500112520351087c0001d9079401d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 585857616 1250 585856366 585856387
    0x1c08070b010608060a0605040501140d150e190b150f040905090a0605090318100c0203030d020a0906090e010b0f0909040c090b0414041415090615010305040320030f 72
    0x2d0f408945803072042001890000b0810702032000c945c01d41e001a5500e03421014a4000ba581c6544a0480351829654459407030080c1406400390320081d03c603070b031070550701d908010f40e1702580d0402140349040451301d01700031403605507a040c88140d12050840303101921088000d04500182c080c50340050500303030901081195024012407601d000a2098100f08007684034400915541d0248400c080e2042d69604441d136220301d010040c170400840c0b07514100c88071071020b03030109003960404500444134079004100c1c03181c4643c1080741c0c90080e01403454a0031506142400705d54915006101c1c01100200c00105030311000460b074110f506591001d0a8002c1ca0b08203480d000c00c00c00315920540889903c0c001c40c02c0401d107014007410300d018101e03917200081340d107650300c48040041a000030340384244101c1d0913104040140082903445200b60202401142c0341103029100c41071001d40c50a41054580b030100400070b60002030741c20340c0d0224000880704200440107901d25620850f807100b81e4041c0041580c00b4031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 585858866 1250 585857616 585857627
    0x1020f0a05090a0605120a2d0b1e0307171903110601051c061a0301050117101103130201090506180a0b090105040e1905331c08070b0106 60
    0xd101094074031980c2d09698050031100c0d401540032107042c1781c06c810003107440c0d006a40c01c140445410010319800440421401c010448135442082c4011601e64801400d1440c0075a80c1c0034079000c00403890360408521100003a1214074901403940c20318044559080e003406d00f000400999a0000c0740b14608034010300380034080294940b10b1914520480001290509200b400700741040308162101240b103082e039940c2e5000e81003083d0300b0380010500c41da044d41d4035038090003610300801c904140d03a80016044e017000c90602100d107092081c420f003007050380310000220a003100da21418598440301c0c3d410031440100c0d070f0009168041944040041400c004001090a01c031004080841d00909050b07076236400a0b00c280140b154850101d00c0c103220810607820a5801d0a500a0704009101c3c1103181c0445500d080f540d041d501c911100c402c80120a1064605240c08100c00c2c0ca0090300d126080c2e6580c0000d580110004810fa12650140c1c8041003000a0718043d549034990000b500c0603250703141d8000610 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 585860116 1250 585858866 585858877
    0x311030301092c030d0b01180f0512010203090a030e130e03250f06021b010f0c0311031005060a030f0f150e01030308070513080109051b01020f0a1401020f0a05 70
    0x4103c1405402d0a4030410640d141e680f45248055400c180603030055074010a80d170b80065050200448030f800310180000c5001d0090000c60207200c00750382c1003d0a00c09480d11050301e1500383e13813040041c40503503540050503c984a034545026020600f0320408102c10510000c004442c1764100907001c1000300012010f4100000040200d520003c0c20121110210034000c40151030381c6905041071001c074803030350020000b403d1410001000f070000d01280c0c9003160b600c11200005941e4a94080c400d0540c903000301300d020101e0850f080d046003040c00142000c15a0b9100c1c1d14401c1900052042a05003e9003240ca409202014100203145220300070001500340c08d401204946c004201c0820908807182d0914141d81d05581c0310200b586da030a80c2035a180d0701015903041800b04800d00050340060034014a0900b0303104001401b41c5071a16441441220800940513055401007042c80307640c21400500d1a08468000300c59020414088080b58024425040e07110421b00d00090003c8015401400904 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 585861366 1250 585860116 585860141
    0xe060402010f050403020a0e090a0f0c03020307050103090206180415080a020907030e060115020304051002010f0506062b061a0c0d081302010509040609060f090b0306070c0f031103030109 82
    0x40103101071900b1a00f40c4110f00009510000110b01401000b100054084c0e1100c60320084910300e46030703511900341249260800310342058581d2018011410107008c014000c010a00381404650714503030000c0c05a00904c4d100c0c1d0705012903c0c007241c0c0c003a81c0315040050001e921001c04200d140d00d030009643c5600154170160701801400010034842c0d8800c2c401e0305107183c010000f0b0801e503424440d0041900300141d4070a0114441407002041c144d503183c41d0100690000d03000042c8407541301d03130300300241d520040629102d02001c0c0040000c0400b9082c10f11039a0361480780c4240112041046e000c01883e4580211481d84e002000e840003240c0f080001740f5410420000b10713405010307521000c075030f1a58101c1c0c034007402002801003500107500407005001c05000081010641c9a242c260410407180c1540c08138581031102e010400c0368406034461031340c0e04d000507000740c49a0b00e0540f030040d003000120f031001003010b80080d840c0014588145000c101c0c15400e00306407903695035a00c4903e80505000355149 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 585862616 1250 585861366 585861377
    0x9280503010b030606090708130b0106080a050a0c080c0a05040f1508250e0d1208160c02090112020d06020c030d06060e030d0513090e0312090d0804110406090e06040201 74
    0x1800303910f80002c10500c24203005021404654508804a940400c0900361324407584041c01081d00240c1c0d5200a01e019044507a101c1d10381c3c0ca80f20b204101651000340450000901c1c0c1a94051070340c2e80900211f0f03001d440d181140c0d0351102c0142e0f0403070350361241b680160216500d0841c0428200c032600030341400540300341d0300c40a86880e0202450121000412101c0f03074a2030600d01d2007802c60061f03940c22111b880c01040880c8189081d1516104040700f07001c014005140c0004028040d10052080b002c520b2041c90b10056442c580d0b40490384051060080c2c0302c2c442c40d1038503030b02c00315612140c0d41801c00341d01c0901592511038502443d5580c0d0409200891100d00703190380401ca681c482c103a241d03080c040090080138260741c000703425035981d442100b13140c0c1d8038120030b071003c03501301010b01411428100d4a1f004541c2c0f00d8148a6907007014001600e020034607017140040b6481c50398030030303001030b04260008448804c6514400000d40100816032003d0300311802e1800c5d440002001040103841a8000e0b02c50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 585863866 1250 585862616 585862631
    0x306010c02041d15011d04080c0307140712051e01020408030d02030411062106040e0f0c03062802160c061206090b180a0e032a0d0e01050928050301 65
    0x11303581880c82c00d018400c600082032030082c06148450801680180c003802045240182c45012141140c0c09a0420b580f02e80720b28103c4001d10380c0c2000040014000c2d1b0342002460002581c41d0340d1200040c100307032030700b2061082e0880c884600a6040303400909207003040303030f6868518909c5140690000c0324161102c17102010420074a0800008640081844509800c06000101c607a49601000642130a0b04a41d031250b110b0340c1180100030440312680b0b5400242a882031100825240050041041c0300355122445001710201c890078100042002c00c10700035131581c480d0080c161501c1500d943c081c00d8070300e81010000d10160800200121110000c205021a0f5180d9019905440c2903002c0705412200c406032500340f041c0c0710462035801403a103404c0864200703080c001281c03840e04184880d0548140207065456012800703103422111401010161401071807915000d0031078084038a2040c1488800504620140d54080c0c2040300460511030f0540c86a0880e18000d0340c038201030090a009601c0c0050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 585865116 1250 585863866 585863893
    0x1912030b040204050604090c110f01020403140307050d050304031e110d03061401111023010e01031214121f0806040f0f021206070c060621080306010c02041d 69
    0x2150281d80d406441740d071519151408140082440500501c01c1081782040c042400600303024401411200700009030319542181015040c0000c00981d0b09407551080064500007030300841c02074403003e014184681c03281e54904003620307c07451605007040d003031420780c1212100c1500146901100d0021900312400001d00010690484519015503200400c0558148800b50301c00c01c0d0a0000e0380c40f082c2501c0402e1003045100301030381d4201005407101801c620401100d180b84c21a0710f4010072840e40c1c01d054a500d03545940143d9401082900c0810090011403494890b1120440b4902c9158280311006890a0f2020801c070145500040482040b0701400090b44100055028000d58018071002900980342c2d449101000c002d12080341c01c651804024144448c06000080c0b080c03a0503110644080014600030040318a01c0e084021450b400844181d42e510f8101c041ca00420340c0040794640d40d031070360401071b608502c003004008d5100e418038020210003403500da53b42ca41030121800300d5910303400111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 585866366 1250 585865116 585865121
    0x801061b0507051009120b061f08040206070c150903030906020d08010b0903150112050c01090b09040e0c030a0302010f050a02030c0f0304020f060403060c110105070203070b091912030b04 82
    0xc00280040e0711501c07043c4a43e00e01249002e00180b0349040102c204c03a0f031407424101e80c0c04208401d441801005040100b141001240f1248190300000361841c41c00341e2850240c203401001d4806402200d0124102c1c08000c50030b41b81c00c014103114440004102c1040000400d13803101400700f100000d503090800200d05000254400c03450b05507403602d0860742e003000070002041e044070310100c2c0d01d40304080c805e0411076100c14516019000c85548420300b00c4070b60802515100c0480f07851810018140001c02815040e0401d41c2e4182c2d90454000c10080980c50170309281451002ea12075142c060305418004040d0158000e066052160030b080c0b103039943e035480c4941240001c40f1180c081310700800c22030315880300000003503600c40e00c000d001c1003030200c815010441d41d8010780c104454495880c5100c07006550021190964561000000d1002d0301d01050025202c0c010098010482d05410012030f021507030500020607682e561820000c00d1854500b81011214a00e10382c92012a00c1c02200064a08050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 585867616 1250 585866366 585866417
    0x80a0204050603090609281b030816060e1c120b0913051b1020070b07021206060a0902130503030f0910090302011709030d0c03020405010e04061208160c06080106 71
    0x1032901a25203885520780c042c847c448008003840c2023454160200000d03201d10060121202060f4800003d410185000401c5403884802c05006038840c0e8001c00341c1c2034444000e00394004075490000d181403842000300b800f5250a0f50f4440c2e114540d2820070054603c3c00c8001060680214112948049080000040030220298040d04a04041e01b01501d440c0a481d44441c0805003a011003c1c00720040461405c2003041c0e040041c00303600c00a409415860011a11000b40706c490740a040d550800000160407140f444c4030300d41d0255004101040c1d44000e503104034008220203802d990356801806940d00312039100ca080f8622880100365180840741c4190740d800c042e2a41a11801101c00c004541540340d810b0007024815184000c00242e5030840681c01488002c06650324050380b1282001c0014007400e090200c3d050040d482c029080011079980031580410a4014403e1640e90804600480b044444004003034004268182d001039000e40c00700160341241c0e003a5031403840c6c9207034020110140c402034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 585868866 1250 585867616 585867673
    0x20d11070b06010c05070f1202150c1b01030f02040906090e0f120706180308040510022703070e0c1908240f10030f110403020a06080a0204050603090609 67
    0x60300c00600b86501a084010750a4015012038a50a5850440500d100c0e030903001481c10881d0000c07520214204801400c124211120070b0310300b0018043c2926136140361110381c1d0503031300916175141c0130141d009034002250903a91a809565940d100c0381c3d16009084280f00e040d0032203241283c5922896000304034156664015009005160a103000c500c0e01500302120540c0c03000c3e9200c2181c007058200d60408100c141c440c0d161503919207440d0030f05500748a0248846409580100311b00442400302c000f56041e920b41e6031414020511004010a180034699048013071622103800911a02d841c0303d0000c0d0003402080310348501403601e0288122010407080c2c9556040d81c40300413060352400842801d480c5052400351441144c80032060004450051a441e4200480d64452007401002014040c580c4141c1422903002e140924607030101e581300c0c01c284a1041045a200f002c81e4103640035070101c80003080e0050550340c50b408c1c40d40d159611150140c2d48442c0900c5070b40350040b0111803044200d000e1650 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 585870116 1250 585868866 585868883
    0x2281710180b0a0209130b01020f0d05070b04110a030c180b0a17150a0b0a08070f030308071407141603110d140a0c1508010f0504090809090109020d1107 67
    0x41c42c0c1d03a140c0308144040d0204808680a200502e46502c850009030703403002440e2030201d140e00103440003a0404112415980c810341000540005007070304181101c402a074841404101e81d07075907040c100019904001c1641d44010701c510000280321103441900e096584822880c0e02103c1159900000c942443c800383e904207102940411480480542220f2401c541e0001d40781c5600c440c500c1c45202c0c883c212034003103803039030b49030514496070412900700c80140010100502d281428003031038481c0e0a82034032000b0308004030100019440d0344505000300885c03028100d510380340c00707441c0750072154101c1c0c0303400360340b010310902a0050325080e40e460240d0449401ca210705101d500d00030148907d43d04840c0c000d640000d104180e003d40000104003104145004070b03400e0540502300655052480c81d201007000800c194030b0014000340f15000080811940116000290240d135894032480a020348010240e201000000004201340280c00400b03010365071280c1003210000083d402c520301c1c02040005440c40c036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 585871366 1250 585870116 585870161
    0x8120a120e10050a0509101a0603041e080711010503100905060d0804150f111506130203040b090d180b071a010617060f01020a02281710 60
    0x345901186026403600c0035542c07214400310140d81982c0c0240d6208200c01c0e074500800042d000140100065079400784014480d0503920b80503052010800303640c0e10f1060b080003002c102000710321201c7c50003800d013005142810001c41e040c40106900421400e079800704540c402c8805940c4168101d9101b88020401e89125501302403d0000403d0020991034014020030010008240102d000d80000c004669116041094499005240c0c80240c07806e4000d0009800c0309460003900803403142c00c0c04209020040f070b1556020300245031002d407010544a04d0303200000f40800e2000e041101403290030304004403007090312020811a0940300d4654030030000e00c8418030603c0715090304401070800b1805003c8251340c0386ca4a0010300441c050a0744804045030400c00d40c008011080d43d030715944510125070610808420380c00203500c680541e900203201e030300000c400202d201c122502d01043c036410200740d901615201c071200720805100c800003a8441c03140b09140f5034441850b00881003c519401032015492 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 585872616 1250 585871366 585871397
    0x130b04060903031d07051030060e07080f060105030705180a030c08030403112205090a0b34050901080702010216120e0d03050f07020604030512030108120a 68
    0x240101803040307040603150b040c1d001040c03802c08504c5801d80540c4002d05603061500042041e00c81100d8149014040d040c558280e54209070400d03914248032035440362149601391203a0304000c04040d003003e130f1000c10000a00c585941e1124101d4890800c0010080c8682c8800c40150340c1790004640b50400120200505400134030700f0200100d6000c0c0c042c05a088040d102c4d41c0f561406a0345400c10451030b84041401c20500c07443d400346425101003136418200e2100c40e0703486000025001d94807500141d4684000c5030b4200070402c070041e4182e400089805290800e40c0e403144c1345020b60100a49055180c404c4507500c0210b07140145120b00050f107500f407800c40000b00650b60020010407407030640d5030030302014020b00c00220700d15401c40d00ca1203080e81106c2035540c01070182c40c211a21075001350084a00100080d400c1000c0760b071032841c000c00640d1501094400558540b02c0c1e600028050f014009110000302c07203040156041c0c42c0b0060655a00706003015845c1864040e600469001a00420b05500c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 585873866 1250 585872616 585872621
    0x9090e060f0c0c0a080c06040302060a06050609100203210a0b04110d050601111c08071704060b04020d0e01090308090a050a12030e0d0206100609050102060402120102072306130b0406 80
    0xf0021038500351444580705864600d50303500305490800c40c58102904100400d41c2c107100240d4080490581080000d0503c004250035000d0120004d0081105008000c40e090080040e80d40c0c0042843d0300c0c81d4100000c8205010168040e1120103481c1e0900811064500e000d0107903000c080a02c01109080c040c00c0d105190143c10040d116a0600c842d910860054000602c25603200c80c1c41c0c8030383d00f680b40c5581040105481c40040c504e40030000366403d07075040400b40b01000398000d40c1201000c00c4c21051440014024850409490b80e1185030002002580300103400c0081c036140243c5900400355100300c20162110010a4010500c0d04034403603d01c001804851100380d030310520b2400081f5404044207e92510301e940e10000056405034081100a01a500c84440a05079518211000d42c0c60b00340040c0d60342c070000e04000e10070201e1510360501a002581a40d0000390444010f140e00f41c03410502d440e240d05020740180050003981e00007440c01c080010010101544102144101e07901c645880e0300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 585875116 1250 585873866 585873877
    0x10f08040204021605150106080106050c0604060f0e0d0e03010f02040e070c17071a0108011506030b0303090d0309060806101b0606050a0b2d1e041509090e060f0c 71
    0x4104040d55078102040e8104001b0554220032540400c1e6541030907800b800e0a00144d01c000200002000340c01c04030140400c10070f03007044d4042c03000b1407411009841440544803015094003103118401c242d001183d84a2400c100e580d8059000308415800b00103440300743c0c440e60080c000341c00001c00206140070f114141d0541a41e00920000215103405a04031f0101d034810401521300e41c5c48100100d00d64154003003401d0060514000803c0000070495029420b030315984101c9080c1a55a00c2c0c00707046403000d00c01c4411550300100004000740251a0240074680a409150b002848120029490341003c603d0015400701e40c1d120007091000401700d80d01118810041180c44030389400c800503e9031144101200500100f46205441e20910b074024841d022001710350614000522340b000f509402d01b00111100152030340a4044910a844245180c0e1722460b408801190b0040e04101c165540c48400a8285d030780300c050500001414100841e61407070b06681006c0c2e40c40200c0301040b5000b010600501 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 585876366 1250 585875116 585875137
    0xa0f02030403080d02030a05130c17030904021317010c05040b160605011403010b04021e090105040b0408030703030b060a020c0108090a173606070c090207060911010f0804020402 78
    0x240380580740d540e800e0030713a00018124010103030040140050b45685000b0240d22901503000200501c4051700c500011002900c140c030100501e40c2c1c1250003001c0144201e4000641c050025036640707220569080c120303141c1e840365071100c030914080058111418020032400031301d01d68034182814141541100d44d0b5100081400f000c69040b1120000036500303018840c000c05038148920440d480c107074281030a42e820900f03020711451040050498840d0b000110f0000c004421400940710401440103980d00d10564001c0040c2650104001402c414000021720f01248203980500c9000d00103018080d95008000c0c0303400c0940c01050481509503c00c82041c0c0c0e0200c1990b040320000710943c0c84411004010170303815140a00c0c00128a500401c8480300e10ba6040c81300350b480220048003854420b040d0b6010380c8014401c0c03600180740310038815a41000000b0f00003604085603510101c0c038100d0000c01005070210b071080b400c1c038580062036000d03c00081c0d0203a20303a241c0e580950b0342c6d83d003080001c1d808150043d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 585877616 1250 585876366 585876373
    0x203130e06060903011a091e0c09040e0a050d0207090504080a0c050c10031a0d03080a1a1e10030c0f11070e0c0c0f0a020d02010503100e0c070b0a090203030a0f02 71
    0x403c21a40c00b40603039031004000d480132003420250036080c0a82054000d14400c004070140400d131001c045014800d50b80203451080d09522040d4510002d070103001c900500312810b1085800010038400f001c2900c801030403041d000c072044940c0d1090404141c0d08120741c00f13000420188004680030f40220401d070000741c810300239280403800030b90014036003017465500c0e440002d0341c0340045211003d189000751a8107008403040003003c6080da80041960900800040c074181e00c0b80c9104001c0d0601e42658041c440000300395403c18195180c9000943c1002c030703803c41c414403001c501c8980b010700a2107040c5003c076541c0d655000c1c4a010f00010380f5044041c014200e11441021800200d1001002e256401100b210f13007120769a98840030740903d0035118a246c050541c010400440050b6103004e10f805003154282041500c9649041000740701074120740c080ca01303a400401c01c0212040c0b16074014a0700c144a5609076103a5250500c1c06001c03606c0c6d00d40700130f4066000300005018280103820201034801e040c03049 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 585878866 1250 585877616 585877627
    0x117040c030804140a0f0e13030e0604121e02090711070806070206010f170a060e01020d1b1112070327060c02100503040b0f09010f1103160203130e0606 67
    0x302c001c0c90b481544004140c1c0540201c000d490b18140103103034001c01800f591024402c0c20304d403003c0748088010348482e05582c1c407ea85182014015028142c0502000f8030341a103850f40c2d40d812201c0c03086006000c9401007071001c4000300301c4841880c520141c5030080c0c1a400360f47d651446c20784541030744d03c20080491040c1d280004006004000e10f07441100b45a01910385c03545485260843c0c1043c58107c0000034844061283d21408001f8071401c40c282c20000201708485902e56850082c481e916000304e000382003816289481a40040c041540d10540e9a00c24006070403141194960200741c00c0780c0d00d10181004010003091043d00c07005902038107010b058121580c100036204050f0314540c4824082400d95440d6001e5241c040402c481110041c1441481e40c41d0550342c40c5c1c06007500600c4101042d41c980b0105006010950000f0170500303541c0030420002e8400036130a9034503001185c42011018000040c031a00c1c52001c404d03125100da01400f5a9451400c01c0512042000c00825254010310140803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 585880116 1250 585878866 585878873
    0xd0c1b121701170c0306150f01050702030d23090105031902160c06020636010e0706050319020406080412170f040501060b04050310050406020d05010806160e0117040c03 74
    0x20310500030f01420058034095882d558246003030141e03000d500d610a4000404015014030303040d4010500c00381c21100850070284042c0107030341500951001941521440c1c0f2182060b035041403c1c404840c0b044002e01030b070285e20b41c4103d941d9200e400c1e1039a0000f6000d2010949075003d0451415101d12800009803e268008a034034130380c1e2115142c141c808451300803041140d1a011b01c95245c010f031120492080d550101030b419002040014090075035410781402c0c8646002080d0b10a03107991040038240c6100039940c0c03500a0060b0000e07241e12007044120f05034201c4030102442118104c820384d484082c580d81e516140c603050320202c241c3e00c1c01404860010740091281d0300303501034032414a60780c1d60601400e20707090841c01c640554014041d00034003000103106a1346e000445960b40b040e204400304440e512860a40c02034060440400c0783e1034144000031035461004a402c034820a004581490054000801200d06030061000700b400319900c000001e038042c0c0c120403250782c0680508041d0f490b081e036a80d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 585881366 1250 585880116 585880157
    0x10c05181503100e090115030b0907080303100303030e03030f010e040f0b0430051903060f030609170f03010311030309030609030406030c0809060c0913020a050d0c1b12 74
    0x2500d100542400c0d003010f12480d41010310f2130b5000702c00798000b0081c840c905d0345980101c440c02e01016003560400d60000b00d840004000003c044c1c80941300352510b0381441c3c0801c0003040418041140400d0030800004a004000410740340308012255551465900c0c100c000800c2d400040d01c180c8009088018510101da00c68a0b905d0090344280d484005800308159a5140c00ea0b400040350840004183d02048132075000056400030111300c44001003e00c0b850303400354028413540c0d1204a00c55000d590020034800654043c03000240140c4940c946000c4085600d400c170b200f5441c0d02e0f0361100e0280014808101c090418400c0d202c4041d00712481c1c8001c40d0002440d2400458800e115503200160900849515000e00c08110f615814052406c5c01d005890300c0d1940c00040c030300f410303101000c5201d001680e40c887d02e81d03002c00d40d03440301150f442100b110014240c2d44611005100710b42010490420b140c13041d0128070b032640e00c0e0200d41d248000c0755616041982c9134109540108000115410380603c000b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 585882616 1250 585881366 585881371
    0x4140f0c120f0106030b030a0201020a080c0f01060305030915041a0a091e080c0f060702040b0109030209041202011802061804020f04080a14030c070909021804060b01030509010c05181503 82
    0x50b0400449601d01000101501e003003412640c040d40202c034110005076000290780701c00b20b5200074125203c9a417104200d01e40103070045001d101c4e6003004000001d02c4000700042001350030079120001c407200100c0c09800030b4443d520443c0d11030180d01950781e00d030200c540041e00c0949407900d08420903598603140c0b403940c1c003400c4c11900442d140040d020030130103408002c4018588c1003501d840e5038842030b86000072041d00403450064096500c0d5420450b590b8803850520015550040599403981080d00302a031503950351000410140d1310b400b00036282a9900ba5a8068050f40108aa860030101c0520a00383d03419a40341c0300d4000d9021310a0b03544803800c503009080a40740c54001001504840d0400008010f10042c07080c4140e001003240e0103040c200412940180c0704c100401048011052000c00c0c06041c00d0203c03d041154040248801c112039500015072400382640c0c14031454445d90b98103070896030010245d1000c18420401c03040310207604d40b206200c450006040928400c40c100012036660b104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 585883866 1250 585882616 585882631
    0x1b030307140616021b130f020a050c0f0a020a03081323041401060c02090403020c03100f0c09051e0109150e0315092e09050607020c04140f0c12 63
    0x110104080050b0f06000450b8032841c40c802000513a8066140c1c2c00080c0d244124503000c0d03008521400045103082d0480304510b0008002150b4880c006240200365400041412605000303280703000100344000280a481c554000789100d40545c076590b1260100d500c007100031007003445400c1c0c0000d2048141d5240c1a00300c00201d00010400307050508010031200400c00f200c1c940745400e40148401544000e1014100781e064801c00140c0d100c80c1016031a00c1c5030955041c1c2d040c0302c0e591003001003c40c50782040300100381003a014044130b0417000041c0c402210500510303030040c42c43d9440c116001403c4c44070b0403604c032040c1000382c056500c0303030701e11585c090800c0980c1d404200c0004c80810707a800d0070004415a205000181c640134140720601d99220284940e1036552068038194402c52081e4402d6450b00070000b40d84100455013440c508030741c9901d012a0850090300402021031080e060030301402c140c8821001c04051617544004c100c0c14a07000141c0842c000c034105106030070360001340800081c020b000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 585885116 1250 585883866 585883873
    0x509190f080d140a030c0c150f06050619120605030a05030c06090f150703020f0319060504091a0702030417150c07080306012d23040303021b03030714 66
    0x20141218a000d0b1160514010050403081c000340d0514020140c80701e0380e210b4940850036915080084811b000400030141030061405403000800f00282d00c40c100b2114825030921441d6650350402c40c1500600424610403e00802c40700c0a0350300c10350459240e0105d00c500003861f142c40d640802c0c90b0000c00b402c1110385a0001594113494201080059404000600240717074200d103410b115034a582d0102242c0200040580200e00d51034080d806450030400c1c41d0080613141c1c5448090b848510b0809500d0049242c6030401c089080d0403e030040b112190b4100765850801c0c4500764082103e000010000c1e002c42c0000d1202143c01d10188000036910503420000b0200841d10f42e500604c400c9000e004a180c008040094100044607002501d0348104242171204081064050941c888948410301c204007280c442c0301c09500940064401801e002d0540020003100364007804d1400350b110794000640076a00009414440201c00d01c058a04d509004c0c3c292420800196075a42c2c01340718004040709980c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 585886366 1250 585885116 585885119
    0x8042a0902070b27030417030d11120a0b0d1104020705010203040812010e01060f0e010c140a0c0b040506041203030b03010504350d090507030213150e10060509190f 72
    0xc213082240103e54802550440400d9100ca10650b079219502c100580c0022600089100000a205070b80052030486000c0c0000c50404040303035426803142032021002d00300c10021403807260a91180820307483d0007811404921202e521440401c0d00c0201400b0382c05038081100500290082c00030b980034a20950419440d2200c008a900c400e0760b05070420080b124404004010080d4046181c2c140c2c03a8075400d00712418039100004980c0ca4000000242c4141841480d01c14001000141c2d003c03107900454485401e1030f19100b64800c140310b036120309a0f0280c1c0500081c0440010b03c240b0252407031081c100043d080c00454042801d56404480a6800c00d103c8640c504241c84ca40355001e410021048611a208800070310f6402e290107100480f001203a620200c8500300501000b00502441d0010040e81c08c109408140a018018800d06040000e8000e000000c0046500d46007501603644030400c20865820104102e505411401107a41d00106070669101801f02c4a4050b4026080c2248002c1c10369 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 585887616 1250 585886366 585886381
    0x40b03071a1209121b0c0d0506240a140a031b050901140306010614070506090304051c0b06040b010302070204020c0c0301050702031611010903050d0804060c08042a0902070b 76
    0x10000103000c00c4041e00084c89401005800d00110342091a144442d06580180345025500e0001030b00d000b250082500c071000018428005a690711078181d940c0c802c0842c100b07a443c50220b64624100030307908141c0d030f12000c3c4044e582039074000c4400c1034082c1840d82e01c0d07903072503d40400500d0710302c00300780260200c010180028205a141140074010314003505401c89040c0300441d0359017a05106140801a03010704815580c80380c40111049681c202c1308035001820140e00c1952640d0062180500c5040440c9003a20341e03c87c240e2000102e903801050f036045d207541350804c0c1303c0034001c092405030401d6400c21030300e40103907200d10141c00c0c900403800040c2000780d0514141421210040c2180081d58020721004010b0711700c59021401c8141d01c01407000744c03e200c0100580700420a07400007010b41c040c104845860581c0440968861070048500b0300001e5059441a03400c004159030191001250880b00045184e55186403030200c040103240302402507a41000c90120b130030003081182d20300304c0c40c0c0034081d05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 585888866 1250 585887616 585887647
    0xb0f0a3003031a04060b0d090602190306050f4606051309060b161e0f0b010b070b1302130c050405130c1e0201090501090b060103050f070e040b03071a 66
    0x2503240c00e1360104001e40c1000c00050b05030003055101b0f00c400740c4034000f1170104900c135010f451615446100c0450704085404000e00a00401d000c1c440c000c10041d8000019842c00940e5080f03500440b00d41d2554041440c104848203500c80890300c10031101401c1c8081a842e00340120071300410441d510f95885882103480e010700100701344e20034040641050004e0284004000843c3c0c00412020300000c0f902c0400c1c41c00300b5506041d690003400f1800e0799a0b0010038448203101103410580f044a4113182c0c4e82e2604020401c5000d1000b01070500c40145000914801e15030002c0c4181c180000c0c600d2000b40404601e082c1961211001da40001d0000305040006040643c08281901d0700c2c01400c0c0311001d81c0f20070061400c4070030701e8045070fa62000504589024001c3d404591040e8020300207000c0c2802c141815640f00100740e48250000e441d080c000345101d040c2e60f202c1d0740910b040356282d9101d08004070400000d071520080352585405140d9001500031103006012404141d11000309071101d241c510300d201c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 585890116 1250 585888866 585888911
    0x11a060c0c0d15051f0b16020901091e1b080c0d110901020c030a0b150a030c0801050f061c03050d020418051605030c16080702030d020a060b0f0a300303 67
    0x440303406038032000008111826106082d5116408060344031302001d03110220b241e4000101a400c2710410b400450032002681010500d5040c2504140c00c0800801c07803039044540448104a560058180503103000b803040d1619508080314030300b40307818500001c95410444035041128841c180002421034160b50f0144495100351904401404202c03c0b50b440b03104400200500d80c403040ca5508000300690b550743e920700c401035074200f40700a42c0306840311203030b90003410103954040250b01424005001e626000ca40e02d83c1200c184400010b126140e6034069032a174120035000310079250244004188141444668140c0361000b950100e03403401c003c0c24200300400c0880c64281041401c100300808c00e0103800c01c48020790343c0714584007a114010305207105240550117000b54940201910a01c00c90390004801903003500440781000310000c40c100f04003d07807141c91002d03900700340704800410104504441c0d191401c4104150080030700c0002280c00a19492600c044020070703500c60100384000c5d5030003070100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 585891366 1250 585890116 585890131
    0x120108010c18090e250602010b040b0303070b3c0604090302120313150c08010807080c04110405090414011b09150908061e09011a060c0c0d1505 63
    0x2e80d022180354060400ea50501801c59410344610808052010402c030804d40201c0650b50100c03984958031420960600a00c1800f00660170b05c80510140c1c03800344030703814072104003c1c001d610300038543e5100302e15690010001c0843c0a040c44628210800410350750415260382c440c49222940c3d8091900710001001d00314a00443c6000d070f5038800245c0010b444c00301009681112130305c90341d0301c511505d02d100b00e0300300051120028814855101e601e41d00072070f940d4401078032110200da0b00d03418000c4d6511410300c0380e03800c0342e4840d0f01110003030308159010b12952040032161500c2e1548038800b041c4610816601200c14540c521044408140c0a1042c403040484454850038180c0800c1d00c02800c5c416a0301480340f88600b4507140b80000d0303004083c0c5000424000300cd8403454607140030095555074000802298078450800041c020100610982050104190b41e034142d103c02d081c18403d460f0451700019034035200c2c1200d40d20440e960319504616946c483e41607904100c42c0c4449180c2070b502c0c00b41100c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 585892616 1250 585891366 585891377
    0x3c0105090d14070804170105070e03031e0708030403020601150c0302060402090702011e020405150304120e19080c040b030c0a09050a020904020c1b03030a1d0d08120108010c 76
    0x4050648040359841d51400305151140c8407000302e254806462003820401490580c00090004030900010503a010510442000304140d6070761010035150704000c1103a443e81078004015045d0461094080355081c00ba0001c04641440320715900c0384883c4d0700075223064015134000c000400070082038817030802c40c070742007031a014081415507540a5581d0101034030080c454981d120005400038402d500100b800300d8005200c44100010b855804d00a600c2401014046c00c541a2040014400b94007164010340c0d00c644500c180c0b2107459001c0710565080d082d055800862003815888103481c0764144000383c241d04001d0804140040100001c4a42455031180a80c021003c80c28003980c844c03c00c4404c494100501140c15030340e81d40f071000248202c20625078050f1022a03280070b0030900254041826103020b1040c60a102035804160b42c07070188800070800111543c00355000205400480490110040d05014000c00241c0c0c0f4066160010b1062402c1011018010404c800007400742880251050801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 585893866 1250 585892616 585892621
    0x10b0c06010b09121903020c0307030302100f06050a030305130e060f1203040807030305070c060809060c070f0b040f02130c0e0409020f1203040f0501030510060c053c0105 75
    0x100d8480005200d00d80303401c0c070b003ca43c1c8640b5031034596000c060044441d0a81e000e8903000d0038000c1c2e81007800001a801442064030182003414002400c00a480e015001006491641110711001d03016127801c3d01c1100b52a800300203a070b46c4030701c0306441c050b40c42510740d5a100d41d40300e404940e2007891035100044210f100b00c10f02005031988c1e002680151000c0c0c505180b0344180007940703495845258440b140c40c2c03140d00c2c00003044c96401406810b485105100320340905513100400c4807c03040036111054a5040400131030407050994000703081e40b07442401050003c4d60541c0300c202c0c01d070004480c00d582c4030400842c0e60f01145460b400b00d0a0800307010b0320401262414110044c072065503a10300b60700465560800d00195a1b5030450307420307181001407141c042c1201e5040583d441390007030711500100400d461804104e96009004c2c0342d21403203000500301d43c40341c036100040322002480c0c2025a01802100c0b0140c40d00c0d100040820390715030110f1038082208034640503920b01342042e42000000c42c2d140005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 585895116 1250 585893866 585893887
    0x5060f0a0b010906051e130801181e0321020c0c030a03020d0c0c03120c02011206030203060403212909060a0b0f0d0207030309110108070819020403140312010b 70
    0x1420020746138203285c600d0301c3c0c00c4d080f00c20400c4804070030880d8801c0c080c00b0502c0f1240d119050310600940c1c12070002401020004180c140e07010240960050490003405072140f0600b4030070042121440c0640381040a80c807003c6a10f040d00c402c0c1c4012030300e88540006034240d4000040000b1072011200b50014a00d800031518001d4403041c000700442d041214126101052120940b6680c003c1c542102c00408100c0f0b08082c0503125104804040340810540c5403c1010380441e0b00c19602213940240180460381ea80d60707411540c4e001072800201d01059411040c11180600d44183c09420a20074640387c031141c01d0400c40c500e034182c14246640701c2d07100c2908001094440c00d0010b0121a680c090302611b905103204910098080e811807500140c3c0701142040c24103078983c0100d03141900400c4440b04000d100e0300116002d80c03046480202044848011481c401c1c4008540e4100900d0480014141500c03030b642c54004401804000206a1000c44c10380502000b19800034010b203480c8002a00d031516588 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 585896366 1250 585895116 585895127
    0x816110d0305090307140d030b032406040906050910060b040f0320190e420303070602180307120314090402030a020304050d08130f110d05060f0a0b01 66
    0x604001c1540300e0000c2151100200141c540841d40014031b0281c90041a0026984000380620080046e0504850342c5260801007a0020303921403c03110300440e501d0f52052002d098902500c00341d00f041e50307101d039440402c55510905008024010181a40b42e844c500c0b644280d400b660007841010404000400030812416100c1c0c4c12654040794034404500d41c0d004207034542520707200d4a80c00034800c032121010391519884450135200404104989038aa40940380030040c43c2d03247d040bc0b0107140e0218048500b070000d4494521045410b051481003803400007007421038218403001c95a481d008240e88a200c20b08c410740f00c20190080c2c004120013490600b809010201604018042c0020440741c0c0d1240c8400204a42c0301035800381055540b8204080240020340c421075044e1040d0113a04d07208055184075102c60781c029041a642d40c00300b00c465498011030006550021180700201e102e6448060300d03042080f2071014003030005030409103025036100c80da04000500084565141058100007a03030800c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 585897616 1250 585896366 585896383
    0x911010915080619170f06010609050607150e0a05190201020303011206061e080d08010501120e0109050604030f091409070f0507050a060203010f0b120402040e1c081611 74
    0x140b41c0b01c41d00351200004100c0d41c1c1c0100502050035400704001059401c6100025048008450202c5800c1059040ca1070789540c0b080c059040000c2030003000300120314003240079022103401403084480c01c000a01100040b41c152010503566a000180307040203110052003a1014407410410400da66503c5500007074403440705020307600f00c142036003030404140901da07030044000c0c0c0600e41603c46550030030400603d4540c03040c845c03030310750788566510718010503c0b8804a50480710185c40720143e600c0d881c0610009030540c090b008a4941d6a0055580420300420034640103a009807100324103404200070040071028580c0081c8075081d0b11682c00c1c1c45544480e04216880303420780ca0640845200c00400b202c082c4101400a41944250a04e070001e0081c00d41c0203504807502040b0102c180c2c0e6039410b119460b802040100060001c1c0e41001901502b46900156040c28000003a9030440000030001400c00303840080c80800200e481081200003070701c003509c925211009040100ea43c03814200859a1070340030703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 585898866 1250 585897616 585897659
    0xd0e09090a230d050909280c020109060207080904060e2202120f0d030b0409020d2a030602070209070e0603150118030501050f16050d05100b0d09110109 67
    0x1c03a1100800111005020350001c4680c4064075800c0420303070f0004080d6046040901e00c191496000b290042c2c40049014806035807220a01802c012890340c03400040880302044400d40d5218090040051154402000341c0c61003000f2042d141c01124045c40b00b15a459008094145e94035424801e160022201c4401c40c20245071030002c080c82148045007c046030b200039804c01380305105034418820800b1441d80c9600b041a80c0421400036000b08000a50b1002c50000c0d4100f1003074000480800c040c00188000004084411415503c05c031940768185c83d0b07242d10903902e00e40e002c10f01f9004c41c07502145540e081704c10351404c4000f41c901c100004207140b0014000701d41d55180c1d007110b0385042e40601e646006500c0c1903120103440a681c0c2c00c1c1a0b010300001c07510300452000e6900000c03040c4607000913445031600e5079541c01d81460500340255004100c042c0191046a08051001075118071850082c060f0940e2a000450b9140302480c4c5013031040030410781c0e9414418214001d000302070b212540d01030214103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 585900116 1250 585898866 585898883
    0x211203020705031c1e1b031a090c040b0a020706020c010309020a1809051204080c030d05072a121208150103180501050a060e0106081b070203010f0e0d0e09090a 70
    0x400c100c40038024650705401a0b00f12001069031510003010f0340c01007a036488541010044801c40c040f0841c12240505c0003581f500349408c00c050018140f4008003a40001c4a21a56180c030303450307485414450300100c10b81c0300103078401c00b810b00c906607061101041c100420b0806020180c00c542c00601080b0b03c2d4081d006d00760140c0e189940341404260031540d500e64100094401e0310b42540d14107506684540164203c0f40700d400700b03034512828000785100450500307903140d1f0b0400b0980d5440102e0050700c600c4944121a43e54031400c0041c4000071000c001305609190510031007290718081d01c500741d42c040d1060030b005101c410051507003c00028080107000900c2c002900020b032846880340380300300f1030010300b240d0320344410800340b080076078420826103101d01324181e996aa03074034049400b5082100d004525042ca280b10400b1080c0100191504d148010004203c031642d002d2540112041038180c03940c1a40225503450034650001d480e0103280500fa6800c0340f4501e080400c099517100c040c44014000503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 585901366 1250 585900116 585900157
    0xe1e0a140c1012090b070914090402060f031312091719021c08120f06090403090302091012120315080606091008070806040302010c030501050d0f050721120302070503 73
    0x20343d41e84800000ca5000c021620380c0d0915100c01001c0c0403a9001d85e1141d2800f2a0340003006140c230200042c800e550080c20303a4504490203054912540014192603090354000482100094103d07801c1c900241e40d80e0350300010145440c46041e0341641000003000190045110f40701225122805000400e405960060040115a03003107071074601d515001810181001c526007114040c1e01d00a54051240d800d4852443c3d1103a1040000c500c1703094034000c021076480c0b10104018200002003641c4140c541004052540d6101e42600110402e20822a02007111941c4400840e4142c820f13040581a4688814000350405410039528140500158414900100015017407643d405240c0041e24040040e504103c3e03407440030507a60780d41910101c01550800740f0b009100f9101c1d1156078101c840051a142e0368100940302da840d2503896602c00d4601c5d00440704045041c201210b100c40c201520032944012041e01c1d820031441c6180740a0040040600400c00c840c003082001082d9000d081c0e0f803000000032007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 585902616 1250 585901366 585901397
    0x60a0f060f20010c0905090106090e0a1a040f0c03050c030601270911040305060703051005011b1e1e121206030209010906050415050303030a0e1e0a140c10 68
    0x6a0302c0045800c0b06600303180e90944810f41c4804440c0c11514151541740041c3d03203429080da4101d03014052450125100c0340000c06940b40740c0c108902c6107100d40c103845c01042d49240440c094400d11403c0c100c2040d200d16003000c8043c1d00d48a41c951190314042c00c541103085c8980000c10104503100004140700800c00c544150944007518a030041400070f104201c0c0f6034040402d40c9168000f44015140d9006007400140310324081d000300740c031a41540484290b003030708010041d120b0b80d00300e01d01744155040a030080310005115003032640d140c8020110322113081d0007620f0200d000c04003d503401c2071140764180b00300c800140180404143c076a06401d00e800c04ca00b442d107040e0010310311540060360100d0039100016104600c0c1d40b0010540e0002d8078203211742e6800c170540b4000e030780081c400c094240c3d004100255100e5019407220b1100c1800c0b006444025200e8900714118281e40c3c038040003280c110b0214a400c201000060140c0e8986c00d001410200d10f01b90300060030602440840c1c1c040c01106c200c0c18141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 585903866 1250 585902616 585902657
    0xe100f060b04080d111b04091104060b0c1e030a032d1506020118060b0109030203100605010f1e1b0b0f04020109080307021507080405060d05060a0f060f 67
    0x791050160380e5840b140c0c1d412407169074806128209012a42a200c04000d01001241c012514194100c450322180024400c0c40000c00550406850340c0300c0c2100c050f12181d49a000b510010004404410b1f16140881d40c881d00740000030134010f8844c28861410343c0540004802e40e20000748034180000c9100c107991650180e904542c1c064240030202007960700442d40c0c41d9100c01114170b100c0c03003510042da0300c5a0b41030b42220b80e8281c4078000046a0603050b800180540c010001c00a018540030301d00d9540d0f030380480d19101d00c01d00ca921070b190701d86a0501031942c4c05071072146040c0d000e1400c80d249461440030a040d072000360082c48104404480110b502d80390b660100b07a071103644418403103a42d15005603028200b001c2660b082380020480000011013138000010303680c0303154005150a0107404a0081102643e01c40e1004403140780040c800012660380300d0000d0074468000080214913490007900708100c00c400341e00540d9080481c00341c20700009912241102d5040b1007402d010a820445080c80c805 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 585905116 1250 585903866 585903869
    0xc080702010606320a0903202202091801030b130f0807030509060a021524010509040b0907052104030e040c091a0403020109080724030209150403050c01030e100f06 72
    0x16036a00c0011798a451a900560708000c4078010b904a061600110300d6511189800004596102d6140642d840031360010780f58828061880403001840c1c1210140480c2010381c0c2c0a070704510144407030b0010420310032811410740e40728040540b060800102a5182d4180e06aa00d802426840c00030841d101014011021246400360040407680c46a119841c0207503540403000d04010400640c03008a080c00742c440a009a11221500001d040c44003140c3c011a003540100c10001e40c8a40c84a001030703425201d240315517016411690303036599169490342464005078030360211860185082402c00000c02e074011000e0101c40e404071070105052503009022540e2400d260008940c0014615074050551051402042128801e032244604140d0f6200c11680314041c41c85044007071000039904045543e06031080000d48400c2d428014288201d510104488000709080a180040c002605100380841044494041c100034602440300300181310fa4542c031028034401c08a607440e141d468403e1041c115402c1b000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 585906366 1250 585905116 585905207
    0x804210812040201030b0d080405040b01050423090c130302060d0e150106030e030301050a05190801060b090406080f07050108090a1415091b270a0c080702010606 71
    0x740c07075090003060300310340c4842690128080f03031801c3c01d14112424035040a42910303400220040c1003d2074082400701034a42d24500703c0c10408104404980c20308458250764001d59401c0e044040711403071201340405000d0107007900001410501000c60f084190040c4a010340b64151f0703240b6210dd400810300c201410342d04d58680d40c117020340c20b100500d050341400c0007812142030f90360601042800b03600d0a900d9100038020107030080d00440e02444503060104a042e0054404407a05140d26560034119003100d4564000001034480015050340c285418041e21014000080107404412203240c15a0b0742c0d4a240d11034103043c001c40e94005541a401807104007003040d00008846104c150f08098a51034580720511034084003156804034220b281c0c00501d496411a41c003120741c607040307001401c0240b8515258800c0c02aa200c41115414549038034442ca4015514103074003040c10013606002410040c8010161000c6a14046040104a81c0301384114110380042ca1140c4001c050101880444181880885c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 585907616 1250 585906366 585906383
    0xf0212160825030b121018051002070206270a050a06020613050c040f02070c0b120106030e010f09030c03080a020c0c0f0406080106031a0618150103060e0106031401080307080421 78
    0x280705c0001081d0100d4a0110304070410044c002d4014007010020381d8100030b842940301d40b1180130300380030340d500a050300760004241c2401c1414040050014500d500400051841da40c0381c8441182403804285025080840e4219052402d2400082d07841c01d008000032441451025144103000c1e040c05001041d40001d001844a04014610078001c0d501494040700e100150350400a2021080030035103102d0f5040e00c0b8116440c0c3d2800700100c0241c010058940043d541c0e5206500d8250341c0c0e48a00d0b12441c7c0b1948039a0010000e030704014001c2c0e0002003c01d00c40c030b801000034040c0c2c6800801d050b401c20008503002a6070344c1d4a000841e00a080740c1d085044030303600c0c010380030060040310091400c2e08440c040100005a4400c0184804908445034040144c500b8101183c81048056403600c1440e206242c00070b0141d96840b420401440203a0100c030119640d5411840104113030f0b001c040c090403d1900071031510002c0c4d90b500101c1d1095206141009030b0080c8405440c00c0743d1300c580c0c5c0c12030343c11550301c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 585908866 1250 585907616 585907639
    0x24020a0201060512072411060a090209070e2b0501020a05040503100603080f160c15091e03080307090b0f1b0a1a0a0f0212160825030b 59
    0x68001e1402c2d02901c2d1164407030480c0742c01185000103000090b03503003406031000703e4842080c01c400c0040625070000c060004400002103005800c01030300c1d200300580240032450301410b0062101110010303008800b0407d1104102c03140703031158460341001c280c4060015001400039441d1891148200e030f0020321650001421240d0f0940c010701800603503200305e040d50030106801d0b030010211455488003d00144c42480041100b928100c00b0b05500c515564000c0007020300d40d40c8500c80b43ea0039070400300c005d80e02c031448400701c03135885400c45000e444a080c0c401c0307330000005201e8004141e9444000c0c46a50300100003010301c0c1c4511010340c000d00f40c2c0700c280381c0c8803032009440e8070054100c204800750000e40c44038500d2800f00300042004580d90008915000c0d07107001c2e2441c88590100400c203105640c0c6840c005460b41e07040c0e1000b0901c1d10055140e00d04e1038180110b810b40b030100b55444850821243d1400d01881c0000e6030074291004d5805a8400994501031344103401070518901100d5101d00494103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 585910116 1250 585908866 585908887
    0x1504110d0b01020c0d0c060309111017100311040c03020c07151d01080a1d0d0e0a08010209100f02011e0c12152c09030c01050c030606072402 62
    0x10500380400d800380c403525184d600a01004c080f030074202411801d418a1304014141c000e40c0300095039030044d14a032410080142c0403030024580f208020000417040480da0381322581015810b034008992070310086c1c01a2841d00d0f00310201c032150f600e2a00c00c3c0e540d00c00340662507000390304880356000c418050b65900b40d9100c090303460400ba030200300390104d055046801d6000b00c01c84845407c0315416103c010803038980300340003c020000d03044d600f03024040c2d211402c03844420410108400000301e55074007800b5003c02c014084600160740c010403290b80140107403003180d903d81002c441e45445600d4007240c801d044101c1203016103584041502c440011140d10100c0c01883d8000103550f046981381c0c698078214000c0c025040f6041003101d981183c0c00d410b801d104400c0b405d500d8141150000754105a24940ea0300c2c803040d400000e403140e040300d501c00130b15144408801e009aa5002c04c04200042c00c61070624046042441001402425460034542c00080c6550f220400d10700350144220171501c03620481d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 585911366 1250 585910116 585910121
    0x604030801090c02070e3904030515040f1b0b030103110f03160504020706021b030406020607050301050f1c050a030f02070b070c032d0f1709091504110d 67
    0x41c10482d0341841019070980c3d0000030840b045600010b20880941d64103810178032030f4181e04624a0708000c211900041c02c298a1801c42c010144041c10369550f1491807401c286402510150b00c41a10110780800010404440c0754040d1180c00c1525040300c10003106901c1c0200c1482d800181600101000100500190782d45c3c11840300c80130f6a00006082c8e40b5410036580b03802c81c000c19030120f585a0f40602c81401c1c5600500300341c030700c1560094241503850010003040901ca87c0c00840a5001003010000b1030303810800300740c120303020b030410514550401c8041260b07885050b4100e0300461508041001d100900d82044200d180c0040594003060b0441c80d00911003003000441c9801481035003800301d81e0f419180111070400340e000c1c030410051403540d44c418400301f83e000d0041401020740d030042c3d540407081c100d00c200c2051050030705214080c140d03d841814030101300008408420f007404070710003603147c2000e001e800882c110f4110802d00c2080c00000c015004802c2641c040c03402c0480d5204840b40c0c141c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 585912616 1250 585911366 585911369
    0x51b010b040e0c030c0f0a030b16091a030406111909030c061b0b070e0909030403061812302f03240901030803180708070e0c040302030604030801 64
    0x115014446080441c03421a524003000040700e61541042c45c03406404d150014030624207241c090480d084059480e140c000c400d81d002c8640506a4014901c14080c071588410b500d1f01514612680002c040e106000e000c03164000148020800c0780d9a1003c0c2004041c01d9003640e40ca5007584a21421184540d04014540e040d140300c1240c207040921008110240104a150041190640e98541c180034584407101c0026015011105000b54409040c1440d121041800e110300c0c2058000c540d118507614110048400001c05441104c0098101400240f5000f0303070b0f0015002103190580c40348030420070051035403904032000d5440c00040e580c0601210000e8004100034600f2000500d5064104018041001d511b0386458462160030400983d075030080c41e0441c20f10002c1c100d00d964485d40c2d50000f15440d0306007038200303481c001ca0100030000c0c524080074105547d42100d2010308040d91801c107249076a8542c5016080b14114800009072500e40242e0590300199002403c95609040a040141c04072200313 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 585913866 1250 585912616 585912619
    0x80d0f0b0406170a0b0a110c0607020708010c0f0804062a09051504030f05011b050304110a0302090127060f0317070b0a0c030f09110a0812041203051b010b 68
    0x4000e000200b10508036081c0240e0060840a07092104c0240d580000b0382500034402c4c00c103141c3d142c2070003281d805144080c00c03420200000500580c107105030301a18100190b40314860701d0781055081401603038409900420040c5030b007072180094130356180075405400825000008100100590340310080030b280f00c46068550390310750391903e0307440368103000e6150200d551400800d04100002c000080b420307505441e40300d020300000540290f40802c0f0b4010001c8404003100010408400c0c0801d10001e9040000e811030115015030700c1e51b01e59400308018490502c04d40c000741400c5903186041065100d02440c00c80c1103d0000c100e07e54913052091030301c0c0200d010a0b640c4020700e040e81251101c0450495000302c0e000300340d90301280d6802000c1d0010b803115084c210200750719040301140c2201c00d800380c01042c501c59280108880b40560a10035841065880325402c1c5e404603484441d002c02d240203d40940303070920a02d19101905040035902d521801c1c480076074032403910825051112065100c6921b003d030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 585915116 1250 585913866 585913871
    0xc0a020d03050a03150509011e08060708010510020a03080c0d0908120108010c09081c0e0405040c050906040b1309030504030b0703140a020c0613020406080d0302073c080d0f0b04 78
    0x174450b050a12501802225004041c4400501200c0030300075060300d120044220310821192100711041c10010161540b00c00300c1d0301040180164607002001d5002c003034040c40103101d0b03070825403401050709402030308003c4045400544032030842065003001d400079400c144034683d14468951000d1303a23030030309215a92255103071200c0d03205c403e803150203460100c4135104000d02094410310042d040700d0135002e05175400d021085886840c1d5071a9070060910450141003050710b1a803800050045141d00205903138407540c508009000745503a0100c0500200c0c407000000100c400280c83d0a451034800d640010b010300c0025400c2100103681900010502132b003d07200c001454452240300c80c01d0f400350010641c440c1c0c2000000500d007261642c5911005030004201181c4140d039071a0b003c0c00e001d00319610307000082d00082c1d24000c0c00a4041041200c80858245400d0245440c0324446050000e10680a0a40107000c5100a01ca80001596000606181c00300405400147c1000080000c01d40460007a030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 585916366 1250 585915116 585915131
    0xe0405070e0405060a050705040f140f09103507080c030d0f050a02072402190b1303030209031504120804030f05131706061306060e060c0a020d03050a03 67
    0x2203000c241c5a00680d80b090080c07503a600c0303284002d809420010104010440113010008000c80c55150300300c000c1c0f89803038555030307800001424001e207040d00341d11140c025201302d018091401c003007910b2041210744001303110b03129100004040b00c4900c45440302c3c0d04010100009150b08000104e01e40045859400c01c55008544040a041e151500a0030306c4003c900c0005036000114061001041100f10303030300c181c0320481e8945c00041a05a5410081d0111456100d6000140360b01003104010109880040800d990560340d945203807030b04020008544484d0902920b400c160103601071f0b6580000080079a003180d0f001418004c00001e04a07400d403242280b40c3c3e4102001406503188501854050340c808841101041087d5015030100801d4026050740840008000d980d21707003490b4128643c0f201409213428000100801d07820b01001302c0c1030a07072401c401000460b41003108170380c80c1d401c103403a4207449104604030380342804005000a5048103200182404241c0e0040003480100c1c40d5407410481403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 585917616 1250 585916366 585916379
    0xe0d060207080f0913060b1215030d110c010519031503080705150601030c0c020f180a06060e1207091e09050c0415050904081b070b3a0e010f02040e040507 68
    0x482d01c070b02c507008081307d04001c411024107818003119401542c035400f49090001a0020a18042154020b074000076034000f00100c4a500c284440c090443d800d10300345003021000349001c0b03a035140c0d0300a0300f005d0550341c0503980c03a200c00880c001c0d0000c5800941554650405007001e94451103c480c10100c207406640002e079041d800384c80748103046e0390980d8409040e8007481d0f0a1194855401f00119444100e8924101c04402b000854501c80c00d000800071410398640903020340a15600c00d441da11a22040c81001c14089000900c0ca00b02c07848400302040701000c0c0c0d2200c00000410700707060071541d401d1840c032a080c44400603000e00804000d8401700000321107050b00c82510704480c003910740d0000e0583d0100f0040b17040348000d803000d00069072814558101141c0440d00e000200d0b88024403120003c0f60035401c0d220611103114800a5100405944d8070004404114520b02d0480b10810300d540c610341081050000d600034440800840c03411940c1b1a15840c140900d0310007100c045400d40720b040c0300030a01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 585918866 1250 585917616 585917621
    0x537020d0f0329010e1002100c08041a13080703030e0727021e0a02210f1c1d011a060901020d142b0510060e0d060207080f0913 56
    0x1031207042c1c00d11603000c000c1c25003100240c000300d00d43c9904010007100c0d83c00c220741e1880c2800480e50035a800801d0b602d03000c0e08402090710280503440040c40340c50000c010204007d403110022100011590202542d9001c03403082242403000c4001e0080a4082072030410107405900451102105104442c04503554a241d544421081680103485801c0601d01c888d0001940c0c000e450f4141110707660f8280c204211080c01003a42100c10505c3c0107078001400c402200840d2100001c00d441880700d12850109040c01020040c82080c002c00421006291003440004265101031030922555215841080c48001c00c903010b01101d000c02044160101e015120524001080350103100042c1c0180c80d00042da14000d68002441100c42d400004040001221444500c500704296180c1880410340c07032103181070004120350004000800c8213000080900221b40c004d0f60000e4012802c581e2031910520b030b4905140079000340080207010b00c0c4045091228073304070f1806001550b81c29108001e500c024120980103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 585920116 1250 585918866 585918881
    0xa140f07080f220606330c08070b07120903120f0605030c060f13032010080103020f0102030403170a1106010f030609060e0a050609011b0537020d0f03 66
    0x40c0509281c0d4110381958010072280d5815005104c0001d01c26518a40300c099640c22400da9440f1010203041414600e0072940080b2068045140031080d608280d41d9007070340c0c0e01c00c800001e40b0311071000f4006040184103075a4840c01580404040c0042411844c002d402c45015501e21070005003007a581131460041d40c4500003c4440080080005907000418460381d68401413050700c15038010400d0701100c104451350031000303603c07629090601080381b182d90340e84a641451a540b142c402c030300510501550007050700381941c0d01203410f540001e07070240c0180d20710b10490340010189903480c1200940401240d0151082e00d065860f034106944075034104a40b40c841c03d01a0144142e5a20000e2010540c5a4852840e25206000020301242c80c0c13000e8500e4004140f8046425038814410851681c03170a008244c3c400d0301e11460b039080d03100c0000f8090007034098180700780d803280c40e800b00b0100240500e07070308a180050040280418021000c4009454210309080c20000c110318168409050340301c2e110307051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 585921366 1250 585920116 585920131
    0xa02010503041b03140304061805090f0a0b1309021206091b040b060313030e03010509340f0305160b070204020912011104080610031a0a140f07080f 65
    0x2480c66489580e0841100e01c0b0003d608200003241501000180b203d5080d507841c41001c2c0000c5449a2500600030070618864a03101c5801560741c03004c100c01d0715000d5070550844030f845c03100461079a424892a0041440005141d80080d411011503500c0d22254420185d0b54000e840e804019440500002d40e2000e054400c0c0110703602ca000f01c02d040d14030071640000d495000400200d40c9084100004107070750001d131110303d8440c1c1c444810344205a04000080c141c1036064000780058a0126100d58546411404c1011200303a10703840c200d11003001c0051101040da4489101d200303180c5404c6020302c94141030000700c0302c5115a5014405d0b411501303103031004075075035070031001c0ca0050540c2c03e01000e90070074082c40b90004045182c001c8080c00a0180140780e0590511094966181c00c21541c58404081c2086000008940040c000703d01e42c920700144007010055aa4529200d1004460007081062960207007902500148003000c5928482980111440d0703036046400d89440b240b000c00c0c11030a8458a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 585922616 1250 585921366 585921377
    0x90e06010b0304030e100512010303110f0a03020d05210109020901110705030705101709010c0f0302072607060e0309090a14041704090203010b040e0106170c0d1b0807030e0a0201 78
    0x1030701c5446d29034204030042030b4614000341802010006000d0303101082e001200800d84447c40c0201c1501c04200c101207540201c0000c00a8804a80f0301075214250561004200b04000072140044446115820b54202c4c0340020084c0642c0d6030f500c880020f411003001a03000607800703074601c1e5a13100c00141e14016500002c019002952900c010030011184d00600c0200f07100d46a164078801400404c00180b291541c10000b04140022080040c0b42440301082a01414418021100807983c0d006400081032880e280301d421a4050020410850085660082c81c8a0400001040328180031018102206041e5071300b07900354a5045691056030b003450242c84c01355418000090208480407421100100b00c03e41080c501915095030000340d0f803098004080800b03000400300600e40c40c60449500602c1c45190564180503449407114801d400034001006030f1401003881344183d4402da116413413414500001100006004001400e1003104a990002003072030145100300591000c03c4142007540e059544c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 585923866 1250 585922616 585922637
    0x5090a142d061e0309070314030a050405041a030d020d03060e22140a050f1b0114071118040b060609030c120f03070308040b070c080d0207020415090e06010b030403 72
    0x140595500300110f80000c408285201084030700c0c26400031802240c00340c1c0035107002415401c2152051002480e501c03101c1c1e000f0803506000543c0f180c190381c00d1302d50450700480c1d20060801140043c2003000c10041d414002d0f009084002900040c0591200a40361403e122140c0d6a4400c408502c00032285000b50000c00380540c3c0311080301035030140009100d00d03040a504205c1088183c036045c1a00012100c0d41c1c020b03030101a5000080100c01d030285080e455101050710960002002c0a664451540850348040740080c108010402c0ca043c164501803c01c0d8502c0c400c5040009560300d0950f0240d50318041c030700100320181032000403156980070250003800011100402d0003140050051210b070203004074600502d015100340010301446020f941c4242050400f420b0808001e1000741128041c03007150907003040010141c009448260410000058a07a182e50010401914840300c4904c50301c40b11034408581d170f021503844549030504100494001e81e88802d0552910b10060350f000d030220b004e4905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 585925116 1250 585923866 585923869
    0x901030f0f0203070507110d020f120109060507030b1207050a12050f0601150908150423160801060518040b090319030507030b09131205090a142d 64
    0x800c2000030280c050014448441c500440c0407a00161080d0000500005062041c400c2103600420481b504071001c5110350751307035800241c20300000d40c0340340d004520004c119881700c9001e6121090031904841c05201d03514101c24007c00602034402e1252003a12000402607008000080601c103070741c030280442d40740c581072207080311803482c0310041220207110384031411035403010510855000745480030055a045100c000060701903100e40d0000d613000da000c0d03840544004208c07100304d60425003000302008140b04001c0320251102448032250458410044a900d0303501e100c17a005011514120004c002d0b4545401c04c202544100383c5101071212080070224011076501c2e0305594204044c5c0c406c980c0303030524206a80844242180000010a55940801c8401a01802011091201103070103400310301d8006e00f10000c0f0030030002c000c1c0820386c10741000c1001c01c0c080c00440d020810001d1181116569030010050784d0201941c080d03009008008038003616050610a41c4401c403014103c1c0300c0c51074010303030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 585926366 1250 585925116 585925121
    0x1b0e07090e0613060b03011409190903050c0604030905040c020114160c021804060f18060510180e010605040213180609110c06091f051005040e0d08070504030206090103 74
    0x107010b0ba90044182e00070107030151091196400400302d6122003070302d80d858105112502400e80194074050940d50040090a8141c202459481c3d80703160400940d41002e0704040380c0c00c0c0075207114210300f03102d00ea09110515801c00c0d208401c0707807004c0b034050200c45c2e110b0300f00300d0030b89000901b8a0a420fa07400041041c004068007125240c801a00c2d10440d0854690000303003080c4e0b00d03c44101c202004030307002d010a00c0f11038042d1040400400109020f50381c010340251240a0103010007400b85030b40c80d400702c0e07200791140241e0f034002c0004d018100866590341880000501489a042c0c4540d840d080b800105810a4003e480200c0346040f401c032045890440f0042840d4040303400078003420381d6980040b0b604011407080c1c407410b0240581d51510340c80384042c0c05241c62030280c032201d0198028050750380c1300c00c940c810044903401c4042010440c1c0c0c407001c10000601400740c102641c0681410100c507502800025480f140710525602d8400d591115442980c02d84194040a50042800c01c0b02d194594000d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 585927616 1250 585926366 585926371
    0x507050423060c030f04031406220f02060406030b1206070e12010b0301021305030d090f0902090604090c080f0709030506040b090c10051c0612020127031b0e07090e 72
    0x141c100c0d403800003c804042c1c25684881d540a903d42400304007802441401514a0340784d07510f4200414030340c240b4003182d41d28104101c1040e022000e40700030080801490100c0d510002e03a014104540302c0d41c60b04006800342c4441c52000e8002c0881c20305034045c00070001b034110b000d101182c40303402d00e00e8140c3c010300c803500b142c0001010166499000c07a1000391001d1000340340c04000001040c42107401c0c50209420060040500c034208148284180000411800340d44211900c00900594800c400c1003c10040d00940e44090003481c60700b41b03400d03146030304203441510a0155072416052607541c114142c8a000740c40c00040c00a81c0140b00140005019407107035500080301608132030034446180001418103252600b11000244082000c401d4402c6000030941d42c0c8a5220081c01140d00f8581000d0035204004000707030401105205500b009038511001d070350055518034003001140c1e26814592112031041c581e81280c400d010100181c032525031881070340100e51b656202e16100780350096809110201 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 585928866 1250 585927616 585927619
    0x304030807020a0b09031c1407030c0e181e04050d0309060b19090b0f06070605060d02090a090302151e0903090a030605060301110a05310e04060507050423 68
    0xd000385080450340600110741718503459801540d4965034010184041c100c0e8817000035000341840e0312800007a0032a420954042c0c0d041c5000540940d50381c1040703503c3c0084901d80394101c80869000c98940201c50120703403041010004080031240d224043c030440007021100641203810400540d40c1042c441d8019204590003100042200b080c8030f000220003110081004400b01d0031034004001d0b0130a507000d03105d4a880101c800300304603d0b1101c0400c07600d10507010018501540c581c0042ca66070798641d0001b03080341d0090101c00c3c187c946041c19000800002c00190050720a040d00498040e0381d034100b0070701c1181f5030211303104003440c5030b8080303601002c2c06498401e460105110101a0b07481e0b202a440046000b01c601090304e06100f41070608540e00c4003640c2c02c058004100582c91190000c7c221000b40081554105803000f641221107800d08044010b2421b040b5890342c000b400352686002c03680a580503507010401030701c0c0e00c4400e565910580c0320b035149000d00c0300381000e840c1c2e8140402c01a0040c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 585930116 1250 585928866 585928873
    0x3070c0920030f06100201050907050607080f040305150c04030c05120705060310050103150b031602010b03070909062904090609020405040c08070e010617090f1605010e040203010308030403080702 86
    0x890403510000b40c00c1214865007100b100410000b80c1c1c5400800c1074898603280c0020002800d08181044c0c4403d03803405205d020b0400050703001d04002c0054201c40603401018200c5465076124900316854040111508130424200b00c007040305000c10100b201c048030350000300c18800d0f0b4501001c0c03007080c000b04003013003555020300440010203840c0d00f0000c51144200c01460207900b0b003010005000c071111854810132420404000303100340384042045039004051400d2284149940031012400350000350b0300742390103004443c80002c40c41c43c5500035080c1d1038424031043c404108dc0c0515900048103000c003144080d100c043c00b51805081c0340e44900000b074014000030a0f2200c0d41e4022605035401a2021580341d03c0101081208407414041580501250304082c42c2d5940340040003049035055204448013000d00340045502d00744100804905241c1e0030050b24020003008103480b10403a5584a5076011501086c000c184918151080b207060b41d238462a41da0035038560313450482d080131009000703209511 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 585931366 1250 585930116 585930161
    0x90b2a0f060103030806031b1302071e120f0509030d080702010f140103060b150405040c09031211060711060c03041e0c080114090a030804080d020417010e03070c09 72
    0x35061100c0307030282d0300985031545c89041540c10715207080b2060b0790b01c060490407940918000e03941c888814000c41c11210340581c8460550401103400303990900212618040280c0501c1002422404001404819160070291030f00e01b40c0d00f40c905120b9101c805602d40c2004230041c0c49039014004494120340c040c8000505442103410302d004681c6400c40342d25040c40c02034010000c111460240100e41181035a81800804ca0450301d03209500a0b4081d103441982c0701e8100465480c49400c00c140219001802200580c0d40b85001511111588401c0c510741d00907000043c8009005003140741c8102c0c640c0d401003040350350702c0d1002c40b01d9820140c4121185e001081da1480040306c2e80c1c0300041000d0107044280c512500c0d001285085505d10219600803216100801c102c0400104000300030981604000b040c5580c3c03468090090310804900c46c88052010502085003000c102d11906907105400003088000100101d06580c2d004903e030007070060b80820414801d80000380c024096800341c90360340103d00c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 585932616 1250 585931366 585931393
    0xb030d11160807090609110706020334170106021b060f130e070c08030609153a0804061115010312030518070b0a0c020901080607090b2a 60
    0x860390b00c152059800103400b489142e0407417107642d00038078035800e040018140b100d00c6020b41d8050301c100501500da005c400100204044080390f04c0c0c1c840f10315849500100d58040500c0204080401c190000c1d81d80c1c04100c804601d6400340030705a84180d001007448142c2c0c11408080090480151034125030188101200140c94902402c11810754000c14403107141400714050341e05000034100c804000c00c0d2600b0601148030780c401c480c2c000c0016550008540d80301c1e00400c20701c403170b07500056410108000b80d0341c242c01703034000b404074554401103030b0350819140291600d05403089000003d020305a0030002005464000d010b4120715822440c09e0340d0956014844001c0c18181c2640240c4076040070540075404103501d44541035200000a58506420b0542c0700341c15a43d0443e0b0044e1f403801200010340b59461802248a012002e0780101041070b55a103c0e280240c80d404295600004074904030350124402e6841019988180440c04a04034102160941103580140364a0600b410b40a03014460111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 585933866 1250 585932616 585932653
    0x15030103030503012d170a0c03050c21100902030703062421060b060f0c0c1009031e240902030d03020f04050d1403040303020a12030b030d11 62
    0x35406511010744035898140d80c1083da1686108070003503030381c80c032080c24455142d01070321000356507141c00741612000140c010545080034003880580840c00d1a0700c000108480003440f051000402c0d0b076408100011090911603036416012a4129034001d80803412443c0d00b6984000700d1203000504855441d0756944418044801035864610710400c080150102209013562050003040010342c0303003425200301d94088a0040041c540240110740760054a020755440d2429100d4041200481566402401c01216078075004402020f001300300005258259600811109003125040644a40001460070358003000e50400038048460401501d00d8500014162150340411405840c0006012400d03004040c50060454400d008041c01040b0003820340c4039041c06c0d0b82c11210199900306018215180580381100c0e16105d8101a00c0041000400d0650000e00480b01d1406070086004040c1c1c4000218192840c0b500310741d0301540507407030001400740b10391043d284060412060b07d00d00461407215424 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 585935116 1250 585933866 585933869
    0xc0e0709090c0f020318030102040b0a080a060b090a0b030702100f05150a1401080a0905150717010608040b0601020703050f0f0f1603080a020c0a0b030a050a05040201120902150301 79
    0x111010340500c00c0d806a4860b4580d044024181194401e02c2c5000003503491186261071600c01070441240d280b10b07102501940e01a0540002498903603400850040030503404035881c0790001d0078014002203500c0b411040b142074100c043c05800015041c49280d48455001a0050301140b0840060449400541c8290f580c4082c4041010520341003407a600c40a500c200400c40c0c3c80f4484003041000450b10700204501e000c6c0c02800d204510ba696101c6800007400300d0b0402401c24001c140868040d5481010f05500c00c08550b2200f14482d0740100001815507800d004020201d003a41010402084490801c1390740018148103c03a0555141c0c0e0b10300e81050645640120740307501c09040440300d500140805000c50341f285005000100e400001c02c403002d401ca1001400c0080c1c000381c5019000e20038040b0745124030000e02101e580d107940f4151450541d200322158046546040040351540740d007400b4007402282c059403012041d000c01c810380c6004100541d0100d0380b00300d21107101000c0002e07003c040d50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 585936366 1250 585935116 585935131
    0x6151e041202041d2a04020a0809060a0c021504020f030f01020415030524030a060212011406030709060e0a03050a05030c0606240f0c2a0420070c0e 65
    0x5401076071500c148010f031005500b000c0300005041d92a07608100300050341200034a039042900c81c0d64042ca007080305805180d5015150003038000142c0d090703950b4203c034669001e214a0011142c05603070341d08282084030322205849006800c41a1413407000161138a0142c5c000380010200118070400d0070010345001e6802d118003110b03035000300d002c1001d00980e0484200a040c4ca05080c401403400210a000c01844c44c59001ca003c1c0407104100761a4074100034020320320b64014800c541d6a000b040101103150000d2007000b91800401c0302025031410f0a0003902d01480031901d880f6a0503042030070030f864100703040315426000801584008085a02080700b50001402a0003031981c41c80395001003810180d009150500920381003030114030421442c0860864242410305c20786d00d40102e010301a006116040c0d14003000d205e14084091b102c40004611040441f2604001d2001c000b040c090105880c0710141e881d5044401082c0903e003a100c0170002e00e011031041d00c0c248400744d00ca0245100c030034405d84045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 585937616 1250 585936366 585936389
    0x70c0311012a12030e031c1b170c040e060f04021611090a060803030403050c010b100519140703030e0a02060418060902090f12070f060f02060f06151e04 67
    0x102c01d10070690280c5801800300e24042c0216500c401c4110b58074442c10303c070140d4a034546000038500010650000c03001c0350f403001c84c4904880d402c10005020f0800d44081c00c8030840f620001c5045d094101e01181c0c100d445510402c0216500e2808128240b16030006194019808015000780e6032240c03542c0040180c0f00309680300800d0410002d100301c5060061004000780d14101050001d860008103486d8400e07814501141d5075102c0300240782c007520352100601e404c01101c00300b100b03074540c200020740f03174251004510790000e540400045901c005d02498040e1800ba0030071510001ca440794200804c0ca281d220211003941e5400e9000ca01d10303034406d44c0038990500000c604408c5010b1305002d440b0041403618001d6040021440008001010825216101c0c01c1c0040c182072010030300b8031030380000380400120541c1c06961180c02414a4180300c0c5000012b01420001906144000c0d00d264000c410207001040340e4540c2101c500c0745a4851005905440c50048407540c0c50001c80004001500694550 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 585938866 1250 585937616 585937697
    0x90f050f0f060603030c19030903050a030e2d010509010c1e0507080d0f030504050c03010603060f0e07030c0603020c0f0609030403060b040c0e1012090605010609060203070c031101 79
    0x726400c010303010700034600c41d03003003007156200d1600c000551084502070540352100600c0145010b6411010b980d10040040c010980d00e0030606420070807141a10100380e4408440c8240340004000c1601040305804401000b2914440c0b40d5103d4005403420b0300041c1480700c185202034842c040c0d070041811052505207102d00425041000030701102008054120080000c4001c1e45406850b8000006e403800130555598001800d1120820001e07800c0d02000d80200a029200d00b05600034002c45019107048a00f000c0002c440442c00058200883c0d4101805141240c104081100654031103110711001c0d00c16601d40490101c01801a030b4020b12214004540c1e4900d0362902c00103132441c00d2401c92003107151107151014150010120110140102e801440902c0405400e90380c0891040800c85218504941d14082095592285041e692591a22094250344420403a920300c40c0ba0700090680f2056403041000580400d0000314400701410029444546c604000c80d005950201804140801c1000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 585940116 1250 585938866 585938893
    0x20a03050c0102071d130c0905090a110303040b040b0d021908011a0c06072a060204030606050906060f09010c15020d0b03010e03040e0a0b04050c190804021003090f050f 74
    0x2a80b002800c001c075901c106034040781704030a4070400040160001d005604c0c144005c0150185400010304201c507410070013403c00c480900d9550204541c1110428010015400c03a0b190000c01c1c1c5003150100302c4420b142ca428540b60950300c2c6c00c01e10020707000f16002d21402c3c1040c541903030004080300e880d84c0d0300d003803940c074101f0041d084580c20b010014071f01c001002407151018010448691029840c2000c4244a440034910222a038000c04000f0b2807040c01c81446c1c01f0002960018005c40c0d00404080c080c26071620200a11503400307a4405900800030030030104800d0a00d00900000481414403020926650b241e0a848506100f00c8004443e80040c00744421900303071045502e1700b40d080e0300070414600314143c40c0c0c0e5240703d1409060301c004100c1000032031022181d00306014624000d007040c001814180c48004198004d144521400d6414041e0001e405103d03185e25031213960010101450f0000108041e03004001200b02522007103154560140822010025982c00300f103103000500c40d4206485 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 585941366 1250 585940116 585940123
    0x1803050a05031c02070317190501330e0910090603080d0f0b030c01031d0d022a0d08030901090b07050903010b0a15030b130c03270f11010c020a03050c0102 68
    0x30b4070fa061041c07041c03100f0008241e200403000b00c842011034158865071501014002c0f54425005240c1e01c00341040000706001c1071646040090b2003a81103911049200070303800119042e8002516400540d0342e144080e042d18060b00310a07080f00740c59500390803c0da01c6002c10000d8440c984c1081e034154ac030000e00204c10545034400e0401d0807505007003c20402c3d01c1440029165803926210504054640c0c1304403011184103165003408588010407104031814003d00a501d41561403042d10064a04842000840000b4250314105c0803008100d021014519a0303281d005420242c030000c0690f50302c0074480cac00103101840890007102d903611030300d8952072a40b08040c20340781e40340c48540c090184440208880c1d0510102c3e0010040e19080108502c2005404503008401c0410902030480c00c0c40140405a60564010701d08180414006030082c0c1c443c940e05040303000c20100040c80b10f500c0c200100045003803503843c0b11201e01c0524124440080f2a00050601c40407900251804e8005000209003580c042 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 585942616 1250 585941366 585941407
    0x11150106080c190503100923250f0504080a0c030b130203060c0c0c030d122702010e0609040e15070e0109060e030307140609010b0415061803050a0503 66
    0xb400301d0b41c80d008400401401c0080c444140c2c6080c00b40c0800452082912000600050103d11104010703500622540c0078540b0701e0310f142e0011845800b000b140d80303002801060600e14110030006c404000e0a00760845901584500711010040c042c071000c91004010302440710450302451450720110b0031400c0010392454090200500c00741d0f945153340040c0c81c00f052917584080d0501c00d960b1104000b161850070706044015850740360140019880c2813641144000c884402c12400c01c0207070440042c290b1009118510540b00017030501071501d40190b1050140c02c450200280089050912003000700e001d603008114040c540340c1094040100005400d405030354050420b180c110681220480060110040390141c0c20401521194a024940381002140d0702d550b03100c1c443c44850398041c444143c50300005d903100d090b95401c10668910341e160602071035004c0300c110200000820301d000000e135196401541402e14400640034004041002403283c0c800d428020740181d40c0d10040070108401040c0d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 585943866 1250 585942616 585942631
    0x4140a0b0a0e01050d1104060f0f0306030206032a030a0e0c090c03060607030905090c030702011508060a1503050f031e1827070f090501050f09101115010608 69
    0x9000403030649602c1070031104040c1003828001d944813110b145c11409040342c4070030b003008000300050004040354004101c03500d1405a42c0c1d4a10120030500d01101076501d50311001e5881001400031844920315000c00c400c10280c00c50a641d50090886842c0c0059041281c0c0c4008642d0350b00c0b07034030000c644144070180c0342500850b824541c51400780c010f91450f0101402c4580500380104421040600a40704c17500038040040c55040340c1d2410114050340c80e8411607080c001035003442c3c4034003500e00035001c59900f0340d4101000b4101c02e6580c1c0320001d00828103a1342d01c5540c11003ea034000003085050152030019000c04000c1c6946654110040f15400c0804204c500500000c10001044110740e080082000c0b40807260344804050056032a440503e5503216000080011014054003d40041c222007000d0165180c1400c005c0d900e2006655030b002c2d94225050400042040c02018506032054084840b028103181007041e07030719440f480c071780010181c0c82d03501507256000500009070088140c41c1c0c01901e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 585945116 1250 585943866 585943889
    0x6140613020306060d0b0d05011109040b010f0c030305131401140906090712230106080c030a050a11011403070306230f040c030f0908030103230615130204140a 70
    0x20000b022130780d50320501c1e074451300b106d0350390207040d0655480c04400c000e810780100003403001c60780e404140301c1740364040509144928544521104154040e03208415020301c42d4950440c19002500c094000d0310006241d0020400c0e00f100c4940081e070020074440c02268040300000b1002000c820185017071102034113242040d03000100300440c01d8000031b4804241d41103009030500b040414a031034291244007a11640402461524040060350150300450444180c881251980c00d0403e05068030741d80c00711405000e641190b80c03032070080340040300b07440b08200062410001844c07081f220100c090700180c90210010382c84403001c12524101405040030b02c60340c50070b44c504922441001800311580d40005a0040c0c1d01c810500300100e009601280c0081c10402051100c0e83d030a180c010b025900074042201d0901402a0740b0002c205414004039001d580003004180689540d11030f05506400c0e01510b03640b10760307030304180003006d122800584014210303160030043c800c0103141000b40c0c043c102c3c0c012850892 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 585946366 1250 585945116 585945121
    0x9030b15030709020f121e04061a0402030901090b01091e020c0f0d050c210406083714090c01080405010f090f051903050a050a05090904081e04030f020907020307061406130203 77
    0x41f42401d45500540d00c034100203144411408260304264041152503409440842084000c0700190000741c5c03498442c02c07450b2200d030380b11401c480c11904841d038840ca40f150350668075441406075a008100c0c1c03d0b680f408a40036a03c0c1940c1d4685040803c201da100040e01c0821420031003941007100c0300d41e5000c0c1d922300710406806081413402500441c8204820810004041a5142083c180b01c46088460721044c1f2020f00b504400d990344c0f402d2811245000703d14011b00c410941c2402079071640180208000b510841403a0001191084400303003080d181e0f9580c136011000034103142d12400d016648580240c202e40030480c01c1ca030307092059898094a0007840ca0f40110b000a0b480001c0701c180c2c030401d00300244c070756100c1902181c0c20f0099003000d64101140d60f0500c000d100e991405403114068492981c442c481c180c0745035029501941c0300043c101116010303000010b28148003641d900007c10310449081807100c0d151502601c007408200c00005000e4411b0042c0c5060805805410700d500030000e40c80c0d0b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 585947616 1250 585946366 585946411
    0x12170402040902180106031d032503021e160618290c030309070b040303020606040f0207062a050703081519150e0109030b15030709020f12 61
    0x40400510091103699604103503802c642d13441107404800c612442e0b02074a25038586602800406101101c62034035500b0a600d104444400021541d80e290400e10b0600c952200c6040000103003401e01c411015400b402d000d150800302040522a041c449035001000c002d061003040c141c10001035006482007003180501200c80349664142c800444c1d03200d020020b0050218500d40c00a420020356080040000241c020b8031010000050f50141c00d4000a454200da50345000a8083c4220722004015030000745c0020317090300e0540d01500500d00c1c16840985080c0762603403948101c0d0380704000b2440120b0401c0b0300075034180e05500c05c3c07590a2400d04015160440c684c9016080b224014040400b4071101c404002581e11380d40c1e001c1c040c860254444002c1c1c1a00d403880b5059841441d001000050310b5114504007962150501074200d0342c000d82c600c0c8454407070340c8011241c003843d41d1442d40c161003180c2c03000902c00c01e02d2000b4800c481808082d04c2e10707440440c4403030b001044050b04c268901c811000340701804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 585948866 1250 585947616 585947657
    0x92e0e01050f241e0403020a14090a050a060315020a0807090b04050913050d11060a050103080a05072301150503030a0203040b0c0106030b0f0105032e021612030912 72
    0x4801100f000d41c0c8500c6500031510b00c20f0b20540d507150009660315200440040000b0300940309a83c070854802c4175658664400752203d00c1d400700100c0c0d000b100000810488140f0340e01c480e400019100001c240d0b1070700d0b13865100b07071002c00c41695240d60b6800034050550301d51000300136130003040302c1c40c145115520b040409140c5005038091240300302c441001280c001c0030a003940c400d200d030f8490140c540009900d1400f520b2813010b840521114040c9c03c00050701c103505442442d0680341d00c00c524504041c104241100d0315002280c0031241c21122280034003480320403041241d41a9010b0340049200707002d4100352009055a03a000d10b020350700a10075094403079000300980c1c0940301220003150712000d1f100480c0c0d014100ca64009482c3d140c0010038000c0c121b104403402410b80714140d0488049061800c0e003a03001400400440764003c148052032a10210103400030080e800340c400d1000e0b05680d080d10350501c00075484030b1030b1000c2996100c030307030040040700d4a40c10f0111042d820003010800c0c1480002e00c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 585950116 1250 585948866 585948889
    0x1030503041a040906090e1005040c0e0c0d050a0f0f020412020105030705070c0803070201141905030a2a030c020a1502390705041a092e0e01050f 64
    0x304a00b2031802000046800b040d07400500d20200184000c0396151115001411641700c0020940250103040120160602400d4000c035407041825040300e24141e0b0000c0d00ca0405040c00607659001c02c0281984810f6015160080c82c101900003086110055490101e030401301c6000d0400c0e005102c1003010480c074080c50800c6580a00b48607907a030382d07001740440d41c5200e03104008041d1980d940b00480c60180c00005095030501c00c0e00d0f160007880d05148801c505003d0034400076041010030340002d0000c0e21490246070070510016020600c0709003500700d001400300da11141d41e005e02c3d004d6003402075261b250151410030390090010b000501da036078072610b14101400e43d8200030582c0024489241005004100d0740b072014218401c01c0d81c00c06075059052040782000c80c00320610454801142074501441180e4009000300350407841d012800090000341c20004001c05283e0180d002c50300400003a0034400c00b4010001d10705006101e040c054004445401030300420300908031900c2011003526541c44881 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 585951366 1250 585950116 585950129
    0x7050102150a0b030c060a02060a0b150a1d0d032f15190908090411030106050d0506060408010c0f03060f0513020c010f020a090503060109020307020d05070f0807081804050103050304 80
    0x1d00d0f908401d002c00d240800c1c82d103841da0001d07000684001100d901040d800d0064074141130a2006608600070003030011620101e02029600401510190030300620204402000030210441e801c003a050005024000c41c540a8001c90458074008418165074048401d02c00303c40300500c4009a0050b5116644540504070040d0302e0140101250040115540a5071050300c0301c0d5090000e84028030348540d1f40d410a2105a00550070061666000181401506c2c189c0354580d4449040c0103111060101602d8050203c81d0800310400020410203400c0c001d08080020a40301c248210010b268010101c514030351100e0070700c25000000b4086907560103032010602e003400c0c07400740c0c98003506114180189030350560508420710000380b25a5864100c0c1c4008204c131811004e0790010707a40c42c440300040e407104035065001608001401c0803041e000d01c024018080c000c1040d5041503410342d45126955001c0e95041d10842800304000c003421070301d903540e61020344056034180b00552441e070700d09690f40510b0203a003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 585952616 1250 585951366 585951371
    0x1e270c060c08300618070c11090c030609090a2019081c17010b0f040f08030910110c01082206140c0406170703020705010504050f07050102150a 63
    0x5091001d01e6080c1c0e640070201000c0e001001e1024103400e60100040510088200c0303810740010b01505d0009160a000c0309040c1d81503040d81d40e018001c640b80368010408032606420b0702003105190f150003040074494030850011503a07a0401c402005000030009000f540243d2241d411100003800c000100130780ca055400410762201001c10002d204501100c00e414201a54080009003107540000d00c54141504510200902c2d0141441100c0c19402c1c8030b809201d40f007c1c00010006002000c1c01030100e000403144c071504080c0c03503041e90303500311140340e10100c0307240c1c808542c1b00024505100010144001803c001c04d00800340c00401c0e844480e80d420031814004c03072000040f103007414200a8a0108400e030204160001d142c83c1070030081100e02d4052a642a400c00080c644803895412981568002d4039014000100403040501c0c0d0100101003000301034003405188001102402154003807407140340941482c248501203203103890f00991003d4119030001e40c07402012101c03c000340d50820302d0010301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 585953866 1250 585952616 585952637
    0x51210050402060705060a060303120c05031603090209090303150a08060a050402031009030c0c060302090603011203140f190201110d0b0a21030306060c150c031e270c06 74
    0xc0c03c9025000d80500a406000d041002e010445d41c400c00c1924400e44888004452544610303007107400440685d004524104082a1640443c03e20040d10940ba0302c0c003c9501f460369800b007820644203941d4054180e20100034481d80c10701018545e00c0520050320b481c0c181910f0005d415039206809890000361079601d4001c00c0964070103015111036400140c03020301c0504003501d0020140d00b00d9000a403100081c0180201d013072407080c0200c030481203001f44054103607420008812900381c00c4140c1101805014955161152083c0000d40030740d8012440d520340b9500c21103400c91150308001c40c00d6045915044040403406a02426205041080480010f04000140110b1905060740d0030500c0060004034080c0c1280c030f4808031402c070140c860b0354244030642d6143c5081e246203036100c3c4002c00180e0003240420080300c2c0d0fa0320140190200b80790104010005070310340b0b00700c5600e42c2c0342049600c0d00d400300d5140400d800c8a01030000c280c4010a00b04000c1a80c03265595000d0b18040e071b80410100502 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 585955116 1250 585953866 585953869
    0x6040609150f0914010c170405090a06080604150906111909080303011206090c0b09100c0c06050a030b13020d150b070807081c0605010306050d0b19020c0109050a0c051210050402 78
    0x41b030324095030144e11016154014642603041c0d401c60320138944603485241c002150146240203103000c550f1400700502203034850b6520144800040400d134800e25035611108008248140241e10400e0b05280d400c603640c00d0084120682426001911404d101045800700203140f00002140d046a00003144044e40102924200000d400ca642000c2d1541c0071503940400e444515000828105c10708a50000180800d09070aa40b038020202026058840341c0c0000c01c10f03a400f03030b40205241c12062500240984503240001c82601d082c080d0742402ca039010480c03040282c06841500070540c900100050594645071541c100303071203103801c014880e00001c600398040010207400d9940750500e2041015030460403400c40300040155128150010341040c400041c0d27410901443d940180d0400d000904546c4c590061039498040040c1c440034255080190b001081c40a10a803039041e407080380942031000f0603051140030011703580c00c914881c202c00c0b001280f8039080020614200a120b40c40403032260768500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 585956366 1250 585955116 585955127
    0x110705090a02090603190e0a051f061d1008070e060d08120703020310090b0609012a050a11030622020604030f05010516020c032a06040609150f091401 66
    0x40f0140c1003071022050102c00c003940301c00300300c000303100c680204030440c42000426030310301c0d0500c1c02034003a401c52010040031190080c440007601c80028004180b4a0359600c07409403002d02c401c0383c041c2068140c0140f1400c0c142c2d0000e890001d161400050181c40d042125030080190050502c502c076400d945406070030002404141e0350310000503020346009250030741c40070f0040d5108403407601c203481a810340412400482d101d44c0614000240203e0f081a00c03420054820400d010f581c06900241c144280010702c40e0025290340d20380c440c2c405440e590703550b4a828a41059a000c803244290004020800d48414040c0420000040304914000012071400032900b44d1040b90409840085003411070303800c0c40415000940514210701c01c038040018560002c81e01c03015542c907203981c941c2100340a4854040301011407900c0c1e49590680c80c2d0704020800000d0080e500c69406074022501e030f400100a4031110610850715180103041003c80d1500a81c002045641280501060150040c0038041c10f070f440b90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 585957616 1250 585956366 585956377
    0x50307020d0c1506080a1118060f030f10090c141c03110102041511010605090a090602160f0c060c0206030a110c12092b060509030c1606080106110705090a02 69
    0x80f808000d1182c0318400c0307580342c040008040d9440b182c03051a80c52141002c0c0e00070010641007001e031070207603292017040050f409914100203a0512880411000d0101d0510014408407200d81000a2041080c0350410101410741e119600c078100c0c000510700251204040d00c18a0b9803860402120010070b46002d440c0300c480050300d00300540c4081804546284c014a40f041e00480702d80b42c2c29004038001030b105007030301c80d0f038042c442e00074030210003054007072090b500200401d5110344405401c1c9031501d50000754144898006a4844580701c1d0f500341440040e900744005091180341c1182c400700355802044251001624580400750744e2424000b01100d5581a6420b0445e8041981c0c0003544421048409403c1030f06041d12400d41c0c032100e018116851084405000c88900782c4100000140c2c50f50802000000d061010a01040002c6048440c0070b10500160080e002e111000340c0e13082100040920384140c1280c418840c0d130741d000c032461103000a0403400721b0300100d40e88411592401c01e07420290050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 585958866 1250 585957616 585957653
    0x60f040b06031b040f0303090f140307140307092909070c02130b130906060b090a1514030c0d1103060303070f170a020619090b040b061c05010516050307020d0c 70
    0x40382800310400d07070f110184600f1a442403009c2680581c56101400380190603003401c950540c0301520410144c81c940d2414006200000c054552060360b8900003800d840010301c0c3c400c1c0708044030f191116695000703102400100025200b6045510700a0710240c0002d00506000e0b02c22026600000003551042d00303e00210759000e0803c1000804030803025000d400e10f40d008541032828000003140c0d806501060b0790000000905040450f45401034a244001210031564104401c138a41c540e003c1ea1035a00a6001d5246034403980e81c0e5862900700c20044a00c00300e2129043c00007001800035555000081da22940c0c1c0107404601c03a020380340340c0607a1070060010020401c007400f0500314100c0360046859880b40f81d19a4982d15640b100000f090301316680390000034240000d40f008140403919618245503c5680034021659124648004c28498041c0640071030b4aa9120801c111b4012400070500c0c1010949041450030350030060340280d280c080b184c081d031003003042c40c01085042c8102820250501c441 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 585960116 1250 585958866 585958889
    0xa12110417010605040e03040e041b06110708120403110a0504230c0c1c0c08161a0f010510030209040f05040c0f0608180a02040e0105060f040b06031b04 67
    0x6030741a401148481c01e5030880d034254a0440300052900b410302800402200d0f5901075841c00b41404548070038010080e20595041500f083c10340341071a8100034007001751030941c0b02d8040034240c00380010704e8001d40ba04410f003950403404109010f0030b0000d041d1426a540074000b90030324282040880d20440c403651150f80e10609040860003069035900482003280a603548100850307641c51070740104c600c200190010395070701c403c0b041c000420880800c101c400d111491d02d10031000403511028080c0d04404181c12801d24020070507801c111400c0c8150070715451406040700d4030301d00040b4607440c00c4014031803540250007042201b04118443e504a8a681800400c1000b94bd483d100d000c46c004e010489044600c0b02c5140004100c8290080000301121001e82d140502c656882c404a1001c085031340080c18940300e030895190050b5100c3c0210b10b409502400005840e18080e000c00000081c0d184400340030314640705030030340a0780301c84d0200c91f40128452802c46a0044100800b0503510075540410080c11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 585961366 1250 585960116 585960119
    0x10b07020d1a0619030209070503090715080f0708041703100b070510050108121e1207030519090201050d110c06090307060b01030e0c010f11030f0913050603030a121104 74
    0x1508844a600a8a0540c0c0044c05900c50710070803010b0b03a03070501010303500400c1c1d1000215210310400c02590700c0401d00c0c080d96481980e90784019000f07a004e440c9200461b62240802c141c07410407814841e071044007881c000130142001e03103038042000d8501c521803426060010000f55000803400b00c850060030389002c0d2555030525401d1540d145c02105d999502c0ca641130500001d900400020380202086000e42624a4400c6200e0001c070060301c010341c904240c00b0140502503c3d401c0e4050070501c5641551004140d41c0303030030480c00102041001010700c0035031402c000c4d0000743c2d034030030161020400000c10010306000d0451840036540034507120b04040e40b140104000300c082d0b0100141c00800d02c07520040c44440810001034084d100d00800549072544102e98042c055071040044001c000c01030300307090783d01d2401241c015086a02c030000b403103c2802c0010b00000903050401c5910041e80307205004001c14242200025228828604504100061612408101001d662002c0071040e05080d8456446 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 585962616 1250 585961366 585961403
    0x20c1002010e060709051c02030c040c0c030e01050c0d050f0403050a0f1a04080a0e01030b13140a1b08100b130627230414090601090e06010b07020d 65
    0x20601110840b0150140c40081280c1c00d00074401101510b00082990a480001c0c04819003038002c41d07a8140c4c1d1600c20a000102180c54900c04c07e40c209900b6544d00070030f08a5410090a07901450402504129040005c428850310107c0c01d118448007914000f50b0350458007180080300c0c040d0350400f070100d004040c2c041e01040018407032004098440e101d21700640c009141e050154003c12034020304841c40401502024602c00c0a2841e002c51050400040c03100800d0007241000c551120f82d0114940e0741c0013010136a58442084e550301900c44030051007100c0680041d01c40940d124002c1405000700040840c410b82810414000a0100806510b4403080300740d41010315520188a0400400c1d544d440c038050701c00503008d0361241d01081213801604103281601a00d46415081400550140d191850a0082da0f42e0300602d003006080c0034407403040341454001c281c00c1c210107a100d8420107190081010b0002804580c0c0e0b03046034030002285c1d07107501c402c0c0045040c5150700000240190140c4c806174200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 585963866 1250 585962616 585962621
    0x303070507140309031b06070b191d07060e011e0906110a050d0e0f040204090603050d180b160b0a060f050402160b04061d0a06140f0412020c100201 65
    0x24502808690821822002d0680d4480c0710b1031040681603000598190035013484c0030524401e049024014501d0007030203840301e001507902518014440d007010324104401648a003c1d4005034100703005103445003a00c1c0020142d84004038819034003844400400c005040e802003d4040d0b03a46d4072200b86103440300315944000d103542a5801181c010482e2180c00c0705640f00b00090034440c05612000070200811201420307204d6084c154840ba501c803a43c040911016281d42c0013800c001c0c01ca402d0003050f440d0942c41c08a0500c1236980c00ca000700031280030a81c01c003000d55116082101c0040e49041d0741c0d2611045e400c20300300900600540800c004e407051041380c880310b43c0403504440140e10005110790b02c40c4100810f070712480304c0c410300e0349190021400204041e2508548c000344689000242104117942484140100558904e0076401291030302c0188103841c007400c0c0324503000e1381c54007402c0d1921100b840c2100c0c0000e0005480081d1106401172858000c0101c501c0701e4000030301d250f100c01e0740c410703000b4003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 585965116 1250 585963866 585963877
    0x10c020f0f10030212010b16061113060e0f1206070c030c080403031805060a050a08101d011a07080d0c1206080d0908010c0c021e040212040203010507080c18011103030705 75
    0x180c08050000040c2e01c071b0032a012340704009248002a2586510740d2600070240140700861100c0c2c040c20000d0284407000d9001100080c64a84c40d000c2c01c03016444100041a05d40360009400f60007105000680d80d100404c039960f10a400303040803401c28426040c03c03103602840da03800401d07401000802001389504400300c800c401d01c01081c2c0700504c1d6154011710815001ea424018041041801031100090003180501e80c8004000e809004640d03a881211150380140d061141541c42c229005000c12000700c10b030300d0000c44900007001d140c80455642c011061140405051802d0754612241141da031060303000c9041c01030304c0b080c00e00041e51580700041d111030100c0300304004284001c02c0017620740c1040c024201880541d850b048a00d803516000c0c8400600800c1c00300d100c1075460144116159200e04c0640042c0c014030070741203500d1a04e441818210740010b0305100c00e00c4180c00c00c0110380e0b4080c01c2100e031209140340400e0b22200e601801660104850503114403540404010040d100d94030002401c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 585966366 1250 585965116 585965137
    0x120318140f120d0c02180c04060212070305040b09040b090c030601030f1514010908070b030412082707081905011d0303010605030414060a0c08090705010c020f0f100302 74
    0x80400c401a04012414186860b2161240c020a1103c44014040d0b8502210030b40040c00400140400704440c020700c250444082880f91404902070040c0b503030400c00600302202c1065001c0c6840b10307544010b03095010f5442000100080090309940607201c0d034200c4d0001b441d010b000d0040364100b010181e52030750001c84003640001c0c90010f50308050349440c00b441110014640c0c103012010b00f4010025031109004503524140100d5036800102d0060070443c44d0010a034201103103851b4185840c249180c20305c103801000030044e07412f0074000802800d05014900c1c40070302c0c0c0d5809a540300002c80c9401e00403258001801c0740281c603044055039810301403801115201c0c030000c1212800c000104861006c40447c01c0d000e5a00600052221900440040d03030401d0240700d40d03042e4079110f0b071500c3e45810401c607685100309482e18940200b003500001100d40000c3e00c613000d4440503081200003040c414212030060b1240510341070018107501c07620110f5984101c044c007078581d810000030010340603510402d14a03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 585967616 1250 585966366 585966379
    0x20105070806011b111f030917030f070f02070f12020414090304030803070201090b280615030b0612072309010c02210d0201060608060904030912031814 67
    0x76030298400c1144c01c101c040c040355501820313a11626003007141c8041681d102e4102040c0c0741841c181020041c0910040c004039600482c040845e85030254040a81c070141a14a540620500118400600d0040c0e03011131a80741030507041041d51022481c010090380203d41c0e0710f080351800308031440548000310b6480d0080d6414043c0d00080c2c0030140105e103040b603c441d61500280700c1807000a1840d001035030031803918400841d42e280107846a0b050380301c00340c0340d40b80040244050800a13081038142e00078000d00c840b5041103480d1422903141010f010f80d0b0103850070582d4078001c0701550f0f40d0300402c2c1e03541020010600d0840307141c0b00101600382d0390042c000d001000c6022003903c14160030b0004448801c01c06950f0029209080c4c0d0030f00c0554801446200451010f156202103681c0c403c005039180c1110980c000300307a9500c0c02801900c604005070207107004950301001c0101094001e0041e808580c500301440e401c2d144503040840b6001c5103180c0004082c0c20340e0300e00041d44508010301851020046500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 585968866 1250 585967616 585967621
    0x201020405042304030f0c02032a0102071a210c07142107080702030114180a02033424031802100908030d0212070c031713060c0201050708 61
    0x3181d02008030a85828824040e0f000140024400c4514050000840c24600f86120107580000d00740500d0340100206082c0b2012901c0350381001030700d022200750080c00544081818220041480d1507243c03e03144402c40d002901103082d001c0c3d060700960b00254600541c07828140070031103403015031010321b05541c0d122441c140311040c1900801c1c035000039005041d50071100d0a1006003034041b80c00161050710340390814090b04c0050b85013800313046010351a056400201d4a02040c0a8074480c01801c03d40303001c0e078001c1045000685000804818003810f00914411091105002450f07c0c19851840b0340003080034000003488a81216041401d1031403621403030007000306940218100d9881d03507414000501554503610143c1800c0d160034050301c50a00d8500207603a105c0d241c1c1851031307100740001e004ca56800181e600311166150481074000b42c0c10b1602c0c003540c0013143c030020220312491407023101e101020804280f054001081101c0c2556100300c05000a184c1090083c5c0208030841c2e00c50b01207103a1000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 585970116 1250 585968866 585968891
    0x316030c050a0e340201060504180f08090f030717120a020a03320d0c0521130f060c11011b1412090601081b10030525020102040504 58
    0x70640181c1c0c4910310781c800036a039003d500318041c2c24a13042c004680204015668840c9040004070100c8102075000411070351314107002c1c401152036854407226000216032190700042c442480c20741d40a0781100c08070b43c4545840000520720844103500590501c50580009201c285c0c40c500e00001132000400c1e40d0016110045068051049554600043e000409000006030245a50700981f00407c500702e8805111101782c4103862580c8010b0500202010580000414160181800d0b5039203600d051400d090740b900000031baa0801c244080980c03105000011440191801480207450700110240c04c0c505c004c0c14032200400e03007101d010000070074420901d10102c1301402414194161101007506c00c401c0040200c0c0c141da0320300b804881042c420824402001c4c45061030341e01510404025000c29450300c43c040e40343c007a54402000151490208075881075540f0b40c80e02810400c0340c02c002c1440e94842c000201d030500f1201298410101d018034100d106607055000d04180c940650301001003c2c0300c100e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 585971223 1107 585970116 585970129
    0x112060306050c0d0e070e04031d06070f030e090609070f050f040f050907080c1e070204091101090e010302030706030b01110a06090606171203150316030c05 69
    0x404c40d00103d0541d44503828205000390014486140b5041240c0c7c030300035006102805105040b00f200c3c044655148680c8140e000c018a40359039101d07140341a0f1108240030030203030001080740c08254894200380515030b0040ea40188102c1d540d688003441206c1002d100c403242c0007001401c2c04550642c0c00d580c3d010304080c1c24540303500a07015080c07a0601c0000c04008103080100441001840034401468003198400ca04c1100401100b034a84041c1d0202071041c140c00941040c50301e1000070504c000d0042c2240d5420099851603034142e6501c64070f0440308428000030b981504180e030108201c5010754480610341c2c0741810f100b164217602141031400e103444c1c1c0340142c511a1700c9620311707000c0083e0352042a001d0b00c0200c0c0160700103a4042d02a03036272074004004584580034004040340e1604031043c1c900241000043c2100c448000d200b82080104070315100840340105014000301e03241c601391 = true := by decide +kernel

theorem cover : BRFrame.Cov 585791366 585971223 := by
  have h0 := BRFrame.cov_init 585791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 585791366 ≤ n) (h2 : n < 585971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
