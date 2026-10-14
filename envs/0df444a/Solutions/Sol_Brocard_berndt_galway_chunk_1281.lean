-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1281
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:08:49.210978+00:00
-- url     : https://prove2.me/submissions/f6ef288b-895d-4a60-92af-8231e9854c5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 230215827 ≤ n < 230395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 230217077 1250 230215827 230215829
    0x1b0a02060d06091a1e040e060702030712052803090507090509070e04020918070b03131a090a0303051e010308040306060609030f021509120a05010501050f0d080901021608030904060609 81
    0x9080988145d0f600d22103509208072200c421009800810b126071142c402134030340f50003100c2d0940180c001081078003c01a424000404502d001e19005090604034541c4182180540617030803c3c1e040115020100c0034000d411a030a4950002c0c2070320202c582d1801241b0107000d048072955100c0c0194000031071441c1c0d5410010380129000f801e00d5801e680d03041d407800004c8142c213149010500c120034001491103a000b00452183c0c000d0005111224101c3c5083d240d4412640038175400c2282800401643c0040014003440441d010b2401049035118043c1030034003485003e8401030f080c558030f0f0000c028403207414024011644940000c00000399640300c121280320b12400006c2140d0054404a005860100400e100b0703a02503112903450801d078500000c4010309041c0070540365800002011082c80030070b02c2200c0c01010b041d10300102d0451580e00084070b8802c1210018a681008608a0001d9200300b1400002e04100e0840c034a5003038862003001e582c0d800100086210b28140a404900c0a00c9414494 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 230218327 1250 230217077 230217079
    0xa140a0e03160f05060304020409020303040303050a1407110f010509191a030c0d0c1b0b0604050a0626070b030c0d0605030a0816030c0602030a0e10111b0a02060d06091a 74
    0x1411984c286010800b443c1e0018000381d03845134594005002684d020710007000198441c1d21000d81d140000d000182030702c0c48100544d498918240000801b141070000700d502000700459180714100e1843d0010b03240c0340229501c060308980c410b1000c4044c44901365080c0181c0b07081c0c1d2011280c461400c4060417180c071003280e2008000b81c05100007070100c11700e40c000f0360701c0c404c1900b0b22004d0f00000c9024501d40060364031003a00c800c00c400d420312080382058427a184d00804856001c1c407200c0d0401401d1050321200c018610108800c1080c4c81561504c203008001c0581403010704140d072030800041c010450780050003202146483c1040c002020300c0d00003581030010703038402441030410140c45280105124036a10940600000c0b50348940000c61506c0258410301c080d480006000440e00110347c170b810b000004e011700b180c2c0352001d4150b100c40d17108103a448414134507480c22102c002402c2c105007450020100250803c4012030031155941064001000303403000c10004003d00c124441d0b100144140030301c51301d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 230219577 1250 230218327 230218349
    0x102160f03050c030a0806040b030105040507140a1809050609193906030b06070b0a0e0a06020706091103210d0e030d02030a0b0d0503040b0a140a0e0316 67
    0x450002039405030020a9607000b801d0903810055440a00b0f401c6505c0380042000150105080040078078083c410f911200c0800d400801c01d0789441c2c2d60341c9a450203c3d0040191882d05900316114607503558884002400e1081c200c1c0c4407200381c00703c550003d00182003040329a400354200182c1200341c001040144c24a20302c21241c5014201d859a046034180d41c4040c2c0d100201ca64034910030b040602c8480b00c840301e000d86003804100e1500c0c00050445180d0b09001d48108401c001c2540401c004070915908034142d18000a02080c003203a01d14a001c894582c000d0031940045039120620095070310801d85c0d140620300c0d10303c01d0a81c5504050729500c1d542005620a07d610440044041403000035210703284820b2030009821142300c0c1014a1074000020480c107240e0000108040c400d003030700a0386043c1e134080d10124040714055070368588a00403405040750729117010552020940c400e031030740d120030760b0260407055444906400c000d100200d2501c046000740b1815030f1301604d20126002510484a141000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 230220827 1250 230219577 230219617
    0xb06044d0f070308040317040b0115090e06120c0904150507030e060708060f220c030903020a1b0e04060902100e060403020909070e0c0a0305090a0b04080a03111305010e030102 77
    0x401c0e0b800d13840c082d2050b020007030340650040e50001134411250095000303c02e204002e614000c0b1501c588a031440d003c0c2c0030050400c00070003002c805030070096040031003280c0d56052400c401000c140340c4105070982a6021401070b0621040c8801840e1501c68804804810b219658800c14103806a84d104030312607085600c02c00c00900040d03c280f019607002040100200f07070103012800042c000140d54841d000c0900100340c100110101e26100301341d40c40b4942e08003882210038503200a510b603241594090a0015034a160b0b402c01198200144050a102000102603042604003038004001039170040340564158400c403100301d8052000e55541d101d005000c185814256401d01003040e00c05401c0c40c480c0e02c680003010600c400c0d900324181c13242041440203510340c003d20b00b000702580d50107440f440c519007191003240c0100c9c190808955001c0e80066100b030f0307a4501100201e0080401c0e511014400c980030a402c489142408450412503100340e0364450f42c08030801c1018201c0c852a408044940b41c0146 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 230222077 1250 230220827 230220833
    0x40f290f0a09020903010e011b03050a0501030b0c18030712020301050f04080301140f030d2303040503190e031f0f180b04021507060915090b06044d0f07 67
    0x4c2994400c0500003240c45404a142039003550f54034031520941d564070800500c1183d915200b99035201c14000e0081c009035140d9101e0404220001e0905e41201c2400600444000003e504c041e0100c1c00c0a030480c0c4440e582c03424540203085030054220710a508140101d20961203030050640078941100c0c0407440c503440c1040f0007030074104180b802c981004440d001d8030090740d8140003a036a0b038850364441c100c1800b10f03642e10155020319002c05400c0c0c4a028424400860000000c0c2e03040c11854140c540680703e070b000d01c162045000b603c04250704d0302c030328800c4000300d102014501c0280e070a8810144082e0021140310b1040d55501d510343c840a803c1d200001022644e07260207507070410b0007d0050803a41b00f420403640c0f031f1303075001d00410703181c007a1280505d408011810001c8410702d0b140c03c204000f018169030f142c403c0d00002500d240d100d182c03216042000706c4450b000c06480800101a01d00c07503046111955a240f00040c51003041100003038562402242c8400103ca40c8611900a028544a60382e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 230223327 1250 230222077 230222081
    0x905040c02010b030303011814012403180609030906020307200a050a1410140d0b1f020c09060a0501020d080709030803010608060306160e06030402040f290f0a09 71
    0x54030a1003150740703031415030703243c3d440c24002107003e000c042e042880c2a19100d11810107a448130020600c074101d01e580100a4040301c800008110801c07031924070300d2a841c0705012406844480c000030b008400d401c40045c10413655a010121080c0b007510741018140c2e0325142030381c480c06651800b030010320070722050039941481c1c1c0464403071104000344420400303511013012980c004016000300200860880300c80107203150280702280c0d19000d61404010485c1d0b0007100c84040d00580302c803050403a17143e0181c50600d64a00c14085000c03e4104840f00c030315202040000d503a1a54a036a084c00b540545000c10410b007000c40921050b030344181c00a050400500c01c00300d910940080c01e110411100e0709000c8002420240118005c01d029a034281c0b007030a02508150600030007402c0c14940b423242145004280e90005454810140304030340450303c80d0380b5400424081c1c49801e80180c40b4900d0410789854035864140c0c191018401040ca480d03120321b020061207001000c02c114240e201000000c104203420180e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 230224577 1250 230223327 230223341
    0x1a090606070303112a1501050109030605040303091b06140301080303160c050706050a020c0103060503120f0c070807030309120506150105070b0a020a1416020d0318030c050907050901090504 83
    0x841d075001d141c24180790304100000030f151030700c17104501c500105a40304601000112001c18084607084555458280041c3c03083c0c1951200070240d139180c0c2e0019090602a502c5104c5480d04808000c40b11058954401400342c0580511804a004070b5555a003604808042d2410b0310180401103107140c964400c00c00c001100301e0840703002c201a50900c030300002c0d0107200043c02440e030350715000d0300c54000500c0a400e00c62424042030402d807503c841040207660000c3c003119442290514195541040040400e46204406401d00c141c820700b180050408400a01841101d000c4d0360341c43e07011522003442c00f903420355515020f425540300b01b000c41c01c5041031368003880700007405043c45c0c1c0c58038411742e5076205080801c48803015440c2c0e02145502415402c412900c4042d181d840d4113a01e0701d03401d5008281038040440001e80514802e0303403400c04040c0201800146206104440207645650346040f5800007441d009240c09510707a2004114139a0240040d5059040140c48141c580781c14034090000500710 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 230225827 1250 230224577 230224601
    0x160b0907080a0f080309120406090e0606090d0201120609090b0604141302011d030a03020f0d020703050703060203041a0405010b1005092809181a040b0c07020a0302090a1a090606070303 81
    0xc0d050f40580135947c4a00140000c140c3c41d145c1da4052450a0404000b01200512141c0125010054449035030741d190075880d825070b82424080660740903446414010207482d006070320381d6454204035034144a010011203110703c5d4210307024040042c0d558640100038209883e0b14a00c45580e0040400640c080c044821440e0a4405424148c114180c00a07181c02c02d94102980507820084e640c600b060400d0142704420030b0540001d2900e1480d660300c4a0795480b961001500d01c0758040f02240c1003041500f070100d650a51220014011706007810494000c0c80841c46842c070030540f0020600003140200f040d203000b048020071800d00b400b40b4902e00004040b4811515403c0d00210002194050082c401c98110f120306045981c00c136030043c0f6200c00e50600086811001d0f043c00002c00000484000c081c40d4000010801395482d02d4003803011491100d0f00c1c0d08003e500103840ca0410085409a80c00300b001707921444c4072a55031421000901c00b240c4800d5400a070060300c104045004a03000790000803000381c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 230227077 1250 230225827 230225833
    0x12070f14010311070b150f0a06050309190305131d06011b050f07030201020705040231080a030e0f180c130906270c020c15160b0907080a0f080309 64
    0x78600d0221061a44070010440e007108010080c0200001115111551744071b0a80d00038071942c00d8000041c40d02d50300da00c5031104025000001030800c00050000810350b042c29030004403104050705d40580360750480751440b00a9102088001811a9516520800001141c106c103205459135001107038041180da2002d452001c44030fa071080025401c1090307040741803994010b03004e107600318400281002001c0d40050712a03801884418022140b42440c04248a00d002c44030090030702410107900248110340c04044e050150035803100034950031100c002208001200c0d00b010f0328803198200311700a0721800c00b83c1901c1d070501000030f8080c0e40400040444c690340c41c0c1c0c2155415990480902510019007290600160040002c0300c0700d42241180034421500c02411f00410304082d074029910003010710203034400c805140040154085490407196402814180028105e455003048425802d042e180c60f000d61144c1540090750707000124041d0815070f8004010a00143e00d40c680c0c00c000e410180140b40180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 230228327 1250 230227077 230227091
    0x19031b2f01020405240306120a05060907090c17070305190f0204050f010915051317011a06120c07110907020606091303020c040e1009060b12070f140103 67
    0x340500a0590500d00a000941c3d1181070106112a1010705030100c000c0404440b40c5460490140e01900d0744003a050b00c0940c601c810803042c592524142140141c90390142c80c007402548100418240241c60400e8010710943c0656001110401e85810030000d001a00901107182244250805a0070080802200c02d508286001010441c0d1a40041c40011070b80040d00300540c1c1440f0030000c14081090802d81c4000c2d01d4a001c80415088441c000800c01400007074000c06198501c4502001c0c0000d440c400c0e42840c0c64810290080680782801521000120f41b545200e2a0a504681801d4226101c09805855201418500c0d403c0140c04980d0201c400c20810a551101d9402600c0f07020755900400c600c6c100356041c041049005010820551076081e10200070a0f00001c02c0341c0115400d90b00099004032560259007070a170349011411419041c0360710340c2d0030b004071394200414911048800d0301ca00118a8200c035690009482000e0300c2c190b141c3d004205c10341c1004901c3c0424001030501080c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 230229577 1250 230228327 230228387
    0x61503160905040b07080c030103080a170f06031510050402030907050d120815010e010804111012060b03060f0d03110607030603110f2b0c06020319031b 67
    0x14242500822062550781c003c1001303002d0520b5903103401490904150b0b459050125030301010307100500000d44104070000300b000e03303584103103a06000b21000170751200e1182040c00c0b4580d0183d200391640c40c82882154503803415451200344560142e02c10b08442c9180c640303081d0900019400080a4445c0d5000b60000080d503a15540c0030031040ea4480ca0008451040f1840b01500c850005030681c6086203440742500b20690700304401044048007403c0c549620340e580e18200c100000c1110803641c006085190b5007990a40200d400b0309420380b0032100340a596254051030340c07107000440714560300010517199074015040002401c0034607030080c903190a449a111161a1408105461070800030b0707503500d4200240300c400034107103080c0801291200388038442c1c24009814060344212000c2d040e040c850704a1800c4809640721845940d004085d0030a10340e49400194503030b04200c1441103070a09260303600e940940720748100110000410010645482c40003002c58030900c00510240d0150710b00607804040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 230230827 1250 230229577 230229613
    0x30709020706050601140f090d060b03010e0105010602011107051e030c16050f0904030c0813030f080d0e0a030c0602030705042106150e0c03042402180d0203061503 72
    0x4100d0082001040b5401c2613070004055020300c901101e0400e001780500c0f001100c60a0855100d01421106045507134104e040c01c000614505091580c0340d840c0000548079183c06400082c102c4500b45c00070000240561640784051160000060090300248204841d861710400300103010740c0184112410080302c00b110500c1c000481858500100003507204001629001c181c0c11003014081c1d0b039449050501e96005071210100c0c40005044141c0400c4404996507084070940c011900415100c003030703183c6030500d10031a0f80550310800340b45003070a503c50501c0400040c0140754607416645c0c9680740c4160b4031883c0094102811308400c1090400001605982d198281d100035800f81c882060003503c036107001c10480d20b40000b407000488640f90104044501408082e03444043c0d040441c2d580d507500c0ca003401c0004002e40c078001304000440f01400c90041c85078041c0c0160101401c0d8860031020600070040103035070680c4000d5265000c03a000404072000e900d58034545420103800c480480600640c1401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 230232077 1250 230230827 230230837
    0xe090f010503071a0d0b0102010f1109130b03100c020a020a150206090d02030405210a030801080607020105010b18011403091f05160503090a080d090605090606030d0e03070902 77
    0x114411000050000345014483c0600a10620440c0980c19040403100511400703031034240c090403a610311108000e0b9000b90000740a070050b441c42002070ba14071505084c96034000004460042c00f00310030100003610280700303607405004001c00800a001206c061038020340485651002140100d1182c0d0300180c4802c0b41a10280803080140742c0c0c801d007410740003850310702c00a03e124042d85c4070301c001c040a940c000c8100c40944030281c495402c104a01e080c000b0310400d071443c0c00c0140348030320349071b800c1850b42c400d882505031103010055900b65141c11400300c0c2652030a02078201d00303440c100010000c584d0b808034180342e07040060604c5030402d0403005910b00260400c4a032002681c0010401015200720156404c1c0382c5d4100d480200050700b01403107062281890340000c03030103120001011505201c810444c2c100d03016400800c5540d119001003a200c054001c40e4030442d01141004007091500c1008141c1a2280b034001d0010110340100e602c4c1203c3c89500311b40300039098090090f01003000b25141c00200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 230233327 1250 230232077 230232091
    0x90904110409150e0114010b0c0102040f08070f15090b0304051006090b04060e0c0316050d05010b19020309010c080d0e0a060b0108100305031801030f090302010603110d110409030e09 80
    0x8600c80c040070807a50f00f6110004004540d591402d07458490308122442c280d815184040e8800e034542d41d4188030309009205030b4010380d905501d042c000203401c890000303847d016540f030445001070041e80c4501c100341e010001c51040010918110f03051182440348005540e1150154089503206151050b44404881658114260b00c5450700410007641c246405024010301d074a6201c140c0b103107410f0420a410b4000075207180f0b80d5030340c080a1080024850420fa460740030180504100030f5030764800c00c14850384072078000c04004048604c80b901b46800401920402041070b1101207008105513600301d61b0368041e0311240d0440d96601c0200240140c100803503001107128520000300c4010403030016009001c024041c03281c180400e8014070001c1c02c08000e5807a03203400c80303100c094494100700044c0c018050004800182d80d00e404001d80502d41d05400500c1140c2c080c2c0c400014000c4064180b00d0300c41050345001e0146152078050490034209544070800c0d20380680f8007803140d406180f001071068801030b00c80c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 230234577 1250 230233327 230233343
    0x1c0f210506150a02030708160506010f050406090b030307060c05160c1707030215030a0b1807080906010b070318030204111804050403080106030b0f090a1a0d08090904110409 76
    0xc80c1042e0041812906500540318106812654000d6582c8200e49000344041c20200b4040468226235240e000c0e011350100544080b0340c0c40d0500c404a2000d5482010700c130302c1c00d20600041904251113064400c3d900900a10f103001140e4a07038a014012030324020041150422401c1003400d030050b001800302d48981c8111030b02c5490200001c511400158510030140c02c0b010042005a031a003803460712896906039282d8a9036943e003100c00050803441c1410f5040700010031080164001108514442d8007980c5070700d000b81e100d0070401a56000c090040c6040c01208100040100c3c2c0a480300303481620070b82201021044e101d9011800707a54103008140b1031500b000c5400190f458041040080341c2c481698104a0b51400e80c40082c1701107010b1090005050340c03031040030300b40d03210080303403140418010b0959055410950140b03401090110507400c00345941103010150b0380340000c4407240340354010f00020700740f421301c0080200081002c6e00440d00c05122403481d040e103841d24040d81e00c00e1805103050b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 230235827 1250 230234577 230234581
    0xd21030b03010b0a06170a0605100e2d01180b040b072105040b181009090e0309030601030b1008011b14090d03030222030f030906021c0f2105 62
    0x61500350fa40030388646202e5070342640103100e000d0f80402e401080c40c062510f1130b140c50301c9200007a0014203154002e140c002c2c23407402103802c007076400c2150030701200300580b0898007004405c071a200110800d0790040078003007541c00304a5030641c03045078140d03080c030380d04158807504954a0703510412591081e4484039440c0c201040600038888003046650b801070fa034080b001c4440c40d04003802001e611490150480e2010045030078903071030105403071a05405602500072002c1102c012405071500a00d880352401d40c40c01e210301d0784070307a41c000320641d110480040c0040802d03900f990b41c1c0300000d82008007403004084101c0c40015414a00740100b03412103000d80740b5000605c102e00c0000b000e03141d500000724140b000400c54501c640d00c40745490a082d0340c05207001030700c0e91907481c04c0c4201004060340003a46100241c00100500c01d40d2a404c10000e0300c262109084c0c1680c03640160703101d100042c41082d500c21021283d00707610b802280403c10005240c40c090300148031400c02074210080e0101a01c1607a41d8440c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 230237077 1250 230235827 230235829
    0x40510050a03050c19141309061e0b030c09060609010c0b0c040e060d021c02030102090a0b1206010f0807080405030708030115030f06080c0112150e041106030103020d020d21030b 78
    0x10703a170303005d03001d40c0319000d03aa42440d2030400c0704054600500e0086070344040c40302c402400756000d000001c0d801001400380484840000000340f49801461810519014002c54640341c0010b0991a450003e400c2c229940d64030400c014103600160141030600102c94031690000d00c5003504d407845541d0745000607450f14185540b0a403d13000042c8201d000c2c01721482c400c005642e41b202851303401040c0d1004244801c8187c804603001e0b00079043c0d0b0503000a1403000100d4143c4030440600519030a07242c0181d581e036503600044480140014102c1e010546240c0414002da1042c4500ca41c424050703000c40340f0301000e6903100d0441c1d6000b40c4c001d401e0540c5c5c03501100050795140c01801805030091030203201190501b0400c2e80c41d001c0325034000d410312000d2a010780110500707803c05007d1044140b032125900c0e503203508910000800702c0342213452070b4407060108e00600c0c209095a060307940207041114102c003142d09001d0700175424202601c40100610100003264000c4104a08040260b80d0208880380c2d000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 230238327 1250 230237077 230237089
    0xc020f010e06011d091221060303031003120c080a030e011401240207080a030503062107050d03110f0718090b1b190c021302070c05040510050a03050c 66
    0x2496072003140d0800801041020a0790001c0b904400c08001540070685802e0141807400d5010b003441204070402103150603200c4a240304035004005402c1051941d41c0e100800c2580ba884103c544084400302c01109101080c5010703481025943c0e50309200204800130f8075a2401c0b6003001484600003a100c503c04e0003604000c0c000d0600e0841c512200b5465941040503888a02c014820081100301c140301582690500c00c01042c40202881e9054070000c2c4140e040c02029544212070710b5024900390f8807406c1d00300490040d090110440380c400740002c43d0a013010404100101c0f0420380070482c0319071007140c0159040c016840d4114566004020741c524110492046005c0c0990140245140203071401c080f03640c41c03e40c1da07403221180e450000409a0486800c3d07140c080e0515900940c811490b0b40440c0b150403c0704443e0450089594801c28140301c003840c8264410600002e2144040020411182c105a0000c80d0801e9000f000d950026842d100810103281040d0b009841c03643c0300c00c0007810141010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 230239577 1250 230238327 230238341
    0xf14310b100e0708150109030f0c0f12030e0121150608060d1a0c0717030f180c0d0320010f270f03170c0c0705011812050708010c020f01 60
    0x2080b1124a41c603061801621180700146102c61007405d01d410305c95140c2c80343c00d004014542c0002180e07092001418000e0500c078050007040d410480da81070206034220240c00754400180c1c0b5a40e09629004840011249100b8076800341480c000c1900740c14401100d0f90041040448000001c901c0d107500d02000240000c1d8040d0040740200d0343c002908010a42e0341c004d8607450610032044040315107490407454258443c040c000b0b881009088800a01c0e0030042c401140551409240880582c581c02c21100c8441480b2544040950001200301c00c40d0408503003e076031141c02130510440c2c503a8440c18050b8803540080c021000c603555094448480c02041c4a041d80c240d1503400c3d45007100c0c81750005089205114407020b0900e208400071102010301c20310001c02c20840c880030005590800760302a1006030003110b003041250007003d40110b403951090b020582168150030011420314540140f04605448800c015907171401100c0300442e105a00740210b031141c00c1e4550044c4021004a017501e8211454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 230240827 1250 230239577 230239589
    0x218120a050d081339030506280f060306020406030e070b0c0a02120a05030d0c0e03060c0307050a020a020306070207031704080304030b060414010f090f14310b10 71
    0x110002e105035140c50016641d14a640549180c50401c01400409010940c005880084045c409140080d103559484200c0480e44600c1c110313411340d22002c6200c40c1201000030700e512029a24002c1c00c4082c19203410001381000000c0002440b25120717150700041c9d0b40550001000300783c90307004c1110081810050f41008159030118a814180c08001c03154403400c030900c3c040c0c031520440f202071544800038041074400b65072140c00c4a41e20580303440218042e00c49092480f002c903061600d0b0b0755880c1001316455205141440c3c0c0c441c03a40d650300c071081c4d8150b0407105c00c98045104d01c4d5884401038070208002030080006170000c00300c99181d8034221210241240031759007501002c1c002000a0390000003504e069941c40348585a050f43c07803a020038001e059a207903c0d412880e0110000402074901282c4505654291205100750081071040c2d03403e5a00b42040e800070000601d0000b9100094040304c0f50030700c0b41849005040044048000700ea509103418140e80d4001c0c0b000600c0005001080118001c2135 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 230242077 1250 230240827 230240837
    0x310050103021602100909020301270c0c03031d07170705061207030b0105090409060b010f0507212705010f09180e01020f07060b040f110a030218120a050d 68
    0x2880e201031030300c143c05040090180c103480340140b031a9800740f0420300c050314140104540740e41c0c2d5291846540504c01c0c01054104074140c0c00034200c546640185e858804003600e41000c0c03410300c0c1c1c0e02180100b01c261420300c0d0010300c0f00072420b1201d00900005000301000d842d0422121a5a101141001c1042e40701f03c0c03160381c0c10000c042614205001e40e0360b00c0070f10b81c00c00050030b11040300161340360720400420542c800c0c548481c8100b003100341e51110701050000e985030120304003948410b540901c180704002e01119111414880d83c482c0d012401c0e008181e007440c02441a2840c0500200001c10102c220320700b80c0202c0505001d9564008400006031142c1e141ca035003024074109075419640c10500c01c0c4580182c48010707510342d0741c4e400d404a807480104910350940d11303090341c24400c00038000800d81c00d1189041004681003900305004601c40c00035520440c07850051800ca06500940c0100c5444001004426086000d80d580030f0140307810300717088405484801a245803030307400d1003190000170080c09 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 230243327 1250 230242077 230242087
    0x20903031c1104030c061b02060d0e0105070302040f0e060f0907020703050d050a080106120b03070b13050906090f0717040c0e0f0f0606071a1305060c07030228021203031005010302 79
    0x1071441740380030100e41da541028048100c51040036044101c1c4107401a4004200240340300c0601920340c0400840c41e01d81000700328030f03100c000b0100c3c03d034070891003072003045844110b080c0000102c08000c40d8002c0d40041a0218964020000c80c0e0300c0101101c0c0303100507801116081044c88001d00100c0c081106502d00f2500d440341010010349045011f00510701085051030010f020340ca46607001e884000402012507507415074958101c0200c0c1d000d0100480c0c0720040d80030008081c2000090b10b4018207006001c80c00c6556a4800711074004401450f00e01040ba00d5021900105034114019000d9401060014802410400040390051024084202400c007803010840d50120b8201c4d050303000740d0100d80b05641d0b4a00e030309241c074001404108800007115006c042c0400000510407041d1aa84207105403032284c1e50710b00440125005801014016800032420014290000c00c5245a49141350102c018040b80503004202c10b6104400d406880d030b800003081c404406d500079194401031409103401e62501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 230244577 1250 230243327 230243333
    0x209060301210213020d0f0908040e04081e04090e0a020a1703070b101a040f060e040603051b010806040902011b0602120c1801080705030613020903031c110403 70
    0x24481403180c00850241640701c41c82c1c90307081c040301019094000704042c04210306540707042e0080d4090344848040c40e107010100c1c070103400540140710465810555190906182100883c46840d0007841190200c00802c4480d040000044140d0151050740b0300b00d03a02d9a0908000e10119071840360101025804103c5c500e005a48180e1030f80103903102031660b45c1d400f8602881440c9107001c7c000c0028451a5407008000d100d8410805c00d600f00c40154600d03000c1006140c00c0321200c0d10440c0582041a40c85400c24080b0b18003c0700700303200f414406000000d84a83e2a103030070381860388401200c800c0ca200751046406560703001c882d0640040c001c4404000b03106290740040c2142140c5a8250300c0d4107200b8050700140012035041e10b200c101100c01c4156140b0f8041c0011905074840c594044540150300c0318002503511480100c4d204840d1911118a1034460b00104a8000d0210b002c204115408010090450701c0c00c1c009003806580d503284686807840b101e40b004095a116208030600c1c0a410700080000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 230245827 1250 230244577 230244589
    0x2030105030d140d020d1e02130b0711040e011d06190b04150608010f0608160c0f20030606030307050c120f0d05030403020d02060114040218310209 65
    0x880e0b60750401540007641400800807038055500d403088070510200c0e44c0e0b45503001d19040f85182c800200120303da2684403071306070320490103803400d03045102590303034070038020415250010160b07180103401c03840300980011b00003003d0b03c045403406003259440d654100390001203006009403000807480a0041490441e00d03525042c2da14170350200000e91141d21140706c0340c490390b0108403990104030f0180d00441e102c080240440800b03105a040b0310240c4600041e00314482d184540c000c10341d4074044581c5103050303a801c172510002d5420591300794541109101c0002c1340c2c0744105400000e103130003042d2a10510000c16050030030040419020b42c008000b1403000840109010b4450042140c6807005812501440303807401e442c642210400e8803030b500862020350741200145110358401e80c01c540c07100368258400c0340c80703080c2842944d02021800518060740e1a1540240c041003450300603901d03c01d13204d40300140741340748811800c144001d0711170380d81d00e0788013000c629128450814140561515040d0004146 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 230247077 1250 230245827 230245843
    0x308090609010e1302030906090304030b1512010c081005010201050108250801020c0a060609091502030702280203010c0f0e04151e06030510061d0402040317030411040203010503 78
    0x4031500340054045802e038002c9000010044024002000756030800d0b1805000350300681b8410a50700c110320004041040000440c0c05403580002c852000351254110120b4200300c0c2c00c12103500030f074890304080500d1800d10444080d10b0039039a580366a03091000103040c00f142650406070469041600501180c100016610044019200032584140b442401448050429003001200b075000242c8a8a07400300010020300240c0a598100310031566444050119500c0d00d80c01051070bd001c10419900d101c490b80610b40c411940d0050701c070860700d01000b03500301000d50300c0c0e5550018105220b5400b035050034803404180c005a0300300b2010a41580001419151b0201440c1d0301c25030b10b40103405620010110040010700e11450b0b010703000c000d16007500d005c811160188100003445e110002d81500801d510036012110640c9501820305c041519030880307240d46560782a08140c0812000001031100000300040c46544200700381c41f820240340114440702c15480442c440ca0040c00180010f03900491301749 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 230248327 1250 230247077 230247079
    0x90c06090609170102071b030204060504050f070c03110a1505010b030f15030a021c0218060f0402070203120c0a0311030f0a080604060e09010204050310180314040308071119030809 79
    0x103d00064014070030301911507140010702c015402c40f841d1385005c4e00309075410306680c8210b03030500c101602c5034244011144225640840081c0910108441a010b201e200b4240740c042d20780030201c042000b138414a00450b40c002102d058460700350000d00718517280f0841d8050030800045618600703104020402c200d03400383c5841c60002e80420345401c155420002e0901440d07001d00141d04080750841000d12001d40f5803016402f07002c031181100d01404507000030340d04c200c0c801032071903050440328401d100084d040702c10103e82512494105408180c0050007034803841912100609107940c5c5441d005256107241d000c11401a8014810b034100f4445100581c0c190308400d29109502e9503a0600041c00342c4001c0c0d000704a10300c040c1c0288140501d064005009030b030070640c1110050024480703441c0448950030b8006801c18034500c08040040e1050400c01d50f81c64112508600b0039442e520307151480d03132040c0004c49101c4642454840e40341405200c91003610420170708400040d1440e00c440a561040400720303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 230249577 1250 230248327 230248349
    0x130905130201022508101d0a02061608040909060c09080c0307090c1205160e01020c240c19140a0309030303050a0e0106030b0702070e04110409020f04020d090c06090609 74
    0x2a400301310780c0d91482030003020454129542c65407150720070703401046002a0040038441e2441c44500340440001c1409070306038050101440c04207070704451000034941480c12113529001b080001001d082070300560030041c0c055140001d046001807406032452202da80503103c030f504108c03200c50b01550302007007190440e00d400710042221290124120742c44262041030700c1a862501c5d087c0034540720000f000e0202104182c41da2894110900c0040ea66998600b042580c84029401c01a014402c0100700850403100301070102e0608c120304a05504002800204400f400901c261050520002500348a0305c082d1810103001403c2c0c1c15100280112501d00000e424507454001060079203095a00103190660300384000c1040c1512450044c030010010303145c00c1c0c0140310b0f841010405404444d101d42c05564041e022408400d08102400054001308500b0f0b88c3c00000551001c840b502c2d180000c1c850940301e1080068610201e00c2c103030b240b90490f9080310040020f41d0702c0620000d03400c14038a2080d03814603014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 230250827 1250 230249577 230249623
    0x302060a020904091a10060318020607030e060304110301050a050105060a0e0a0f030312110c102007082116140403061103010e06010e010512070c020613090513020102 73
    0x10070003500710018018030711800b01d03050b41017944c000b403001c41c02105240d00440f0b41595402d401c03020f98203801c410703114003039030020310500524040004104403442410418050b402140001d40c05400031201969041300703030021800d1601e0b0030f224041c2d024400e06c4041145505000209925009510804081c400b207a183d05101e60390349080000201514940c210301c05840f80b070300070201d4180701d40e11002c590070180c240c80c00070561710a030751402805200500c0e001403040e010340301801070000c003044440b89260166001100c114000c082c05402030319040c2e42d5041d03c5094541c00c0704290cd00f06143d4001405201d2028440e440c50a0304865501d000302c4600d100e40c01041680c41540d00051008d03140c050201480780c2440c001d036040b6107030b51045d003a20b0f0b034401d0019074140c0d222541007800a50100101c0c00c0100201100c2034010b0424904010300c20541d901181c0b05501c00350b401c030b81d107401d4203104000d141c4e102e00840303620160680b10185c1048856002030342d01d19000e20407011004802139 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 230252077 1250 230250827 230250829
    0x908090409060608030d020a03140105181806011403160311040f0b10080106090605040303050304030f120c2102040506090f03030d050103060603030e0d0c050105030910020f030f010e01030302060a0209 88
    0x20540c084c000303e20940c1d0703607984201d0381c0c24000e601c010304070ba010030b04007070700c2141038072501c41f80c14101c0d000071708803081c014000e100c901501c000c004c0a1020300b944039840398050840030861117001e002c005101800000c01403040614104035030712001d81d00d80000c0c6040c000900b0720314024045613000e48011508504141000d40504032004800d50010306268081a01542c0440440d041f141d5541301c1841098450208442601c16400080e01150301000407600183c41450f418481d2406c6280c68445201aa5155400c1e1040729103080c2c00640c0c1c2461400c41078003036440314032008070f83c4102145041d2174500440e616004010080b0b100d1a0b1018002e0a9130b02c0910450706c25401d080d808209941c1c680c58542c005280307078002900010101d98030825541444d01050b20342e10b400c8000111580c1ca001c0045646902c010071500c49402a0000038102004ca40058007904140180083e100e00e85082d0030040000140e01c10000381500070010000700b5000724065800210525003d40d5554040c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 230253327 1250 230252077 230252081
    0x90b1e0d02030a060203041b06050304080706060b0310080c030a020f09040501061701050906010501030207151e0c020312060f060414150301090f0c031b2105070507110103090809040906 81
    0x9080650140a0302d03d140c820001c059006502c0341d8400c1c030440d00114038400c112180100103008010104800308041408140c640e00603120603840340d0b40c085601c0e6291038040380d0b560800e480380c400340101c03d1414040c00005021148a1002c1640200500c040a400003505140c1440085d805107104001007414008290811340240414015446200c0c4809080314000c080484d50746a0328006c840000c15a51300c24021540c03090340125000340182241282c3c03100038000c003d00c56556112450f114407000c801c601600e40d99004a40107103482d00d03c00c00780c65910841c0140702e20300c1207a1083d004c003000d50350b080c196419039040400040340034040d800460003003185180c50b18a5940301000004404115801c8007040e01c8e88040e0920a40c2148002a401e5038154110b807440e0200171054a00fa0f188643c0c8880d0b00c031881442e44109068815840000320b44c3e041c0c0d521000034800044900c14040c000c42400f038840320a1030208211906e42d21645106d000322408203101c0c0da103d030041c0c41404281c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 230254577 1250 230253327 230253349
    0x7081b01020f0408060f04150216060e0c04051303021c1202040b04082b0c02010339090b030109090311060c0913050402030601060f170f060a090b1e 65
    0x914001c554481c1c0c2c0072401000c9411601c40d00c5045d00c190307800180c850b10f0b408107481c02241e21104c2013010568103000b07040650420182014610065980304000c20014050741c2c078441c400c4006402512044018402501da0081060b4000c111550001001030350010f4004040352146143c9445511400002c90794084103122126074680003190118281104a00600840d1120070442d000001640590400c0744c080184c20200070880c07842180010340600130301c80d1500c4c8145800a00c0c044016205400400083c81c00468070314220304141e03511a030300762440c03046002400c1006000345041e03801403c900c414020000720310307100c803048020540941c0455101c180c00d442501c10510709111003a1898010381070b402c1c810410b80d000d480e410041c500c6154007664004e4041c10260382045815102190240781c098204004a41c0c0072407038000c1090040d0041c1c603060310503036143c1001400c0107003405c036030340200720054503191000000d580d807000f5402a40c0707101c908107045140c1c8100083c0c00c007404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 230255827 1250 230254577 230254627
    0x31b060a081b0d0507030c02010b0f04050c040509010905070e062502120a1401200904020a1107090e1c02210d0c020109050d0203040608040308060a030c0b0d200708 72
    0x1021a581c142c111240c0c000d02e1203074509035420440c7d0142c10404a09a501106d18030b50001d40d080e6845406050503084607510900ea540c806180c03650310004218010026402012066500c1041c801800e0b0700061034804000c04448075420300d004d040300c50340251070009011082052a100500864550040c0f00c0a01c01e01101038421580c554100002d4140045030340307202c594a000d11030311800d4502079203004d41d40d00d80b00456041114071400d000c0254010340c41e58050040071f0301c0c2007108150070460103000d8505040041801420105802e181201100c04282d5095007141d043c500ca82d40092801c034200da0101580003c69001d185000031882142413a03503840d0f08010031240f00d02d40542007500480c0c46071048480072509444101d80340e000728020500010240c50120780403a00c80d42400d40c10400003800015103942d60b689d10b014190095200114090003c9190448040070303110711580d90850f00c80e20502262aa10107003a903201d034400040025101051851051042c11240728141407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 230257077 1250 230255827 230255881
    0x109081902070f060f080c090d08070b0a2a0c020a1d090708210c190b090a0209011206021b0a0c15091a120f06031b060a08 54
    0x3040c4038100c0d145000c0a440c000251291107400100b0354685200310084503d1603441c000500784a51003200c2d01c0b003025048000301c0c0e206000700c61181d591121031700307200c07485113028683d200500e02d000201908028140620361b4607103400d50200b0201704502455034043c1c00320004402c109443c040c0c40075900d07204003942100c8000c20100f5004000a440e4203003001210003888185d462009040d6501c00742d0050b520303190480200c2c0507030103207400d00f074010315046100860306154508a50034a0038000180381071203d01c1d02c1851034140702d4800f202e075400019260151180200030f070041050201c0602c03034000c107011241e611409100c4180d054a100f8003040b201c440e0455600d0700d1165440840880039502c4120030800004c0d541c1d0b182c01c946584844030f459140c10949401329118130500002c2140084400810480b000c428030420b01c00e02c038201c1c20b00b041585051070420305243c110f00c190b0030265241c810080c4805503031000280c508a440030300d08000c2658030000c1140300c0c0d02903010004034100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 230258327 1250 230257077 230257087
    0xd03082a0903010e030f070209100815060f04090b0411040f090b011a03070c2301020d0e07092c0106050a0602010b010314060904260f0d1503080417010908 68
    0x12400401020725103000c500900c00e00100b56280c644034400c40e240510400001c1003004014100b01030350581c0b000050010b810032998907000c0e40c0c00c01c071950900d03401c003281c50740401a46150111110001c0c0c00d0554081040070810390b40e06070140d03005040500a020b07400c01d000c0e950740e101d4005400b5144d03501414042c6090324500700300e46d00360130301803907425140d008144a01c95101c4c0003503d11600d079542d104c0480070309944850300c90706003c5020b08007426601442114003c400d000170040103054a100088044601c01114148070b01904044516420b080802c480d2100054681086032016002110184012070706940100302580c00260400612100000d1803a010760215040c91820b172001d0040381d03440c5400c0482503400300d4609500200706004640801c600200c0c50481c1210220071601c00009006240041e401c81100184e03040350009500381401c00a0244868640000103407048007411550349040b14003441c06100708402c1d6021040c2007412003500441d45030307034015104650b12 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 230259577 1250 230258327 230258401
    0xa032a02010603050c01080f0705180607110a0902040803040501051b0a151103010608070f02011d0307052a130b04020409020d140f0703020a11060a0603150504020d0308 74
    0x1802d55440152680e0080107480e809650141420750310034021090540d40d00e9070b03103820617111504860196a0124055507103500c50361900070040030031500a0306d03280e4100028104000034404030390820401d460050000304600d040010565040d10070908000c0c1e140ca06003105074002050b1502d500e109442421060014814911841a568244d00d072050150810318941c503070841c48203101d078100242180c0e0016050300d100d001c0b040402c41140c40085000030003040003513420003904000201c5070700700064030000c200b420000791010190081c4c1901c2d4200740e50950303222b1540d400c800301340624454401c01078213140c254898044400010f208646668403018000001d4111280c3d0b0301410345419007103501d0280c103900d400c0c4684c00349411440c03a0364680c0380441c00380d0001c0c0c102400384501d84000480f1304030140401c3c1d2142c1100b550014009155080c2480041402011410030070b140c8000c1c1700c0582c603050810040725400d4101400c0030b40b100592007100850748421040310f209255800010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 230260827 1250 230259577 230259581
    0x10504080c100b010f050703030b0306010b03090c03071202090612010e100b01110c2103030f0a180804050d2a0806010801061805090708030d090b15060a032a0201 71
    0x14058200071518041c40d40d0007001d08607602d0000c07007804140c17030306485007009109030010403d962180c0380c0070030300e0305200000c645080301c282c110f071440d41804002c0141c2c03100c08000c50080024218001c195246c600051208a00c80c081c001a0080c04400b0003d1010f4030b03a004403d00d1100403600070072a041d40e01c10f041d92600d00000040300d0072411311f84884841e42c480c0655805825400028040207110941000950004000c0c906e40e0701e07240c41d6150310800014006503100780d10102000926140c03068110702110036603030f4100140c2c808003100708085811541034500f900c80517030780322800c0308032400c00110a06030030309040360360704c06101e10248480a41240004403068141240c04590300ca50f90642641c085008905170042d002d8405a1905110b0300841e070001412003c0c0c8001603107401d2168210fa00c2058641545a1562001c41c108424403c4040d030002c00040f21a072040b9501001940c18815900c1c401c0406448010000650001c520051444100300300b05524607038403d003020740 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 230262077 1250 230260827 230260837
    0x20c031501060807031b03090c1505070b250e030703120f110c0303070327230103050402060a030209040b0a08010c02011802060a0c0f02040f02091c0b0604180501050408 74
    0x5080c0e000412202400307030054440321b05114054210b145020801180180b40140f0242e8100000c0c2c0d03000209070490a1803650394000740d1356003a0b41c50342c01e41000204d1a00c017902a160750800090300d19910126040c2d0340c159110315180c030003042803030640045e141ca01c95820180c440000b1a042002440c1c01c4680d80790750704010f4552910310313140f94050300d89070076080c12400d4050300100510000a44075481004403402070400d00e0500c07443c02180880030420765008400004100352040312240e00002e240c1610780001d00c1c8c00d1003c1d1400b070b80800d03040d00400304005d06054001c10700c02d06664480d0000d10241001030200501d09a031104040d0282040340d440c0005546401b080300c1e01034014140000046030041d2070b080c030b0581c8203002160340099450007503c48080042c862b100582e138500a0401c004003140002d82c94854800070891030506440c0203504900c2c0005140740014003455000e86c1c01003003150001344501d0508458000c80c208028001c01c15403a040c01c100030003e210000e40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 230263327 1250 230262077 230262089
    0x180a0902071202060621010e03040e010602120304050705060304080c0a231b061e03010305011a010206070c140a05010f021305060412081b01021308062a0a020c031501 73
    0x12940500742e0034141e8440c40180e0345181c0144940080303500036100b0b981040503071100003000059481c040c00040341180c1154115084140358003004200e440d90400400501c14240f01c841865030070700c5d81d00d075903075140316104441c000c1602200080603c4851015540c04c1442802981c840004034541181940d480c17006103280100c02c0054028000b00c0041d00d400710f1a004032420100070a071400b0421b080c1c00101c400502842107030f480d40000310000c40590300841c8030390004281402003080341d4661204016000d411940f00a00304401030380d218000202040c1c00010940c8170321740d0195490700748090030001800d690700f40040f42c811391010398010128840d909a02c510496180c03020410355116610500b21503504000800d0f010604550041001d483e844504003000b11300b880c1d0f0030342607821114401c41100d0107183c04001044003401003903402030041c04000c010700d40c0c02404040600d41105150034801c0046954043da0b40200302c0301c21341c0344008044882582c8401c1032010204024013500d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 230264577 1250 230263327 230263343
    0xa020111010608070306050402060412050a0309090b060901030f0f02070c051c0302061f0f0e1008060105030a08090d0204020f04090c0206040305120601020a12030b040509070b07020105180a090207 86
    0xc40c20308606205440a03240801c0c00f91900c2451500d42c40302600020308180d90100381080005186110b100608254901c100e01a040301402c6040c0541503030302c20380c030101d2810b007804a4001d080d40c0b40030440f0200d10090900044841215400300000c180c218003090307505100180d070009020382d521360141155001c035a2802409071000541305240c000b020010b0240e4001c0d4040795500c0340502007000b15140283e035448191390359201d05030341300815900c4a0b22680d07200d0103000d41e10546040e180041d040000c01009103500d0710000c241d41e440e01202c013400119002c68402d12555801c20030304081500240159100c49030300000113a10b600034428420304628250001d0626400072407045e10494064507200d0415884002c80465a00018885811802080c000c1000541404034014501d400703075800040042281003070100b00c2c3c00180524100d90700100c0c0420552048004030717900d01f80d0a01c3c03c6500c07a09105110703201040c0d080e101070750000d040000498082515405086028011550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 230265827 1250 230264577 230264597
    0x31808030f041e06020607050c030c010c170a05090303010b131e050a0602010b0609040c1209030201020406110f120a020f01020d0f0b0402181203070b18210a0c0609140a0201 76
    0x4074500c161402e200b1391025811201c00641198018005850104680c5099a00c1e204086101c0b608460980005801096500304000d603c08130000340f26620002c0480104040d0800001e482d50340c2c001403083d19407144002607011300c00304050001400500c0480071124601d01c10901c0541030f080507010301d60141074250f100141c614814080c070400850083c03e00d500e002851428400a0308840d51803000b072154000c48c100c1c1e00803180c85002c00c820701a80c0016240c0d0b0a02c90014034010703421001e4212303a40301081c0c0360038010780400c01154045040e0450b61340c403020181c00760f060400c5031210441d9544041540d0038045c1c21034000b9a8648091041044444140d05c00c1008902440d20003031300c550f4010310350305c08a0800c46200c0c400d034200d40c0d00b26402d0100903a19000c603180b040744d06007460400e4440141c0304940402c02c205004024a00c52100a038195010300c03203e000304c4070300c0820010764208a00503c0510f43c031602d1000d400409000d40003122807117041d074807520424101d0022b0355180c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 230267077 1250 230265827 230265869
    0x3020d05042102071a0d110703090311060a05030a052503050108120f0a0e031f0e070504090503070b100b0a0e0a05060c0a02040b04020d09051b040203040f031808030f04 74
    0x70f120083e100c0f21804280ba41c2c011075900d100503045403006d1041d550b07035048a80001032908000d440040c0c031941d580c40c1c4807030641c40e2102c000c003100c44415014440a100f503140c1c05030004181e950040301e0740c1c0001095a07804084504012031800401240040150303915007503549030704400d050707841c41400c40f507000c80d17510281ca4180c859455041850318040c0f1069040e24418880310071010f40086c22541007082aa1080795030420b9201e00c056000d5803074040301509a0180999402400220780800c03410140341c40e481c1d228415188024501e4844030009858114140e281b07101074030341144140d4440112403800b42010b40010782562095108900000d642c0c0b50001c103c4030206902c41c003501c102c0029609002c041c01000020591158003401504030700d00700c8d481280202ca006000a028180303808900c5201000e0800041340a00e0041040001141d0a915181451035145ca42803003408012140207203402196085095a0b00001441260303080d0008043c01c00e030b400c1071000e001442e00141c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 230268327 1250 230267077 230267083
    0x2121905160804030807030e01050a0c080f060a0b0a0c1a0405012417030c030a09030201171e150405040c0f0806041707020612010f0e01090b030c040b0103020d05042102 74
    0x2007040c0c00082c04920000e00002c4c0308000494101509090208400700585030032803d51f10100d80490003142d60365000784205a00003c000e0300b000c040602f284460405501142a030700d414000d014201000003040c0d8142441210300d180d4507504101400c81ca038610b4400550030301c106071000e480a6080c20240135141290040d0207641aa01c488200f8003180392400a10f0303084200a11150b041c0024400000e038904c00744024a0f10715910b81d20400100c1c214030000d0281046411280608814002088803110300120f90180045036180310040c2551401c48100c00f200a04490710381250408060004001d001302e021029a02800300c501d035080d85400701e0f542d85400856000c0d1000d440f1100c29241045068020b1400b140098244d501d0000d40c80c0c00d0005031402030380030f6065408038a10030404111241c1c0d07402e001d000c1d003020501070040140002980d4206216030503224590b40c007070041d07041c4c2c001e03030407207030042d00da5a000d10451416052a9030340c034201218180802e001e901142d1800f92001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 230269577 1250 230268327 230268361
    0x325210b04150524190f0902030115020a050309010311071e0302010c051314150c0606030733030f0e06040b09010c1e02031201091a06040807140402121905 68
    0x14550500c050811304104440050700e95903802c0004e660700f4000c9007140d03440686002a01d400130001d60b5a5160044042110740c084441c03038115000401504005080402100e1a41b0f8003440c0108106c20145a400c2c03c0380700f1080c0041c02100d1b42c54a12080e030412130140740c90f01340a07400821619981c5c00080d81d0903c111080b5035500355601a0600401825100d00410b14034003400342c2c02c0300c0100d80004100d40d40f140c2c0c00020b441d48200300b0032155160810461003e0240c4c09000c0d2a20f040e0081050103c980254140000100744940007039040e10a41c00646002111300d814042da080da1144c1c5a101d01c0c068900b0307182c0541c004005034810f2414010070b007000504c3e542c0c0c86032a8207403528090389040c041c8130001c218001003224458040c481c00c40e0f9406040501c400140b2580c006800c62041c90301001340a0046205100c1040f074044086000d0084854040720f5211031040440060000c0c840e00303501d4082c8400c003100340000703220310f5013500020b101021400c00c075545806150740204170030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 230270827 1250 230269577 230269621
    0x10602060601091205010207020904030c05210720030d05090109090608030301031719080117010c0504090c03090210030c1b020d1421090325210b041505 67
    0x250030f8104090300e03035041004600b60140000505024440e400a48038580c1500d003900010204e04924061010601c548140100c81510a440d0400d04118280007400390b200050003549104002c40d00804691140702030304100201030756503e2031f034030f10090882d8000700c5e4111700140015501060720780c4c82d0b1194405581c83d1718000c0d2300f181c0c82c40e615803240b0210700230b80708506802440031041d0f4030007098004280000750340b194036443d03062900b11400940d00c0300c0300501030380c10048024100d13a040401c5509944003803a0116940f51280760580c040d04200780000d411044488070040101d40c143e0140c0e018603000d940705014094400c40c0c400200042450113907004410722000d00015200e096115000c05c4418143c8801404c00c1142004105610700e001076000300004408050340340920640b11030070782c41c012452a01d0317185201d03038400100078083c03100424100d01005200001c2003c00341c0d0896400079101c0c14518041ca00340030b0400101410031041401d0001041c1c0920514169000c030240e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 230272077 1250 230270827 230270837
    0x3100b0f04050d0305040b030a1b030212010509070905130c09060f1b11060d050402150406080105060717160615060c0303270b06130905030415020705040c0c0b010602060601 76
    0xc1408204040f0343c00d040f00441c203000003080000b030302000c0d69020f1031007812907060025003294031802c421034140382c0815100c1058810400d01c2209144c0300d805605440d0240c51031345d0b4541c0d42e42c070155103103900c1d038200a07071114481140b00390540702c0703401c4480b641c4038a40c0c0c0c04000680c0c51000303554800300d83d0f00810110780154410110350042000d03640c0c0080c000c102d0310107248044808141540d0200101074a07694030f910400040d400c042900740618480380f4007551420345015402085250107003d0345205003000292340092203800f14158012013a0724a14075595000b80c441c5a002d500b015004440d02d506016940c030202c41c0c0e04d5086003c6075105d84484030245a151b90071001420b040414461000c1000b08804000151248541c2c1c030a01c1204091020305050003002900305090140c02c031454241018000000c00200540e070484002407040c5501944007501681458425042190400c0c0341207044000640d214044080490085d041e00748240d0701c0d42400c030f0701c42e14102d03032090200f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 230273327 1250 230272077 230272079
    0x30606010f270308030906010f050a1a070c0f060f050a0512090a060507050d0b0303032703040504090b0105010f031a01121503060204030b070305090a0605090f0d020303100b0f04 78
    0x6802890b050742c85603501d08100122028582c4080103440d803640041d01c01403400310411188200c10001907014100007441034120a00d8840081c03081055405030065081c2c0309074200035003034001011f54514680c0031890090300d985521860780201151300c942400149540741190055005104a808404e61652464a0682c031260341050340c0002a1204002d0b1080d02e011901181d080e00c03485024090941d180d558580c0f5002440007510b21850f82d0324885d4008005101c1140c0b81c050704940001e64042c4620f1051002a80080c210f0180e0751200341c01170b061209500030040103501090589000744c84500f24014460b41c00c40403241d41e42d0f520381281404c124001050742c0540007160046100c01001714515094441c80c401110455000700c0326640c0105081c005c002c40d40c0c501e01e40c040d105140401c0b0a2509650065807001400000f5010079074810205d9003142e400d201040d140701d150011100c9040013a40003e42e40d0388103e8020300561001e680c04168810342c44201c0700c08080704a5070038206 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 230274577 1250 230273327 230273357
    0x902031b0c06130f060c0f090605210c0d02030c030105040e01150b090402040f0902301f08030a0c0303060501030b0105030a150807030303021e0301270e0a0507030c0503060601 77
    0x650043c41c0941e5005040798600f0001103180c00340c81354141d442d0341c601600001c8403070050400c00c040d8001406100040c000c03d001003980001144440140c6450740d01c25403190010b00116200d030148182030640004100100704903800021412104159020040118812a61400c985c0c07000010100d6084401d01000f075a400c6801401c8800c0e0020401441c11350703211801e01d06018160f1200c9806600415002d64254040101c0740342d03001c2c02d40090071812800481d021440c1801000500020350300b840f1141703480740035030b1400c0180c40e60004890340c4221845014000403644c080460010f0708100c0c1c007243c154401e018890042c41d042c0c40350f90460f240c5203060340140680c0c05010030110010240000c0d003401c2000784d100214041c1c1c90050b950f01401c1c0803035074030b481e409025a40d03504080004004010400d841380032807070884450040c00140c40404e0310f0151108003a00c01891040c0c0c1c500400b400720110340f120481e031164100b146415940c1041c076449a10071135219000c65000160f000003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 230275827 1250 230274577 230274601
    0x307020d02010324050a09090b1305030904060303020309190b070f0609020d0f0b090102030c0d021810030e0f1b01080a060e070c0308070c38010902031b0c06 69
    0x68414100802d8621840501304d4406500c941c041000c011019030811007801c080c810f40020700031018040c800c0c0401901c405850f801d000e0403500513270403145480800d000003442a2000c000009106018040e43e0b0b0600035500e42050210320b1259041152100e01080464061130407660aa0100790400b805520341c0a0303008400c1d0402d903441503e503421403006a0740d0185049005200700c9130088185228201040c007070000a1069426078070410a11030003090030301c1aa0f561094080c80940d4900c0b81c820440d56490482d200796401080c4403104410540d016004680082e00c00001c03101c031f42c84040811955241c03181e40640380040c2060042065501c20f40000b548103d1400020500c10ba6400907504c0a40303003194100006104000e15000305079002c08400e420480d01d00d00300200100b1038507181c1248102c0703180c004000300c2070b050122000e40e80e00d41803203400320242030800856943e5042c46020354011200d111540300b1125000007184190015181d0f5400c0c0b03030000303012a54481011180f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 230277077 1250 230275827 230275849
    0xe0d09030309060f122a091a070305071202030d0f06030b040605100f03050105060f01030c020d08220f05060f04031d060d051603060605090306040b0703060305031201030c0512030702 80
    0x204a84014170601000e40b41c040c1010300000d5550240382c44228500003844400d034116100104a201c80040100004522014204c50308c100425540c0d070f41981f03029680784c480d03502c0040052409803004d680091300030010348901408001c09000540c02c0308601c0c0304944080c000104074410110109002c1015640803a900070030b4070320000b5074140c94414039440008154001c8070680c0d10b0b50108900e500f0104000403540c082070805001c2c0810b13014000c1d455a52072001c0f681080551000503003039480018469100306c0964024a01c1c00469090a807075044414409841501ca8107021440e5040b020000d01e2089400d561252503400b500418024501c1d4070401c00c0c1e40c40402070003049810255849880d019a125401c0103401005601d0041c06a40d100c4d031021050110a019410b815180841d940354825400ac9108a5039070340c2220a400034002c64101034410700c40070584880c6800f49a00c04c0e81070304d020740351040c0e40e160f840040154801d891144030400d030700140030810042c00c0c82c640e030765 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 230278327 1250 230277077 230277107
    0xa03050312100b04120c0902090631170111130303030b010210020d020717031306201306020f03040501091404060b031009110a02070e130b0a0e0d0903030906 69
    0x1003200366904034480144c1c1041d000b41e001d1184410240e0708100e560098100182100501075052055100c00503481e40145e500350401c90001000c0c0c010041e15000385242203002c450700007007003151204040c0780d4409800002c88855803a09640d04030f00c40c941d106a52034444440589400981184d0f8118054040071008506512500015005841041c000307403100702081900140c03588401c0c03c1041e81101c098080081003041082403090500c5100c51541806400c00c1c070100b001c00480e0300a0f8490490325104945214000c10150075240da101d003040e003110525422600f0a41d840c3e808141c5a100d544121400306d1128141003102851040e1120364296000303000107441a0340762070b03040d401e03070086400200040360760400b07001c00e1440348118030350b51840c00046428282440d4001c0d5480030781d405901d00100c4582d0010360021240c4005800346d95100f0001010341c208141e42d88041c0584c0d0144207654003d414001d2261482100181c08894140e5681452940b4002e002e40708801036a54003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 230279577 1250 230278327 230278351
    0x9061c080d0b032104120c0b0c0321070c15020c010509071a030112020922030c030e0108071211090d0b060321092106070215060a03050312 61
    0xa4011600031400781c0074030400d5980110b50781c100c600c00c0500f00140d1a00040704400c03440800050f41d00c207241070328251442141d4011a0042c9400d000c44e82491540c0302003d2100001602e000302040807000e4018000142c50b400485462903d1b43c890340380b8202e83c80c000041c109101e40c8003040d10000c40104107180b00b8401407034040d0180c1d046095440841e0045403a5115480407c15020300720265482e190300d0704000c2c2d0455041c48000b00d140340c000c50010340b0a04650300402e200c506820350221100b5070190903440c0c00182c41c5805020041520300c2600814a0040301184550103194550b201ea1071594070114681845e1b549480200740350079202d00303440310500000655840b40340a07448083e01030050724040d450a00c0800d0f2402c14516030354180601c81c3c0d40710140000301c00050390000320044400328022031070380207032001804800042c1e03842849030100b8086855000300c0c20081c0814100c62100c0c2c59030303c0000740400100f0304c1c80018000d500401c500d000a11720320320400d41240300001c003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 230280827 1250 230279577 230279629
    0x3160507020301051e010602011e0213080312010f0f15080414030c03041404060b0a080402010507020607060507030b010819051003020d1208100b0412020a03120e030105150906 77
    0x30034211001201c03128100280d5280034501101c42d804951b0051055100078000441c0c0c682141c48400c6003c0f01620132a80c001c114a0003103080b04109401901c1480304480c1c0ba4801810f452048034401c0c0305007445107500620101c0c2c1002480b483c02e09540f94145042c00100c2940000c85d01c9440c02807050340c2101c890b03200154071240c148000c11300000300c44011034456090912031200b4071b000d01100d51013503150000410003110000299458051581022016035442c1d00058419103d0b68000a42c084d000160754420481340da403145000e000306580c100900c43c00000196a2000107444006c1010410030707510006001c103801082e4050948030700e101c0c041c2c0d030b2603011845e980c03a003180403513000b820314900703035507040c0c1c07040c03115500803404a1800551351614164610a1150b40038030381000d1005e007608015501d40d2544c442c000c50b485034031080a5040388000400c00549002c295100c0c0d4200404100550801c2900f8120300f0f0000b04681030130788944e800c0000c0b424104c880f03003450340c3c0c210f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 230282077 1250 230280827 230280829
    0x30209011e24110109050a030c03030b06211302091503070b0d1d0703020d030f030b030a0303050105030c010806030705040b0d05010903020a0b0a020a140903030f19080612030316050702 81
    0xa190305440102d408001400840100c05003940700320f01401c0c0760301da1510389840302046001a20004858040c03c1001c106491418101d026001c0b101d1842e81003040060a400040c0311041c071021a410000c41100c0c49450315051510441010040030b0351001c0d26201040b961030f5805240c84842c20000c0480b244a030340d0f0b9105111a4110b4841030302c040d50b0f140001c282004002c0c0800b0391403646000500002800c8d0340c0000c00452011401a0801c01d03d15070f100c400310301035401074842c3d000c028101c1c1c10101c02c51800902409007401954041d0203244540300d0203500800005005020050141012905000600c0014040445450350102c1811010b201040081c03146030b02d51400703940a41590351041c01c05200e040b00c003904040701c0c588108a10b4040542c42400d00e150300101204456554000030006807031800345185032000340000090f0544542c800c094018010010390701d51000756645c032030070809201da203203089506640040001440c000d0144408440c110032134200f0a08100f00d45d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 230283327 1250 230282077 230282099
    0x11030703020a030c05040e03040308070b060a0305060f010311040905030d2408030403050606090903120903040503070801061a0909010b0d060308070f020411030721060b0a1215030209011e 82
    0x9402680e084c42c0c140414045030900707000703549000425100640ca810b01d1039076505014840c151000c0c05500d200c5000c10603036a95075607a90000e58000c8101c0f0035074103000682d903d41e01000c0c44200d524001c50152400242080d001e034842c401d40050140d070034003041c00c0502001d081d080c1d1b640072a4002000300300c40c04125002d40c0b1406403007244002c42d112030840c40e0039464850040c100610400d2100108a5012030000c1111100d0000001c0c0010a40354842ca152442c0910f400440c0d02d40920400031a41101c1548038000f01c0e4a11041998003108842c65070311180b043c6a2600d400290640050241a5012000304860100e80000107682942c9460340075454100d0703401140d4203020742001c04150700d010300078044800a801d80003451820b0100010b494150034041e00e4002d43c0c032108480c9523010441d8026801031a44803032035a5640610b05c0d004103840d0009020f91a2145086c0089901ca80751070161815030758007800a24940e400c080030980c0001248030320030a80c1e2105d05010a03018151 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 230284577 1250 230283327 230283329
    0x30302071b120510050606030109090501091203020915071a1902070f02101110090305090a0e090f010603080f0f0c010e030a031416031e052505030f0411030703020a 72
    0x280c129019000c0c8076140c002e00700f8550725426880c13141081d0511a09541d51300440741183c04a60002405020304c0c07a0880c098100080c0103001e4140700e41030714132081d80540040c0150a4229614040410741c4540c01039a070248030340141c2001d9440d110460070710715041e5a1074020118410817584446408554405e07680a0a41117503000000c1c0c00b014210b041c4170051031401001420490504154903400075503500e0055010f4034010b407186180070600d8019000c4410147e07005c2e040305003154444a0102002c01c003900d4020280c0700d0600ca10011200c10300c2001c0c10386c6d501101c65440c0c041948030f4413656170480000300c00b64100400c031010030703010309100f950741001c46000510340341c0c081c1990203002c580d440c4454085600e0000200418a1118048207110381e400c0d040000c0d440e500320324203480a6a1984c0c4041e945450403003031020a0b1002c1e6440c804203044002400310100d13440d241101d09001c281c0d120314504c0782ea41d000c1030020754082d4071840d0103000607046400c655540c1c0c0005030a4142 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 230285827 1250 230284577 230284589
    0x406080a020f180a0906140403140a17090c120a0302190804090f06050a061112130b040b0c06070507050c010e0103020c030d0504060b01050c0d050306060d0507020d0f030c0507030302071b 82
    0xd03074103030241041b46a000e96040103e541c500304101d4038090b14040d1014a5a11024818000c001809081d0b24010100f00341e40d503004408541141c503160304490380e52203011600c07070300c600000c0f080c0f1650040000b48680ea07055050340a040c103c41d02c014001c1d50444220400c4800000500011810803c1440350181001086c500421020714210038001c01c0c491a030400000c21081018040e811080014024000002c45050356a03521408040c2c841c450019042081c0216001800190b80c41a810160420742042010364240b522001000e660910509030014016003000302c01100c0d41d80160320004001d80b040c180036117000408035403141550b110021000411740d949081c04140100780c0700704c441c96082030a109150100c2c5202c525519449018164100034000000a605031680000c0c0e40d0902c030800400e20260900200103521354840901c4440005d000800a03545644a400b995001e2403480d214240380c10f44c2034504030043e50204000355081c000c0ba0700d13104103c0a440700b0513001000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 230287077 1250 230285827 230285831
    0x1205090a0605060604060903080c03090402040e1f030b06060d110a021b03011a0603072106180b01050901110f060c0a090801050708061c0c060810050406080a020f180a 73
    0x495490404102d800c007501440c01040c00340410f001c102d030080304030815250410011341c0c4844141e10001e1551280071140c640041c00803a0004644d02040501030091505120f602040083d103207400d012484544005480851034801140d0355044ca81e0081c1000d28000f1070104803180c3e04102200207900c24090040164000c2c0c074150060a0030117558020901e08034000d03c0081c40c0d241d03100c20b081c00d0178101a403060500002041285001d101d815400451203030b0b016001c0e40803400301c1c0000380721b80d11407041075079408144e0280c00340d0790344521098000141c4400c0c1c00c0c110030100448200c00400c4a1a00341e204c0d164a61030451010010070b07100340c00c62074455a82d40301246004040c103006501205541c1c4c1800c0600c0310482e001101c056002c503080d0303040441c0806019513900d143c200c1102c09081c245d050540450b44540c40919288160500d013003044100b0f9692040c00308403030442c820010300350031181880b4010302d80103076000c000e080c0040c079032080301143c4030040318040070945400071001c1d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 230288327 1250 230287077 230287093
    0x3140c0712020310052427130f060501170f0d1b02090103060c020c01020a050c0105090a1d070323180a0b0703050406050105090124031506230a090312120509 69
    0xc01071001c58080d0480030740e01c007c00d6a900c2ea00683d03c58000d50114204801ca4000007940310326a41c190300c8049800c0120031200c450941015002031400b80681f802002e80c80034141181000001c0341138040180c20300903c407075088108101d6a08141c1800c0d03440d49660340910310f02503a21100707107601840c000c98000450380c00c16030004e880d0101241ca5181903402c1681c004020503c00310324180072040030b082050741d450409000800b0005190804041d00071001e6510b1282c030307100160148550955101007180340c2e1140003040c103191702224011f90101304600041c1103034186501854421596004456808078903944400c031084e411070b66000041e964104000620156005860050406540202c07443d4100307480e124100301c0a05220b4803030400d503104d200c49148a54424040e0b28500c1261240550315040c004200220170921000021980400004101604422901612240d40311400c2840c603554549078a14a030508081c01d00c40011034000158005001da07034801d05100300a040b2038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 230289577 1250 230288327 230288371
    0x1005061803070f030213020d0f0608010b10030e03040515040b0309060a1808070201030207030c0204051e1005011b030207030c0e04051005070813060b03100903140c071202031005 78
    0x40340641c2c0c0900d0300c9400820b404c00244c6c03500040340c0f000e8000c540c0e005d0303905c1000610755400380c0b900d00003000000c2c0c542080082c08410640c0510a541c10407242d80c14443e110042c214103540e403900c00e0480c1c0d41c00402c000c0019150680700921001d10b03c003199030902d40c1e01c0e2006005e54200325400d039603541200c030030040782e0800d9200d100b48020281400942c0b1520320f1300d40010500a002d4003e040c1030740014020281401803800000c0e55034002d1090026203800c80800740031200040c001c2c1e42c00ba9440010032181d410010384d440a494040e55849924500c03200d08850b00300c003241d07044d0300f50b004000c40030011030002d08036030380507080014682445081a24060703141031131075100a01d07060726081c20701c02d402c2d42c8080c4543e0860703907410380d00c40903a503281800c4009024181c2d03801ea1520840d01e030503502c000250000071009000351101c0c050a0301c02010752080d0311444c03850705119048000d06014048051444030b2000f800503044030403403c0c0300c1c0003030021030380d05490500071160180490886 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 230290827 1250 230289577 230289583
    0xc060503160f021b0d0209010807050111281a090610120f0212030c250e1005040507050d2d02071e0501020c1605150f030f1005061803 59
    0x1144814501050380d0150208000e4a95041d01004201c48040f0341403013400f5030b5444524042150000c11540403560b403451129070b214410b100700f90218a10601c50405904082004030698402c22640780d107502035400c1e98444010040c00c2114440c1900301c100188540c150032941c85501100000d140b2130414071110022070303c8a42c820007003143c00b54140000a141e51034451034143d4151641120346040d8603015046015072141c0801070301c100c620701400102031410b890884074030320b4028407209403504085107000008a4003505c0711859011300300500c1c240340d405903070700224a14000381000480c1c42180d0aa490688500d800300d40651119181d0382c00000643c402c82c00c00c90000c624098450703444800302001d9603041950b900700c3c40380341c3c42804400c6d0111918a400c45003a161510710500002c28202214081c0d40d0207619000560446400c48008546400f00540c4e004c50550742c40e090044081d1000601030740301c050850310700281580b80d0b0310180c4480f0004103907402a41000c5001e241c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 230292077 1250 230290827 230290861
    0x5120a33140a091a2206140108030408030a0804050109020a0e0708012301110a0803070809010b06070f14010b030d2a0c05010807030b190905060d0b01150c0c060503 72
    0x101040c500196140007544140701d4a4480401d58400d4130b50343e44a0722400c842041300c0810404082c245000f4008009141d4030000281c001c40c0c4903e003450740c0b0303400443c1d40c81c081e80c010b11045600410104104c1390045d45c41650061243c0f0000c90703030303442d96070220315144001e6200030795150140091007506c5400100c11800340c003009100c4203100e031601c4481d00c3c550f401c802001c0d0600800d038108500e5140c0a00c52079000d160000240c640c0c03414000b03002031520b2001c07101c101c941d51902c2043d003803a00e070050840c0c04c4a60850005a013510681d11038122521401c4003d10750356582d520700070015181070006500346151611289502400440129403070003040214900d10441d1032460303000200c240f00c441c8269542840d00f030641e40d8400500390f00400340302800950111600d002c250044402c100110140c4070100700c180103549030b01091282401d58420003c0c0310549840c014000600108104c60b4080101e02c1c0126071f1310625264550740f198550442000204d001040003911805004481 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 230293327 1250 230292077 230292091
    0xa050a110a020a060f03090b091606030b0603040b060d060f020a020f070503101d07120201030e21030601050708030906010e0f0c0a2f0d0201050105120a3314 69
    0x3103031620071940010000300c00c601480003800641803042e011188282d0103841c034140c0c004109036690a00e001c0055860407598043d40e40c611008102045030b0b44240241079240e4805803a081c00c3d034607160b45421108a004101d00d0300304860700c014001041e078501418102c3c0c144a200140d4803203414100074100101d009002800e507204010402460302d001842c00100c001031400004ca4601d458441e8002050204080880388610130002c41d00c0604207640c5c40400d03100341c904100208241040c2c64403026041c003911081a80795040c0c40100c48982c0045d07070301041c1450600e20b0151290788400c110b800540d1080d000d07a002c00014002c02098003006038000960040d480e0051070281003915003440344070409400c000645034900c0d141503800e404030a403c0c0440710032604403401c031103100d591501003561000040d802c0400010740f504214011800344001c0d2409024001c10503202d821080040d200109a8601e80400c03901207007804a107113905003507213000c0104511800c03cac0c0d21968101c0241c488 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 230294577 1250 230293327 230293333
    0x609052509060b0f0304020a031a0a1b0c060b0111010c0c050f03030402062706070b0a050a150501080603030d1b0e0405060619020f0106060909110a0c021e060a050a11 73
    0x50010500d400107032034820300c44441302582c13a80da51010500031402070784010801001c070403400c5140301034140424810b04d0419402c000b40c0d82d1907280442c480c80e07507018107004a540006d80d0008501c0e160840c2c1340001060400340d420b01035503100c0a00311014100000c00140b541014001023080602001200d0b000c540c00450030b600741500002c1d003d114201c54004021208281465098000c401201140c44014005034a07a201810014510001118020a40e40c41c1400041003071030765120b00b683c480351a9001c13803040d5013400019650400043c1005070b0503c4180b0411400103c1405440e05c1010656a0742c0800c240c0050301031b009a8030200d419204604043c100241520f4031010340b00b4007001040c81b07e0402a040700c090303050000442416840754207080d004541c854200d604041210004401000960300e070000f1489103000d000c040c0000500340105410161400c40c00340e00680704080094004245010f0001d040e075841250b00f000811800304844020301d4100e044149032140310006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 230295827 1250 230294577 230294579
    0x219020a0608100902030711060603061621150e0901020a050708030a23100e100b03060312040609030b0c090f01080a0b040509010501030b06030714010c060905250906 73
    0x1148081240200000c02c6041030001d0020341850080708014102c500c8215540c0c00d060400600303032001034060340780c1c0c0d100d0729004c1202c6050020b003182c4244480002c40c224105420001c4980d054040c1001c0d03107a40c0e10130b80704440c00a003845034950000c465400554030301d00e005260201e2410042c0000000e910500412110940000480355a264007030400340d0340307644000c0e1003001800c500c4030614003203101090000410841021150058004110131652295541d9645910351030894071083ea12001c418108100c00c070030b40c003a5420400060590b5000007045000c2441a005a84528001155441c1c2001400564884540c0101d5581c052605d8800d484001c501e000141c4865181041096400281d4074031140d40138080707188000f00248014101a02d91a010700400c0c0829545441501d020544601e40040c0340302c102c500100e01203d030525075400546001828100030b58032161a0301008001503014000d6100080c40b40000e9003c481204046e43d003120110b0b00003006c2246031500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 230297077 1250 230295827 230295829
    0x60507090e061908030d05060a08010e120309190503030403140304080711040209040e0f0f0102030708011a12190c09050315060f030f07090e150103030f020708030f0a021902 76
    0x4255502402c1510300f698685030000d4401c0700c0144591102d682c50202040c00d048400d260f801a81c0503100445040b103003582c4032900c1394220f94402900c0b1010741d0044a030710000d03004441c091640440710300103681803880e10561201c183c0040d090112015000002000704154000c0400e1003141c0202c8230440c11450150354961003803190600c05440e80743c51101701c911b9661039030110f400c020800f130014800e80301410030360340d48e41c0301a03046403006001d40c001212007040140b083e01c4c42250140c2c3d803c0026440c0499030131400c10071602040d6018801c01024014041031151940150040d844941e044100100780e0310031140f400c40340200b0042c10000402c01603a00240100071a0100a514009520742e040090310030031032004540c0d050f004030025285d1f498004100841100c8013550700340401c4101403039036a10344c031001c090130858608890041c8046407050500c4061724003640100c94106480740f41e41031035a042102c94010210000a04000aaa051100d10041b40e141c048000700f105140d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 230298327 1250 230297077 230297099
    0x30a0c05061018020318121804020f0702061b01020a0e011701062f010c0915050c100e0a0b09071e14041112090303060a140d030503060a0509010806010306050709 71
    0x10412400154005c8080350400044050a0540305040e200300e49040590083e20101500001c43c07003000d481500c0c0c02181c40d81824001c44401e00590116940350542c00d5007084842e800000514028181840800c10340d407000b48000c2260900e070780c80700364900c031140e0001840c10102c01c00700e0510380040001081900d422039100003841c1c001e484104e80b40c3c42c0250324015240c0030184c030307000c1540c2480c0c400418150040300a8080d6101d59040701501082e0150960303042c8588000070885034420b0350f094040345415031064030069401e00c00d4640300501c0b510750244c40301060700c0d15552900009420011312100c07a1074100304550701d80c15038210500c1e28246414800b5a0501d441c0a192104943d10010031a20300329042c048602d005900107082c00c0e190250350350411074105e030207003221100118140c01c3c030044007154410003d014080e070342100d0b0b408403040e0304003821403504025808001304541d61002c4096000e010124010984c661442c01c0003001da44010703001c0018404440414410103280c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 230299577 1250 230298327 230298359
    0x3061a01120c0320070c0f08071e121506050f21070b2d1c09140f100b06090a03030e03030712120b090105060403020f0a08030a0c050610 60
    0x711001a2480e1004819800740180c120300707113000400c04004d41d02242d440d50282030590302459079108025100e401d41c030704072080d50082c0c17901130380118000c01980b00030150002c02c076120007003401c0409540340442c0c545104140c5044484444920402d544036121b4406c1d08014001200d00c3e10f0410484004500c210119520f120101c4103203105e0b954144a0806c0360300000c0410100b1640c1d1255a2030061001080d540c00400b0903000701c0401c44051800e4100b036403803c0182c440d0320081007140711018001002032040403100c03000c01c8452142018014040358107080d01d40000f0700368140c07112041c00c1c12694400c520740c3c0b20f9141817008802d240c44003140700080d2985400d014012146000001f4072710300400034000d1240e0300c0756203001b0501d40e00051030701500c9040c010074010003160508114a8490900600d60040c8083c0410409407912007103c6000c030380003800c4d6a5815807146522070071607000c00c04c0072010443c015044070410004200341a4400f0320300c00340110081c141000081307141d040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 230300827 1250 230299577 230299607
    0x906030f050d0e220b10020a0611310314210301030506010e04050a02060325020703050619020715091b0608010b0703050909090c180606030a0c11010f0603061a01 71
    0x4d2000d55001031385455000c2c0014560081c000781c03070360855840c020355900505504880300780c101400c100603000c0c0b54080d5001900070f100034000301640c0b5000b40040920082032080304c8410f034000000403450003c0107410815072400a4a203c1c3d1000321034500e41a07100c20240c820410410041021500104000b41980c0f44140c190200c1d48540c1001441c10350145800303540300d400081070003039801c4030b40c070350303520740342c8040705850703001c00441020781e04c1d28046d10010700660031840c001540c590b001c900d19407203150140001820800d4913240c50141154082105068641d0303641c569003488160301001c5007804120a00d00310407810028000d2220740180704503030604c00041540000c06003e03c05841d0000c80251506060f49003400c03810b039890410101d00c90103040740e10b088050f0307007004298103032189001504041c03070340d140e10340000002d090201229003040030440549029007400c0c0207000f90300100c0880032a0450442c2046c50464450030110000d41082c1e40c8820b0050340c2111f104009254 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 230302077 1250 230300827 230300869
    0x1d060c031b120f03060103140915060111030304060c0305160c060203060604050301020c01061707030c120201020321012310030b0609040c0c0b10050d1502040906030f050d0e 76
    0x250000d507462828001c2410500401c80c08115001c07034406040240d0702c90582680c09118030b00340e019401d00b407103009503918201038000d030f6200b188501c0c23003860a0f03400c010189010034109010403403440c11900b0a540440c2d0194881c542141d40c6589401384170341200c1d0590f000d8012240125001c0c150944088004142c00d03004000600c190f900ca205803801810060029941d0b81e8032380305400d00810407400340c02c00031211651002c00010300000c0603000c1c0c0f9400010542d070603040984800038110640710490462008010103280c2c102e040aa05945034100d8603015025410f10220201e4100890352843c0c20140c502d08405030740d51824131880e4807000900b80000c04010000201d01e0900c200c0300343c0c03600709003845880d41d850b50344001d200445a008004013042d0743c4414541d01c2041c29248107040c0d2140401380e62401055565502c20040402c0800040c41d059076000b000c001e541941c0c0c030a8607450401101802400414003000d00e440c440707442e200e00c0c00d4501c0b1000070b02c44011a0708104170f0a07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 230303327 1250 230302077 230302117
    0x712020a0602040b030a0501171e030702040c0804050d03020f031512010e1005010b13060f02032811060f0112020312162001020a030804030216061d060c03 68
    0x9000344120680250880815566180c0b10144c203107841c2e000703484043c00e00d4076100c000a5114070401e281104405180f000d080480b10081c051030080d00d0000d0040968041040308134016501c1d445004c07031440380751700c600c0d0741864241401c90410b50b11991446c02d050040015406825044040740c2d4003503d00d08603900c3d40d00b07030b40c2c001c1030201c52074285200d0998604502c0d165130347d0001548900040e00074130300303002c6a80c0b46c108512582c081d14100c20203002e20800240b02c014020141c105070140140b044904001d00031104c208901d1212100b10030300f0318000500c94000d42e014001c000d5103003070440203100074140480d04a000810510491541c0f6050000c1801199020710106c810108008010ba889030710035824542e400e4003080046441108020000c0c80001020040e040d0030801600908480701103900e0545092000030030450460280da01e007461800e10032081040940b00e1179580d0415020090301e9203013100100545e103440b500c01404803404030395000049444c4020344070b003d405c1c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 230304577 1250 230303327 230303363
    0x31b010b093402151f0f0803070201050f0c10020904051303080117010f020d0b010906080405030405090a060305030c10060501020c0303030412090b0a0507050705010e130c05090411030402030d1407 86
    0x48544d0740042c440318800f07014003030803142c505001c070a0380084119804600340e0728070344e01001d401c01c0c0c0700d00141030700140070580141d0300540c0645a118004a1000e01d0310001c1010741e03040ca901071340400a41c0b030380820040240c2c2094031407558080e2015511040b1280c3c580c4015050100522413100700c040d4814080d00302ca8001e40000942030314035a015502e41d50380340c1c0d020b8050081d803e901c900054130031900080d014416202c1600a64020001d9440c05040a0500102800042403d880d0700e894920000c0010003c000a10803540c0c0200540140521540e24070280e90050744500d0440d40100b0300d4207810b40e808000c981e009984016404408003010f041500c0303002c0c460f84409142c5d0000310b0020310300c582040c01440c809220f803003541d6a00381c4820041d6210325071706000a41060a030352072180e14050f281d0040071201c185003881424078003004002810745800e500300148000004c814001181020000f441081085041c02c480c0c41c4060224a805406034080140c080380e48d441c000303080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 230305827 1250 230304577 230304583
    0xf1413050f0706080f0c1e07030e06040602010c0e0609150705010b040504030908370c090f0605090a051e100819030f0201111b031b010b093402 63
    0xe841000142c0d071140390350b2500540008021107070512607860120000b150000d42c1000c90328203c9441b980c2e9030110a01e4a444c2c146a00120030441c20301000501040311035560f0300c0648010602c0750b00124110081ca2002403000548103085401818207008100c8035940714140e80c22070f000c140349c0b25501e41e58030b41880b0303016143c2c4005154215150070140320506900c405070406075a031b890200c2d045004000340301c0040301d880e00c00030100c00801c10100c01000c6400ea0940809a0042903014403080d29961250111200070200d810780301c2c3e45040c104111300b020040f2583c011409a801c10807841c050a4680b8440d100e520500382e101c890100051940d4242d01229000d09010390864403079001e210301000308031041d814190045000701c084050014414010850040200f00015080201000540701450307411403031080540001e00400360f2072440f80c5032851001203c00d0010078110304100c140a0900006000e05074960b038585017440311060702e01440c000f080c900c42407564601003d001d0481c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 230307077 1250 230305827 230305843
    0xb121c0f0e0d030e120c031b04090b10140f030a2603010902270f01030e0f030c030d0c08130213090f05070303021c17071404180f141305 60
    0x140c402c584100751402d1562100100000394820f41d03801300d464601600842e43d4580358914107a16034000100c0700b541e09260984400c0380301c2c0c00380c07010818140c0d0b0756494040392022105c5030301a540c400400c0260760301d02d49e07054030800001d0702c02d0364103a070300e41d00805c1c3c0301d000d554005020462a581c1c241c40b024000d4030f04019822200400036260750310f4800000c0a54405141903000e03c0c441c0c40e69108055034102c4070303000e5220040240001a007030f94010b4010340b0a2440d480b24a010701148a082c004e01400180300c4d0090400142d651840f102d482d200c11140074001c80020845001c0400080d510b9120003044440e404a6515040f00000308070f02c80500300c040401001101d12030681c00c100100040c070741003030300d1085d02642c0e01400d4241500150021840b5078000080c5c4000081840c00403c08556030040c5461500e1044411000b0b9403a1460303110f5803000c025000070b102850f2000c1c00d540b2072030013072085d00e41091080c81d9282408581500c409081d220030300c030000950714200202000500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 230308327 1250 230307077 230307079
    0x31b0507230907020304090501140f01211418010b01140d110a1706060c15090c0630160809010621020405090307030903120e040504060b121c0f0e 64
    0x82c58514002100030f44940040c0700c0c040c010303800c040000c00e4113100c051850f5a071b0840500a0304070b29080d040112005585807008038400607004480300141e03842c0740112200e803000c4500203800e40c1000d007080441d882d103000b0540b1090349000c1441c170260780d1012006405888601d4600d0302c0b2800400084000e0090540e50a0b0705580001d2041004d6000211101c0711558060213020382c0d5a10f13814031169100707800400320f15810015080100e640300003180c0b6000192002202c0b07010900001003034851b0700c120102f0348a101d1036001001c2294441790904141c2c02c10b908007807401d0924060084850b00b101c542e44083c42400400145000001d51000c00107082d07000540c1c0c0400c5001001050002c1c2404060340074500300f00000e02061400011550410790541d0740e254800d24680310310803d00c1e500c80b000b90800540d034101d0840c540e00c2e0300500d40a030f40684400600d0789100401c10aa0700c00101d80d110081c0c006090a4490b19494449520a64050304150b402c1c081c4400b000c07503c00d0071a042035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 230309577 1250 230308327 230308339
    0x1303050309150f04060f0507090b0c070504050c1c0b06040603020a0509030109060b01031104030f0b04050f0f06060103050610210209030f030901020c01140708160204090f031b050723 80
    0x4401140700203000c2c06a8041c013410420000c6c0c4603d02416a202210003030f020590322801006814030000051000341c101100ba00c0c0b060780c82d20b0001e01965402e8900c0f086104020612080c0100c400f0000415070585001c204210410784011480c640942d204078801c0c5540850844813590159084840501d40107000b00148451494000005d040407040703070340040d1600640143c8214a44112410f41e50010034108041205940300d0410300001441281c80b0300400f140b482e40c078203081101c1e0103040380981c050304c200c2c90705000040450b400101414880c1003c80b01c012042e580000b58101e0900c1c41d46901d4010b4142058044040d02c29805241e8040c401c480c0c10420100c00880500010300c4240c0c01d59001d115407000456071401e0400b00300015440c00c0010400140322200203001000b411a102c04099840da00024119130204a090f84e0440820105000709580140d4052100c21303418000d00784480300741c40e142d503508094080c84111a084100301d03205815186e100d810503d200820b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 230310827 1250 230309577 230309581
    0x15070b1312050f040b0705030f03070e0f091302040c110a0c090b0a03050d05090a09110a090e0910051003080a02100b0f0d02100e0307090e060906130305030915 70
    0x3030000340d030000c2801691892240707019500d00c1e07407088080381c1410071118400e034101400c0c4545590645d0000d90112080d1204210442c0007000030340255200c3d8180c0d842c1c200b28800c0d42400d00018914042c2031912910b0004208134030304c0f1691480e48503107901a9400113407400122425180414884074440881c80b900d00c04604001e0f40d0f025080995241800910411a004060002e02d40c414040142540c0ac02e40006008a1040e005031400d01c0700180503c0c050b0b84d540c14a0ba00f02c13140c044c1c21082d425000134459103c290440850001042c54480d03c95480c5000c440c1c00e41c841ca8080d40210f80240c50b100440c50414240d04100701540c0c00c02c07072a0756170311184030000e59541a0040200e14442c06c003241c1020b1460490b5050300c024801078110580510b4076400c021704900c01270b01c10001c0c8441d0304d041d04115242005010082e0180100014607400c4c9500d0711854054000c04c003e00992020b02004044c0c0030594030612980e616040440d229242d400c9024100451110056150351900701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 230312077 1250 230310827 230310841
    0x220b010902090f03060424061a090102010506010c11100201060e09061609030302060f0604021306091a040f1703070b0a060e0a050714130b0d0b040b120a0215070b 71
    0x3005000c042d42c2218100c83c660450801e054032401c1c03ca50280030f010640c1003810f0240d4001c02e011110340803909000400c10344820241a403200010404d101880740030480500c103580900c50b090b040402400e1105541c6c2c0ea683c0e8500c2c01444403c446401002d200800d910058001d400c8500980300d03030500c1450034a85500c0e8596038440840e00130b00c40c1020030444c495103e000742029010740342c1650140c4195038801d800040111000f4141c07503000b0b80d00300301c01e0b1070480303c1c1e5506001418150350b44400d901d00d0044060380d402900d4070180d0020741d04110801160441d05404811140d810040c0103c5c4c6581080742030560007204006070001c90074100f00121100254058001d495908402d0390083e00c0303400018080794401c8441c01e01244101404e503140c00703200c4002c0c4c8420b062128003010410340310310031100310b40c00c034402160340d6948a84421005242c14000c0c034000c03160270f850100f08980d2450105654800d8544003a000700305400321240307925003040880301180c2c0c100b0600c40040c14044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 230313327 1250 230312077 230312081
    0x6050f09130f0c0f0c110a0503060f0109060603180b0402060f13180e0d140c010903051305010f0f05030a02070b0f06010e0306150906030304081905010e010203040b220b0109 76
    0x211284039545401848500f40d03001d991000344522182c3c1c1d9582e100c800c82d50700c050341045441041c5501015407c0c00107450394040042c1392040c02d0561030b1541d19450503000d0340555100c1d4001070103040c1031a0010704a00748a000c14485160010428030303464030b40c3e002040240c030402e00301e29410704000503080c0d040d40100803074504039101e14074030b6a044003c1d1040c0c00c0c00c030341d501c0d00c0f42c00740c039009034000d030a509106010261054440f084c2d042d103054107680340c450031500448001c0780030070404221080442c041d1040c40c00244001c0c2000e64543c00c1c548001440c82c6d10364901c880c01d007c0c002c4041420351210368143c4030314030350000304072800341028001424100021a42d0078001411821924506d0401168140c0503862946060300d034200d80404004c6044002808184c042c070080c0400a85001c0030000c850f80c5034001003c01c100d04050303040003130a6803003000ca5021180e0040050000140041001517401552301e4010344560044e00d0854070121002400988071202d148008201c0b00181d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 230314577 1250 230313327 230313341
    0x121230109081c021c0c0908010e010608012316120204030308010e24040b0d02030307061401060c051e0309130614040504080304030c02010c060c020a0b010b03060a06050f0913 77
    0x10411160311920b120041402d170b1142200d0082c0702000300c0010130364140c054200340c91071004d50030005c40d9151141d07182400c41e0707000b200030b100a0391521010400908203101d000230011407814804030704522501d04490040025248c0191707404c5050340390b151107100b95481c00401004000071741d600c1740d27a030800070701d081300a0083c01910101200412402407003000203041e4010000605103030100200c007000006c0501224041d005010080d503203005a905000900b03a0340c2c0b04110008a01648034440350280c5816000b1000340240310f101c20f40840e20028050880300b040700da1460101100b90201801d50250069042d0014400d40c7e900007500e00030340040d000e0b59849000358016800110401040d980240c902504a00e010004140401d2041c40c03665295170045c184201c1045503a500c0380b0494010700700240040c1c11202ca204c0801040415050040900c60b046c035080d424481c000170001c80f6a4402c12040c04400152000207e0b0614140c80806500030320900032010402c00d1200a007000e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 230315827 1250 230314577 230314597
    0x211203011a03090a060b0118170c120a06050402060706090c08061f050f0d0f05011b091508090f0f010f0b01030905060403180e01060512012123010908 66
    0x1c0c14004040a907541c00542c1d00c109002c10050168103440d40700c060040010340fa140b07040200000c05465018050000840200a0b40000261613030200000320b040000d5411060f1081091600750400300400181010b201e68001100054944803840012064400d04400900700c17410700344000284041e8401e0b100444040c14103480c1180e5850800840c0b41800a0f0b00129026510906020300e003403882056594a001400e2201805a2074071000e03251016504100c0c0c40b40e449000c884660454015400c54a054900708241d81c142804d0341daa500b22000c1504200b0020000001031505c001000001a21a002c0d0141d540704201c0c0c080590107403c07040342d0a0a80b90900344080140e5110780700c0c1c0d60b01385800c42c01520040e200c699003120740958404040d4549148001d010a100e14000005402030100307031503280c0c1c0d41640205040e19404142d202d40d00604a07a0036015425240d446904d040551000c5c00b19505448400e8560320360401c0010078150358a401818030400c15030500401e0080c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 230317077 1250 230315827 230315849
    0x604060e070f020708030903030703050319020714101b0c030315151b2f061204020f0916050d0e06090f071502100b040905010f021312020d0221120301 66
    0x905c4e01e003610713603a10590484540617030080080001180c81003001c1c2d03410401c42c0110342e50102600c0c2280042c0e800c80b4400750390300800d210400f4103d00c0108409a02e0446e042c509010301034404901c05180b413035a021803000c1c46501000381003010b129501c1401e1040c40303e0b0719203003855110780400480d01040c003040d101050b034a048110891400d40c1c4600d40895216140791a00841e0303444d0040076405003d24505d080b852040d50011030790781c40028100c0c1d1b10401800c119a031826004124200c25200c00c4180031302c0b056814091a80c440101a000c0003142d424081c0c2d5460501d00d400e4006c00d125200e0010030f00422040c01407031b120200d03241c2c540e004410116201341d80c0707840c119440c0301e486031004800742e0b0048402460030501c6800400300060f0040c4000b540c41415121182500c004078a080e07205640010200c1c80c4107500e00f4040050a403100c25503803400000d41c0405c001d44140b044c041d21441c00c1c0c401030007050340c0300025041d040d828041a142d400402184024150f0028018010014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 230318327 1250 230317077 230317079
    0x40c060906030209091302011e020c041d060406050c040b0408030912030309150a0608030a08060102070603180b0606070c030807060f0c08070c08040801021b060105040c05040306050604060e070f0207 87
    0x90b2181c000d650840710010a4101d003500c805500c145040c210200c101d05024111000c1c0c485c41400104110f0700c601c03603802030720108034000e0421080f2100d44210300d4074641d2030216210400300004426034842e511240000302919224245d86003801580d1000741003080c0000d02142010010000d44054042950402907200c80390318200c1d140c1c0000c40d00201c0079071000c08425002a55484c1068011640c0000001c40c66201c0712040d0031540002c0c0d0b15000b16001005000035940d0401c0480020040c5180412070030550440d0210f0348031800b5070251501d04400003140c40e9558860465a10304e5009005c5501e0990301c1c900704901d07810110096a0162801c2221945a4928060300c414800c0301c0c1d403911480d649030541602e07110031110050321100024840440c881409200402c000502c05c41e0f5038055504070340c4020320b04001600400e00031070030503549200d030542000a88050740d52250000c80c096958a02060091085034404c0c1d00c1d0302104021300c141d0a410200034034000c0c400b030342661451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 230319577 1250 230318327 230318339
    0x9040c05070b060a0b0f0307210c08060909031e0903062409040206390a0212010212010611190803090c030706200114040503030916080304050d030c0209040c0609 71
    0xc04c10b4416a90445010880002d0018282000f10741c088046d003000c50400030b60120b80300562030f48a60030021070783c1e111091000c440d000814a54070203011602101341d49401001c00d40c0f00e014800d04401e10040f040380c1c0c0540c10380600c0c2660005000641243e14502c1c2921494510400000c683e2400207520b4009140301d050200b0000c3c400c907006881107240010484011040070307010300c0640300f0355980c640d04c003001c1169908507030300c070044d080300410143e2070900401c0036160f420b000b0760055a1040160305288140541c07942d0448100e410803080c0600714054190610144514400c601e03051280c840c41004100c070060742c0180c09442c21101d03402c05500174156603644602a00010650070004c8000001d1006c03c00c60008010400100b541c04403c4080c0b001c1c04403e4604441c1a00040104402100304010590f01c480c0900c03107000e00586450001034030780c031850107030a0086040002c07040c02d041c01820034242e49503010b8443da4207840d142c1801c0408100764000c7e00000f400c080000101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 230320827 1250 230319577 230319589
    0x30d050c12090106140d060209040e060a11040f17030f04061805100804080c1f1d0d0e040903110a11040507020c01050904090c0e091b01080112030809010209040c05070b06 75
    0x1502e00d54000c45107001689002c109528000c810207d80700f580800881d2126103a0707009400b240c02d0340c4d0000708500c1c142a02610309550201c410040f00c010184804c010108c441c01480040f660b0070000d1820803c103040e4582e06510420050780e408007400a000901d295000e803c4441100c1030400340507001d91220b0400c039000200d80b0803000080d865002080204482c031004080115034034007110040b5000f0703440302909071880c19441a519648110074880741c00c40c40c03905e00038110b240b0301505010b0012440a0180240f040d00c180c011035883c2442c60800d400748088204000b184022141c0686080c03070142e40000c8400ea60502032820540402c0c5038500001d40c0310031b0038070161592404d00701407101348401072412040594144d1480b4100081c110205800b041c015402a000b070b00707081005000040b6000c107084647c0d410084050010803031003800c030703c103841c0e02e6906140014058a0340100580680140003016a005107040512844241c018004014080c4588ea400400303650380070400c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 230322077 1250 230320827 230320829
    0x103031806111f020412050106091503020306010e0601030b150306211002180405191107080a050a02010e030a0512010b07020d0f0f0606091e0e0309040b03030d050c12090106 76
    0x52a80c0444000c11203a02240203c0c10300c1d046032040141000c0d80c070b529002c04540016410787d01659100c10500c00d0028038001c07813134000040c0c0c110080451460f40070035030740c1c01c0500c01c4903100020000410150fa00c20b400c000345201c0b00421400350a06080040e00282d8419140c09100b0300c09c0e11810f127001075030a4403100340700f01c00b031001c2d004888210315040302a6101b550f89100d0350000c41c600d03e401c0c2d600c521840e401441d4200d946031900d00070360010001c882401010800074042400130400082030f041c2140d401c02581d107881c4e82c444e412644168003401442a03161460300011800c403c115038082c0140035103520011030500e060b680d40c84003078142d100b0550b0107074020102d100020701081095a510a100e0320502c00319078000020b41b100b604841460b0001350301c0c0c82e02e40a03050300114130030310124440340d880c4000300015403080710150340d00c0c8030710303590300f409a902c8981d042c680d944c0c01c1c4150380a40b0034a030414482450b21075150078442d8014581c00400600080c0800d0000c0c8e01407090380 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 230323327 1250 230322077 230322107
    0x6060a0602121e0a05030417180f040221150a0305030a030903020f0a0804030303230105090606071a010306061d0c030604090f12081e01090506040905060103031806 72
    0x6441c180e8941072002a48402100c0d00d200d01c803d6680455900714200900c01c1e5215551019182d04040c54864024020a02d45014200040c452035074102803640c2910700c0802c0c100d0780c42001403000c0c40820040c1c003c21140f102900400c1c2c60070940c0d1381400c0f001a1207100c0c420f0036880841c103c0001c211480c8446e0002920a6000f4407504007000c1c0254418558039011340101c1c0d684050380904145826803043c41290420404a0f04100305905402844261010f145004882448076842001d0110301407003054440c00618000c250f4648a00c000c4070304542e045a02540c10301e8821a0050400a003072008030749140c60a440010000f0800c1d002a070072030001c00f00310705a921401202001504041c01c000da100c1d588481980000e0042c00c041d280061164109400307950750b00c00050440d90b0b00401022840100484200040300b8160b0014103698a1b4400040c4948074040030400628640500030960710440d40044107151b0070251074082c01301e4403408101429210f400c2100c12400b40103400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 230324577 1250 230323327 230323333
    0xa0f060303050f07061506020d080a0203070f12020409020a0c0b010509090a030c1110120b01030506030a0f0804030c0816080307150c0c05061006030b0411091504091d06060a0602 78
    0x30b083d010030001400e00174040c62001c40d00c03800c0c4441408580c3d9081d0f103c2000f60b801f04071071821041d001203019900c0f4142c040118150724202e900035100b40084403802e170802c00803031021180382d0481c0e8107031409058030100864543c045080050b282c0d0a00240035104410b41c080005030038940308030003a100701e60450103064848281d9405591003d002c040840e5280e81d4000022065183e01404200142c3c40d0f50ba01250f10060002c0307201251030075415181014105030070400c440d10006650002158000520000b071007290500c6078250042c2e030030003007522920550004498030300082c0b1010306e04902d40744017052035894100fa50390f842103582c0104018000392400828505c1c81d404184014003504103844012482e40d00e00c1d080042c21030340c4004562621006110040e454418001c441405030350400410000440c000c1c10390040090b8a8881d03411070440505001c0020b0948000703184048041c4481c100d0200d02032400008082000d00c070384a00c0d4001180d80c0781045038481114880d0300a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 230325827 1250 230324577 230324587
    0xc100c260714030a06080d08160e010203030c07050c1207050a0801050f010510020f01110a110a021e0a170705011d0a06050c010b121e031804090311060406050a0f06030305 75
    0x80074140c100a0481884d26039440300000c04100901404aa03d45156107000103450038040850018200d80d1280301006210319468049903000801c80e030f00030448500300c6855500c1131500e5460207607501c405941000c891707441c50455500c0011b8030303000c0c2c40c01100c11620450703c5040241c200c60701103400f01408101080100001e0410065034141c800f903620603030782039281281000c2d0035a101441030940103200041c0c845480d07a482110207503244c1d50a00078184400007500040e44044844c80c228070b40c8101c00460128640d12802210020107124441207015050340055940390000f610641d40810701c000c85080b003100304950040e0041c20021300240d10641407181c100c403d9001100007490b5990b80ba6900e40c000e41d10398021010b002e0048004140c07410030303581c5500c00c1d1650340c81510503c1d4003c3c030505071001900d8800c0c00d9055030940d8001103002c0c035401c08450702c55400a00c8421801100184018804030342c0240384101d580c0f82041c0900703001c0c440312230103c465a1101030001102800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 230327077 1250 230325827 230325857
    0x6060206150f04020d050f01050f0d030e04020c1501082a1822050c0a05030d0503070e0f040e0f0606060901050706020706140f0403030b0102030a080105060c100c2607 73
    0x1a0b01e0790004016000500700b0b114002001c0032200e080d03030f01548009400c001006240b801a9003940c220405640c0603495a2480e034000d071280c2d1001d0303e101d200c0c68000c03503220240c0d242003009500b61000c2e010701e00c07060b594840044c1d4640b0f103410000e1300d20f02c20003500e109108100c64007240c5130000c090722072541046e03080c1811040c510050b100d000c400810540041460b60b10185401c840c50184000d060b00510303480030032034505443d0b840395000c0d070402c4c0307046640160050180da034003a486084c142620103219001070ba07440000301c2c0250b4001e241c44105031007a000080c17804681d46101048504513200d140c1040b81c14040c540c0090700080302000044009091034001d007848078032030384000c60320083c040d90540e07011004843c88504000035104102c140b41c1d06005064100c0303020300145191000700c040041c044a014007406010742c10000307240c070258074104a41c1d20700c910742410803c02c02c05003401c0103004151811300c200311081c1407400002540c06403110103015600c07588484282d82c40b600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 230328327 1250 230327077 230327089
    0x806060c010b040204140901091a1201021c05010306150f26030c030703140c0606010e011106162319090e01060314090105040b070e0325090606020615 66
    0x30140d144039548584101d401900d5a0000d000a80020a07940c036003074219005200e0544c070142d000d040c10500f848420030700c000703500c001c41c202c42c08241c8151412698400420340a403041350004e0981d4041010a862820100d50116060300e1064505001036040320f110382c181e82200340034004110340701c050108444861b683c83c24194030580070980b500e2000c20741410b800c5400a40c000c0f12244c2001036003d0401d176000c41d012480001c16030320103080000582c04240d46200080c041c40c10701c0500303507241d0203e038040d1041c0c1700c6285409003102c0013440e1003084420711301580e580f81d1004c120405110042d0b500030414062107804051480c80c00c0c035401078440707540a2565038104092000301000840c030031407181580f60280c0003d0b00c01040180c0c1c03803902c0c40001c1b000105058003d900d04814030002442462034039400c0700c0a854821100c01824002906142c0b8811440e802460f40c10320388520352901c2c40b40081100d921000070004d41c2e6075080e09980f60102200d0300c1c014200031402400c60b80c41e1107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 230329577 1250 230328327 230328337
    0x10e06030a050607260103120e03060712020715020d0603020306070e010206060f0a0503060a05010510090302010512072618070f3609060e07140405130c06080403020c040c080606 78
    0x101041e02131402076211a50f172904800e030401c1c0d60045040000c00ca40c02c4d00021444d402c281d054000341410710300b14000501a5610b003150a103116000038801080c46903c401c84210001e100c1000c6580340c031501200002001c841c4422406030041400041e100d0313001d00650385114406030058045556042c0410080000034031400e07910400c0060046071507101005282c0c459045200e000905504201c10468400f1458030b00e11708000c2080300034001030364000d00355001840c150b9090407840c1c59a02c030035202d0f90594010030103000004919018000c848000c0107010700c03180542d107002c4030710505c01d031a1590200e01034840150720b144820021610724000b2400d503c00c1000b03a40c1c550403490008002e10318008030500b2030540d154100d0710103200c42c5118040c0759a0f00c081c01002541d25000c150030049510f84a050320455031400055002442d002451210f03691154800684035140c0c2000360040b03030b0690381900144219a140119428240f081442d0303041c05031501401d907a101d030f042001c142e1107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 230330827 1250 230329577 230329607
    0xc02090c041208031b0301061403090f010c0e0414060315040501090602031806061f11010905030f0406080a050709121e05030c010f06050a0b090a030c0e010e06030a050607 75
    0x4200000600301c0c81940c01460010300c181c0c2c3c160741da828514076507000022812040c42000d00300b0001082000c0d000682803043e00045000d858599031401c02c0141400911400310350a075003004070001010390b0143c0c1107010002c045600308018103501c240811800002c441c01d9400d680005c2c000c070b08851040d26030300d034418860000883c0442e010b81c3c820041c3e070800c0d038501c0c40c0342c03480c84114030204c0000c0c45915031060b002d0700c599000221340b07aa010034407041c1c0d009000a02005000220b00441d0a400c0200c0c166000403c6035038803030f80c03807400c88040d601c5403082500041241010940a600034060070b03000350701540d0341c42c0c407050802c98551550b801c0300c41c00700c860086611443e1844400041c05030981030155000d55264437000d00d000742500c2501d080425034034038281050007640c0d14003051205541c28102d69984a0040c04089100c0b0591600054002904103400203585401c1d0541103040c2d828000409070291142010b0598409610300000e0103900100005000f2500c2109441c442500e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 230332077 1250 230330827 230330851
    0xf1104140d08070c030b010905010504020a0206040b100512031222030f031b0914030c0108041101090e1015031a0112020405060d0911090c0703110102090a170607050a0c0209 76
    0x403130341c0e00780982c041135001300c8034400108010400b070314140c1b01c0c0358014882a5001d525104a4010003529240c004000500c0091080c000c101074150305072100c4090100a041d0654405140340000d5807500008101e8400d103410000044c105001c448034680c04202d8600d0081e00e4102c07660302901c01c810761200e0441010342d10a518a01420b582c10340180020032a2110203240d03040520708069110340f801c1c0980a035000440801c0380340d034444030309640a41c0203071341111500d294800485426620f80c2c4150440c00301c030028489143d12000e4000c00b102c210601c14441008446010341c25110145510812102d901c000b41c80e007035000b00d035200042c5040030401481c081c4c5407000a805c542003104110b20300d03540c500c82c85080200380704040b42040411240c405c2140b40140c1d41c85a14412144001c0420030380c03030801c1191940c2501a1307241904014400101e150b01d4004144080114441da425180b26080200d0036150040d4115800c1d444142e85028042d01c080c0c0a002d41040080d01c2d19440c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 230333327 1250 230332077 230332087
    0x3180102090a09050703062123060414210901030b0135010f08061f0e01170d030c08061207050406060804021003060b0d0b1c0302010f1104140d08 64
    0x780da146489400f420803460001503500305004000c00321000c507000303415a0707000320704000294640b205e84840055800100d059044403003400030303408117001c00321000d4a40f00300f109110402000e19541c0040c51211380440e4100381105090402d48421021500c40440e800c2002e298294030030b800c80d00c8103c0060510100d05c0003541a011121b14004402603199240c03129680201c004007018203004001e490407944c1031509007202c1a40b00c40300640413140c0d500a4912107402c01000008010040082d0a14942d0540c2c0d10008a020b66844010104850180f40e449241c0c5070300030711503862840f40503a01c02055036030300f100784207407151031001d000d12510a040c800107a560ba5400345001500042d942c4009605280c414417504d10246c0c0904014142400028001303140d923202998080c1c80c0202c0c004c20024694804108224404d4541e000030414501d100c50074903805401040d0551200729080203015050812803400780a540102d6120201da4041408640303010b5002242980c050440b0340d10741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 230334577 1250 230333327 230333329
    0x18030b090a1a070f020309061210080313030201031427070e0907060e010215060d020f100806190e010e090c0a030303090303060f180c02240105091b0318010209 70
    0x4048810b80300700340c0400b0001046212644401c400d08501e240740000c50070501c094001445900a10124104416500000031240a00a03264500030440001501d5559030034003207050109402e0701090340464101112400d44040c1e20034000d1080c155014030844010741181e05140c00390488000054034803031030301d010800c2c400300ea0f240d80c00703800b50000800c5041c0c40c04d5005030030078208841c1e0a041d5040422414621010040b04a07030005040780c881c1c0700601c0c20720002c1d1b1038613215502190404160b12241d60800d42004e003050082500f21f941c16440100d40f004d980e01d01c41140900a40c3d02e4480004000c80c0a00c04540c80e082030151090f243c421202c2d2000c101c6151096005070006900d8560b914141038051007004050f001d07080250030103e05001c48100035110f5480110308250307903600c0c0c19018034820f000b0f14031081d00411092240c00e454200c00402d80c4001e0152910981c082c1c008074100211a140100004d2840000385045a485110162b0042545041c002155408109800309 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 230335827 1250 230334577 230334593
    0x50a0b030f0105090c04060803030a0c0c06020307080a0e0606010e0f06071407090c080f04021216090608010f020702010f0f0c02032d0109020a05040902030a0b042118030b090a 77
    0x110316070380c1c400001c103860240c0c2041d14180c404890640240d00e013500c10310240300040201c0764030a0000c00701155904204a04a400790040100600b10314404030901180a0340300c00301c1400385144690a0000c001d122901e103032648025500c050114600d140c40580e2424452040c408440008003180e0808a59442e4106c140d00c3c0f81a0082c1c0580040c0c0c1d0034440c8442c0752194a007800614680300e0004d1030284014400e503880640301034455140170304020b0341c403035080052a10350405607401c801460340d00c46000014003298080c16145508128400c00f20880520070b40d403507150140d6403c6034008200109a851030b02d000d1002c0108003600d422040036031010000844044a0b902c035040d40003066200311451804421f8000e81030b41d040c0243c060150b0f50b0720f4030405c29503404880c00101280d00c1d10009207092600e603c0180083e0b0941c2c1004244008040329244c52907414101949a5204081c00c81d01d8420003c2c40ba4020307072407000306101160f44422029800185070b001c40701104295260459 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 230337077 1250 230335827 230335843
    0x30c0203010c0302120c040602060402090402060d0f0606030b010c2307150f09050d170c01141f0b04030f0b0a020423030111040f0315110703020109030906050715050a0b03 75
    0x480e40001c1c0c403214a0340c00d074070070b00d1b03001603500b41c0c240c02d160500750001d40303440d0050406031191405e9400704040d5500d0808071925000184000c000c415031080e5010090480c174071503900441e10705030f0600c00950141d584020038a80c46007000030203125451001c0c1400d22450160030091040c100041100c06d8040e81c001c140074150f858070b048810030740100030400b0130325400250140407880c1c5400002180020340001c40c0702c07017010180d1242c0c0060000c1d401050180310302c1c41e17000e81c040140080312442e40c0404501055414486800c0c540300c0c2d030b400c41d0714030071803200270890f032008803200c00403070b44030391805400c20090f01d00036207841e40e00c5d042c45a404003000224030411040f070841071000c4c0b500f442600003200003941d80500742860230341c894000c24100d10010306501d0b00c5500d00103220b48180e110558649080b2402d03501c1c1da8032824020300820b0742c1081207012500a200100380f40e03000e541650301d100d5001c84c01d5540500000c040201804014108204a50310b0310b08103401e5540c14003104c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 230338327 1250 230337077 230337101
    0x118030509090c0408151f0e040506010602060f0a0902010c120e030705011b03030905010e060c0a110a020a270e21030408160809030a0309060e1f0c030c020301 70
    0x191078900d86010002d00c420301900040d040b080c10041041a04000701d90303519240076003500395020f507699091600e007070002c1e1030380040507040da0200420344c80e40000310240514001d0040360002d82c0c030307028240d98803181580c4192010040000003240b804054020392411441850706110b98080359a56202411030300301c40c4404100f9036003607054941002c10039480205424602405c40b488280d82401040300344910203801c164452503e00c1c00c1c03180135000407800d4a080c07412250103282040c588402900007541603030010306a207020001d60740001800c4141550001c0949403594940020980741c044131690100020075080700d0a5054407140c41641ea00c0e07983e6030050844180c41043d618501d544215001052440c20b00c180408a0800c0069591510070b0b000441140146414410864043c000076103034540f040444a00c00c056105110504590343c5880d01d45181038000c0400c0301e00340c10817403143c000c101c590308500c0702e180c407810f50018500c1c001c0c1028403411580e60003003400c0d9004240300b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 230339577 1250 230338327 230338337
    0x150c080a0806040e010504031b02190902190201090b070804060f090305040807055b030e1c03021c020408010204031112030304032a0501050712060b1605011803 70
    0xd50b043c180643c000008801c0700800c414070740350360090036401e03400c1c1c0c0301034841c0c402c0807110085495407601e49402482082e42200c84d203950b040f10764040e51010181d40b261596249000c005140140a10104982e01842084541c1da4243d012548032400400554070281c4910308003001c00003a1203080c2c80d60340a5540e940d5160306101c1e500e81381610b039a120500400700d1584e503074404000e5075480c821003000001040307400d0103a61007030785000034560a0300d0030484140e100d82c80b00c210f4a070001e010351641754078240a0011110110741d01c0e41030f070014501805004460700440035101e0381c0203085401c080c0741e0950404d8540c0008500f240c21a41144c1c0203a98001000c1c020305c19020014550b5100c201c9101034a500c942d01c0054407400301034002801c0c031042071000203000040d01104c000080e030440181240040b68205640a4035099602101146400265a08030001c90242c04140c1c0c0d09940d0491a0100758203c000d04020201c50548040d50307180301d010880d181c0c2100062040d406503880c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 230340827 1250 230339577 230339581
    0xe01170a08090f0a21120203120a02070c030c060809010b010903020108060111210c0715020d180b07120e0103051303110a0605010605030a06140a09020a0915030f24150c080a08 77
    0x1a1b00c010400e10b14500f0b43d030040c021141c143c18035881d0710b0750250f84ea4501513201d0b00240b802c0c4031070800303a030401441c0c240ba07007a0102c1d02590061085110b41c00340d00080c00002c40540065034004514000070740000d0078600041c100b54041d801c0b42c2d00c0d00c0b81203003ca41e44d0101e4040c034034100400c20001d800d2880000a04400c85603410450040542404880c0041d22815940b010350b030340c0d503994100c0c0240160480320084181c00080f42c10020280050100e54402091070700c18556600351003080003151000480030b80b25403007442840d00c289001d03c4060310072411504c0560b40262031a200280e144201111200085c469000d55030003000e90361900340c1c603410001710100070b507105c0ba000444132241c0c03500418016aa11034040c0219515800016500d44070380350704489440694102d5030030a08120103814213203516072b22104e100b800784042041031000c00c014506500903120513190300500020000e000c07803240c4e407000040c901e9036410113404e040580d54403e841600500c00150110b0401c2c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 230342077 1250 230340827 230340833
    0x1d030c030901120e030412080408100f05150112020c0a080a030e0d05090a140111120307021002040510200d0201051e070210050c0c0303010e01170a08090f0a21 70
    0x545029403400500c080c4009101340f131a0590300d01447c451226184210140340c41400a514101c5014256a0090301e813030145204d21480640f41c0c509291802c1b610b014000b43c54000d10070014003141005075078080c0f072005007102d1907004c1e4000e040102450300540c8004400900020010218201d003a02c0110310148480565414000403841c2c0300d050010400c41d0409a54800680c08241c0e0b1000441e0034038000d5002c0121154041c2c0c01c200101c0f441355103448042d900c8860051440b0f01c209034201c1d0360078442072280c5400d90066100d1545c100c2c1c1081000c40805025455419913940b140b60010514103090641c0c41c40c01200e41403050150350b464050154012064074044684165510300503c24204003030000d690307105981400942940c0d50300859800e9509034200c0700030480c0c410803203899585802892108060a100c0e00e03003001c01e9041c0001c1040c3c4040b0300d80c80181e4000c2060384c1020640e02c14003507000500c0e001345502c030101044c00b14580c0e24018590400003500c0101d410411881d00d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 230343327 1250 230342077 230342087
    0x405100509090307050303040f032f06060f0105040302042013091118190b0a020f0c010e091303050706021801181230020a030f0306050105030403031d030c030901 71
    0x42c069040d20f4108000600100d10000200d80d001940025250307010001414121000c0c0c403c001e50604469a042d140301108842146000e0040c450b50181e40039034070b0f07000400003590000181280800c009010030005460290b0105130607001c1108090a0072030f028240585680c840e4401040302d070b06080042c0160985413192004c48100b01d00414540150302c601307829194030201150b4441c0404285c40550024102a120010f091b0445025160681c0c0700d0042e48441d41c5990414a62203158042046984502e41840351030f600604011003a03113074201d003043c02029606043d07040c040200200400601d140c40100024003010191400c0010008001400204171445a1030030405440c400d0015425204400043d203600002c22103529001200003400d80161a45048002d2070300201c1618240d004141e26001c240710380c2d2245600324207048250211009402910300094040c000103001901a90280282d40038002c44454101d50300100c0c02e1540e032000c0304814082d0000315640c02156001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 230344577 1250 230343327 230343331
    0x13060f09050a032d1b0303080907030f08131206020913060e060d02040f061401080108010c080c0c150705090a21022e050306090f13110109050405100509 67
    0x219002c400407440c50710303002d0030100c5a1010030040d00d202c0c86028a034070b00388914907800c1c651204054803589081c41000080e800144001d80121707241c000000d562003030215007042502d50103601440c040c1c0d09a01d8103040c40d0800b106440400d82c00782c1d400318069440b01d510540142c8038800150703540e85480f05000214200d0aa560034a5091100a104140b41145007a900c002c064810301403500709800040e001e00124007605071000e160000120300b440000e41c6440044e0800e0301c40998590340d4074800e074221401120b0300c2d0000f4180d334011600308501c01d0001c113a141ca11400320380c5c00303c81c52002c0007001c840603907404000c1007002039000310f681081080b01004018002400100c420300c45d500c02240b01569034028803d0200d8030754413610310b00d1a0740c1e0b68042007070840d43d10652000100040c0ca46d5105a55540c03052400000003500d030700e0b12140f503034840d6050440602070200c00d581e4041c50b9400505106040c002c611401145c65111441000d120750000a6081d540503c0c0c0802e200100c000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 230345827 1250 230344577 230344579
    0x1050a0b060703120c050405060d05041101020616080c1c0606090512030403060f061508010602100b0d030c0312020d061502030f1b01060504020d0b0108060f01020712050313060f0905 80
    0x400d005400102c0d412043c41307041c03440d183c4804583c04101101c2102c0900c541d401c40c5a100802003001c254800f000d5220601c00c038412400301c91907002c03034001640d40d540121584070b80c000f500400760701e0280c841d007441c0d500400600c40380c5040c010100c5a844004140c00045141f8aa40700c8013001140d81c0942640300502c025144100c1d0320342d04109082c1c59110f5400b001d800c55844007140c4030a001c09910501c000c0140514403100060343c440010704140c02882000e00601c510f400d81300000c2e060b0f101d00800c1c1c072001040e00a81e0421a80c0599010203070050503800e003c4d03078903248a03441c8400e0000388081d206060380043c036181007014400200e11070344d03200000c55001b80614401641884110b0f02048401d04005c500300345d08800795800750115402081e041400030988134008913943c0c104c44007000c030076200d4a6640d6a6107041c0850b000c40200d0b090f0044c2c0c07041008028005048014040c0d490203001580c2c40c00c1c1c0c002500410f0162941d0003403000444200b15401501c2d40302c0c08000207000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 230347077 1250 230345827 230345839
    0x20307060f05121f0609060f090e01122d0b01080f030412240204051f020606011209061107150b10140c01240605030402130209120f01050a0b 62
    0x101c0c2020081203400b030f000d00c2441c800e1062003c200552000c02d0180c81d003642005102d1031081e21060300800100300d07449214042031000e001c550005008043c13203002d90303600c0d20008245031b18020121103c1001c1090a81d40c0019061070071004640241e803425180780c45501c501c003001402e00d410b0002d0703401680000e10940000300c5030b084001011080380c0486038055100010640396007880d0702c0c0403016a103c2c80c9984212a5201c506203269005401100c404075444a0210b9a10381d6400a00c0d454a100e1070068000380005891503015420400108a0f480c500140544107543c03180c0c220b458400f41102c418802190010070042c3c0105002e0341d810b6042c50074400e103403038100400c1080484840a03418041e81d891100140041c42065500d000d110700700900c0b180e1140c00f120000581e988034089030060341000e000c00da660040f02105c0c000c5034050540f6a000105500010094002c0d1118035070101e8500800200d880d0100844a941151440002032604105000c001212000405c46016a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 230348327 1250 230347077 230347097
    0x902040f0e0f010501141308010b04050c1305010807051605070e10031106070f051b040b030109080904180c171612030f031e060e09060126120307050702030706 70
    0xb999200e103c1c1180c50a00380b10421901c0030030030f10003c0c012000ca0301e014064840c40000c13205030541200b40c10704001e550030845500c40c1c020040041c494144d19002d0101e6041007001194412140a6442030307141ca4110300300317002280a201a130418102c1554a0307400781d1001d1000300700102e6a00e03044400516040b01c0d40c0e10b150ba0707200350302210140b076030b20030500410072009126070240040c0721182c2c050255826400c80811411060303002240041c050780c50440c81c4495820305125182c100c50f0040b400a040010000c02c000140500a241303c00c0000d030706070391000040500c81404050300280c081d40b074800f0311111416140c09501d00248032441c8107040d04000380c0340b149034040199501860450044d0282c1c003405d43c054200000f0200411102d501c030216128590380c090340680d41036511022840d101ca600c22079a0320000e001c0c80804031190350311407820103108002004005a07a000b80c03400e45082c04c014550b5a001200c440d8086180016903100f145010322a003070143c0f03511304101c8828 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 230349577 1250 230348327 230348341
    0x906090b011701031707120201050f0907180f02040b12010e060d020f0405150907020307031404240c02031f0c020111030c0c1906020a11010b0f130212010902040f0e 72
    0x2c0702c041c070000e050030400803030950707120540c54100d406a0380c02010710b5503450110003000307009003000c1307514035035400d00e80c0040754080001082d0b000440b820010311003292400c69007130708010701c1030310f20301c082d60b5908100029145610741d0150110000042c0440269850030400000682004201d0f07841141c2c0a50807800607541c8041d40c60300b4080a550004455481c0b041d11000d0803640300d402984050564100700e103080d8000f0051480500ca0342c3c5400030301e000116802140e015034091103001c05a405c000405250595002c840189440c0c541101c9003002900401e050041e0900c1240040e0540014101030f10141e0044800c0e07582a13100810603089445d504144502015241d01030031080060340080780c003c01c200c404032039246402c0404007411646403000081d8032100c2260045203402981ca41d000906120b03a507581c0300058403071241404403204010b0795145071b0246810f003540c03d1011507040005900c01034064005180016919804d00101840c5000683d2020300c4e0018038900b00426 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 230350827 1250 230349577 230349617
    0xf0e060307031a1203041a0c0c0105031f090501060915080420040f0504050d080403080f07090b03090703051b061b0307020d0309140d05060f060402040f0906090b01 72
    0x710035840e14002400c0c201040030310214683c0450b10b5035000f81049146401c4550102c0200107ca03400700b4210074002c5804250754080c05100701201407a000b162203028154040d5000f154801da11070307a009558004c0100074a02d1403810342207000310b10f07070f2040140121500800d83d4030142c00d0000d0f00c4d940b0302000e40c0700140b1109000384010308560300310b54004142504021042c2070014010304c1480949100d400358802440c0c03c031001d0b203203071041400c0030303800901074680f550290f030301a03031641203c2d95003684002d5801e4000d00104100302c201b0000090700340420000d90b00030090100074004803841c508249107004190003031055281c20040840b0365a9a40c00100c80c1140c001c00c001d0608810503a00060450041500103134002920030200c03420075500907000340c241d520910348268070706060800d000f20781b40148801000340d0301440115402c80c07200240c46901180043c0090300d010f45440c903003402050941e22442809d42c9411091000ca00c090180e28011040ac0c0303030070b0315140078850025807 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 230352077 1250 230350827 230350831
    0xe0109050d11012703051b090910022503180e190b0f040c080103050105010603140402091f06020f0c060a050f0304110409140607020f0304051219060c0f0e0603 70
    0x1c1801400c030402c580341d01014402852449001d440d682c1060385c1ca003000c0b52266015440c05c14000c1c10303214018401c0c50300407003403030107001d0340030080200110b80101e00c4025800849240b48082d01d0003100109110380101c015220340c0b19540c3c807403411400411109400c1d113160400001008100b0400000126060410704040ba4a640209440706d1000c0032440141e807880d1000d401c541030894038021590810b04542c106d0340b02d24020044e50ba607420080b41116481c5296014001c0540c010030702500e0421003054104484903400b00c55400107140c0307992441349990090015030041760001c15000c0c0240b06510703a185c002d803116403900c400f541004000340701d08062481350b03000100200341400f88005040b1807001c0090820040042d240c00c100511100d0714540e070001e44151000190494404680100e160b41503000943c00c25007458208600260f26001f01d98080c8941d0445d0002e404400e5041c0343c140e4000c0ca0002515413840600400b02000c0d4540801489121002400d03940c88260072a9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 230353327 1250 230352077 230352079
    0x120818090420180a060323030d0906021306030c09060809030405041d01090804050a12021e0418060c02010509030313030f0c050d090f0501030b030a060222060e0109050d11 75
    0x41030910000001800c4000389a01c00f0424510744040043e00c1c41da60f0f10079426a4040c0d9500c520707088812100c0c1c540c04011a52440c030301d40043c4800c003025120303604888401c1e48100300150a00414524001488910350310242c0041e45812241b0030302904008501d0181c0b02c0b91500c1407940c0703002060f041e1b8912403403107003900071580d80c080e41c183d10042d501e42c1034035070140200a000350b84450030011a43d03042070003050b20410607a400043d10300e807640030000c851907000d4100d1030f410400503036500c56103c411a100723801c0b60300d4000b94600002e40c08030792a1402e02c6030900150f494906000242181e400800c40714180e1700030014800440200401442550351601c1d000584401c0790000b04e03100030704000c00030414400c0385880d00401303410010307450540305140050440c5c21360315401142914034214500d03402d6000441c41401107641d41e0000c1c101216240c90340c290311040c011400301e10981c2580b0a038001902d1203035030825980d0152000e002800c0c201e80ca8101034400f61190343c81c11812900726 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 230354577 1250 230353327 230353373
    0x3010308030a02190206071e020a06090302010b030a0615060504050102030f0703031401080d030c020705150705070f0324020a1e110304060306050111070b030f07091208180904 77
    0x28202ea540d6070100c07003036080010151100d00c0b6a40202075601c00c6c040d6604000715015070481400842c0091560003030101c01d81c0280107400c00c64840000400d4510720980071552158902851902d0820042d08030714480c010016040d00f5030070390000e03c80c200f81c02c20400c00030100300401a50782c1c00026a10350310f1284035079583c0c8652501c1c00b54000c003100c0c2414a82c2100800000505100228020340001c22640701400b24450380c06040340c07a540f00d40070b0b495000c02841c4440c80045241c101418481d88501c085440c4070b5144c2140c4165100d0581c000c444417a0415440103d04142e030086d03290000c007080e02981461181b910140c00d6094694030010710300b241da60a0949207128482c0300214070307044002c1c0c82e0340715298403000b40945170318001d41d8085481500c4115815100085c031030211160702000b1402c50312001000403071910301030242c9082269184010803a244100480007070103110b6000160f41c0d106440008581c80d4811070140d110710940300030000451001011054141c1c800709007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 230355827 1250 230354577 230354581
    0x1b040c090b031e0106050304060f15090f0e0303010f0303170103030c06050c0d0504030f1107030f12020a06140a24050f210a0b06060a0f1d09090a0c0b07080301030803 73
    0x80c80f15036030402c1c01202014003a000140260304603009500890148105000303c200c0d503000c200c01e40d0850280d511002d080c06800f0410344086034001e030b2107007071111008140d600e541c800c002d01d550020b810801c15990000410010150400d004502c20100d1006041c401d6240d03440240c442151000302400040d01c41000550788a14802111818405d000c020442c504160500406041c0122455004070701408881c49021800160080440380d21041d241e012123400c0e07a5901245d441c10359514150b10640c02c07a000002c0f164014030740d140903044180c4405203000059201586c1c0b00e110729000f120510440203054045810301c8406841e03054072501c0c4400c3ca4180890890034040c003150350801641103041c1c0d00300501051007100715024004103146600c40c1c1c01040603500c500c051100119480c07080d000e43d03080c00340c3c90300d01c1e2200822600b408940840008511001000c0380c5801072608000c0540d0200103481544030301802d810b820050500103282c2d03581c0b885100600015000c09000306c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 230357077 1250 230355827 230355841
    0x206160309080d022d040b0708070204060812120703060303020c0d1113091103062707050402030702030c060a0e0d08060409020402040f08100c09351b040c090b03 71
    0x220b40f10501644011540d440b01c05040f01da2114612078200d03180240307981c44c54446000c207030179075042e121460890b520f0301c010b03541c500080340d2000074200d800035200c20001512500510103c100b01c900c1d82806980c5200804441000400003024030003854607084090000c2a8005000d411100c0242d4600004035201d040403071005040010346540100c080005c6c22039946150000c545880c0300301d000c0ca10100072001095180d180c2100c04a00c0b04040200360b1030388a4010b0400c01c91701c910703a0705554083e6101c8000c50143e900484181016a00c0000c5403040401c0400090380e00c140f640c60200b1544048604254440744220304070002c01058a000c01d900d0791b01c0360700c61030b9400c1c1e00034402c40d91f881c1e441c041d0707130b550014910074150300303000d18201c40605c03240c00c1c09003a4030b840451b030300c2102003410a1184150066040c1c0519540050524000e08404480c031413006501c03902d1008104074a8001c002c0c0b4202d84816181d54091418460009010764000c6c68402c03c2e11010001151241d039030407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 230358327 1250 230357077 230357093
    0x18031b0b030c0a0e06040308220306020304080a0e010e010207150311040f18050103120507030c02180925060c030c0611130801020a0e130e1605010f0206160309 70
    0x280080140003000400c1c449241400c00003041640074a840b415901e0a0680400045000d03900c4083c241c1d00042226906002c3c440f4095000685403404290b001da4494640808a8208640840d00c0b0100000c204410580040000d40362543c00d00e4101030034140354000079106c0509101e450540703a040e2900190a0740241c0002001c01c072090f4105484035035031300000724650003a11030348203c00070141c84604541c500d401803c0c140c03030304611000355440d04d03404d044071039500914007542000900b0301d0b05070060f5a15000040207041d03202224a041c2482e440d42800c04251aa0031100b800c3d91407601c050302c6a00700c1c40c55040794203500b040d02081c1d20703509003900d0701042c044000b41511712b44114521441d4812000d00104002061384200c0d090316041554200e1040400c40d0300443c03a030000f41c4005180c41c071140310050000c1e0341c0114001003492142480d10703603041e00c043d2900884030700c18401564843c0140440701c000e07200a0145082603452100e0720000348030b11904050300c0380c5005051009207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 230359577 1250 230358327 230358329
    0x321031308120103060b490c030b010618050d11030601180c0507030c020f04110d0e10020307080112030c1505040c05010518120a060e0d0f18031b 64
    0x1440d80b6510300c414010b0703a00100c001d000489681d40380c880c1c411800e00380b50450383d5029500300e208090503203440a215200d0f20905070000000c0d104e81c030314041481c1e00d0605000130244140c103800650750035440e00d01c04001c0140c21160030007010400395200c075201c0c104000704a54003582d10032a283c1702030508010001d610340210360103105120000035802c61040030320000c020209000c03c400400d036581110f0a110b85d903806000220500300b00c4000d032602001c0c100240f1401000091000d03000303112040c2e01d411040910f040c440d681c110502c0383d054180b0280c3c241c214400d004607c1c601c5d0491014146d0101801951044111310300c440701014080e101f0b0303050490300b12900818040c09400d46038040d01d0b04940c1100c6a140e20040019194010000e03217507100c0700c0c41440c6103900221801e116590420301071131040c030305c03c41c41c459001c11103501c1154018500c81c0003030410a040c8410160007440301581c10004c00c0850f829101005501d0705003081a2079108081d03046400c48078208011111035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 230360827 1250 230359577 230359583
    0x603040204020d05040b01230907110106051215010b190c1a0a0c1206030c0b0c0309060c0109170a0207050f0f03060c09010f170619030c0b04031103210313 68
    0x2e444e0a20081c0a0540703601030407a14501e450005065810030704c159a46c058400380384d0040490008110854058845007852102e00400019401d594600040c0c41078403100101c00b1640080004883e000071074502507000d001205241417514200c000300d01c1e1590b0820701c10704108038081241408100e664a041002003800300404582c0b820600128401010003c40c0d24010130300e00038112030000102e024900440c9e030003c024032520792802d400c1d040a0b50090400e07180718041006685803551f9980c000d007072460701c4140001038050780ca1a02c1c440c4000a0086c04015503018441040640c3d0700159031011b50b601035450311008010000490000b103106503845501d80200070401c5510103000300070f40394880099030344c07420071070701850169442c0e0f952441501040040301c000401a04110041c980d0020714010b1280205a490f10b854520f111150440e1081c900300107820020702207003002d03c0000000880240070f2505082c1d03120751148914041040050300040001031041d41610110141550 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 230362077 1250 230360827 230360831
    0x504050a060e1516020703171c0203010501091d010b0f0705150f100806010e0c0705060906010f050f01080601110c18180a020a03032304060c05010f15050603040204020d 74
    0x4100c0b00c40c26110041e00003402c0c00c0d402d43e14002448054140c9030f014002010390050011141140c4400c10f0769000a45152000c1c44204a8221805001d090600303002c00d210368016201d50511000408116482d03002205007094031805d404481103881650b0f04640e0700083c566078031485450100b065001d142001340c12405065059842c100c002d081b0305128801d03039120f0483d940d07601103020040e02d113540103180c020b17031200c401880034006982d81c183c2c008040180d11030409011f550b481e0302d030520850301c82e036158201d4401001903103d4100440040d000444043e40340d017400c0b0000030180700c0001d101c64104001d0050705452401d06012000c2000805000d05201d000c00c0c00040381c2401090307408240181121101c001d20a5001c160014200c0d4002c24901000e03181d0f4608035021a40c0825105a80464800540e403485140000b00001c210300d40758601e40704c03054100710382100c94044841e07400c40d0403c80c03103a80d40c01c6e10580d04e409961b4212582501c0740c85900201b0001e0054140c4905414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 230363327 1250 230362077 230362091
    0xf1b120a1518020607050c1801080a03050304110303040f03110303030c0d05070c020604060f080901050915041b060f02010c0801080c04110c2e020a080c030402040e1c02010605010c0f03030504050a06 87
    0x44804507801c11600005e0320340b0300230401c400c03e0408814801740301390f5030541c0003034150f400002d220b01d0045400034020145a2041030107400003c0c159407040d8412107401c81c18141c104200007200000c4045440214061415403410340c03803120350343c4220b00c200b8110036690b00005403105d002c1d8a000220b26005007106403529103840024001107450a60600411012070025480a41c14040e84e40b20346a458081d00300400320451030251440c01500459480d888070300610300f034101411244004144940e1803860b9042041d00281c00c49150451050030020703004018002d40100245000c035048068a00003000441000802d440c0c0c0035820400725a0f000d01040c840c61f0000c003414201120350100b804400340404a01104101e11800710b084010a81d0907000485c3c2c10303080f001a541c424000340002c5494064a00c0c07a0b800d004401d0041001504040f03021044e966091007604050032013030a081c0c43e084566107525608034400c4d0350007070406441c0e00001e02080418001036000540c0028240164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 230364577 1250 230363327 230363333
    0x1911060901021b010b1305180a030f1704170c07240f08090a0b0a11031e0109060501020606060a031b02010e0d050f1207020f1b120a1518020607 63
    0x20b036101c0b400e4852400800e50ba00f0080744010301c120008500005d1141c0b04501d1041090800703010028000341010b01da654002d000c02d001405603100c214441c0e501c000b008804400060001013040600420740e01e03084041000080000320442c003507000c0c01c400c403902d51f04100005440c01c803030380d00051a2008020341c4a110030118000039a14121543c0355107851480b000340440313035202d00310340e040300c00d5201501e032201080d9010141038000f2064040400e80e05001c20421005500c240c800641e0044d15800e00399a09900c1c4198601401d41c1000030f00a00e071030700f00000e6542d00c2c0034080e18890301c0d00248503c00749010b40c0c88011501448401c6d034101e403003400d074083e000307145802460785680102d64202d034510b0b00c030350211410440000700300b45c00e022202035602840305004081c041548501011040007900400c44812085206007054240940400074040744042160402c583d0354094120f603c001201c2010080c1c00c0040020002000a40e43c800304c4400045488065040b400002e9a0303014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 230365827 1250 230364577 230364581
    0x703050405090c09211e0f060601051c0209010509090103080a030b03010216030e030c040e0709150501050307030b0a0b030c180904030e0d2d0515010f12030e0a080c010f0f02031911060901 82
    0x1241f0b201400e4030340c5030380c6203c01502d0510920f032070480302c0c0d4003003080c6500b0000140d0280401e603106140c40c2c0c1c240080b880201d241880280c00c00c0d6060100410f060140a40c1030040992241007079000354203144444100b900c40360103a0b400142802aa11403001040d00c00700b100d0080140000c00c2400040e4000d03041544035003c60140c0e2245a091000140f507400c008903114080350030681d101c52031070380c1b004800c0303000341041e140b80c8c2d41c0051800c0c4001400c4a00b007019500030a201b946282e510414807441d40c4142400c1d840c411b0041040d0010000480d82282042800c90015102c025512601303250a01c00c017044005803180e0780503180d64144610f0030b1245150f110a21031022160020005548505c010702300340b094480d0007007401001d001c1d1010884030040a00c2c42824450507001d660030015105046075004200d00394810300900c046c540c1e0048088011480a080003500e10402d40c000a44912502080782d0900101c1201d4004084c851420b000403d01c03000e00f0f03a0b80f1030030300d00010741c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 230367077 1250 230365827 230365843
    0xf03020904090606051207080715051201080f10050906010b03090a05060a090b06030f0618030405040f0903030605241e160512120f07140703050405090c09211e 70
    0x80a182451303110351103a100090b80006070f80d61140148403d600e0828402003402b420200d110803c0800d0040c084810a03000707a03507019006100140003100b115440c086e20b02801c0d265414a020300340020b010b41e240c008141c99040d500680046c0f0f179a941c41c01d002a182c480312030b074024107500c41c040030041c0d805040e50001242038862000795015844003010140c0d900b44171000c0c0c1e6601e411103c00705890302d052000d8159406224001d90707081035030761000141207078071382c946040307a258840104608241c0d040c45110050035048400250450b0800302405900ca0303000c425100070f08002540c4084101c081c0c50b10000380c1c403c4500c0c01c1d55078034541000401400500d10440d024443c1211407200702d05c00707405440c040d1000f014511030075512107402c2050280301178098010b110050000c0698080e0142c003c20b0014040d4035001ea0f65450001844652400144401d0103044140141e000b5039940f40d00c401118400d0540d10851260580b00c10390401c5060000940001c2500038005494800852450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 230368327 1250 230367077 230367079
    0x70501090c060305070813080912010b0406030f02030f030a1b03050909042105090303120a0e03031006020f03190305040213021305010305180303071b150e0c031c0f0302090409060605 80
    0x1846c9895280403607084043c8554010034014090103a001c503420854440000010b4a000110f002d0001c41c000c2030403a90580c00035184918803c2843c0c041d07040c2005080f81c11590312000354900718202000424041618480701400720b840c8500c107080c18802c006071042c1b550010403500c01800d2a1a0a1000701031200c00c45d0012105882c80b480014018410303100100c5024001e14034040c1d60310044da44441000700480c000135610300d0360800c1a0001c1000d035205003001c0200c000c84c03c4c10f003000603190030311400e0b16178400d5208000c0703600440340480c10446414000d00b408611501e8510003e050512003040c041d1040b4800300e03000d5007098081051a084503001c0c0c03070070002902e80302c2c94005450304000102c4a540e10070400b203901584652032920180d0509480081c800d5540d9840091154119000d010220313140c20147c11015000d02103841886812001080242c883d00e440d114012443c01d14501441202303100100020b0003901107a03034090780240100038480c40352030100f0042083d4050b41e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 230369577 1250 230368327 230368337
    0x1b0507050c030105010b0406030b12010e010b0112050408090d03020312041211061b03060a120602070b070e181803040b07121805101101050414060a020f0906070501090c06030507 78
    0x80d0241810b00c00c46040e21b04a00340035141c6802c02c0707420b0b000f0300204c0d0324654000d45000010852000288543e201a4606800104603034840100042940b05c035801610802d5140c40103000008000200301c50140360242c8a13544181050b003816401e601501c1c0109100350a61000c00c0100411034443c40080c641c01c3d1a0608042c07011050503aa0704001c803100c801900c0b18142e001144c4241c1400b45901c000010180380025444040c0c1a1028009240c112001a0046941010440c0c49840b00e0b40c0310340c4514100b0051035080c000a584c6c0c080c0034140141c88070b420b41c0410412602001040003a400c404100d0350740c1c0b035850105004030342c424003003030ba1003804070540c680056200b1000e0a06203100c00d9906208581000704102d80c9540030001203043c03101d054a000d5140e0001c1c000c2d0381c0315030300030491204409120304245060400c0207024121941c4100a008880c01c0d00c00199003242e1400e8902e02e4555030320340351280c0102015400a445a50b18800008044d64036800c4a4414001641c81e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 230370827 1250 230369577 230369593
    0x405040e0a05010f2d060b07080c070b03041a04050c060c0318090c0d020a0306321903061d1c022802040f0f0e01020405030115050307030210031b050705 67
    0x11450032122042c80742044440302130317041c1a00054051501200440f441c0c1c0029403996118071b503400c41e43c03040104403041900480e0700c4043d0101403003000c00818060a503e440c5290030b039212560303442032031914885000202d0114061102c04c019a00000380098551603441280d000d82c20303901d802034240c1c1660f03501001c24400a500f402c0f0b40d814022820080242c2c00d010101d4000d2019400030090082010341c2c44000107114082c81c1d00b8081d17402c9440b07202140410159100c04200c00720101c0b2240a00c41680091450240d0640d524080780c1c0c016400044107102c0d401403002c24040c05856007144d1140c1d910784102400c610980010311078154007210715003000503108846154801f03e182000c00e03c04480140076080680110300000c11450700003609c02075502d5190110f40c001c90907103031169808503087c0060b0509105502401140540ca400c1e130760f04d043d0009648100c5400002c2c0101c01c260340250f0114000d42140054a08a810008103401c1d8003a0041058100c20000ea490b0b10500d02c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 230372077 1250 230370827 230370851
    0x8130209070c0c140d0f08190909051006050301210b072a08071e06060b0c070f14100c080a020606133803010603110901170c04110405040e0a0501 64
    0x541c1343c1813440040c0003050116030680707980c00341c04906601510111010018028036095140b4429070116064545040c01401c00000b04c08413013004110180b01110088123000d0950407809483c11520340346040c800f0300e0007040d401c2ca030a41600d80300410100802c0e040c402101c1d0020310b200c0c00c82000c80c1142001c42071001e0b10b442000c0c40580d02a01d010b5041100001046500180d40703880100400d405100c00e60907a03850003122440e0348038586090000c695a40d602d03034244012401400c0307031003020342212b04000b00d03091407092903802e0070b1180d0b03854410303102c0c118010050584546e4101c001c0c941c4440d40351102a4940c00300701c034903070310400800d00d9044565034144102100091480170380244242500814102d0072400104461500010941c05c4040d503030900400001c0d5129900c442c620014200c00d004c8280010381090784c0d20b01c0203140b914104070000411200c01d000c101d50110300800c01c0352000a080c411030b00302680007030402103148842003000810006a9200324001c00a50340442 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 230373327 1250 230372077 230372099
    0xb0720090115050703031b0c03020105090109020a0b07060b12010204050103050a0e0606040903180801060e07030e030a03050a0f090305031f05010e010806040e0f0615030d05070308130209070c0c 85
    0x400380024011850a400310b20038400c00251140903c42e0800040e4418090941c0c4540342c2d11f2160f140024600c8540300f000c0640c2030065980000082000f40443c144540c0014540380341401540340b100804034600c8203000068001c0c915210f006403030800c00c0f451421815020394814060280400d00381400b04089032854840d1740380100c58100500800d4a03008104009025245419030400c50300117003403048001c10b40d02003401420060000640d0300e00d0410a4840405d004043d182810303c1c000c50145444404400c683c544030540c81c000400d603131b0f004050b0f0000c0001000c2c455070300386481e070040205a0032100840c000e220756002c1103801c0c1ca84851011034003009004580c0003072003036911000d0f44d5004804250b002035005001240b80c080808005140000d000040c0450740d104000384071450300c203240041d04016099000c1c100c00084450013801f40d1041c41001010002490300080101c0d11146681c80400c1e0300174544042400c2440004250304004142582c0400c030394000000c0784038402d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 230374577 1250 230373327 230373329
    0x80a14101a16110301060503031303140609030a1b0501181505060307052b0c05092a16140607090506031303050307020a0614011502060907031b0b07200901 68
    0x105141d49001165141c0f00840c00c0020b14503015920740c44007043c1698144050941d01408100010f40c4600c0c1d400c0004030602142a00c60315a040724051200144010049507003607501420704c00544070b80340c41810102c440c0c01c1c034040c001d07502c1c10444040c00540700c580000603e005641515948036201d500c50300b110000c0d14803946c5540300030020415800d10800480e450400001c94980d140400d10300c402c070b44040d030501200d6501a4400070710843c501026415007242c91001e03030304d4106c011000d026040281702819807081a801142040041001800a5520503800745006c038160401800e101e98a03001580e108005c602480c5007c2010700b00700080d00e21510740c03c010f2300090781e1603071001d80703041d031000d041c440c214001c90608401140b080e000e003603418550b101e8850030a40c0351021052203040c09281000c2103410440620a00150005a80043d00d801c07021040360714440d03070000d02d0031011300d40c002c5004c0071011a501090100d000c0c02e10460220800a50516a2a240030000c0680e42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 230375827 1250 230374577 230374597
    0xb04031706091003030807020a020603040f1208040c050f0604090e07050901080c0904110a050a08060403080601091215060f1e06050c10022109060412020f0d080a14101a 74
    0x4190400c00220784550300981c0c200c240c0c8c2c019030b4200049038000c41c4543e0b00c1100c05030340480c4031110709410400e10902c07804a410b80d5103010f0440e81029910104171124911a40d40700312a102c0d0300c811b030351786d5507001c8074014070800307030104002c0c8141c10034591214a03a1041c82d1281086038000a000007022510443c0d501009084011035611a5501c940070040054059003003e00c2e8100802c072511009400005041110011301d91443d1500e4001c1030124020200d60400807a090b0402c062000c0002846080e81d024400712250f40d100b20100c40203140680c40b01d40030600c10407000031241c101c00c0000301d09142924850360741e035840304070585952007005000d41c116408280e140010340d815a018040c140301c2200d10518001244c1d448049103c03041d03400794201e40110f01800100000d0440300c03002008079001030b01e070114211044603121210380702000180140139000450000c3c080d803040c01419146500300300d06060440c181400002e890107840523011883c4056580180f0300710541340c50380c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 230377077 1250 230375827 230375851
    0x418020108160f0513080304080307060c0c021507060902090a0b011103070c1a13060f080a0516050f0705060103050d02120301050a05012d052203080d180b0403170609 73
    0x72034a030045540354402d94451720030185010740401e100600780300800003424400d001316107400e80783c10000e00b2101d900c140c50040c480c0701c045800c0182c44001201d540010031811075511050103081610140a05d000002d61040c100401c014402c0c0a5a0200445203c01c0c4e0750450052500540903a882c40340758409030084032000c10070840d00c0b421440b41b600c24000360840d6414040d5120400c4124a15900000302280011080161560703001d40e0a60340039800103410701082c20310580c107080c81c02c03034070840340200036000400c1c448009540d0112062590b00c03900700ca20f80d41e564102582c440105060310301c0103004e1000d407406c0c40380a180941341a1407004100404c02403502006480700c0004000200d0b1103043c0744070801c210108444240030045d041c1d03d8003540d0301d0341040c5542142c1e4901607944015401040c051022440e0b00080d40c80008403072100140010300c4803500704070b4500001000b48002c4424007088100b583c8002e14090201280c062110703ea1603040403c030180b0811500004180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 230378327 1250 230377077 230377097
    0x501080603060f07020f010218010e040c0e0f010c05070b040602010b090f0f07141209010c0201061a1305030a06090203010b010e0904030311040b0a031a03190609050705041802010816 80
    0x20030943d440c16080b40b0740c2e0040700d6100407284150f9007640c10a89109108120410700b88a00d560400801c442951040b40c04112000386c100f1f000d45040d0060814078028030300c402da4006d546c4d005640c81640c0070b4208007251156907807100c00d86407550160140301c00550803c800404141005600113000e008030030702d43c0e409680c8542410f40300c0c110040a06080011004a0390900344c1032070018040000d0111007541d140c1360840c042420344900203443d504580c5410380c200f00c58102c20b0007410b00101090452035903900c080c0310304030152036a500f00079450b0044c02001e40800072a680800e41c2c072403080d030003802240b104c1001543c06a0400128a810680040020b00000d06ca50f0000600d420313050491402d10380c2380c00886801c0e400c100c01c000082030340c40c2803840500702c1d590b20310410410200c0051026640c01980c411b48801990b40003130500340c8516181c81045070600c504c0000c0c00f0064410810b2502c80c03298510441d01035201680070581070000b05070316480d8902008845e20494844131001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 230379577 1250 230378327 230378341
    0x723060a12020f03160e090106020d110a0602030f150402040308040b0a09030b2d060d080c010f05190c0e0105090d03030b120303100b091305070507020a1707050108060306 75
    0x40c50001c000700e540d541d07081218001d003540d5400514003442c1c401490058250359100040e20130121004014841c4892000401459900088074100480700340b4003140c2e203005084285107082c292540c02000d0701d002208011800c1000f40c0001c0c41000e82440d130600c1c401d034540511040f03104902002c1c003d0074081005000510f0000000c0c5040c401c280351010145a880e21503903c6138000740d440a0524500480c40700300c41060100c5c1d418000303000d401e507400300c1c1055800540301880c8580d0081c580840440d41081d41442940000d0780481d80f91410b006500d403061442820f9494110a105400d151102c401c1ca0184509071424540d58181c40307a61a2031614000c00c0040c64004904900b0191200340107946601c0b03651081c0445842135006640700d0034084100305e95403242c0d400c0405c5807503040c00460302d29070b00c218206600b41540350f03001403030791101c0d00304541c139100b1854041e401c041e00010000343d651802c041180900e90318030a442030280c0719001180d1020095803442d61641c41203000c03884e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 230380827 1250 230379577 230379587
    0x30e012c04090809030709240f0e040203030c1516020d080604050a0e0304031211061303080c0c0f07061101060e04060506010c0212071d01380c0723060a 67
    0x1ea5010380c1c0f48504001c4081c00081c42c0c415a5082281503d0322600c4c071044054078801d0441b0304106d803209041003542004d00c03490100006202e080051108400130a0175902c0a01c2198818060321b0252041d0048640003040c66800c00c0d05c0d90403015240c40240e500440c8041400030b03100402e40d40b550304a880e4002004090007010304020309581e5070f05aa018201c1003080280b005511501501d2000b42040d80051724948080d00e03105010b40105080103400038180f5101000c0300d80c5401d0540580d103a81071619610300800a00040ca4072a140001e000c0e02c000158080032100207a403560203018482c80c184d800c0e00e0070f038403a603400c1c07060348000b08001070019005540c2c01041858074640400b00354002a8407020304005866003600918804c0c0300b0480504010348034030007900c1c60b0f5040e81d490000e4010310515984c021084841c1c3d102c0c000509051401c402542c50103a903803680d41c8680d55418030544608040c4566210030030340712844003841a00c82601c2003990001020281003110200060319 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 230382077 1250 230380827 230380841
    0x40506191104180b0a080a060504030302091810090204050a120f0204050118050106020c06070308062202120109200a030b0d06140711060a1805030403030e012c04 71
    0x2108a48401d4090707030814500026000901d5440c034411080b01c9600341803c00ca6000703030000360244484100500690304005226840b90f64030250004480d40c0da401d088000303004903058240d011281c41c20303c440e6190084c0358640505100c0c82010541c0f0303a1591140120300c501d12400c2d811288214041049004124004010900524205e0280e03403407540014200c0d5800d800c08c3c60011514050090301210354441c03940542014001032000494190000e501c500410030014100042c3c0d00019a0684444418030140704a0070000710b040d0090360100006074020307112400d907165035400001410f0115001c1c2010840310084900c015050885020760725502c00030030541072546400300d80c140c68445141003980c441c01400005400700c0380107020005040094040e074208440c10000c42c140600c0482c41d5a0002c0c10104005000b000120b4009040c01c0500000303403250001060000902d60010076644049109036500b000143e008011400900d040072007a184010b01c4403000000b03420994001c40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 230383327 1250 230382077 230382121
    0x70206120703050405070f140f0612010303020f0d0c0c17030c060112060c0e180603070b030c0a090b0301060915140d15170c060307030b1201050907050108040506 71
    0x1900d0030000100890548105490360000240d070740003007005024007408040080c205900880b1030407403030a049103260b12032054031a40b10303030080078268007280e80354000c851303e401c41ca00c43c800c610f41e945d04002e5140d5048000366405401910380c030b115194402c5401900455008401d9204541081548850810700549407100b52004100403041071908010140c001c04900c00d1451801ea0545800410340c0c0d00801c41d2424006030006040701c42d035030342016103035000d0501c0b16501103940b20000a46070140ba9400005c14800000500c00010f0b130020090000c0030b00c0e9115091500c0c0d5400c15015103220901c00e07140015040e41e4148032035907451640c080100040d2404089000c60b11440e842d07141e2012041118031075071801c6030b10ba00450065810010845502400240c400d280c80c425151b8649840a507c208800000130b10040d00a82c00b418025802800e100b514080d101c81b41402880165028540c81c89500800a1950701c5802c129225680c0701019015030307100c02c405905e81c40c611117456 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 230384577 1250 230383327 230383339
    0x13020103051e01093206011d010503060d0305041505190207080a080723010c0806090601020a03030908070605040503120c030c0405040515060a030605010909060e06010c0f0b07080604050f1b0702 85
    0x440c03100c5945c4a443c052603114580c2202c200d05240e0000b50804649405021040900ea003000740700703030303080780503294081000e94100c44041003520301260113106170f410030786900c0180c40160301e59aa0005c082c016050018401420b5041c0c4a00d084c0e075502c180e48964009603010500d004c0002e0308490140210a200720308041c4691261030203401007040c1545090034980d0369440245005900000b05034016605a401400c903082490000391500122540135051640f1100d0110400814500316590590481307410407050403d4503240d81c8961210b248000c103142c1d0750004c074074081e14100c00c6030700400a1411a03443d040c1f62509010252100502440360003096000d0016140c507000014030751f540b0075079000240b041c01c180016000c0402500410f0790f0303525120082c400d002810140a41084007401d10800350b000901e085200392001d25401890b100415083c0f2250f0707a0002d4502d4080c0350110b4040c03145646042500800c3c545c115450407541c041048280b00086a600060501da4005050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 230385827 1250 230384577 230384621
    0x408250501020a080a0b1206070c14011805070b0301050d140a050f07170604050a030e060f040605030f0a0e153114060115030f0f0513020103051e0109 66
    0x240d1401c9800110310140402c0b024005c204c83c01d285803182c41c150171000c1b0740803d04640d8a402142d584c1c4c07001054001848000266a03050002c2190b6203c80d0200c480c00078001d00d106000c07000c0858007420412201d602c00d204000c17030444101c5040c1d038181e42c4060050314005c003003a01c0754064200300b0f11000720580210100800480c10034410808241c80c554002c000c4603140c1404940f4140a101d180078003a0000c005001c00200f01281260301c42d5014034248440c1003d900010380d042c4124011640340c00d1001800050840d04030f0040d510034402d1003e0031900d5514211804155403500f030054856402000460380d00280e0010b010380c00803040010f42c0300312f203040031100a1060741500402249103650300604204403088904091002c6030030041c000c2c070b502d40300013035483c84203a0448106060f1542f0303c100703060324180d00c80007800207405020b01540c04c3c07050f4110302e2040490b0051780002c2c1880c000440c03481102c62010281d0b04220851516a880e10004c00000e0001b0150004011b8030218 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 230387077 1250 230385827 230385833
    0x601060e0613210209090a03050f030619060201061e0b121906080f0606030a1208040503070b07120c031b120f05090f0d0f0804030c1403191106040825 66
    0x103d030020504214441140e00040f4010842d985000070300381d100c1544960380200019074810147e4526545440c911030b20303030301e80e40300003a685520300440510010510100041007913054110004691280c08a00c07528841c411800322114507500400000d0501040150350315031060000d1513111400d0701103000800301380c1e40000c041c0d40c6c65a0020f40c1550007c0c0c002c0c06070030340500c00d2542001d0118001c12a010103683c90510709981716040e00180300b0780000080c20710030103204841c00710350720039041942c5107170100b0050120361a40040000d050f181c03043c6561594001c0c401c1e524400200504c40440400304c010442d0400407030040da2401d01d4841440e0102a80d0901419000e901810080e141c517800c5a1115460000c071040c0300360400c01448940d14555800490351a041501803030281c4000240d401c00740003075600c1240809641c80700144a075403005141c0c4412a051086035901d03120780740070940450b43ca000030f50740036112010030403508140111401541c1181445a0520507031614191 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 230388327 1250 230387077 230387099
    0x19021015052206090c0c05070f051c0c0503030d06060e0312041502030702060f03061801051003051e0405010506030d05031e1806070909050123040b010504030609050a0605090601060e0613 82
    0x94000170200f01a041564100501801502c002e0070800100700120391070100010402424600c10840040f4049860414011a000030002402001e4122692007405c0b01911004042d14810100060802e0004110500d404604603000d0201a10250700b02030600300210000c0f607092508806500c820090a001070301c448024000c184c260316443d5840e40387c1070043c4405038520021320510800755000500456462000083c3d4104d601e140005559170303420010301020600320700b42d8102d10021001c0104108054210b01e00c40d07481034060311808038148a0546060005690b41c1e2000c00c2c038000003048041d881c072142c80e480280100c0744001550808241070908009650482c0016031030803091100328018023525005000006031107030030016a5004894002ea20032146200e5611509241d0300e81e8411000e940156401c544204228522850844d940d4007000e9802c4075031a00b07040c0003a188000c003040b968100c500586581d20001400c40802080e5405103a0180042d18060700201d0700000c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 230389577 1250 230388327 230388341
    0xb0d02120f19110a0b160c0e0901050a0612021c0804050d050313060507030203031f0b041409130201020703080f07060204080a0303110a09050f03031902101505220609 73
    0x2c0000303094a0380f070904207200c1c03449102d418084d6400b5081041803104890841d00800180c003882840386e406450441c200042640c0824915400b4070203100c0c0180040d403000d80120580d600c1040f101e640c0740784131125103400791000780d80722800000c280d031030103004191000c100e40b003a110315250540b03c600050300281085010b07101a4004a0050300f4503060802400c007404080c100780c2e0811b020ba41d002541c9120080100c4c00c0205904c55002584407094a180040c0443d04a02600c0b1500d03258840c252103080703110703036200310a0b000c0866130f2403000710900050aa0180c0c09480411f040d5200d001490380200d89204114000b01b100c42c021440910203400030b4180c410140c44210003500b40181682c4015800a6090304104100c0d4001c41d0400300101c00c48130b0540700020340040c504002403c6006400e991800011011300000103150b000ca0218400b00312000c04000402500301e0307800c0d1a01c0c0c640260b07508418900700381080500c0802c0f20341042107011742c001c6566921507030242c09542c80707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 230390827 1250 230389577 230389603
    0x409050d0c11010c0b04080a020c0a06030c02011401050a0302010815060d05250504090f060b180a0f08100506040906090b0105041d03070609022404180b0d02120f 71
    0xc00c418040c204010b200100381482000d20300461000e00d0344d1124904c00c0c401520003045030f040010710814450091144100040d80207000020b4503588140103000307410407068041c015403030508007100d8007404d0030949050f202d014001f0085917045500665620b070010b4400390700789605250031081e959540004054511b0303412030200303030390503e07010400d802d984480c5403034502195981d120000c3c40d8000142c80c100c5e08103d101151560313001007031100904050b00302d1143c0c0c0300009003480c82d414801031056194441920403e010950710a21804814080d01889445802020a000d04110b02d03400c0540c010600500c0021519107aa440c6002c072030942c501204c80305515001001103203400e110300d00c10520f0302c50b40c0c0901c0c509003805080d1644101c9a0003040365594192143c00e41d03c07017409484202d1410450103010340e111250701c41e1103402c0361088a100300c0000380031103a00c030001c0c014140a0710014088044c0d0580750b81c2045448040c514800e1402c1c480c406480782c2407402044450882c080c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 230392077 1250 230390827 230390837
    0x2a03080f0901200a0b1305010f0c08010609060903080a0302090d0501050a0f090c051c2f0d05030a230a03090605071e0f0216090209120c1503060409050d 67
    0x40e000c4005803602c140e60700040000d454940c4010709403c00071a070758114550108032601700313079a400385004011211031000340c10f961078546425081c0b0342542c82a00b040d00f107503d4624403030780c1c3c13004110784c00c10450240034005040d8a600700000f41d00000035210041c032509000d800d05021a000c90102400c80d20191460f079151405c3c030580450754418480c00c0007420b8401e11400c80e071034035110301c039500c58403415004003c0c0300038040b5080415040704030781e01c2c5c0c0824030050310ba40360b805246000100244030300b0401007400f40e04100c0d03d01003484190380d40e8450095814100f02e510203a8010100c0c0099800342d1511031150101c0541f070f035006080c0c6040c29240000c410400f42001c078102c5d400188490103108049413070003900158508a600c501200c1e103001d0345040c58404040b030401802c0400200c101c80f00e4403020800718050b4000e0320b0220b1058170145454811041680d84d40c040c011025030300035a141c6204400c1000c40002164461000b9001003111141a580d061804015050b41d10000d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 230393327 1250 230392077 230392087
    0x50a090b0a081b03092a06030f0412050307080604090c0b0406050d0e01090b06060c03090a0b030108060a1103070309020303072a06140307050a170f01060207060c2a03080f 75
    0x3c03820b000f1055101000d542c80c1401c0d490150303109030755500c2000d10b00d04540c1100004204122801e165541c50742c102900d50307038403402c14189440c10050240c40440729041210481150144110141c921031180d951b43e0840907100c020902009243ca500e0940f00401405070108034161080001c1004081035aaa190740d5510158100300b01c0b00d02c189035610a03418440080302140025120f05d4101c4402c8940710341d500c448503446803551003a50a4190071008400b000603952000002640c100c0b01d40320300313a840d00d5480b03056140c21142c1401c07190b20004001d1004c201c109110340d10500b0801d20180c1180c1c644174450300c8040c1c903050072844019a031071a2a00c2850301c800181e000c4030007001c290030040070880c008840e10402e4080144075104000c004120031010b80d01c50302900c0703031040b04541c3c1003481d810402c4010200b180c0c00d0103004058420410005282d520600c8031009060308800c3c0c400366088440000b60300c2d10000412603200d200b81803404008104414001c1c05880880b0380030355518 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 230394577 1250 230393327 230393341
    0x180108030301090e0a0c09051f090f0b01050a140c07080f01050105040c0801030507030f080f0a0804110a030305030402040509121801020d0309020d11031903080105041b090303050a090b0a08 83
    0x1e40c00d13209456941c0e4020003018400600c3c1c0c8031502068841010000c1400e03502c480c40d805080c21200107200c08000102000218601d10341d01614000c110a502400380c00f03602c400540e41072140400600c0040c59002a604102041e5405007800d5004d40341600e9000d6503ca8040740f40c040300c4001410280d44d0f5400410040c42d06108500161200b400c050100d58076545440392182d03954480500040f02e40000e9004100f000ea0803a9484410100c4180d11140302680c01010725104940844804039422003080d220320700000180122039040e92458595540d55080c00090b01d800307001c59045116101002100c40c00c081d01034010314030341a410743e03540d501c00d01c0020700d8403101180900c20b1514140d2400d002d6120340500000b51900000c9880581050101103841c024025046e500780e0100040f60201b0941e218024034100d8400716010311004010700f038004201c012040c01e1a000c0f40224400300700103030040e009015030030341900700b03112415910701c10b40c60140e100d9031840000542d40000c1102d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 230395683 1106 230394577 230394581
    0x803090d02120304060314160f0f020109120503041103010e0c13020405040516021b060f07030215150a08060c0a0f0201090b01030b01091503030210020f0906070b07080f0603060a0b18010803030109 86
    0x1813b0188c2c028a650000e4900f2031315440800d540106914050080d01c0c1c0480c031102c05040c05400c988108400c0740d00305403821141d15002e10000946a6440c400d043c070404031255005100c600902d0b00909090fa40d40805565014040210502d515000305440004150641c0d9955507500b6040076445c0500b0b000c8040031603240b510810079025041400c00340560301c00d03a01c900340c03d500c4008040d20f5043c121020042040180300b407038440c910440303242d00300c0000e40c000001c03c12910b84658a072202c098000350341d007946001c01040f240601c0c2c8100d035100640e03440b82d10b0b20340303045580013929800f200400c0c111198002c11640a541030103402c1b0380e80101d000f80703840d54a10892400c0c0c5103041080350240d004c40d146c1e50002d00004001b1004034414907000b030190229581e0500400024600075139155007003d0380c8941d810084800840319406062803a00964481d8540407942007 = true := by decide +kernel

theorem cover : BRFrame.Cov 230215827 230395683 := by
  have h0 := BRFrame.cov_init 230215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 230215827 ≤ n) (h2 : n < 230395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
