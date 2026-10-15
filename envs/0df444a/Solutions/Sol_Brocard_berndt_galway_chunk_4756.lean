-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4756
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:38:00.497112+00:00
-- url     : https://prove2.me/submissions/0f50211c-3adb-44d1-951c-8c795dd064bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 855215827 ≤ n < 855395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 855217077 1250 855215827 855215857
    0x2130e09150c1c20090a0902090105041e1a030910020904110a020d031805120a11031216091412010b060706050a0501121a060d0c030f020312090a050d0206 68
    0xa280f425031001031030603d401c1840140c103580d01c0422025807804450030b03c203001c0d1072030f014103042000b11741c00307907119040c0e00b41006010071000400428201c609003201010101e00d403049464215004000d5030b4203941203504480420500c4824440064550002d086007500541c0341c0d0203c5001034020400c013445120500c2000404100c983d0b400300b800030425445890804c80c450741e001d60510f205032903400003043d550006a403140407040700c00c090015007a191a01440004003070031818115089440d441034007084800a124030b44014a4043c0c0d0044020720f0500c0c2010b181c031001803003802d81446140d004050f1500741c01030b500720a4200504014020748174035036038444c514114008050031034804055a207001c001090300c100105101c1c2070145c00c0b04014641103000c1034290300c1c510014000580c081542c0c40398100041010a12000441c050f100003000340c900c1d40103141c1000c80420150f451190700b01311000d210360300c4004040503074000b5120000c01041da403021450510521649040d421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 855218327 1250 855217077 855217117
    0x3080a080906070201060b09090621030a0806030309010903061832030405010e06031f060903050c0409050d1404030b0c03011e032d12020102130e09150c 67
    0x950404582401001c07071404032509562400e43c12822a48035000c3c000d009181004550801e1500c81e101c0e50700b00c1401809200a45562a0384242d03507030305604031045c80c1e0400f142c1f0714030b0304c6d4002c0c98940e07105030113402440c50280d403000000c10400b424003005250554801e2400c400c01010060742035030343c0e44609640004001a904480f10340d215003000b8542d1042001e0030b11b0750b2034001c0191011524182c441075440c100c0d000800c511034000034846008166912136240d6440040481c040c0180640d854039003840d8210b050460401441c1900ca03070180382401c1d1100c000860001d0020344060692408994410301c5c41c2c00b1120a204551014007007000c1d42042c8901181c00000a504890740c1c04510503410b0300350220b003400303020f4034480580100d0344501c4950307459200c000f03c0f501d01c41c441000e100b082c003010756485180312050282d01c0010b0f03501103417142c00d01c45081082030190000d04895181c80ca0040e26035951503000c0489110790320740f5440803441401002041d90a24252a080d2542c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 855219577 1250 855218327 855218347
    0xf110d06050108010b03070b040b09010219030306180207050601060e0f090f0105011b0b070c0f0212010f05100503070302060f0c0609032820100903030b1e0907080603070308 76
    0x905000e00600e10f040d481d184841c1c3c003d18000802d00e003125072460f40907003000d01e4600c03484915045001c2c2107065002e1141000050b0129550740c0000c80e20a841c0001c20b0b41c1454910b04010b80350100d00402c07103104200550120b240002c0440c11508185030180d0014220b0020400030005090b41c5601301c07a4600501c100c3e041005820b40c181c0394280c0e01ca000b582002000890300310f038000d10140129a81d103000c00d00d0030340302c0c1e0411b071240d40c010580d26035149100c1d03011450741d1a80d901041080d0350b440350302c640381680e18001c494110b12500b1800b0149070403d000a51102000c0c40000d11031140010080440c403a101c00b629001e80d0100c040c1c0d0305614282e04250b80b254043da05800234162894410400c0f01020012108949041e80c1c900e48880300141e80c45d0440f10a501c413840c9648200d00c2e4011402009020303001d800c42c825600803500400100038800042101c90b03011641c2c01600319816100c0c0c440e19626544a189464011150346440b0080703810407415030401f40816400007026002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 855220827 1250 855219577 855219581
    0xf03160e0a0e010c0507060c051902060709060203180405041104021603020d0f08070c0c24090b0901020c010c0f08072009010b041509051e1005040f030f110d06 70
    0x208840040091040d12410407500f03080701c03140301d514408110180000004504180d000714121002424150300e006003040215140c0080944080010303800001000725950348100040000c04a82c0019402c24144480b80d41d100c0c0f030718110b458004c95846000078140040d1281c044420000507004559441030301b4210400401031001c00d4026100f240249000f80d445851441a03000181d0340300c1c2c0356074844200469402600d050b0a031b0781c040c0580d00104121081e015002c04170111000b40484840d03040e00e0241c1100c1d40c0b40e00c50b0a015809000394007140c0d0300840c0040d440c51092801b18403010441ca0403820100440b0006040c024001c40c00000f0851900012840f81211855641d501e944070410460b9411007401500c0d40d101092104102d820301044141034000c1309400c14101c001d4843d008100210b10150b591000b6011022290001c1c1c05d280c0158541d00c4000d04d456440c0c40d0500b1a100340c0f048cd42d01c0001d040340f80c0c0c40f60f41c505001540880c0303c44420b00070441d444002703e504010300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 855222077 1250 855220827 855220831
    0xf12130b22060c08030703090503090414011a18010813170307090803070f0b150306250801080607050d111606052a0705070302030f2413020f03160e 65
    0x8442441000115020b0f00074419403030081d030303c4074400b461596258401c4029101c90041101c207448140140d014550b5280606204940d00003104202c40d03140c0b12480401001c01c040d24038450504100081045800502105030fa202c00e080022040d20707500759020054a200102a02102658a010000d520004000d5004a00580d0760318002c1f2b480300c04181c1c03207109502008160040b82d82e0090005400d25004651082d1180c400346841007074400482c0c1400021969180303c883c0d40f002c06400c10403000b52400c9a08a40e02e401d4020798100071000795540400307081c0105014000c07400c418a82c519412025151850200144c0c0b2640c0003441c141107660a031a04640d01810000085d0448240014a0b0496000c14103918054030941d801c50354564040401502c1c94041c480c00070025032000c00c5074080e141800e4000b020b0428001854044050000012503080b114640500140403021483c01080c503070111406201c9024080c00246004c820046031001ba412103d400030740ca20302050018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 855223327 1250 855222077 855222127
    0x2f04080d0503091608300711040e010507080103380403121803081509010e07030b0d170c01060e070f030f0c050f0f0708070c170f12130b 60
    0x66440d04e020003c0300c20300046010b80e03081d070b600c6000183e61000c0044d00d040c2c9010151045010b41d00c8018180618a61140c00181c6941084804503da207040500c500b1000c0304040d00204a91b00381071031b00401c504010f11020b000c1400c2c0a20428001540d441d0064500301c900b40007403c5400750030321241c030380318003120141e000c03404a0300020350b010316501881c4510742c2c2803140da04101e84540d805071021440584803a28140d12109c0b00e5519495014074680a030010a104544504d0102c10090580c0d0b4000000e070301411020b038240001844a65609519294141c41151900c0c95494010b00500c9140d0155448400400601045540100c030241c450210b55038240130b8500400394040681d038030b101c508800102e0070091301000202100261001421042106103400f0044e221071605401c28042543c480c0038201003046100d4099105e00443c0c40303030b107000c2e203086c55014049940700d0a813100000381c1003000252010403a110030300404080c0401103003043d00c03861303044440100c00b0f00c40003602d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 855224577 1250 855223327 855223333
    0x512030c09190e0603060c030703110c0115031506121103010e06041514010f032405070512090f100b0406031b151d010f03061d0a050a2f04080d050309 66
    0x8105103040c04986c90744540004401c140c0fa540fa4424221b00900d446061400308803010300403c4108682801940344000c8402c01c0c2810f9a070a48c20080e441d44014191009140e14049041002000070102c03400c24903040f030b0382c452020790504003180c01752900c04681b01c510b0080d4004c1208200003a02a440c110f00f00382010040d5010b0300c0c6c602d128846083c040c00e0000e260180f400c100044170107031510f0142c071440b01c00409030071050344542c05541041d0354100100f0b40c0407602c80044050098000e5000a16900400c80b040c2c03c0720015450307400014085915030b807900c451040702c5c0c441d030300124000d60340210000c8000d94400d0324041e8082d11070056000c0d130400200325280c8244502146010a080d00e0009010a81800c1c01941c40541400348076040c90340300e95000a40b050030014540180200c0780840840c2d141a00d00784080340d40091185058500e01029260912000091001100285081704141c0100d58100c44858041ca5015a055124504070042d445a200d006580036510705000c0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 855225827 1250 855224577 855224581
    0x3040309061107030512031e0a0e0c150304021302090622060c02060a11070e07030e0111160206030c040504050405030417070312030c2a1e0512030c09190e 68
    0x40e0f519084035200250841c2c0c81300381d1103080202910011600055440400d0103100016401141d544000f143c0e0b90039440c1d902c140b0540e6009003400320290a0710200e5001d0307062881c0e41c1905c0014000500040d00603400000340e030482041560407200b81c1e40c4018941900c03031540002c1c02807005030185200020381582c0c1c000040f6a4080c4031820b06059005003024140804000210740c445000b00211390340d4401c4010000d601450600c400380980800d950100e100d0f0704200e052401d6524140381c40c214017004010602c0140c05d54003c02c980c00f035040b80c0103903498460b040c14441034000d5401c00c9a1162410080c0410024008014403c6501c0020091108158100b986494030540e100142a11021003c01c90045120703500c600307051a11802c090f1351210207041516168070004d01111a1480300304440340500c4900700715130389190081c0404401070705113580c4046c0c4804500203007410003100840401d50000000c029214a408082e05001d50a443c06a2650b4480820b208181c162044000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 855227077 1250 855225827 855225857
    0x11040b180303031302043207050409230f1605090402130b0c07121e050a21020709090f0311070905160e030303090a110a0b030a020a1b0b0403080601140304030906 71
    0x1104c00345400156214400c40c1c6041f45141100940007803003003080007401c2001007461060341c400c0100c10366941e407a590004041c1c00351010001c10213001c54107848141020083c038840840410025448645460342c2c84014150218001c0e001f0146200c0340340c40781c824041a1407891101074911325034810201c3d0350031552207008010700f443c550b030046c20321054130300001900d1484e8841007103400d114038103c0d0004a034a40315600c680d175507080001c0020400c104035051890b030400440001d4421420200030000044e900c0040341c0c01d5100008050064040c0506c0d400082440b01d00b00504031650180014a029101c030403c0b0700e42140c0301c001240c020300c0031640d203003400170540b8402c16481d0001d0080106039240d0341c8031100903020441e070003541c030003021400074009406103019a400b881d0258407280040c0c5c1c05030415005801a01c0e0058031008404081a40d41c800d02d500700d509402c050260382c07100c10040720750004c1490360301c51400000092000f016401400c0400b205e07015a2031a00e618443c030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 855228327 1250 855227077 855227111
    0xb010801060215100302040f090b0105011106010302040c0201060b0a0203130f05061c0e03280203091f020c062206031104090b032410050411040b18030303130204 71
    0x201640780103a00c001154034210480c415255001880c158241d921282c3d2980058240d82a8190400207103458518080401104030015409000b09007428a815554440340e65a155014070001e4401c2c0e03141c02d60607035154003c0d44944040c11110030750565520030358101950340d922100352405049212000001c041011040c034806403000180120300c0c0400807203210b510002040c64003400c05075245191a5104810401000c14074411120016004080400d2120f005030500422080d500704000d94183c0b95104400d241d85030005140f20001d09081c05400c80c5010501c246541e0080000151007120052401e0811074034071107520720305400d40d1120811401d07a40d51003080e03034004034140800c1c0100d903602c1d042001001e8024040310107490940b8908c3e02d9040c41460000350050b00745040c0240c2061110003039000d0402034500303001000d8440d02040c035520a03032082940c10f207004a8034081c00642130391451080035004048031380300d0808480401c540801e00c0c03400c0388683e24200c040c5d85420820 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 855229577 1250 855228327 855228329
    0x50a140906030601120609020301170f0f060c030a1104231e0f010c020d14060a0b030c1011340305060c07140a050307121d120102040305061503010b010801 68
    0x1510711802d54544a0055410119040b070030030310161100800300e03201240d480a1030081240c035503c4a0b84000320703004a4106500781c414101d65402c54280000c0b608400078102c1d812002d211502035036030390f824448200420122081d0140788000050000e090710070000b032050304c0c00c0bc0590360f1340307900d00400070440181c1d0000c8006611400b010701c5599245056102c4031000d62040c100640c5015055000803106000004c4c11540b0b030002070312035000403d040104660191074882e042000c0c0d114080000d598081d2200214812100359075100300d2280315440e0200300d4884101101e0b8500c40400700d5080c0510044d1130b00e02d030150108540c52030710000d601c03c141100d4002000d0406074440c2e2016208981c01640d09030b07120056104c085009010800c840d0340900c0c007400c0955215103451402920041c9824840310420068004c00200b070261110002080316007101c0d02d529800e81019174502a015660001e8007a004281c100304490030901421540c000c4101c0080140c0b0300048015100b014003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 855230827 1250 855229577 855229579
    0x60606180501080a15030c0305010c0c0c0506030705160b06151201090e010219020a1106040b0a0c060b06070501061a13092d0c0e22111207050a1409 65
    0x8444420050742d40108070789a044a03000d9404210108000e500200309042d41c2d2007110007440c68501001070000a00c03d0304200c04140c40c04200e841d2042d00d43c919040524054076100d0303031000000c20042c900803811205110540d80100c0000c114904004100c000d003160014010a526100403110001036812603815091500468480c3e9003003d42c0d0b80028230780041c15100c551f600b00030301c59241c2d401e04105499403d1550081c00b91016910304070313009542c140c248500969092005112442c0079406803555140c0fa4981181c1c200c035281041005001e540a40075003009000894074203004040d0404400d40d0300030142d0b805c40741c144c0c0e0090080c40c071402144030003040d8a001d0910101e101900300544000201c410308207010341c00e0701601002c0305040584010700350344a440ca441d00360000380100303105074210703001017507004420b4a8120301403100340c5000b5560f070760741b040c400d00b00411015510010340186184400c3e1508640182c03041c0c3c0200c0b404070110300c111180e51801a282c40031a08030b87c03c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 855232077 1250 855230827 855230867
    0x2104060b0f120d08090f0708030307030605040b010c060528020d0b030d020613080d050a0f0b0d02030303070c02060403060203131a010321031d0c01030f181704081504060606 76
    0x1203c1882181c03a003101404c0803415005001c0c184544d510100005405418040091662030502c01c0014086841690110380202e040038001403050b03802c90f080e807a020b500002d01046aa0b6094000d05905003041d60690b200000c130340c1c020702c00300580e40c060b1046805820741080180c400701c1c10035035101d10758200d0200584c0102c000034480c01041c0c0140c1c5445205640c3d0710700b0f24030403070001c0094030f2084802003003040c2e44900302001a046405843c031045420744040300300c0713a410340101c1c2e101e1000404030f50a000107a03101d903045440b543c1c1220019908090b086499080c00b401084084c850580242c2d04a5072001e41e40400c0100b41c1051412a9401041c0d0341c9101c124550ba0035009525861070010b142d52005004100e26181c43d60b00510150b00300a0b08090341888005403ca4a080b40017820580c0b92080300074403400a600c5016599400500c850740c0c0541c0031440c04468400c276000707440140228113a0014884550300c440e80201d101e00d0342449a42d49a04080f40c0700c106134115179400c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 855233327 1250 855232077 855232093
    0x10e1c08090a030f0f021c030f0e01020313080303100512030d0b010c02190e10080303060f061e0a0816170702070f0b07060e0d0507082104060b0f12 65
    0x941424020300c4900d60242c4a0041c0b10358a407206401e550b05580280c5140310f04030010811817410001500f152805070b200c00216803a0354500902061170030140e10107020300300404d01c00a030700801c1a41c0281403440c84048145849409243d00d0750425180100d2144802030003080303510780b9140264007002802c0c0154102001019054007401c90740c1c92030380c14403141441050160b19504001a1b20212350000a8409850040039202c1200014550340e040349021206010001c804001c4a030010022104030904500d13110024649100e4814000d5108a801040f89080c0800d4005040c031400107485400d956961440e8048017080030150b6540098400102c2c0100052022862604800584125410301d03886002401e03081c1000d40001d0303021000492501e04024941c040d170586a044500a40301100300d2103406401e1b4014090b000f040804003103854070011840038400709100c60350018401c2c80e030400d41030030b000074129150000d01614691043c22214207100110b40c00320301c002001400f0391 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 855234577 1250 855233327 855233333
    0xb03010b131a0d0605040209091c0e030c030d08150109050a03060f06090e0114130b0609280207140601060f110102090a08031308010509060c03041b0b09010e1c 70
    0x6100b44040041c1d600000140706606455150440e50214454500060700d03040c18010411980001020500658400d100202d0072203002c0c4a4284010310030300703140295002803c002410442c180e00c2c0e43c1d800d4402e28021090542d403014266001c0c840e03100e100200d14454000444600610740202074000e1a248010000121140d01802014842c60030000307000340c8070754014040d2008500e020340680c0d100e1109000c1a001c3c24405904547e00c0100308074124070315030b1022130004000b001540300d01100c00000d40440d1070003940c0c14007015244040c01c09404100320810080d000200142c9400030405440800d9490005a1a050b11060b46031455500303200344017100d4a00d40d05034141201e54003400841d07525100e280700301c009004141c0103551034003280300f040e070300c00c0e00142d021208a0b0f050805011840e08d02007a101c0d007084c0c190720301c6075583c0ea540c10300050480c074100b91401c4901401d0400640d40c8030900c094000c00750240d030b50210548100381046241700c40928459030140a0001d10400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 855235827 1250 855234577 855234581
    0xf12080a0309050d02160e0603060604021c060e010f0b0a1403130f060506040e0d080604020d020c060f010e150307091d33010b0307030509070f030f05010b03010b13 72
    0x4032044070301d0007150000c0c6642c0c849090001c68000e60300503030711040000009010010044001c0c02c801280d01003540361420009035118405081c0d140a01d90026000300320298441c0171444400742c0740f034103109250f0785d035410800c070341e01c24483c1c0c420001c00b40c0400300300381040b04102d41413103103550780311808112080c8101d5582d90000c1c0a0b40035074480411180000b42829150f16803050080100140710300d040d000f480f0a460400c003020701c07543c02c0058101c101e150840e560340e4012506603001600d968030700342d5a40c000e100e152412034291241c1c400b000304c56080540a0341c10381c2c804a01e02c420a4884d081c011480c0d2000e0444181c4c55000341000b4488803010754003603559614816601c03142075194000103800d1500080d040c1e01c441e40e1280a1440d803042d0503030b40210703105001490040940c540fa1f000d5055000280c0101c0800d900d41001c1410000100710782c4018200603852500f195540740340009030040c0e07c980840c0d0039402c040741c0701c24916042c4070b0900004000341c00b02141e42c5101203d040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 855237077 1250 855235827 855235837
    0x1e03190f0212070503070e061201150b03060a090e0a110102010204230a0902270f0904081605010f0e01240510030e0307030f171b130e0906040201090f1208 68
    0x11081c0f080c50400580c80e41e00f0050300000308140303a0004c0e91030901e0800d212a403070a118464089038100b40f00d8074100d40d00c0207800e00403aa82521040d4981d1074440c005500d0b250264855401c1c2d0b0309044000380c24603030106021790031504c214070794420810f248005a00b41d0046110b800002100c3c80e14009800044406070031066030001d05520030580c03500c92000807070b0407900c4c140c042000b41114440340030f085152501054101150101c029600711070010b0b45c900b2000b48011703c04180818003000761480f20780403513a8070780c0c041b0092000f00c3c0d00c03003070040040c409400419460360a0410003020805102d010218084903410b281018a0504c4103105504001d681c99800b01035459136100c0d02074005101271300001e88a030b540c0c00303980c0d242070300000d00481d024202280c0b0212840144091045955480045510090017141e19003400e105403210030541a03010000b000003010800c006400d0218100b8403852003620355820180d11041c1c1c400b0340310840e0280782d400400b2480c5141c003040750000680 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 855238327 1250 855237077 855237109
    0x4020a0b0a050c010f060810020f03131a07020d03060512070303030e030d110304020406060e010c060f0e1e0f0a050a031b1a090f1906020307020c1e03190f02 69
    0x41c3c81d1648802145085035041e0311445440ca03a0380d2405c0c400b0748000d02c04901403061001e81035041407405030a0b049640b2000d0040140410442e2075481080756131111140120040814031841d4a000303403010351144103454000d000607181a4010490b407601040c3e040350303040364130020001f05046660584c0100303244028250584420b000ea200c0081480c080d0944040302c2558103500e0703007461320500003580d00c030390011014448039401014140c2da100402c68141508180702141c410208061400100405612561940541480c0c84181c0610262034200d406866086034071a104810030142c552040441c01071081e0455600000441e10420343c25600b51088021044e140000340d441100d410503503a03440004619103001c0048490041c059205a0594140a40fa04810302410b0312022070f8884001400301d980403002c12411442040380080401003e01404038413404000d0409079644030845080c0700b4401d10281080c0040355541c2408000c4d0b002d0700101c03820940740e00304112488000011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 855239577 1250 855238327 855238337
    0x60840051f020c3d0b0306130327081911030703030906050c070504020c0c040c032f0c06011e06020106030b0604090609080d0c02120703020601060f050c011103060f0904020a0b0a 78
    0x10108845540f0390001300890b08450006442180c64281400d1210042c0b03a10408000d802c45100403e03003102c050004011112412010711501c6c0b4030038503940c412508071100d04d200d003c11843c11424091a85200c079402030392060201903141007055a150468003000f000121480001c10074540941c01528a0b10305007400d4030b010315120404181280c00c140c10442c0340364001da800801c5401d044c4140f42c2100c07400c0c82c0504c0240e200d8170144058000c0d05030102c0228410f40000000750180b00182c1c0c031145200710954040b0f5035140c0c81071202804202e2142c806607507801780061001e00500c00d81040b02e84c44001003040f40e86075020803000f0f0040d00b000359549915504040300281a14009008200d041c480002d0381e01c0c01498020f182013500d0417076041081c010805070001c203400280e01e504647d03092404510607081c80c0d50072a01401a0307202c01e030140d030070850600c0701c0d250b001000e103128840076120046c140c1184000c00541207010354020f074000d65850014403400c3c0b810030080101d20238604107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 855240827 1250 855239577 855239653
    0x15062709060f090605181c18060903050d1d0f0d060606110c010e03060406182f041802010503060604120c0305010501060840051f020c 59
    0x18203025104800350b035644159a9001c29010000d00d0320032190009101034070480b04445039101d0715910350940030b500c0f001c050001c1050308414800d45403006280d10120a01062130f65034600504800b4681c0401c8865001c3c451110748690700c900b040100684c2030340108064401c15200344000d136058500c03c560005112181140032841a0143c240200748554690070014100c2ca612402c001e84d1158040c1085014005c49080b0f540008490340c100340c00c80c100140b2081c2d04002c02d00d40100e03140000b4802c40780c419240f01d2409020310444910010f031002071a500a44008001c2120b18421054215038103250f40180035501c40c1c4c01a640c4003401918940c078058941c0310060403010104011641a02c0700d000900400c1004c0c0509401041c0034101303240c82e4181050001904020450740b13200d1180d00c0444070f4a80044c291103249401728180911482520364140203458552820700031991000c0d064180065108502c200c4000c40c8004d40540300d070710b20f41d0012070344015019112000f00b06000031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 855242077 1250 855240827 855240833
    0x3031809020a09080d030e06041104020702030703050a0606060305010b030a1521110301090804090207050a170d051b07031223040c1d0708040201140c0a15062709 71
    0x8000d00180da0180c44070f012007850000014a480301c4060081d04041c1810410034010400283c401d070031a6020041d13030309998403040450000e004050010754144200c0c0e10010a015000c1841c50003070b80190340034844c0035200c02c0f0036802d8070801e104000303400307604000103404820140d000c46151010b21520f000720a40d00e411882e1124101580a0300007007004010004100200d203005400c24026070090041040700e40700c4103001d00952061000c056000521102088803d02100c8081c5910190b0441c1c100d8180100760a15041320368812400c034073f0f0401042e416240b4850907802d440301c0c814100c0c640006513030111a50185900e101c810345844060005005045c040c1c2801e1940031410900000d203841c0c200480d0440485e03100d251900466007520301001d10046020340d10150500b4101820388480c030040390743c0011040d665202840104150303614010100300004410301444d1902034070580b242208046504602c190001e508000c1c200042500c0481d4003441080d0001c1d400240700511a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 855243327 1250 855242077 855242081
    0x1212020708060c090a090c021c140d0b040507030e19030c0203030c061909020109050103020c0a060603140c032410030b0c030a06142202070c080f19030903031809 71
    0x5111000c000e0f0001c104900641000044600242070102042c0704da840c14030b101940f1820034609022000501440c5080c0b02d9004ea10381d0b0140000300e0321520340e00d90710050f865008252400b407840c4150304100c04194602d1003070107400e90540011010300001c8660b00c04600703031f856040c2411030600030280f0945016aa003071010300b0350811143c0c0038110138a0310400403240980c40102d8101c0441c900b821410150343d01c01301580a4a40a00300141c0e280711161001d0700c0c0001e80030000b0011030800c0008001c120000e0014030038110403400b100c6408422104041c1c551055022061010407841310341c0900d281403580d02a0440100050240d6031501c2c1c1c0c81d00b005c54203040381e070140d80d1178000080c000c42c072050748262002003070084008490f5045800c005a071440c2030700101c4c045001001444251107205a0480d804958001c00701502c5a41d503e03000c2e0345641011400c076038507004441091401d0b460b1900d482040c0c42c3c0c59601c0302c101743d05682c0c00703403000c403c2e0800090811143e00e8010031140d55078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 855244577 1250 855243327 855243331
    0x509130e06070315150507030909020c0f010b03190b150d0b221203050c0409090c03060b24160c030302011d010c0e090a11030408030406060f121202070806 68
    0xc580a4400c528203120054250341d900c8194401c242d5100104100c01e840110150a802c3c8251800c1c0f56900703101d080c1129203818540103410000c0c0700094406c090500098040c01e10380c4d201000307000380d502500403d501d400c0c0ca0070b1b181101c80c4a0010000c0000c00c8010b81d2644031450102110701192402c000c40c1030000d4945040301d0030728141c01403200b17000c288604200c24455840750006804055540c00030580086000d00090540311808100c0700daa08909a0b03000e08454142080905c0c404d040207a0000b030188015a009450b1420003040740c1065083c000098802d000071400c6140c664040408590040030100808030b0224038550004d58a802c40c00011406030f80085001400c0850860480c20580c01442c100c0e071400055042e076940029507010030901c1100c0861582d40c420001802400c41880d80f074240740e1000040000704103e010140d405280243d0040118035101d0121141d0b0030110b000784140e000c0484e810300001001034610856000041c0305480b0701a6488198514003401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 855245827 1250 855244577 855244601
    0x50604030f050115062705060a1805060a120b04060f050613050405010b07031e12091106070308090607030e0304050609010c0204050c09030c03071d0603030c030406091a0c0d050913 79
    0x3c2910b003c8451140b0581c06010b1511541d0000c102481c7c9400188644107080000080c0101040256075069000788030310b0041002416040d0741d062400300c000d1107000421802c1039240c0c9012010415410144160003d441d44032000c1d151803410802044400e4001601e1124800c0c90781d1000311341d984130b5004140c000d00802100c03984414661034040c00f12001480980c1072010402402d50040d0b60103c040f80b0103101c00da1000a00100071308000810b604e220f0f5a0781d4008000040ca1010164003c00440c070a54400041d9079868507031001c1201902e449a10701c6406074400e01003406645000f2000b0305c0d0046050404104440702907001c0b03010b940307044590018000340401d132240d40341024061a01c203070004401800300c035030500c190704204440d200c2d00b004503a01c0309000540c03261010001c40e002602c245044030346542da680002480ca4a1501030b6101c03040705040780d000c5c050100c04c19038641c0182e48014052450301904111807982110030116030000d680c005964690b03070940300b00200250 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 855247077 1250 855245827 855245837
    0x90804030b06090f01030b070903020402132108030403180834050603241f0e04050705030f0702070f061805091603020304050c1225050604030f05011506 67
    0x128504044110010060a00e80a8400300d0101306441c80e07088046030641e58441d8010005860742c1d442290175020310f400c000e40141c4000b0710b220f41e02e400208080b080700c1a105800004100320310040d9102488444024014070b424000306000074080e80740c0c054440c001c140302806490369401118580b104100002c0f502c5001e15440101290031380c05408004c2c0c0300003165004052801022885901c0010b054140d03801e03003200000b6101e5441104002c410500078030128200e44510b4000100c005400049400701d01c240409403113508107802100e11503615500c405065075620320084140798001000d110031800b0304000411450131070910300010b4a11555a080480460189280c56048035005075100b4144a0200450ad01d501080c4084a125a1501507125121840c06528010310302c45403503488240303020b6000303c19500180d080c00c48951020503840d0788841d01c0c108240c0c00042d008103034100c08104424004616000e80242c000752060000292490030490a02128031198100b400020303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 855248327 1250 855247077 855247079
    0x10315150e03060106020c040e01090602120f060d0f02040c09081606080603030f0412150f0f0c090e1f030b010b071202030f030714070c0603150f1505070c09090804 72
    0x250700055000401d00190014800380d4180310f4041e545150829407c0d01c40c6480d00030040551400390454054250300500954a954150100341c502100448500000703c0c02c1000080072880c6c10002c140300c6940248406510b0b00c1c0a8080c0700190100b555813605010b12900c0000d034081042010f1900c03645c0c40503540610a0401000030301a01000d800b01c0c0c403a80c010b21502c00310300c070050200e4040703c071211605000c0002d903103007400820414041c0d03104090300c0c4c008600080744542c0c0100c00130204401041240102105c1d0640701240a0702900048000c840c0000784107000403405112028a002e50800c109aa60f075107020002009802c10109040003090f1903080210f507407960a000031060001d1400c00103902c11801841c000100543c01304180015445003c500b407204803202d47d90040900f0143c0c1c2d0301d07814090003805000d1070070b0a40040c904000118606008000070030b1b41c452210f00142c98520080803100303908a0b40098072403000c8540300060308101880b4891486200748207c03a199 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 855249577 1250 855248327 855248369
    0xb1b0102210709050a05090115091503091a09100c02100504050c01080601021b0108100504050a1a0f010207032003070e090d08060108040212030c07030317160203070f02010315 77
    0x3580c0303107a115502856540d0b00510007a501c1f07907450303070641e1401d0100c40c4403a24450313005c940c18002613000fa5000509542c08058040d41504802d00c4540648642106100030349074103100d03040110741ca4071245e0400d541202c030b03d00340c940000d8800883ca1040b12040d945410401084074800c1d24202c070580c0c0f2140e00004196040920b07190321120900250000120b40703042e0200002100031454100251000010307825000180d00300060720010304100501c1c078000c240c040c02001145c11349c20400302e0843c0c4d1840c0c5444c1c10452600c1035181170b800360100b5031659680003038902d101c9509800e2400d514a500c01a03440800480008080070a9018504d050031140303a818803411304610380030044030764200050b0b030760003451064225605070b42d851541031402d0041415401810a0034010340100719000040c9944a820712800c103401500850180c0c071160340c1c0310711140c02c2d241d1610242e0018411000440c2203c2c03600082d050045c1004500c04010070b030541ca0801c0e558100902410903201c2090003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 855250827 1250 855249577 855249587
    0x702090708040c030b070507061d0709060b0a140c06041a0a02030103021005030421050919030308271207061b02032a161503060b1b01022107 62
    0x2640d810848031600301521040c3e02e00d4464000644050107601c01b181c0560f01c50030440321400e0b081070003000705502d802e044c401200429050440c8905c651a0046545480c074821142120003040310140340507c8248291030203c0181c00400d002d1006101c030209160307062041a100e42d20071003c4508810141a1061040d01c020700b400488610500043c40161036115032030781c1413602c6007480d64981d0341d645480700710031522051008002c1402d54800b41004d8001002d80013001d070032030320040941820812245241883d00c009030000d00c0c03690220b001250301031710702c00c03c0d601038005981801c1401800580303090f100406503010502d00090b96428088544280e5a00361802c0c9079000709170b482c944000390742c0d00503401e4017844000030103030b0703804c402d81ca402e07262101d80c5410301611551403105104403441c42d668450b8000c068002013207003403034074405d1003284140c0f0a1030410030704254010303205009804c045e0640e01c09940d801c1004d0300f143d40130715100c2030042d042414440010714140a0043c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 855252077 1250 855250827 855250831
    0x60f05071701050f010309140d08090705060715110d020705071a090d0209090106030611040512030a0915053603030703020a020609030c0a0e0a0b060901020307021023070209 76
    0x40074107400014062682e554603500388602c003d10380440c00c0506418004030380c24090090580302d00c10303406024070741a0070600c00f91248040209070b5544590303a2061000d20700c901c84005220221441c1244203404480d0300014034a10495261800e140700c1501e160b04070380c0003400507560340e88012001c01200c0404100d011050201040380c40c284101e207008100000c1c2c020000a218000a100103040c4090950010700116003000c4140414448681c0143c103652090241c03074010b134410302c4801d10b0648004126004d400207a5692611603140901c29803440383c12100c0d40c2c00300b2404201c0b040140c2161041e41c1c4070081131039040c40d201600c051140030040030780070969000f90010320400b40440e030041040444641c06540c01503031690a08002428410001402c0303a128181d80f40114240d04c00e07460a91140700b4004042102c80303408403c20100b030090708605401a80304001080050400c1c620111140e02c003820002d0740d2590b01d20001e040506411030f0a0101080031a9400a620f01440055 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 855253327 1250 855252077 855252107
    0xc0c230c10090905070f0f030f020d0614040b01050a020a03141c0e0c09010b0405040f090501020a211e022107020a05070e010506190905060a09060e1518010309060f0507 74
    0x36a00084406002d0b111040d0080f021023410f9a90514070f182200c5501220401080002c0800000b902e4402c43c44129a0b11181c003800356141c405c0c50b40e5a5401103085a040c2c3c107064005000c510001d5804446403001d6002c4161440c1c018800010800c07800c1e80419620f50381c000001c40c908981c0030120f45046d42e000c02c05440740c3c504100400006034031200f10340c152141503801148844120710000701410107520000c01541c0700290100d08143d01039014242200329100b180c45c2c000c1c4900e80e03082625012103010780c03054034070702c915820140303c1d03070040c1402010106000d10a10701c42113620100c6104490035000760308180030a008102081c8400006024800c0024100707504000118040b0301603810a0300f060a20b8040c4110080d0082170f04500915004040654a13440034100412061061141e1000308082c2280542e0b149444040000324052841301c5030706101c080340d005c106840005880b58141a40c1b03400c118003140c0c9034016070b004050004404580c1307050a14000342200416440c035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 855254577 1250 855253327 855253337
    0x4061407090b030c1b0601030803071803020a14190311101d040e03042d080a020d03120b150a0807050c1903030b060c070303030c0c230c1009090507 65
    0x1d002e4001e59038141c1e83c11190b03010003070703440d00704015074101000c2c0907421207805841804000000c00c50100f00940c4203c0d1a545e030a01e8440300c1c0c00c4803089185043c0402540300c1e1020406020300355105c026180522402481052082c06020204401e2542900140c0e00703640f400c00c3d91070150400401403d00908540f0b0f00c0018121181861100c1402d11403143d84240e4403031100c0fa8400300c04009640140035100c2580c50000d03900d1074008600118640001c2150b28285c030000b582110101e28050095000b504c10066803c07a030364101c3d510103e104101c559140d58481c28249030f15200090000502d120131440d40d107441c0d004001e4204400240b171001003100c10000070802200104411004401040780d0001d21000c0c0d1900390044c00b20901000c4d0011000709129199100000e15803048078000d490800401051039801c8612000c601000b03490000c04070200e00450044024a030700b1104201c0a03580c40510351000100000b0b4655000400246a0502030000c0c030355a10905400c00264180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 855255827 1250 855254577 855254579
    0xf14011b02060f06150a03020309281401020c01090807060b030c0a030b0714031e061e1323010e0702031e16170421020603010e0912030406140709 64
    0x790b9400b00141100030100512011400685132901403050030b000510200f5121958010003d0007904110b40c800c81074415581a941c00300100244040954501580891a5103054413403e84d2490300c0485030b049503508102c0c1c08641a000c1c41104503140c03048032034903680c500e03c1c01c1c94015200540e615510a410000c1a03080f50703503c2c0000035048a034042c0c0c107542c491359400415110703400c0d9001082007090000080056030b100d61584014004110030340c0d110951612018400c00203007461a0100d59074120a5002c0b061801c0d400c4511a8103005c2c0010451068050303d140d548850000c2c440501c41e0706100501188504540d2661b0003c1030344001e504080303a81c044081c01c1c10f4170480c2e0079080c00f400104524000107600e01200c49030b8000002c3c14410034900b0340109c895119205c0c0140e040d41c41c041d47c1c001c00307144c07500e1100d045400038030340c0d07040d03908141140140c00b801900b01091842000c845041c1417000034060352086000f81c10029030b200c25040040442500185504104140920 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 855257077 1250 855255827 855255881
    0x8040c0e010b031f0510020d030b1e09040807121e0905061804091509021804020d03030b0f09100f0e04021f0912060b0a0b030f04062c0c011404080604030309020d0f1401 74
    0x5030180084d1049070783c60015241c0b42041402cee03101e180f00151148400030080e004042d004200d04849201c103040b06c440303408480c04200c418042d00d019403a4000401c010842e6410341801c0d6a62035070030000c000180114140e514082e4407c1a141c0d00c100158481024030194909190350079001885035901d2003ca07c0c05a000070496042400000c0c00d2580d104118011070301c401c1d103401ca40c810082e0030324205051620250313040c843c20b8481c10390441c00502001c50300501c02080c407409940c2c0a400400b444025901e0900007031906524141000301c0e0140024412618101c4251010b014a50018922480a050242440c40c0d40c00c9110881001c1061028101c08071182c10303441600003070001407641402d0b0010104641a03e00c00012202040030700c40e50100100d80f4401e418800d807603074205014800d00030b0f0300c1ea01451003011142d80042d40040d010074020381015044903c0245512a203809c9640c800c5421071903c0811350f12040c0c602111003c2c0402480303000d0998108109501074088001c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 855258327 1250 855257077 855257119
    0xc0f0207151b0f0b0907090c0e061b030703030b0a0501030504110f06271c0312150506040305160f05030d1b060c08040c0e010b031f0510020d030b 64
    0x1841c900e0401610040300d00300c65042c107041c1c8110591010800001a070780c1d003060391082005898904050180c08800280001240304403044a03e0304c1d1101d80030f041c00c0404014190704074411740c1030303c40486d149400c1040c1d8140000d1428034032039140000e202002005020341030005030815810f151800d02400701003080080c2c1c040346190200c402445a00c1840d0104000340290000341100c075080240a60b0141c801c100e9070051148107940100712460521302d454082080c00c41e000d000309444059000300c0b485e554000e04800946540042e04299494010501a0b4099802078079150003a080c007030b4104000c1d0b401c81001340103075080e1000890410000944031060b0052030350a0003401940c0c08030b10b40b01d16800313500c4ac9411110030401c0340300c1100c019245810071203080340c00801001000c9541704941c000141030b654600c06c80350456613000541c105500100319882d0f00580448000212542c031445696103d54455000c0d041c100f98280340500bd440c82d2180480c0304008110800ca4540006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 855259577 1250 855258327 855258359
    0x6090f101148060d140f060916020c06030c040303020c040501030503090607021809010603030f211d100f0f200a090308130302011b0b01060e0105120a0c0f0207 70
    0x20384021451002c0040120804a8810000e540000c07000c44c803000062950fa001000e20f62000825540b1961140600f4186078001c80b0303020392088a440104d240f494010000f007555400d01e0040340c4200c810b103c00641e20b900101c50340030351b00700001002e2007010760500000c00d80c4803042d1800e01203075056544058803030091400c001d00507940402c0c0c920a5595590780c42010f20035104000c203481c246519864041e1809001c20780c0032560000b803240c0c0403271081c0030403501d40e0704140d810441028048071081c090190200070803142200c003014914250014041100c101329030010002d1544901a140015039401900043c510f501d001c28241c8106020fa01c421507403400c040003e036481d000f5030000d0307a05000f41d0304068100c01c0e02003100e088040080c00c95406881c001d07210341100030058000e0181100b5403040c01000c955512004000050140e0582140514141482414004080c080b42c03080003084480424060302c0d90405526250091420304620358144094a0102e00307045810807020f00b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 855260827 1250 855259577 855259663
    0x6060109030209190e010606020111030c030a0c031b0809300c030c030f0918160c03260f070903031d0a030f030c0b06030f0c06090f1011 60
    0x1200c0002c004c04520000540c02e500700003020802c0c10112000caa001744031034040c8501561801d0800c03101040340c20107803807044610705902884d56a598580ca80a00446c644c504141600c8041842010085070b09900840509554440b414600f11006034074100c110b0b003200e041d240c07a84801c4c0c00c2c2c1d00300840c10904014000004903560b5034051000d5482c51180c03801c400e0050002150464089a88800074440b24408441140074407081003144039180006035240701000040114030012540510318900155000c0d05000c10180c00c44000c3c00c00c4074a4100484e042c4030723041c02c10044a00c5440d01c1c081d07008000e42c908048008d0459401a02109803204c400e800310620041034800d80e03a403228600040c5034420228400c0c01c0252030301912020040000b150010103803000038026044c00208105041e074640d00820701f0340d02501c14010a40c0c400d2554540040980102c101030341c440c9084001e503040e40303982d52040341a00b900000d003800c800640c0007075540d54455010820014181240c140922 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 855262077 1250 855260827 855260839
    0x1a0105040b1b0a2102010b0a0609030209060f0a080c04060902070b0f250908210315010c020a0b0903061501020c01050306030a060f02041d010803042c01140f03060601090302 76
    0x1c1c840e18003031911000340300050004003081e100c4c40101a140000480e10342e0b07150001c1c006012400d041103140348035802064009072990400304058648a9030a40d001b41c4042e02c01c5021900d00c5001c203112144c2c1d9001658594404002c0340c01609180c400c0500500f4604000c40c10403490b50744107044010080c0440c01e0501e0920b0100300e1500c0c00864040c84100c001c2c0880491850200740613151000d10720400c0050301880d009540b45250030f030748000324024603412507032443d550074102059203a8000310441c1042400b0b40700000503103840d081030000d42160f42c010f54440c000c0b1000c16141c04001402180642d640e10f20b0b608059800040c03884c001503003400e00c01e8a03070f5030714808217140032040320003d410b090400ca08040540040d900a0061b503040d00d00502c0340e400301c203035945040d58082c4140803a0b540208810070058a411030500303041d1101c2100450340ca2161082c9626410081c1c101101c010300210f9a80f07601d29004940f45150030068004e0b01c0f0f10301d8a04006001c034022444003a000744 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 855263327 1250 855262077 855262117
    0x1020115030b06060c2428020d0e0a380609041e06090c0801020c0c06030402060f0309010f1802031906150605031b0f070305090a050d061a0105040b 65
    0x15032107806990b10741095904540c43c8850049134048044000a40c808403603200001251f0091465000045208802030070307203600340500030f2004001e41c400881c1c00081036a44140e1a150075042c402c2c600744a0007608528181c1e04c0400b43d522010401c14000841c9285084601803035410211031168071a00484104106640f01e0034aa030812040145113003140c01d941c401070040103019440b140c1c105014201408038944c03550112400c0b0f00c12843d844415a00840081d030f02480e001c0000d5521134800f40c40d960408810300f207002e1040e00107070381604480c2d4403900c003600001c1003407040000320060f09002c1d20103640b564010a440b001c3c4900e022079403041400603581408070580000500b074541c070180c0040307542c1e2a200100300340c000ba514403000c4070301800e100aa03802000c2c141d038510304400c413005140c0074a41d034040e2600c0d400a542c40d0341206d20301c60009202c2e40c1e02c04003081301500440012458112040c1c01e40507881031040c8040c14400180014040304060509450040b440b8103820b001d01d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 855264577 1250 855263327 855263329
    0x60c0b071b050105041a0601050d180c0308041a0a0e060304031e0f02011a010f0804030210060b0702040c03061406070204090503040605121003020d0b07050c100b0f01020115030b06 79
    0x4003100440640716030000044650402905611051040e40119030308106c11410201e100e0421300103859003800500140007e113510b4140c1d921402d0808041c1100700081031140d45c0b001080c1c42d1552081ea0410000b040070444000c0c415920300403517540c8a101031400340ca200c4040c28075040f80a13214007a0102100150030107001d00704005c40241414041b10700080b090340f000300351003900d04484006500788041403150041400700e4212000050310f41c40c2c04107001c1c210444040000800540c02c5203d0400308101249481c4290009082801351050303445d8524010710060302c090b841e0a0041504c1c0000400140440d52000701ea00c034802c0351016560710f65400014090110202d000d4404e0100050001f0282c2d0400010b106400950014100c03698070f010070508503a8040c0710194104443e10303c0140007510201d400d5511024078244241000c15641d4094039107000e900c000c501c85d664820040700185802201c00000fa1801d100078411001d4440c20311100500500c030042c04807403000045044c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 855265827 1250 855264577 855264587
    0x501262403070305030429070f05160815130c05060d0f0221011d042904301d060c030d0b0a0603020a0e0f1f080a0c09060c0b07 56
    0x200300310060880310312940f00e003844d070b40300e522500c2240d003000311006043e0810010b070b4403440084031410841700d08100b00e90721151944442c0800485860143c403007120070b41800b540003100605408001440c82c098a103121441603400501180320700240208004001440300480f001910f0056501c15141e1401450141c094003200180300c0840d4000701c0d0050900c098400703034912040d2490301c10380c0d03ea41e03508070800680c074000401c03190314200540020301055142000e200345403491821500010480e20f0407144d58202980c045800201c540c1c0c1d0800900c0c40e04440382d020039030400c910240803002c24805806010780c1043c1e403030600b060044100d000c0e9182c1c0d003601c8c0038240c040706480d035911450020b20300a0460a2035148181020040072030041d120384207560107034020384c84501c21052a0000c1100418481c900c0ca84e00c020b0b4140d400411418030b083d10303185500310340c440e005a803d100c28440282c0e4115139584041043d4031800700142903100c0c0d034603442d0303e8010b81c200d1119112070300c084035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 855267077 1250 855265827 855265891
    0x90417090301020703030b03060a0216060203040206040e07030c031406240417301213060c030b0a090902010c03050c0c0307060509100914210d09050126 67
    0xd81944013207000340c00e054261304103050b100ea0841c03ea9880381d0711040410200d01609004508a8120309003650000d1070700e90056800c680000c103040c0c10180e03140459000710004603292400a0740b46c54a5164072905401404000c4845065200d0700b40b5012010400c20b4000100881107600180e408152071400c8100b20385c05421030410074030a025410507060390f40e43e034000707640c1900d064150b4105100c8038410091040c55601c00d1480d80380c203200c80d280c000c2d52000a814602c032000135002d0b001c0000c256109007006101940c0340800c07900021801c014105500e5402400c415003806501c000503079202e4240c00e0341d80da050504944551541c0002858845d8040206170148140007020441a800002610010340205c0710441400c00c5524115032000c054803c44c150030f60070f4814803800b860314400e200c843c0c044010460386c02c8242805218500020700c3d64a0000ca80041c00500c000d5078043d0404496861604000d004820511034101208500501c0c0a05d524000c1c01c1a020304a20060211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 855268327 1250 855267077 855267079
    0x9060d0b06030f0601020f0f0d0804031106040302060601142805040e0c030402040e0115050618030115080717060601080a0e030d0507030606090302150c0c090109050405010b090609041709 82
    0x20b40c0701d203800c0040554076401500c40a02520415144208503280019071045140940020700141c804860042d00c032084003410480a0205010082200703050401c03c2034032490096006040f141070201c00580450709041d85401c200c202000406032555600d958204d090100944814600c5480041160f4600454012031101c090710024441c0ca0704e5020080c5014900031103042228940c0140010308036003600714800301950711184200b02d00d26012001c1c1100c0c080325880a4183c0001c0800a0b00310340141c02102000b0001043c103020118040180c00041c2c40c2e1070000c02c603c4040f8400d030350b03a0b0b181e0091440c1e0400450000180310b00801da04401511840602140d442c4c80c070100d00300c4082c0004603440800246172080000b4024855550b0f50104c030b40103400f203085074502d600068100e030b001114181803403244104205890304e40c4000b00d0300a08060900044504262418900b92248000601d01c204c1c5000d05100315641c404900941066022082e81c5400807034012104407401982d0400e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 855269577 1250 855268327 855268339
    0x6050d0f0206210708011a070f110a18022113140c090406090510050c04032012070801050a06060504150309080c0d02190c060809010b150c0613020609060d0b 69
    0x10050a03a00302c02421b041e00c000003030f5118402003032201008103000d40003016000110008104000c100d0000e940402210050031805072180c580b84d1600320a04405010185542d0006481001c20721400800b2090303410b4007404d80e8142442c03510070050981f0341a01602607165140e1158031700108100481103035001a0840341946410304048000b4640500e081d681409052286040f080c418800e09100300700b6582290704082c196126501ca400c10707441a0700e22103410307030380d891908c0e5100014080110200c00051681901300361426083d103001400080f0403030700303101c0240615900b00f002d40f0199240414403d0075102c1c4400100c2c09040d00800282c0801000181c00a445038089070007480e40006800b03d80c0d900030307041411440c107095907501520307500c80b68a007404081d10410250b90004c00715000411b4007010000082c5a00310300704200304c1040380014440c044d481051180c61f07441100844403480c148101e40200d150f070f100c1c607038007144127190001d0400e108070060703413240786c10700720242030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 855270827 1250 855269577 855269581
    0x160306050306012c04121107050301090506010512010204140f01031e20041a031e0907030c09090507030b190609063201030b0f030109050601050406050d0f020621 71
    0xc19459002c500b5a48040e00c84e0390319032003241149107032217409264851090025051340403c21030b2401007800c56401e09019500000a255400340980003076070b4000e1024082651410081042c901031210003100c003640144404c22001074818900b540903d41511840368020400d00120b006051507083c1d4803158582c3c689192415800f0303449020389031603a200c060340a00d050301c1ca00005002d00c0c8920300c1a182c848000c03640e1604628042c54110382c0b2804400d9115003030100f00d908405044401c00b0f80340d40415002c00c1801001480c15001f414989410400e4542c180c841c252105c0b0075000282503030024101243c0d816100c07121202c88000300b200200450b07500e60b80751101810701807180c6450310307007210001e107410f501c0440d229041e0003182001005440003d0010760103020f2003921703698441c4801e1001c0033652020300a0b020b03424411b1015259560411082104598458204c1401107040311400800100550b02e9905070a0301100c1c03060310b9240601c00e0b44901104012491948401802 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 855272077 1250 855270827 855270839
    0xf031b2e08061905060904200309101d25121b0b04051305060406090203070e04140106120e0a0203011b03060e0f0403050918010815090a080316030605030601 69
    0x140186800c4a0480f03007040034400c030112060039401615030000d4100031142c1c8900d425403101030500744040d5150a83c643d1290500382540088804041035000100c00c0303030100045214401c0300043c3e181c4804003d9008018245e5942194123052142e8556030092081780c41c14003c7c904001c010510201051b00a28945611089000c0342d40e24200e003418900403401e00304000a0f0380036142c000d4110aa0790b031101d1003090240501414564001d0341d20031020480c00110f00007144102100e40350001c0b024403100c144000c0b500c2c5007190780b0700f90348481d0040c000280c2c0721402d0030380f40580d01c8022035141d40202d0031a042084c0c43c08000c1d4903600c4e003050320b900c0f010310844204d00d000d55620200b207020360b203140c1400c210404903a4034a05041c140c00040009000348094284544080c1c901c140000c0340c031100c01e403072081c2038001009aa00280e0300c0f405100d401110705030f124810300041d11018600d0382d100005c500002d803226400005103c0c82c087d02c81d100754454001000b004089072080c0d40c0d502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 855273327 1250 855272077 855272087
    0xc0c0307151701062a1e0203150124110d08040c15050a110c090f0a0b030c24160b0a06060f020c010807090803070602090f031b2e 57
    0x1d540d14002c030354500c42d08038040041846250407607190307488001035042c4480e20260030242d0395240640d40b031280504400400e0f0401c0d11340400e091a00541d08105130140105403070010aa08400b03003030281d41005002104450101e000000d030210030308020b07651030103000c0d01e001043c3c5205080901c40c43c6004250345500060a5000790b0007444420b81c810307211103200402c140b01e0070b4003001055080008501440c840d422003003410418000f5507401c00c003600300088000000341e800d00440480b202c02d00c41c80d1011441160081d000c1103004000c6404100007064030240e900c0d0880c08109103624003400c2c1c0c06180411074140303900700303030340f4021480181c07400f07812844065803210384451030800041521805403501048074440d80c1c00800046615000456403000020700c00d008124400c075001841c0d00042029080451082e0303400b6860b030305124240000c4c0e900d680140d82c801d60010724084407034180b102136500c1c0304d101039584a4000802c0c040f500d100b9030030034144c41c1c0761814908284d643d1681c02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 855274577 1250 855273327 855273359
    0x3030f0a030b011e050a0909051f06020102070b13230f1527070b21070e0a090f090b0906070801090203090d1107120305120c0415050c0c0307 62
    0x1a2000c00c900440040110f44e8045210442840764040320700000c1c0043c003a101070140d180c45454a0701b00d031600c0e442c0410503190203176076081040030b08006000e00f0581a13641c400192041d48021414405c40d0b8503904003068028101c0140c8a1003070303031000107011000300c6002d812041d02040550101805c03083d00d81d030711282d0660340321501030b5040d9501425410210300f03000d500481c020240040c840001c01280d03800101180b6a68030a001c00003821544e80809000d0114030801c040a40101c0381e41170079020300d401880e0b0b03400c00c40f024051011a1b5140d6489200b40c3d4901d00c0001000301c4000d103042c0041012902c042d1540044500b082008600001d00d41d20601183e680d010990342d031841505e090740025110b80701a9040007501c800001c0c81010f8110754010103404440304196180503050100340c0300502900000d800180707400401d508061850780004803c0440782c5050b1915541f80300c102c6030740354035a0400000040f0034040f04030401070700342e85c1c0b03000030140d95905950740000c900d40620 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 855275827 1250 855274577 855274597
    0xd06030c0b1207140702130b271003050a081606060902040518070822060c02010b0a080a03020606041d07090507020d05120708130b09030720030a1502040503030f 71
    0x102c02c0024400301e104248480c4400b5000039850704100181d13081040040d1015210b6416555945c00800b8540e60380c402c484504410700c02c04101039007040295110000c3c0117200b01100c2c5440c1c001000018400504031040c2e60300854a1038503688920f416009101e42c405014100c142002404075a0404941c0100102c0b00211241d81d0b084602009408014070116500404199a080000c10303842d4a14100d04480001d44c00c2100d0519071a5a14001c60b581c006240c070040c2c5d9640d001c82c44074280104004051f01c0040300405250000d50743c002d5071210700800c507501a41e240d2451100d030801d030765031303100c0d070401c000d004d0b2050507488601c54401420101c03400310040c0b16140e4204c40583c0503004903818030548000d0306695a482800c241c0300040c0c040c01c40490303915803060700760200d401d60030024020358621f0003850381e500072070402e07506141e6030810002ca01a05000e82c10050741d00065883c000f50381c015035a0045101d43c00b0040001e02850b84565010300001070f0741d400005641d4010141e0b83e403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 855277077 1250 855275827 855275857
    0x1e050109020d050115141b030d061d090715031d0a02010e1516022e14041401031a12010618020406020304090209030705041a0a1512020d06030c0b 64
    0x20380d0300d01c4007903240c5c0c08610441c003040302c0b524a0040316011800400c0d583c00c040c110018250486040340b441c6130311541d1700054a43d60b03040305000d50740d40c1060f8240c1c04603078003206e02c0c0c860505c4034009884201c00d1003501c1da490800042441c005000341c04c04200c2034890030f95203601da81c1e45034401d504c62100b40801c9000132030178501401607281041c0d41540002030074848070304241ca501286c8c51612207c180c241d90204aa816880203d440d08404948418010356100b116240c0d403900a40030300c2461b4654480c2e104103010502001e181c0140f200032032082480c1c00320390201c82c05240007000d8101e601060704804c3c503950340c2c0c0700038074150090b10458a0036084008100325040d00001240503d004079001a0402c00c0200022440340d000760040c098014161016590b840d00041d04031902d42c1c0d4000019041500e41da21645489500d1038014142813141d081030104400c00100035440c082d10744010f460b40801d148150361000d43c805070207503601506c01c25445032100e140a00f950001580708034140307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 855278327 1250 855277077 855277079
    0x1060f09091a06072d1203090206090127090e190803130614070329030c0607061d031c0e06070804080909190c211e050109020d0501 58
    0x14061240e0204100780c1003401400304408020460503500402d0151500020060325141c507055500e03090170310b90301c203020001c1820511710300b8590b080d0340001d000040c185000784802c050380700d4400301c1c0c50440e402d2030300000c12039a2180c4446012001154803004815240c2e0218543d80c07103500650000e0301c0744d404c80307e12280c402030845c0d821200540081c0715a605102256030036a040e0703449c500312885414081000301c0882c210f140200d100b1251400003a4403100250140c110406100ea00043d03004400480085e90501180c2d94030f0604c1d08082c051400010301e1828030040e9440031400e00115003101401051a0203056925008003902800000300c09801440d00d0080b03225402e0600503801c00703019155034200c0309030354015006005643c0070380c04010398074265486549080c4110030025150300ba8400c2000001d003128098540380d010301120340e45450030002038048048a110007400041244205041f851140041c8800d14100544c00c103400410001c00c1a0040c250501c2c030b04800300700607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 855279577 1250 855278327 855278339
    0xb01030e0a0f0605060a1206052e0e07110303100503150f0a02070201030f020a03050f010801110304020d0f140307150b06161106041e05040b10050c1501060f09 70
    0x381c4503004004018001c1881d40500040050700700c00c0d4071810040c008011655030b07001c840c8200d0302603030302290071566407410040440719a03040104410714460700800034007141d44d40390324881c01c28015288403000b070340001102136200d402e81d48180030ba883c0a070790312414046909000c50281e40a814441e009070180300070f5405102c05886e104600b40c02c803960740b986038480d500b0700070361280d03078142d04140e2909840c6800713044030f00040150348107030341c0c0c0040c0c24500801440c9500c24183c10214059041c940d800080320b41d8081a030b600283c0403680c840c02e80180d40f0b002e070712140c401040288172003440c10f0003c408440100141202e103004d14220b1010701c6902c1d159900715405420810303403141061010b40808a02c486003258164031501c0803c100c400c044000480b2908240e000131041c1b112681d2040c80000301c240040000c2c030040c1c2c1d0501c40c0080f4480010011901d41d0f112130308100003c01e5003a41c1030010001a100d075500c1d40c06050542d44c44003002030813140408500c070042171542400040d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 855280827 1250 855279577 855279583
    0x305010b090405030429040e0f07020c0a0e060f0306070f020c01050403120e12071205070e070e091005060d0b031e06010510110f0f060a0501050913080714010b01030e 73
    0x1240d0f9110b030107945003a00b8800e018520302141c80c0c014900d000c104c0e1035460b031003819034000d0014002d140662183c0307250103240001d104900404500440d04000f0301c4681c91703155100d058042e030300803100650310760351103401041362200840580b0f581885802d0511500d04e070001c1007001411545da00b683d0b680b4900c58010340c0e840c80340b440010040001c0040705280306c1c6c404d0b100302040100c0100441d0710030741084805441c1c000b00d42c1104580c46103003915030040050801070b081c0240826014500145272511001e44520328401380c6a0013040c8071130000c1c1101c02041e030408080d2000401198a640040c000c0d0001081004081c500074401c0c03070052520040c02c44008042d1024010051400360f0904c02808000e40700c428085080c0b1500540c624409801030041450034130303100c0010f10348044000912450040c010740042c003130343d14010041c8419110003d0461713008061130b617400207030342c1207107014003041c81059400741112004240103e00c03040107400040c0b207114241e9050021020350075046031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 855282077 1250 855280827 855280831
    0xe04081215150d0213120c0617190b0d030905010f09081b12060c0310080109150c05040503120d150b04212f0103060513051e0106020109050706050a0219022205010305010b09 76
    0xca004800c0004105282b25940071020b00d800d50404036180d224640410301521441004602090400e5803d0200f568004040172a03240180b410800c1c15190407a1a038403040198103110b2422040c1c0d10024035500d0700c01802113003110740000c0740d6440c5001d1501c045a50015948500d801040000028039020140100881c007078000e6408034010642904180041420383e581c0c00c28044207010008255409000032407150490b140c54540c1c40f1155039a440803554150b14461040714050824051503510700251000d5880006054261000d0b02098042c0b070321900d100100405022029060301c04101c1600d060307101850b2158003042c07402000150151625402856004944035040aa1080740c0d078004035044017080c00420800d1841641105190800b60000300160303448031036000c00c1000030081c0400401d4285480c0d820801d400c44001d440c1c0e00c0b07984521500d0b401e442812002c1d9a10340c66101e0070600b24289001000808030051005441e00340700c150744951916010034881c2c1403a4400034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 855283327 1250 855282077 855282107
    0xf0e0a060501020615190303120b030a120e03120313020a05120312040219080a2d24020d0c030e0109080405090a060e04081215150d0213120c06 63
    0x4c0169074130a03290240300e82054841a0784905004a0261190031090045c4083d41c003d41d10303640801c41e40d10980050750042c9141c44e010394000e00000380031030321036080c5c8082c1c0000751400f41440c1001c50006841e06100d1040042d40c80000024030042c010f001c10840c07110b5209441e040d061542e10010050464a0203d03102c403250020840c079004800d100110036030051004256800c00d094024080511110301c2d0845411584241c02040600990741d400c4911071070490403000751200c6140146244d0221013030003d0200b0500000210020a03801c0705201e07e070306280046448802e200c5009002c0c2404503410804a0300d000003820742030b4018001c1c0b500540e0403407440392510346000c0500c000010000c2105981c160b0b03c41010405101c8003581034080ca000720190703074480d06a1646042d440d1005064003213003101c030b04040d10454440500303103101100c548900c0d03078a030782c0301d9024200644284400d25000c40503502c400701d40b40581e4110b0384512800303419009030782521000140c40341d1440006070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 855284577 1250 855283327 855283333
    0x14030d020d050a1b0b040c1502070501030b0f090f191512171305180403080403030c030e0a08040f050d0317070509040e0f1c120e03130f0e0a06050102 66
    0x1602149002d1001400d0b4000a490400d14a0907a140d6407512034004400485900100006101c18000f0360004400038012009006d0f5032590710355000f035030b692038500c21030303060580b1413a07024044e0b5500803401070040c81c0602200c2d034918004003100541c400458003a401c0da101e1040ea20300e9101c0c1c0e88507818026181c2c3c10301180744c9041035400100480d11071400c0355283d09072a00c0d080f074151618060b015170002c003562918031508101c20441480b140000d000540c1c00c2090800011030ba02640032500503070141000607000284500c114013400e1100b1819200b07120360403030310040040c800c1c02007044800448001e5001c43e220000c011800740c90b1034015000401c071031460184130034645042d507008003150500307519100040c8041801d650110050a1150300800045a1320300403d02c450248100e00d1003a411140070100800380001d40214011001c0c40c1c0e56800001400c04100100c406e10520b41c00580c802503030381c5c0d0000c00400c800740a446100c904500c0803030110000350203000161a07050b005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 855285827 1250 855284577 855284593
    0x28020306010e04080714061009140a110c0d120b0f060f13090609150f210206040e180c19031b0b0c0106050405150a061103091914030d02 60
    0x49000b060005041030740c84120400c50f910000340036914071400c9a5204024000910700702512103440f840390350050341d60038189800c0400a81c00d182c1c900b64400c2031480c1c009400511500340744030600503215062164401d42010645a0b5080030400c4141c981c408014829500a1070620400102c070034001a008a000d201200045602c00c004e4419144000c01c60b03003050340e50311000010340b080740c1d10181825135500002c0f001d043d01da90284015280d4401c00c400d982d803070411401c00308650614132251a10441250108641d141012140148003400301c0000354104581185c80d4039030100311401007442130015128107802d007824a0310030501c000d02c601742030902d5511115413403c420780120303801088003140030400c5580240a0241e1540c0e0b00000a10300c0c0c02c120601c4111240070701082141000000c001c01c4070340e2449626029075042c1c1c5010241002008001c41c658001c00381090b5100c01c1107548100010b6422103c0822124400340c0145420715040071f250b00c4034100c04038400182c01a203a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 855287077 1250 855285827 855285839
    0x301110f1c05040305030403020f1203010b130f030303052a030c0c190501020a11010b06090d0c09061806120b0114012705030d14160f0b092802030601 66
    0x1000d00004501d41c00c4007014244407070031000c00c4410485003100810070200920042c940d04004180c00208140d00a0018200450000c11540014410030800380c400044503031041400203841d000501c41841c58480254580c038000d000b0340b108450400b0760a4442080801c200d08010700381c03007007851484105d840c41c0c8543c4012112684a80c0e064402e80c41000c000c0001038030010701c1c0742e00e024010000140c603200200700041002c460320200170810fa04109000789581d030f400c005c4590054003110302076820f8000f4608108000180d070310000d000c602d4510001102d00c4004101075a690030901e0800442d81c8070f040c245824a0040d070060000d009200c01480725403281e002500d07a078881410400c01403030303424442d80d0064290000141c040040b680781084641010410003900ca080d038100688814145140701400d801003d084002056080310341c1d02c24442000c19a0b030f080c82d04203a2420552408100056850120103010240980c075150381080000c035071102150360980c010041c00c55039103000c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 855288327 1250 855287077 855287107
    0xf0303090f12030c091e12170304050c10080c03130c0b0708070c12031d040f0c08060901060504081b12010203240307030803070809070801060b04090b030111 69
    0x603049a04240d00080400400d4103900c0400c4481d00e980d07400b0806601a02005003901c1c510340c8510900c0d14840b10010f2002400000c10301942c140307200006c420242e42c1002c04003c82900b82c10b42d51200000107000502c6000301d01c00c1030128065a900c03500e480c883d40100c804403411140e0740c10040061010444094118524010f90f03405002581129616445515101d51100000312440381c00010a00100320002065100a100381000d51349001200e0320b02034141e0b014040c44034070300c580403400210a0b070ba07258810601000a030908028540401d980605120b00641c0c0b04c901c6030202c0d100015200b403094049500b5220b140014240000214440c609480c980c000d605030300100141039511000804d02c00356114800e4640c1d040fa200300c180501c0030900c010004410302a0b0424071086c8045141681100d410561078900441c240c0e40e14503030a800c104264100e20125402c241e00020485031040c00303042650a0f515040001c01c0030b03441010300321081d414003039000c40e405001070500c0c50122 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 855289577 1250 855288327 855288341
    0x10330c0302010902090a020c0106050405130b0a140a0207060f06241205101a0a0c020d02180f060f0105070f0303180b160807030c02070e0604020d0f050106030b0d0f0303 74
    0x190002094216081c0c4c00190003642c00c0b541030726080c0e070100e03551148007030034045c0c4402004181e07400c000900b0209800c1200002a01006d0408043c80c0041241780d201c55120110b40c00c0f420030356154a007000074500003e50700c024001d40e5101c2c1000e01040f49410240318840407540015030041c0e080181009100304400851311070000e2108400b81c10704000041d0249074130421f03016004845403410004c48104003500a412101107901c10b00c5800c644a820541e81c600b00343d0100c4681c510040e251000442c07040c00c4200030305600c0d1280301840b190202e005141030240c102101d0540451b04030340d00449882c010311750094102c40c0c003500e032381002c02d010380c0c0654800181e444200358005055144c1f681d80c1d200070788a82c0b039184a211089110341c1c2c0c2c800354082c0c000c10985010301141d4602c980c000d50720328250248030305490600c00882d069940380c0d030407900e046086171400d00c00080701111220050500340f08d440b0200f0304002d143c440c03a16180c040350864550040c0094403120040c0c40840042c054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 855290827 1250 855289577 855289583
    0x6030f0b030f0703020a06080417090609030f0a060b010e0a170a02100f14070809010e19030b010e010e0403051605030f07050109150209010215150910330c 68
    0x140d0458024291400d01c1020401045030004081c45850352041c084015a280c0c000010001040213010000b105814600c61a03d500c0b00059111406440000c1540c450344240a41c180300303001051031107040c00702d52504900d029500c00c002032811680191600c0b5501d00119500020404c410f1000c080d018030400b4040d0700c580200d54940b41c680c5e002c05d032601560080c0d40041001e02541c000c1e002d030b000e8222509081d56606c901e041c01070076a6440104e002c0c00c03005c541805080c07401040e00c1c1e102c42e0300303082051b00b8000c04000b4035a5681020314803d1028068a155082c0050001c200c03072034003010303040c001d55156840b00e260228000c1c0405100600040c04c4401e40400c01245401d0325224000c2c2200b24066000003c41c01c032036140619072100078030140789800c0d00520022071681e8001c075581045d44000964000240d84589000b81d4541d48444240d40c00009071052280b1424804082000d461620541c03503a4021892007658060401c0c108a0140c1020200680b003198441c1c0c07010411644 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 855292077 1250 855290827 855290831
    0x41d100615360e150a092f0702040e010e030301210f031e0f020d0302160b010b09010809030403231c0e04111603030902190602010203060f031606030f 66
    0x800b1501c10a10b46100c2c4804151001c0680c405201040c4010f03490b941000682d091a20500600c1d404141c2e542028030800100c103070349039503442452603c1c112904e2109000710007103140036035140304440070360011001680502d183c4110000b807004140b00310403510740482c0085041d030303107003d8564268410a0030060800317130341c800003600041e01000d000900d0368440c0d240c5205030352000d5825141068680d0b6a03404021a1507400c4081c2038003c5941d0520100910b00035030303a081920741e0080003522220004000c2d01710031000280620840000d0448503000740e031800b0103038480c2e5460300c0d40c90042c1c0c08060071000310b003070b1a503c0b1107018401c00340c13114011078142c600003c6400180b2214001145800300030031f4445400b1003d0785414442e01007810090142d450a1031108038401d045000c64903802010701d681d0303101c000203540d20380b007410700c05943c4664220841038540380024043e410980e11113004081164a50b882440c002c203461051406c821b04c250400c0707240c10b108a018244034103102e4403103030b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 855293327 1250 855292077 855292127
    0x10315090206190801051219080d0b06160506100f0b2109010501051207180518030307260606031303180e1602060609130302010b041d100615 62
    0xd440c0c00c0f80002d1404071500d8900740b640c036100510001082c9400a000c0720317006156139403403e00042c01413003234942c5c0018034281c49000b000c011a000b00300d07031151568460740c0451001841344104035030300305441c801c10603030f0555280c152405101c9a9640240a65201112014041c8803e110003400d1803048200090040f842080d4010701c100c4425541080c5a9454400500c281d0428041e0000e02614240051a400340b5105a0001e200d000304140200952284082001e8541c02d1062080701c019070002e403a524208030b40054249141c03940039607911405c0b0603c4107220074010490600c2060044c10a920b181d40300c2c0f0007280d001050b51021818000d440340441e81d030109070b5200740041c000c400210106400c040042c000c03642e0b140c80c604400c550058013000400d440e031100d05900400d60340e400e00d10518451401303a01400b035402c500364200b4940401400c0505221008440c03500e122800e50f1203040c041d0306002c1c02d403003840c05055118501c5824400c5200e00c2061801c4c41c10000b901035001e0a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 855294577 1250 855293327 855293347
    0x31109090117061b0405010804050304080f15060103060e06040b0d050d051206060a0c0311070b0310050f1e1210060b190201051006050703030213030311070509010315090206 76
    0x410000c1c1c102c03a006001d039480c400b40c188000c008403900300d0192400403074a85034a0000d08050700c19400b420341001900c80200d020090100103a5000e89680310603101c65008204600d1794840d80c0035159003134400003202003070295009104003800c0d109618100105903403035105001c06400c00030030203034100c180f480e44000891406c4c08480c5250203207035942d6507107406124501e4403510b0040c140710300c60b9000704041110380703030080c030742d0009541e050030140d080580304e1038102e0a09000c0d40c0005880c2c9000010041040140500c3e03c068401c211041c20742c819100701404180001808000846058a8151141ca242c20503107000100458021503a046581e840c611068810395405040e440c0170101f4902400d40c681684070712111810305c001c00c2a880d00354500083c2070300505c10714040c0000042c072101410b100e90101d9103803010300d40348110390603540d28000781150540041648140a256000300d05490034005460481341c0019950810100342d40d0080000c04140e8412644078400f00002007003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 855295827 1250 855294577 855294589
    0x50a14100c0906030b040203010503070e1306140f090f060609060418060204050f1002031204230f070801020a081602070f0f080606040203190903110304030b160503060a06031109 78
    0x1d41c5042d688542e2030303c0c82c080c40a01030328825209544120300500052045850000784082140d0100261214a0702c901b0203264510a1081c40a40700c1d5061024a09000b42e1015030b0502139881c0d42d00c880ba4a584140040381c80e59840c842c21100c94010310041465881c0c4031640581100c8020310004a840900e014000201502102160818ac01203801c00c140e18100c903446d0322880d401d880280050480b44002500c0e4451035020301d0340c640e0f144000c42d05000e802c105c0070300d207050b400d414800c001c0501e013049690b410800441c441544107254000c02c0c0da20060094a07124486070715000301d1501c1d0140c01f42589440c1865807011445459070026084a80540044c020710501d820f80e54060304003c0e9060402500a09050045004109000c11500c004104260424130280000340c6852145802c584991141c0840137451001203804000d01c11140d5196006000701144d080712400c4405e42540d4a000440b60958001e684040800000d400b81e004108a0038030b074800300380762035034507800100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 855297077 1250 855295827 855295841
    0xa03030201050a0b04020f04030807030e131e0b0a06050904090b0f160c0201053c180d08031b0c191505061c0f05060a020a09060c050a1410 61
    0x20050391140300f401208005840340852070b84056a00358030703055656000e4149031007a0f12009000100c001072803414540702d0054110100e000038030303981c005010714a1090117001ca110f80300c0c02c0303c3d2000020000d1040280b04924454101405801c400c0c0d14140058500f6003110b00740580042d11801184002840990058401d003189400031106041c488140300342e90640c0301c00f543c24041c0080c4000d0240c2c2c0c009040c0e4030410741020009000c420391602d419100620703860340c07180c484246141601407601c60405008150050750400c640c6c00604410030403401140c14000e40003440800100300028940180c0f11010a5540c17145480d008018040d180342410192090031044a107040c000e04000c004801c84040b0196407100f4012070030705100061043d00b400040b0b0600804840040080201c0060100200390300281621820300d84000c140e4081c0d03105c04440c00004056010104041d030054418264103500140142801d0351070307945002d001030168a9644482c407502861703668180503070003004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 855298327 1250 855297077 855297083
    0x100e030c0d1a01080312010b0304052103072a0f1b03050d031d0d0e01120f050a1d0303310309090c030911090c040e01153b010e0a03 58
    0x104a02c201103060744a180d00c10b0b0001c50305a0030400442e420645018041c0741510002d40c220366507078803036103492407410b032040007480c01c403207880041c000280f04a080918440c18240d00e40200c41680e507898240f00441c948124a0380750768002003140400c140c000000c21040c0700c2e0303030040840c046020140304040a6036004483c16409002001c22450349401340301c1e81c0940b411039200c098a1030100c1c0e41d4941d00d04000440030000d40f00c82c00000c9a100320356070780f0945001e820400100d00356450305400740004982280f20103043c0b1002d0107440b1031442c00c200d24200020007441c19500e4075001c2a2401c0e00c014030703c1e03100030315099100c0c18289881c40f0340c00081d071080d20f070b092507280341009039025038144000303010034075240a102c500468a04201c10040c0d00d0202c401c52010b660310714021000e400f46400500c07020305c5440010554000322698402c024959807900d64040801600082c945611114400b8005d100d09011201e0142203100198084805060020310414801c000c1096101c00c2d074416 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 855299577 1250 855298327 855298343
    0x303070809011409100f0216170f0601030f0b0c0d0e0f16181512080408011407120c0908030a09052b170706060905010302030d030b100e030c0d 63
    0x21401507800c02000f150801d6000c0b4203030706094031a4005400d03e040400c1c11800d2103e07802c098000c062090103c100e07041e05140140f01038684590010301fa03c005c0300801c101c64407403000320354000000045d845040300c3d0701c40c0c3c00700f00c008aa03649070313040c41d000906603210403e410b12180c1c6140895000f880940c5440500800340c5003800030045281409140441d00e41c014441c5007807108844001c03500001d141010408202107034480840010402c0c00da110403043d100c07920514040211a4000780b040f00c503480d00034840b0580301c0a40d581540c0084d508200464825030346070b115013159030480350302507009003000302407103907209911411070f0300001c075407000144080814407042c17500c45280303000c090391512500c2d050210b14032800f5100840400103054103940c1411104034880040446034195030000d0305006150b0784085010241c082800100d100380517a110340c014080c802d00c103203070300b80d4001440c00207400c0c6014802c0d95440010060b42d905400b45a000d1590794951520040c2094071508032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 855300827 1250 855299577 855299587
    0xc0905240d06030b011d0a0608100b12011a10180312030b0301060902041505120609100305030a02060403030e0f121309020f0408070b03072f0f070501140f0d05130203030708 76
    0x407a414210300104030480440c40e1110500440d4400600380604030ac0d000400280f281c1c01d003000940e5007000740e151078010b60815400c19200b603602114040c101006a48035665034515800030b862010a19031105d00b00508000d080010030045404c9062801d076506001a94540f00c001003425942140c100186590300014108000460b045058001c000d952030300c00e00b440b18181c01c02c505690040d081c1407050250340c004c00e00da2010b86901100840d40030049176510300d0308440c080c0d20b5000884003230b00860724000c00c1c0700c81a58041b803030348024506880540b4100303031302c0b0b005955217400c0003254a100071402071011541c00c080348001d00d821131002015544480c98161514034000386604540201d090a1041c8030003180c100d8100030400841080003803a0307102600050100d03204000c00100d1038070480c3d0055283c07200114440c030903554203a0342c625030440c03c100e1304590317480380c03000c0c88488000821031020000c103640d200c0741d0041e200103944408990141c000918540000d603050380d0442e00040d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 855302077 1250 855300827 855300869
    0x203070c03110118020d110319060b011d011110020412060b0409031e02012702010f020303010b0a050310091104080606010c02090f130212010c0905240d06030b01 71
    0x40c00203040c0c942c0c100922091110540e40c1c030b407100040b40028015010100d60070108440c2550041d03d40c2c40c0a021214030219032841d40c00001041c0d40c06a5100d07143c1601c5034140d5203c0d6100400c000380100300700341d000f0a14001110030b1240c17403404c0d40c070034080c1c0d201030201d114550008200a005000310319400c6003090030a00c0440d401851810304c02d80c07511440c44002908a000d40c103996800c4031111040791f1541d070080c1d014026402d1080d19040b0b40000040f00710254017415000c2c18001ea80f000070046c0d000301c06980c1ca100070700a800c081a2306004480c4c12500c20b2009660009038009100030283c4c2e00e0f0503c0c0f0076107045811421140701c02250a200f440030070400f1a030f000d482464540c280e48880c0e004140c400038040d100c00f01c07071520040066605282c4203071100b19035901910060400d8801c1c12198000c140102ca80c42c0040c2d09214001081c1c07400008440d4440c40283e01c2d50b4072010b08502110060b800040030303030200d039218100040400ea000c0305050003403c1c2035600744c0c040b401502c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 855303327 1250 855302077 855302087
    0x50105010b120108010506011b0f1a180c1509030f030a200d0507031d0d08091002060606121b19030b0111070b030606160f021c11061303060203070c03 66
    0x10f00403071340b968502020041300d40e038802d01003ca01c0300340c40180c00c181c04060610b441c40014240010f485400504950040c001548580300c1c031959072071403c080000b001010207500c0d10920320502c0e6100325240e00f8410580c200030f00070040325100404440465442c1c1e18440d017150030198000f0045440e000c1481d0310201b0703888181064804200240074162030301c071006050b501078410040c0030481c0d440c0c49402c0810750b0b88004542c1910044c0354041601042c585165507611030f880c03160040444404000196000155490040c40010100313401c0c42c400c0c0c148041c404000030400c05003020740040070801a0007580080510307003c9060f04021002180b400601501c1c03203c034805040180d00502004241c8002c58986c0548071840011036403512010005006800344d15801d0750001d100c940303240100524402e00c00e000d5813090300c05400c550a83c07160407585c9440310380e01070240618544518210314280c0c0003006d542c04045403c0d0f02c220f0702c98446108a0300125000000711305180d004806142c0c0003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 855304577 1250 855303327 855303329
    0x30a0f0609210503040b1e101518051203090d081305121e0c03010e0124030c0e060301110a0206041b140906060c0d0801140603040c150c050105010b1201 67
    0x50750b240d1200d00401e0000a00c0c5100090020703100d688040701064409010511002c900120a82c80d17162a062660858420316003500c21444c3d00c140640324407041034020341d2400c5460b60f00d070700701c0340d08145080c0034041c03803107001c15a01405d0300003007040d048280d030b45e01040b002030790203a00c40a840d012086501c4100e41240e0700441d01c00c2200c1d000c141c1240100044006040c0c0b02180034031000f071492065585000ba4001c2c007940e041d4200207105900400c154404c01c441d43c00754411508990b40712440204e0b49465000244c000341d1100c0c0c080c0f005964240149420440140c000103041e42d1001395129150000401c041c0140c003c0000d1000740700c030012032401014410315440408500e044035010500c9101405035001d00c10f5000003c021f03994100076240003110f42ca09950403112801d01c001e201000034010258030260700310b000401c6003000c800303517440b0300d40c00010002c0c1c8a080c5001c8810b6404814258801c00008030030307050001d1004c1c0200c6008000c0150f803e522400f14441d881c0d81d0480c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 855305827 1250 855304577 855304613
    0xb060301060c1e0b1515190e06040311060c03040e010f031202060f15011403010603051807050625060606020d17132405090c0f09090d0806030a0f0609 66
    0x88040740c001242c40113140380d1304000e50000510a09110078040794440c2a000351040350000007099090014490074144844585543e0f501d8140412180401150b03005902000d02941e001d160301801130b04100008003d0001d001c400c0700d08281d0b80300c021109035402600030040301c40c01007504004009002d00c48010342c0005002600c40d6280c40950304040c0c1400809041d0001d041c01220316099014520042d195103490030f007244d482d038403194090007502c0d050b203192440784130703072410b03252440390200c0c91500b50790380208032030718101805204140103d03000b8082503c040920089000084191003400d00411094010340003641d00d00d40050003000010340034072010101c51040040681d40e50300c0c903406e400d41c40384003102d41100c002200d49003c00f9403a2204445864442800440000060b19408240c000c40e81071140f25005401d00c69145c0d0103541040f600d07840b0f80c00c0c0b801c429015103080c55101401030120342008200da200e48580b10000d100680307101d541c4480750300c2845030042c05070034100a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 855307077 1250 855305827 855305873
    0x201021b0a032708151e090d0f0e040207060f15050a05060a0c1a01030519120305090f010f02030a1103010b0d0b010306030609030e190f0b0702040b060301060c 70
    0x600d52009007080151103035605499001e0043d041c0010140b0003030b03a020f000e1030002c450030b2880085020850030011384c0d89800441800800e00690a2102d0f245403090301b19101500840d10b07071801c00ea40c408000a61641440030940401c0c80c00c0d00e803440a0400c2c2d900419002c00c42c031003202015400c8410310141030190507000c038000d1280d070311650001e03c21200305440c01a903500d8511400c56040c500e08500500041030302410045071144a01885e050b680502c058803030704443d8005140da10054440028038000004001d60a070301e0081e07021a51109100c82541c074128014002c890031201090600c0030041e078080b0600080d00d10a103c4c18480c40c14a0718001c0c0b40d94103104000100e4000e03400d600c0329080d00d904002c04030344d1098211400850b0300c090144144143c518020341140c07541d400050081040303a0351110508070815640701203461024402868505054100640d64480e0380d081c1c2e005601c0c1e600c4440b640d00c460700114000c081d08d43d42d114002c00d039481c014441141045903090080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 855308327 1250 855307077 855307093
    0xa1407140d0b120d030605010203090a0501230c0d0219021503041e0c0915050a15090b0f040501020d0201060608190902130b0301060501180915150201021b 68
    0x94002048206140300d030814251280d407000038200c00b90041102c81e41c3c1000242d003598164110003c1c82d42d00400898038240080c98545004990701c0c02550301c46680301e892244200f100d54001c0d0a5211001c0c1494119402401401d51004140d0704c0581c0101584d4032405d00030085030750501c104844404200b00c21002075095400043c040700c0780b020602c840c10760000c046810400703071a00c4d0050117248841c07104817843c001e082c82d0001c04204e124150300c940c1003102000001c4043c05407441a104020300400d4680c6c20500344481101100c09050140918500b0110b03454100c1000f4003685408294010398550902c400241450f651a0014042d681001130501c0990f410070b18541d80301c003240041c010714203459140000a030440e10b02c0650000c4500e02c90941440881d0842128420240d000340450355440e40110342000c0798504451041d401614248401074203a00448003e6940581d2480c6081d12000c031031115100c540f4405001d030f90300240d0b080e00b818441d00440d81800c0c0307483c090f068030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 855309577 1250 855308327 855308341
    0xc030303040605100f030c0e0606130e1e1501020f07060f230a0309111e060a02010902030f0304050a091b030e010e10142a07031e05030a14 61
    0x1901000d00000d00e00d588403c00501d4140704140360000814169003519a030755520708100d04925268000c28926a0042c4e0000700b050401e00c045a00c4103a1448444e10214a00703401d4201520001d022050b2201108400d48440005170f0115030144c00c0b0450200d5601ca503020000e0700c1d1400c0d0404640312a0002442086a80e420040c503120251081c2400d50006681c6030390705c0340403c012428003000b00b10109040c0656071381948450314040c4240000d45c2da1700401820843c80c095594200844e0590b000c42c800f0341410000c1c090700300d180e44c600003c134904c682540081d040c4007085078075a0595102040401003450b048036000c0081c100341004004000008200c040d440b144421001c0a058640714600f2580c5d100f540000e101d400011b003a02c0c240210030343d2104c0030f080300e017000c0e1034401000342c08075044010380d486246c6008206860502115000b80c581401070700320392400e03001e00502104103139103003400905855104c6580e039101d0341c0d00d140016406041340e40100442030b011070404204554 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 855310827 1250 855309577 855309583
    0x305090a0f0c090c0806120c03070b0f12040f05010b01091a0c0f010f0b040615090302120a05071203120b10120609020c01140106020c06041a0903010c050a030e0c03 72
    0x419040a503400307000e040c50038240c010841c1c652002081c2468042079044c070701c1d070200550703000c1c4004407403500350901c60340321170340d80c1d1401c45280030341c5038111007810821ba589440040500a00000c01d0505005003c6100003084004031000d8901c0540a07070100d041082c00e10a4044012003400c20010660500400350489145a65502c03620440007501003410342082004150350300042000344050400800040090702d541c0e601075014a06001c0080b4151410341014094100c9039134440030f04516540801c1080c07600006d252205020b40c00c010004140180250000380c619040b03600003441d00d0f841d0081c180e1220149480c01c051070003804ca011030342c40d00045441440d0515000001000002001c002003840340c2c0425861440000e410030101c0781034001c407580c40c039103910f4441d080c0c0c0da901042c0d0b228501d080310b1039441102000240034803203140402032248200342c000142010030060100f8219410b800e10320003c6030012601200d03039a03142c042c403501b00460101801803080c4c0d000100307507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 855312077 1250 855310827 855310843
    0xa120908151009020a1e030b0118030b0c031308040b1b190b060301150f05090106020d0807050d02040503160906120213051b03010303170a05060303070f11060f130501030509 76
    0x1906500056110101403146541611180c550740d401b002c20111018094003d0100700807003408540204c3c8044841c0348181d40704000c680d00b0414145403a5103920581d02e807a400108000d16a4040703003500c00c0850103810241002d403800a1030181d865920102100a04060420054250340901418840c44220343c01510015501c028452211385400300047d0243c0b0662800584407880c0320b00000e0b856826814203821a0800d440482d800e03625030748200d0322191400d4200003c10845004902c000d4420401005182914000142000e45682c002410041d8810b0780d4249c0c030075481380a00901041d4810340f0024441361021011036070440c1d012031824a40086140d0829070360f03d00241d400d08000b4800b4060441c6507a2907070f5250303103e18014081005200f02c0e5010f241d412000145000250301c038087c002d180003001507003441200e98071010841c8180104540002455154041588410018200205140d1411510b4458074a510450744901e82d000d1070405083c0703801d01031596400700d0921 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 855313327 1250 855312077 855312089
    0x30b0915180601050f0a031e2c03040f0905100602030310060c1104050f100e0709030b090f071409310f17030108010b0a030305030a0b01020a1209081510 67
    0x310590b0384400040e282d50040c0d5110310780c10740e0700242e10071003140e066020f12019000910101d590034482c036003040469545019203082c840c0d43c2070200c809c03100c03142c1c41401d00b801032104491810703849051008440b00c05501266605484800703000d4000200321210018009520040d4154035190341000044a41d91096206000707401e10254280f0205042504486d08050020b02040c00d02d11001e82c1d4420701151700c50002c40404c540860f101181b1b01c50240590781ca6a14154824156210f040c240200a440314a00c0c0c0700f0111180301840d000e100e460014409c0040740c8100c4520f1070240014040d0042c0034a444c404074010858240600784c00720b100c1620603900062109a070761510400e100110758024044841e00502c10802058010045040c0c8040e04001d00000f1010b80c01c1c4002c0b0511400018041070040c0005848480244d100ca030281c2d0052046442402c80c41d204c1900002426814000103041400184003160b01048683d100d403d00403450b884600d890000491a8074560040d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 855314577 1250 855313327 855313369
    0x70c111009050a0b090913031e0509040905030a1202030f0c0a050c010203040b06130203150f03010603020a081506030303240409080c0d1b05060f0c0f0a030b0915 71
    0x68040107206808100150401410350328140d034481c0082034440d000302c400b55102d4012440000d1400e0f010a80f4940c40c81e9168503a180725011100d0380341c4540c050398442d8410000c050205c000a40d441f406004a160f02420146640d03032001c540003060020301c01d1548802c10700400c24041240c05105c041c941c41689903c020340c48a4400c0f0f01240c080c441c01502c10003030341c004000c0c0018044501441d9010300c0c01140c002c0c06802301220403100340e0000b00d6a400c11504841e506812a04112600c444411002000064a10744070f80c00580240c125410a00c807651000c0190225030702c010030040c2c0c020104500035400d5183c01480b1240e4488040f904646040101d0040c03543c9840c1c507007207101090791040c19561030f40a00056180d99500140c130420011b840400b001040c17007c030381400c2011640000c0070309010780c0c41e400500003282c009803101c902c03840700b00700c6074018800d50000b907c001021940d0101c1d0124501c010091b98400c09891514400f0304090442c4855485a000c05c920907284481 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 855315827 1250 855314577 855314599
    0x6090b06070f120c1a07120603050312060a12060209100206090a030507080d0f0905010b0a062a060212090f070608041103330a0b030a20030d090608070c11 68
    0x104075944070041400805c08900e030144070000350b80c045501032098210790b0b0b40c0d51440000040000542d131451001500d00c0c0c108100c0141510628064075a1202015042001256440b10744c1341e20071360b420005850042d40420b581c0940d10f0400c100d400ea44003684000c12190410400c81078540300240001028000d0001d0f542c1c2c1002025020b848540a69000c100300c1c02a180c07580102401c0d407524110340319443d1500090781c903d015808002951481e40e83d00781440c3c800503424401010b80c11601c250115480b03420800070700300e400205204003008207800411b0034115940e51030a506c0124220168202940520900d035000d803001c1d50140e000503c414070600c00d5801710307080481d124400241469154104070f03060600042012130075070101e030003114a90303078a03041800b292a07042040c1d038150840d505a00118001688a410713501d9004032000043c41c0100009150880300d00411020901d48501002803e800c0500c481d4080c120741014800c1503541e665603200b0304400b150083c0f0070400d002c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 855317077 1250 855315827 855315863
    0xc09040507120c081027050106030c0f15050906120703180c1701020c0304060c05100204090f06060c0f061a030604060f0c0504080a020f130f06090b06070f 68
    0x4120001000c02d4050208206442c0c286811003820324080da004c148500e0340c807107090307084510442005004201003020f07004a001c070540d054805030701003a00c1941d2504004004510902c0082000f4180d034011040400d14081c5408110311080d614007042c46000e020200e4182c50322000c90342c43c003e200500040c2580c4285c0141c0003814907940440c00c0ca42039030720a00170855850b20720301c2a109011442180141000c0c141401d07407194141000e026003051004210703c0d40601d940d020200d1040040d940075060543c146402c0341c000f54804d00b4042d495654203126540302e80b00d40c80240c225468800c91900081c0c44020310031400a2005150590342d07005088460740012821a2031400102952000e04040c1414070242c0840356000100514020071601e0743d074014411901241c3c54803002c0c2c150107005408110811042c01641c035040009465082d030813030b10354403070003c000c032103c1c000044482c10000820100d032800041d0340c0c082c003000c201083c0071a02c204005070f41d60358401d000112000141c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 855318327 1250 855317077 855317083
    0xf030301031e11010513091d0723121524060a0804021e03161403150a18140307030e060c030d1802030f06040b0901060b030a0e0c03100c03060e0402030c090405 70
    0xd4070802d807c51410040b4071514160010034800307174942d9400c0b10700407a140d1046134500c0b42c080b19000c00a0720184203071145802d00c2100d81080180b540300b960080e0382414a0213400e0103044801c580c0d404d40d038021f03d489098282c411444d4104c000c1d143e140c28131040c40005401168060001b81c826100301c0e0001075071071f1b00b852500d0f000910260a440c0000c07405040c00d44959514040c241d81c803400e82d401101c0904000849090112401e000703200661108101d000040c03035603900f0034007040c0211900b0008129801d601c103111841d8200151781e80d40e10790a0003801700403045c3d0100e204003c01c00000e14072040010a64840705a00b040024000310020350f440300b0030813071050081d018040c81ea00003000c0394000c11014400d1f409050441003554030f40304602d08030b680502809860010500108500002603488808103642510481d070504c0007600c0021f18016514082d5148103807114001000e0a40c1401010000d0401c0424034200c2d0400d940007035100e40c1085a1140502c461100103400d1103420 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 855319577 1250 855318327 855318329
    0xc0903010f06060512090303070807180f170c01020115090e10060305030a120b0d0f020f12010b1002120d021e0a2a0c260f030301031e11010513 63
    0x20100410202e5924a07000d09190003030800b211420600310300140d52180084101c900c108030139500c08009903208031007541c2d0601500c0c514002e54100040c080347c150020010000504000007080d03080c0c42d4502e0440340b41c41c00d00d4840a0459040c5500b44800400002c0e90800b074811480020031425070000f6860700e0300f61201102109070f070038004000148000400101410610b0f81d03500b001c0d805007440541e00b0303629000050f5030084080308503100411200544a004e0b90310040450702003003046030026501202c001c001100a9540d001c00c2d262902d0314650180b214a09400902074902e04420707080080e00034071100020280d0001040e400314040302100d40781c0b00d0a02c03082c440d1111000301008140e02c8904429115600d2a4050303143c020350310021040d400c4d980110a4503602d4288080013003241101c519041c0c4810768540c0600f42c40d00144a010002c0c8060001507860751f144d4148540c00d020b83c0107030040e207a041c1c600c150006c40c612400003621402c080c24800c3d80d60a11325000520303134140d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 855320827 1250 855319577 855319601
    0x10b0c03090a0906150c030e041a1f020c010c02060d0f02071407060e0609211207110a06050a0504090506010c080703080709050f01090519090e0f0706020705090c090301 74
    0x109900c04183c003042c903440030061380d0211043c0d042e01203441000369416164554050301241950001a0203482c198021100242401a0040344c100e010408200c0c4107400b48480c120480c2152440ca61031941041100c51910003440c0064040706241c000c01c1480c85440600d00307503240c54105200700d00302580c0460311115840014007030f4205440001c3c85d16041140507440000d8105207950409140a00c10b0310a4804000c1071318040d01240d00500c2800088449810740501508618000d1500d40341c0140070303003078012012030003000030b0407041180152070742d04500f0a2103018444c40d10260741c00340942e01034404240002540b6149c10005031214000b10200800602c03000448004140e0303c41101c83c0103045135220304001076141c030200600c007902d8203581400074103202c000704600d140c6070300e0700c100ca0b04c03159500d250055141d402500039a940480c65045603484490031118154080116000911251000d000c0303950402002440e250400ba002003800710000c500c0e103d155070207501100c14256 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 855322077 1250 855320827 855320839
    0x20118031112040b120604060302010e0d05100f0b12060f010e13060c120f0b06090d03030605060c0309180405070605030702010e0f070f08061306020c160e0610020a0506010b0c0309 79
    0x340da40200e40c13682d48100c1d0b8154502a84201049840c10075000c0d0500b82c0340d0584440300c040740313002c090081c0a12400300c01e5815109900c407055404082c3d00c54030b40c144020710b8012481cac0201e582844000c540ca10303034541540d8010030410000f0420000c4e820705450002405600507150307001060f2428112610150420340b900e40d0003104583c1028071000201c4044009200f202c00508109084500107041da5811940c20804030080b403a0245130b0669061290800041c411344440c0441c180c0d411510070075080b944009104429403909000350b20080c0c5103844680442d103010307a2104d440743c03424440d03141032207004000314408030700030340003028003a0800d81280d101445402980782c4d9004c00e4814800c40c11a4200041000f07100810134610459070341100c03038610b005540c0c03104000d40c00b05401350760714006c801804800c1822100e40a00401d080a4111450305252081001d40005440c0c0c0800350b5124865641c006078020602c1030441c2d054081154440c00034102d65070540c131440c0d58590f4040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 855323327 1250 855322077 855322079
    0x803030a020d05011202030a1103030c010207060c0219170d0b04020d0b09061207150c0c0306021e071a19061d1e0114010909050106080405060702011803111204 70
    0x8a03640c0a030401c00e840c00720520140e41e890b05103017124060890043c1d0103130800c29121011505411205140d94030103000c89281c01603a8803a0b5003240c01400040340d4541d15600404030a5038100503c02c000800f90b007840b656040b0304d9072040311000c8003c58460790700b9408a4a441040145d5102d00c0003a00d015005541d112105030400c4000e003900e42049101c2c60740c0f00085011340c10210301c2001a41d4000004203545400d100c100700b60f402e0107202c41410841c00c12000300c001440304604000661043d48090380310113250841400ba007251100000780e4200522620700460101040359640c406050180ac0941e22199440d800b207a0a107180d2040070703401c0010010300b80c2100b440d07091460000c410000c90a4440f464035405085508980101c8241044c00601c404420506840a007100505120300c40f19950241352055031002d03400b2201003800c0f00d003040140b103814400103600c1211403008101e8400c140040c1c03005400780640140c100b0403000d070030198000741001400000011101c1103a161 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 855324577 1250 855323327 855323341
    0x40203010806062e03110408030c030301092004030213060320031002031302060318060703060302010e040b03120c1912020d02010506010804021e1f030605060301210c080303 76
    0xe110103441c1540140705035400c2c8194040c9115109544444e40c9a03041c2100d40c0142c1c04401400001d540b52603500010080020311003030804c01800783c00410805107071030b985000c684108480038400c580e90250782107604901c40061034070854064a40c104d03a40e003210212142c00c500200030540000b00f10700c240c1742010030205400d16103100c103083c0490448007003180115812040e80000d49407180e400c01c818003c6401840d02002550b44010f04840b0842c24080300d1003100e10b03002d4241d4004002c60b42d151402d00c2907507800b4103900200d0301c040c1c40c20700c540d036809404070b969020600d120090741030000c9a05c101c180000d005401e049003006841c402c1c100541e0429005400360440c6007800b602c070341a1650081d6006020b018450310050315078108607a0b440d000d01850140d41048005a80400f0710808000e56a00c00b65803402d01c050080e550f10300440100c05021507000d40c1105105003000e100400c8819140503103011444204032901c48814644c1c82c042010510700d4100c081c080c0004002c01c020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 855325827 1250 855324577 855324583
    0x1b1107080706030f1d070807050a080c0409031106070309171201150c02090907050a120c0b0310031e0b1b030a021e12040c050d1a180708070801060f05030307030e030109020402030108 80
    0x50300e5087c8244c1d0b03a500d85d6041002203010880c8105001c035041030715102c55134036007a401204928081c2c01c1c8195015603e42d021400c044048400d400030a40d40c568410030302c450031812400a00414140900d0862950342c107600100c0d05218600301d0740c0c88915035a045503c0f4050f603e08065018140748400d0030030079801c5c0d80b03800a81c01264080d44019000084d80110782c5000703010b60b90011810700c3c260f8180400c410083c0e000030a1900105c07101c0000000080c6a141c003803107200002c0f80018420031640ca400c0340c0d91300000d031404a0304c5400000f0b43c1066203840c2d0440350051555080103036203c0c3c100c80031603922501d0350012a0f240780003081103081d51500c281c1c483cbc412407040b0f504c0c0340166160010407000c1c504e4200b0181c00c3c0b000000c10140e030310188120407a003000365516560fa1012500581c5441c10460340c00c0000540c0081c0c6040013081803d00a030400b80c50458080810542000042540c070f0085180290400100f0400a04940c80a512546410350007070415541d1b0340c0c4803900d09076 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 855327077 1250 855325827 855325829
    0x6011b080c101a030a030c17041d0412021c0804020d120c0606210222020d02070b011203020d0503041406251805040e07091b1107080706030f1d07 64
    0x43d4160f005100301245103004141d4154082d455160301c0b0104400d0b8451003080d05410301c4900302c6060400000c04d80e190401c9182c140c07a043d0300e80040807842e0a280c1080c1d640200c1214030150751103403c00405031000c10181c03500380c1e8590300d0102c1e0f0607511800003444040700e0303071005031104500079003141d6101e5008001c100118050b01040c8503859654004c81c455080d528442c0c280311064038805d500514044409040180ca0003c044031800351000343c1004a9100742112130065070700161704410403207080a40ba00616058440d0b07520110079032800783d00c4040e540c41c61010004000001070030080b604880403081d107140c4040701c02a01e00030500b071a41c20328134092458441840720724003030664801c00e48070700700604c0d070005452440d15000c1400050029a103960f24a4020003102040058192042680041d50b1604051520254500c09401d202612201111035080414248480b080000f9058101c1c0c3c10b5260014541ea01e01107084010310001c90010195195407150307042032000092410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 855328327 1250 855327077 855327101
    0x9020904030c21080a0b012606040f020322152d1e0c030e1504120207081906060b13080d09061b02011701030b0906070806011b080c10 59
    0x30301c4440c401d07800c00064181030700c106000861343c00000382002450b030085020008181000d04403844080401c2429480010710500c0d00c0b03541c2810444141740c24021208450410b2204624500340f82e0024034245640c0c22020240e0b803040400c210400440342d250641208210004102848a0b01040090a01072544070030000700f4541c5201c24010807849070b07080220702c0c403518020051801c9507002c05013000d10016004d0599481000208030760a000440280c0100b1150240901e49803820340e0f000440542c0f400d04550110105015500b00040c8841002c0002d84040f12403d602d40b802c8400340c441074000021400c800306002c061800c1601d02d000c2521251415101102004036044584144070300c40c0000094501d0103611441d4070312004212140d0043c942102a909006401d50f41e0311001e90040383c140b0708460030403862403018042d46811401e24505400c2500308100000c00020342e820259080e03c3d0100030002c00c100c00c0004803003d070031400050b6100303880d0119076600100b442c05010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 855329577 1250 855328327 855328343
    0x12030506040b060a0f140c160f090506091315020c0c030d030e0307030c0501110a02100c020106030305190e041a0a0b030c070b0a0603061404020117150103020a020109020904030c 78
    0x441245011402d4400c29006a510000040c80001c422101b414081d0801180d5120402c07a0415030f10342400b1955a0880c03504403200704902e0b1003501058612960710030031680e0710b00002d00043d941c030f1071005608148aaa140d004810b020305110000240c85d20a805240c0d100080f40500c41001150380803c920003182511008141080290280d0f0034500c0034190f107400070400840000d024010201d01e6a002c3c50000441c0300c00c039400810260305c1000c14402503404071454007040821740c090307074110070444d00c0240205d131701d16500503100d0b00807956001644203511001d40c103a24400c18078030700c180342d00500511071900c1100f0310101c1c1c01a00f03d880c602500c1000c40100b99030043d80c003120f020301030104c1d800307141c422280c0714070344030302009001d00000319158080040414511300601c0300c030000058031303071a0707604080c40090441500300c120313520441a4181000700f4030307414038111041d010080c01c016a030b034014840304034010101088025440f8410300240002e140d40410305142540c4a4007070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 855330827 1250 855329577 855329591
    0x2090310060e060409020319060906060609150219200405251112072301140114011211160501020909130803041b080d0f08100302010801030f08071203050604 69
    0x14030056444161010350158023844880507494405c489854096000d00d078001221003407507607413109640460303000c00c0c0050000c2000380a007907101c080c203040142c45800141720007990002e80c8581c40801c04e030060005040811403103001d0149842b0310514040c0140100110314120300c42894480581110800740141c504035035482c0d5000d80e2a804c080d450000c000c040c28488110302c4d80303c40d4040c44e401c036444c94030440c15865080110382481c0c0341c100c80d0800842c000301c09400e0f280100005a018800c2071712440102901640c01c003c2d00b040c1401450b82c0402c00a40e4034414201c80d1044c2e0222250a100710105030080c80303010340c050444020126022121601d400350806020314804402520442040012900086c80046080d50081485a41202c410354948545041c001e007070b01c2140110f5020400c0380d101d1544424450741c8074110600c102c40300d60460300000c218080500000b08610941030a500034001140300307481407240d0011011400b4007a40c00024003070310381618034900031820298 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 855332077 1250 855330827 855330829
    0xb0a0c120c060605040246050307080a06030f12090f030f0c060f080a0e10020f0c0601353d090f030518120c01020c06030705160602090310060e06 64
    0x1c03590114007035083d00580c500c1d2120954907e0151110382580d0030211901e41024013000c41c150511324080362a1b541c0c9a251560b0054107c110040801052500c1c0103414000508400ca02c050b01d01d400001c40080c1d06051380c015a41025a600440410350f0540000410411510780025102e84a414800089951884240c03118003640740c901c03010a803200001a041c075242e51060f100f420214040b9603582e982800010300301d0b848450413030070343c00f03000400da0242c2900308400760060030040c0c80c0000450209044034038040003e003c0c58540080c4e51156510304204010007810749030a01c10000b40182251140402441040340200407440d01d92008803c441052048001c0703070380c00c481c40350038549403964201c5041d8040d809100044d84030700410300b80358803510495080c5407146e10003052080780325400603180c126421042880350408004000c9055809802d95103800c000c4141803081444610b8003401034068500c00707a4051051040c0582c80881c030340c000350110380a1846540054881c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 855333327 1250 855332077 855332081
    0x30c1b0f1c1d0901180902060f0d1a060f0d060e0c07031b1208040510090b01140f0609010e13050a0516020d170604061226030106090b0a0c120c06060504 67
    0x20310071641c4243c0c020010810b4181d001c69100c810945034000107000d030496030008040707801070342d4007400c0030001103a41c081080071441046940301b103034100030150315031034800500d00d13104100c0f540000710408240d03140e4008003600407201400750380c1c04400c03041c80e15404200640e08100c03000c2d00010380c11440300e82c3e0140c0e2280c0c20b8904941010b007100c4009220351040d9030315003001d0300480d01032048071104002c04c0c0a52051215151188015248035403400c001e44409811142c80c1074803d104404e45541c141c3c2d16031088031400796007820000c41c08010300002a0102d01c0c0d44d9024101c40d4106820025828a10303405075116110f1064000c4460308500700490350307040104465030100e2000301b4001c41108007047c1c0e0325449000100007054031030300c6410700282c1d0700040c24100c4521100010070b44c030710b001e0800001900d8413228102da003507615040c0000d00301c580500c2800303010000040d00d65a0039205006680203150046030a6528807035050000780040762004040d00c505141003408036030b6103028 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 855334577 1250 855333327 855333377
    0x2010201051e040605150603040609150b130902010203072915010512090712060504050c09061509031006141203040b041a07020a0305070e0606030c1b0f1c 68
    0x1542c0e03070010359486594100040c072018003012010f03603600580341d20340c4d55514011841144142c001095640903407410b042442c801802c680100307414218010b10980303170011002c1270300502d00d802083c152440e00040c3e0071440741d00e402600d42008110012154031031081d07a14040000c1021a030100e13510080c900c400d07502c0042042c1d000900412524500220880245030032019400a80341526920b0a03440240604404201c5445450340d00304414800c0c24040350f1407241c1d0a488400749407404400150741c208100b40340040c44803011982c281551010000c0100b00000300d502000281d03150128200350029200005115050301840700c03644284c04820743d000c4a00d0b00c09000d0800741485c0c01070032603030340340314949a80703000c184001d50250365080920402580104003400200d0700f0b252410800c520001d02c0c00380240810418058101c46074030440b03a244110891044c0b400c05514662410014544042507882c81081c1500404045100100f0010646074841e02003108040c08140101680 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 855335827 1250 855334577 855334621
    0xc050304081e19020705030309061204080d06180f380d260a020304060e0f03011517010527030f0a031d150106031e0204120201020105 59
    0x41400418005501d0070050850311031031040c1003149031940d09407501d158100c0741584907108603100701d0815094050200700c0240909801840c076207031508d8081081441b0305814104030f00f22540000702403007103800564101014040013400f08650314070080760003000719001d01c031f8031a00d8051140202e840f940b0400960142000015800c0140d124401801c4035580c4040100c01c50150043d101e15900c15200c0441c02d44140c4080e1107c01b4030608940740d0b411541404054014200700c003a0604c2e03000410364045881610300140040d6400001c41e5880000c83c80740c540542c2007090040c109010051000151056603958503404601c3c4150642070716025941c40040002c1603007004030b0301e000360504410b6902400304491800402600d031403903903800340e40e401001a50710503421168a41841e013400b52400040003c4c003030300740340e40700c0e03c0010134043c4100800e155442004000d03141d044a41c8900000c0322035401c645480d038034030310150940d942030800c07070055181030001035452000d86007103000d10b03035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 855337077 1250 855335827 855335837
    0x1202010905010f0e0603101809030e0d03021213090e101a21120a020105090c0a0602030d05090c0a0803130b0408120a02100501082d12090a092a030c 65
    0x1842e20288005d5900280c1074903200c2486003404074640319007036896003101e101100300065032041810300501410414002034855120013102c5008241e0000d60007524002e56200300d5500c038840d0801581b5a40d05604c00450b05040c24106080c41034045002c9004100d03d440512120421000740c4143c42c1c00200003540c081d81400a10b600c1980c11480c02c0a11001c800803a40a10b0303850542c540560459404a00141e44420410824050601103404004010303603118088a0800ad006074881c00f80550107107510b541c590004c3c1a520080140b1000000c4c003034407980c04a5101c18050751264030080164111141c2400005440e013425021101152070300780242002100450384248154051084482184995800c1c56545042440f840303001b0807040e0000c2000f1060300c4100789481007051031109080340d12801c04002641c0204a1000035015440c1c0c20381e07100c00180000f0b02c2203040b504504800340c50981401491506032030603030740345160740181c04407005c54001c3c110305440d81c180c82c00001070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 855338327 1250 855337077 855337097
    0x71101140c07110105091305130b0103150b03011e0b010c080d0b0f0d020919110a0905010f0207080d0c03050f04060302030601091410122d0e0a080417070f1202010905010f 75
    0x2002e01c2d071219401504a40304e40204151a03140c042d002b180c286c1080d42c2d09556840c404605040f2403280c86c0304441d00b03178001e01111800c002c008000500582001440703a40f07031610010300b617219550a1216036030195286440d1141e8081c0c500040c50f40c1c070701160041c09078008080040c03405170308480f141940203041030103c2c2c1c0d500100c1200041c800c0c111442d03180c4c4070443c0211409044018008112040d66100c2c00c89103064001440003140003841c00941d0400b043c03d0100c00c0c0c0100c0c80003d0b001e490b007070030b06a4850614085503103214808014030088030115001c101a5491340046020f8034099131454006034407002000ea4441410400c26801007203120040300303090003000c041040e1400014000340c10b14203161441101200c180b200c10040c11140d441022440b058451030b20004441c40045c0390812041c0d035484114420742c01004417040c1920350064060b07800700103a502410319100c01041040c0d80d601c00103240c1030488012404100d020b0800b00c0d195106500b000b41c01041503440d03988203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 855339577 1250 855338327 855338359
    0x30f03070f110d08120f070c020901151701030c030c08070e07141227070e1906050d1506141e01092c160206071101140c0711010509 58
    0x104042402c1203800090041140c004100c2d204c01400d222080710300310500d41e28140e44052125900100345505001c002ca60000c00b41c0c41d0902190305650305064083d01201110106440003c3c4201c0c2072003040c04000000300400c05820500750881c0d220307441806107561100039050300c441c400d0060304c030740010302c10010703011a00c02e80e0480d00e44014030605501c0c0000c0281d640c0e208050450302c00061800610340945135003118070b0032070748048103240949516070400020810000d4050f010f50401945405240501e1441e540010001c150040103050110707007901d44034a110300d101540314181e80c0b0b00300c000074910070114901100140010450486a017100c10400d560940b03010105040114800010401140b0403c000600c01000c00b0307402c03010b13012a40700c00c4d204080140540701001940308e0200c7c4880d000103890340c002110303084c4200b450900070441401802540030001c00507683c601803200503d44a801481198000c1541c1c4278101c0100005688500c501c440c03294116521800001003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 855340827 1250 855339577 855339593
    0xb040b040c0312110705040c05070318080d11160f050904050a0b010b13080c01020706081e0f16170c0a09080a080c0706031e05090f060f0105030f03070f 67
    0x22240c4507251a0700401d450351100c0118907001044080801d200281c01c00c420101045480c009102c100c80910040031b61100042503405011802006c0c03100d411212400c200914091101030b00b900d2046804014030807c0040103d02d122088110300e01810001485503200d80256106403030104600168a918020901c070241500800c1a42c031402002c40342c900141c1c2c450150750082509030b12064469030f0000602882541a038803102007640403143c0036400780d8011a4030000c55505041540055031480780c0c40102c00a05840d0690500d0390f2010010440b9041d04a01c0c0202c03e03140b20181600b81030203050360103130041c20002a0005861000820048840d4001d1010000c24602141401c0d5554516460110300000444251a0200f00035005560030402c40000f002913150501005205120350a15041c104902d8103413640c0304e400140118004100c0c40e034000d601d42c02190850316240f014155818800c2c02405d11034007401004462a00c0c000052314941c6030800c2c440714105650350303030f0307100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 855342077 1250 855340827 855340831
    0x1a060a0e0a140f06030d030e0712140706050703030506040c0c1727010809030313060c0e03030706051609080309060c1c030c031811100e041e060504090b040b 69
    0x503855450300030b03445804440d50380ca207000e140481080b00a60804108050400e039412200c07104062900b803030b98a01c05c900080c0da0045030002d02540c400780c00c5508000031a5813502d080d00343c442c4200b03440010015801070041c4103050096508200c00e489880c100429103c0c0c0c07000714030028000d113101d0008906000c4980307a0041d46440c01c9803800402c060b41c00e40c241d40300c1e50715656035040c4003001140395812480356a4003943da480954994940b00c8d9900c10303240f00801000d828079039208101c541260041e0754007001d08100804698032002c40d0310344440905001c451098401c904181403a0b6043d005110034820380714024059410100e8102c2031242e40c0d00807003506005445408401e64001451041a1414400302d40e000303c0c040d07041400c042c060f2204091810102d42c614041c40002c5400121662902042151440b000355035143d01180d0341070500c0c03c0c01c0d07030042c0303414910080c10030001240c01202d8102c1e5000e10060759910304000498207104c2e0082c01c41c022500001c2e0024940d0f503075490b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 855343327 1250 855342077 855342091
    0x40b0103020d090c090e0304080a030806030732100c110a1502030a031a2817071a0a051c1118010e0f0a060e0402190c1a060a0e 56
    0x50408454030302d06420f41d03842000c00e81c2c01d94022030b4180140c0311240144000a4510002141780c940b81c45461595181e07207400c05800c000f07902c0046412950140290002815120800303e045410030702d540741c094152400009804440416540ad1810602d1702100d8025094596105da90103d4a45402084401007020351000c00d045010503814000c1d0307441031400c110707540115140c0c6903100000d4103c1e03c00000340941c0d491183c0c072450a513030300e00d407403000c81002080b41c0c505803640f50000c41010282c0d54000e24624240100381c8210071034000b5078182101c001050b003460114200740382201c94420003040400003a4104036400b581003c400c03065030008005440028008594503c0312115080103100b10710110702c1c1503002c51550783c0001101211082100d40e0902c609610f000259002d2445c400d072000d024207400010240d03611581520803840c203201003664090f0101000400c004502c62040361007000002c0b5104017058a03101940c81804082c054400050074002d001c1d400e640018a92 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 855344577 1250 855343327 855343331
    0xe06040605180d12020c0c10080f101a220810150b071b030b040b1b03070e01030b0406120507061e02030a0e06041e08100b010c02120705032e0209010e040b0103 70
    0x5000c9440f440b02ca01100401135484912030708280c10015032b882c00140164038981c2030050103001d0011a003800035121706e075003112a40e42c0c2c3c031524082a03810203221000b00ca440540c182c0061100d4001c21340c031481560106040048140400c4a10400206405200d0041c00300f031003440300062540b0043c01c09405c402608021560f5251340700701d440b420450381100c3c0c0d02d00c1c600c180140600940002080c144440c12240d04614005e44000c00d4200c1401e0b00504054447c0c144414030348496000c4c0000c0c0482ca008100c0101480c02c180b683c0d01517a00c208030000c0c00f00840076407940b810085690f10000d00754091441c1015654080b282503810004881c0c1c0310400f0800004c4400580444000c6500c451509980076490105203e00740004003102c2c118040c1807140c10081c9030390007031400c0c4130964101e411940c2c600042c1c0b21607240410340e400082c1c1600c50000942c100c1420030284460301c1c00769013240c0f02c241c180e4502a2040e4020100c000740403074005c021b4091a4980341c1c0003852030034030601d40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 855345827 1250 855344577 855344593
    0x191206020408120429070b15062a060103050a0b2710060905010b1210080303070216060c0803070f031b0908010f02130b0d0e06040605180d12020c 64
    0x7040303042c007200b10756144220703000240411005502024041706138210881c40c107552154903500844601c1582801004a038070382c1c0000d9440b0b4110116a1a4100050952030700c41b0401c0079a039584050308400704084034642d11501c0e0b0070302e01c001030b164140c0354013102034000120341d81d4a000490502601c034910496603022107601a5110124807100188848014030400d0f158003440d00458082e508449030503410040140101c580c03900440301900d440d020500c42c159151f0f01c40800c80e0449800c24481c1d0b0000100380003800758002141044134400c1e0007008141b0796544002e54410960905c01004041c0520010382000d005103410705054409040c04590740e401e028020b41c81c4440e0010b100045002800d040c0510340c8248a9292040891081103141078a12001d03540705106911441c26601400224120701034440d4221a020004031800c46080f030500c1c0c5000d00241c141203c0c0244c84451380240ea14074103500003148603100c0859240c0704030842c0412035000180d44020000a001d11400070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 855347077 1250 855345827 855345839
    0x1509060904020114280504050414060901051002070e041b090507020c06070618080d110c0307080703140304080405040c020307121103070b01290f1c06080a061a1912060204 75
    0x1400c241c0b2459a00d4aa446090400b040115002803070107480740212b1030200314517600c40f05030040c1583c0088941d4107405100020880c40c0156503001302d5903100c2044288420000d2505200088441300070240d038520b81c8a124078400c40390120781460050348000d141c48c80c141004801000b001d8080c0c0030101d4011081d02804240702038208040302c00600006d00100280e0182c4145101014044d120601d081e03c03d05007540d41e4090004007410507240001c06d6000c040c082d00d19130150120f803002c0542c0741c1c90203060001054000c0d00c03c0b640554182030790000303041c0c408400c5400d070680c8140302c0c0d4104064250201e032402c0c41c0c58000c8040d80710800c005008250550041c500030070054802c0400c42c9400c0040a4480e1000c440c41c1e00720315403d1080c00c68040300102659441c12040c00342c03c0c040d1281e00c0c0c40388003a140950003070142d80207050000060041341e40040c00751400802c080c0d0141510300303040c0700904c64900d100d00c0040701a010700707001d0845841d10f00c0c200ca5000e520003508181e1030391 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 855348327 1250 855347077 855347137
    0x1e0e0c0d0f0f110402070317060a08060105091807030609150606053408090a0b03010305030a1b0f080306040c0923031e07180c14130801051509060904020114 69
    0x1100c1030780442d1040d203942c02c8071075070914449c0d031002c1c0c15940e2400140c40e1804445c1d490302c0600800b8801c0380800300048028030412501c00300d4461090442c1c48140e030b00e0400d5001060710503816607400d6645c68164204115030700500086034000e40c2c98518180c15084089503942c900c104444c0c180d4114280c1e00178001221681c41c000358061b044481d9203030801000c001944a03254000c00c4035190034001003000c00d5010040d2002c0300e034241440c90b0582154084503403c1c04604e00c00401e1101c0300707001c56040c00890005144914403c0d901080b4080b0740070402e0368094098401d4840c1c041c0b400c805100d61240c4584001c190140c09070807030b2040c003e503c52040d039205000100710f1040c0e0100e10100013800c441960079542480c01002008907060345000140001480f02c5031100c0c01c000050003014045c940c0d17203410001c241050081025041c035001c00030b50383c803d51007420b118111000114180f4640b8080540c0550741c16110651500c0310400c0111050304038400e550303503066482040790412200c02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 855349577 1250 855348327 855348337
    0x537031125120f0f051c03020403060b010306210201030209120109020102060106110a0209060f210c060c250308040306090204110309120c011e0e0c0d0f0f110402 71
    0x44078112040540c0c581800300d02005070352000e0007500064982c40042440d2403031402005800007000c030741c03030505420301c90700d8055501d4132818150151220301080c154036a018100381ca200304024440c0e804564011010780c0e07254001c05034141c1121081055010303d42412200491060401500700040c280c0041e00840303980d403442070580d4443c001c101c11584c1c1481964050211b6041c0b044840a480e403080d50f95100100000303000302d000ac8003143c00c03a59280041d03100d007040144000760f260160500d80d02c0c0c0410070340c11100e01d840b44141646c1c9a140c00e6050790a400d103420000c0c50000b0800e40035581081010001992072000d0803800b102050100c1d00030000380d0300444000c02c1002c1188103020803111900c1b1111040d040600a1009140c00401d4020b440316141c160140c82c1c01180b00030301c0c010420005c0080d81113102600115040101c0d80065a00345624000e0310300b081009802d200d4882c1004030000c04e08000c50034040d0018401104080b002402081c2c40d032008840b84c00840d04036480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 855350827 1250 855349577 855349603
    0x30103050309011e2102040302090411091b0706050720030301080709091227080a02150301061b03030902061210081f09050a050a030c05370311 63
    0x18580741d2540c118968150802010304d40f011590032510b4020400101c8008210544031a1011079041904540607100a15001484040300f030900b86050790640900100d03180c083d034003000002e40300510901d40410003280c00c5222506e00000d075601c3c0c0b401803078010000700c107012891000c1c0c2c403680030315002801d4860b0244020741c0c0d40d5042c200302c00c0c60520150300200d54541400b622000249480c411610302c044142030040b0100400c02c0401c07050000d03a1030344c2c4801503c03507400140030340c80050610803640c02607d408409050b10f24208505100900881c400326684014241940c1d60380c41c03022a83d18004d15001440e4121076000a0f401d078000e41003900741040d8501488003480b420140a4014060080109080310110982440c80d00705d9601050203e99100e91410922509102d10740b20745600200780c5103861070500c0d01512800e00031005440d18403c005600e0801446007001201c07145c02400c076480c0c02c0c103c0e07814030a03907216010000c03410000c0d0781485195210081100c1c04600740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 855352077 1250 855350827 855350833
    0x20d05160f0306060e01050609040507031d0a02090c030403170c0d1407020c030d091802040308040608180102030708010e040212010c030204180605090112021c0b06010e3007080303010305 82
    0x1103107083ca0000d66070180c02040582800d10010049a41d40b01c08844e8203010548003c074403581c50b041c0580013850320301c0c85c48240020300e402c01d003032065000c45c91000452003140d010000781c90301d0b107405416003c11140240401c280701d80d00c1c035414507002401988999004515441d00d00340900280568031440820351005a8410030710203c1a01800080da1a13002035004102d0ba02c4581001030401c2c8145c421260000405101e14000e404c040d01190701464100003096a2151741d00c4000301034413412500000c1c624844284c459003c41c043c02281d005d25640c0da01c1107256401d000c424088008040e200301e0b4800e0b00305100200c151000e01400c5400c040d9911300580b42c0d481d00e171880545000201c03010000c20314000c4103220681e98111340c281941d84e00d00c0009590395940c400301d02c0340d5034054203401400b002a0030305010800d03a518864810071080c1d8844614100b58401e1003440002c2c020703141000700302000b0121107002d01e0b894410045106004840c0c02c1c56a13a080c2d40d080d5402a00141c400f50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 855353327 1250 855352077 855352079
    0x130203190e0a1b140303190f0201090218010311090405120d09021f020705010201090b1302041d0615041109040e192307060f0e0607021039020d05160f 66
    0x1a10195824600081c03c1e4050f44c6003581d069400c0c1c1e241d8000c0700b90302e400d11040b50031107222230f4800d40c0003400d00c56028113501e065646c0c1040d00d080b05030702480b08541503207841c603502c1454281501064011640b050007010012008400c8502175040307d0951044180ea822203207002d40d8840701c0b0324910068520810302c001d0010203000303041c417140f6005a81560b0426205800142402c131115038400d0320340a0503503002c42c1520024001d8582c1c0b030328544a0040a0002151501000c581c2600035200d400e00801c180e0302103800d000c01d98105959104641001348614080380c102034110010442c030b800140d030039901d070540000c016100e03c0942900d84038800a003c0e26050041c3d072011300c40b03126060081c444030b2301e00480117001d550320f85124800c010524250301116141c210075560207603402884405c1942c00b0050061841d00300f12000b400700e0a01805400b5905c00026812144902c0d030704410001d0300940c1c00784400040c0106003204c0c607109240d06164a55580003040020305500c807800c43d841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 855354577 1250 855353327 855353339
    0xf040507080c010903020909150c04060e150301090c0903020301061205010f060e01150909020f270109121a0a1506030e06011a0c1b130203190e0a1b 65
    0x20111940184007954082c141c0c0448a07a0803040340d40860764125800b9a00369241d621306803c0c040b110010030700d8030614000b4001c040c0d8568002d00140c0760155074070312291600e1030800407004422801801c02d0107007000140040305042d08070102149031340c00e01110440d5254003007421505c00c0d44c042c0c07075544034110025040050030b002da54200c4074109005d220326400c0023a0510604010300c12800c113540115885500030b030088500c80010460400110f407100c0c1e10001e28002d40c0d203c4040707980d94044030044244940801d91108840380c0701a074a0110300303400c1590310308107020f0001080c0d90340482420103060004141070410b2184611071004103540800401d03007444410160491b90605083c50996490008d001507000d04495448440d601c2115028000008910880c104140c080c050280d148032000c41c01c0401d0000720400381c4040c1c0c140d006000031501240000d489912034100303050548101040c0c10741202800360f0500c81500c0743c040095640e115401054441c40805540d20351041000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 855355827 1250 855354577 855354583
    0xf0a0b06030709090206090f120102120610030207030207050609060f0d060e2508040602070614040201080c040b030c070512130e010b040315150519080c01030c020a06230f0405 77
    0x410003070030f0a100c1c040240e800520603000d000d0429016804841040f09680d4070202804e00759030540000b15501c900d01610240001320488015014500f00310000000a20034070892b0b48080d0140c2c0a0b00009003400104101c5034049210a640000140030150001440701c0080145020b885e40000701a0700d88001c00c2d56440c40280303500003a0090401261042c1c04c945220307140b04115143c00d142130703580c40c50464000c1c09103207005042c01d480e2094004142d01031072180342c00799000f40c03505000b41c0c3c2c41181c505020b1055004515041e90f0600c0419180c0f05004003425100303101d031040c0c400c00741c204520980240c010150001c408582c99800308840d45861080501508001c00010f1030142135840c0d4070100304892044d4944a56141001c55810460b94244809088000c200e21380c401130011080b601e0148038082c904042c0a03100300c5e82c0b40744d0302a1117007014410b40380e009040b4441e025180c0c2d000800d40301e1801880030b20b038054011500701d030049a45120f8019222882c60905190a10340e00d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 855357077 1250 855355827 855355829
    0x150d0b010201270804030b0702060a0b061e070c210c0905071d040b0901081e0106051f03110307031a0901140607080c03030a020c12040605040e090f0a0b060307 70
    0x10542e40340c00d10040b0424401d141c040300590184501184100c042d140016541c42207030f00181600900d00203100d441540411202d000c0c81e103815052000e20360910400c9140d200790403c0e407012135400c0444a1410301460090800e040c06040180705040c1e84013a1b010390801d03058150814500000c5101040001c03ca003903101404c070810007007000f40390244015107090031000c1c0c40503c0d4508018042d40c1c039902c0c0d40210b512100058424282c3e0350352400481c0c2c0d41c030810300d1401d031000940c2081c5004030703205219000855100804009902600341032135959054007920400416854490514201c0c450380b00031401002d4a80d00016290034441700940764051810a051141c2240b000402103001c0100c1d1007002c0c6201180c130b09507201c8a520b441c00d40c600c035080740c580c0345020204c2040f90300325283c7d025117011720b003075401e80d404242078102d002c0c5644101d001d0740c804035009000a10540d50303900541c0f54401203000440da114603888585500d002c100c40700c03c0715210a060300f001a503042c1400745038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 855358327 1250 855357077 855357079
    0x302061602060f06060d0c12061e090c050d0c052a0d030f0f06031a060a031e1e2a0f0519030b09010c09320a05150d0b 52
    0x1510048100300000e440c0e800240c480b0280303540d50342c04680740396901c030120b440c081e80c0801c08001006548502800040b82c2e40b209444803450410300280c81e09400c20003210700070118025801e10744c101507c0c040104100700c1e0180400106000b818031164044c4a0207a901420b91070b0a52a0b03481000d1541500c0c02c43e51b400c0f00384c4207541c892032038102c0d0009480c54444d1020704002c0f036100c90f507180c808020a40103c6a40c0c0d80c508001000061000ca4030441002c802d0f08a442121030f9540c0040c80655252403200134055000a90640390152640c1000002c1c644111100685290384c241d0742c25184c0c403c880241d40f0385030055144c000c0d08030302c1c80c010315215824030048a510b514040002d4401c101c01c1c420070340a10030701c42c0301d86071107501c02094030043c650211a000090030500c21361402000384400c01c1707020a250000200d030404290200e4400300e10b8100b0070391032a00507041c2d084281c0c9100e403241034100310a070101103010f0740e66582c680074014820148a44483c5180c001a0070703510415800c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 855359577 1250 855358327 855358351
    0x40309080a152327030406030501050a150801030809041104030303150807120b150603010803040e0f01030b180c06160b0c090d0b0711030a0e190b27090a09030206 71
    0x80402d030442011160300071030410240360f091002e51203c104000740013100d8100c9001c00240800c0d015091740c800e90507681e0944a1490fa40e031a0103100501c00c00d030404000104041500400015810740010040f402c0c0190010821419000201c0c032190070a4200300c1c0804c1d00c40320241d03100171450b103501e40241100da0040881900d00300c007145c7c4294030b040001d82544407400c00a1303d00c2c02015440021158050b00c00c5076a90396581c0000d460350030500480340d54080d01404070f450340701c51503845410307280c0144d00740740d15884003200b08090101c90300c100e0480307002e1108010920b9543c10081c1c0400081900c0d0441012981d1414042c0b800b8001d020400550007403180e403000e03403078442c8107480c1c841d804812071410b620703a508150b0382100d014580025502c000aa039450b43e5500c00c07c038007042402139544051400c0807400820692110380110202900d060006000c001441003032044403001c4404c0b2415042002000300300c0580702100c0108106883d568510105681080665808a400710350 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 855360827 1250 855359577 855359621
    0x6050a0c08010b0a03060e090a02131505040c0c02030109031e0206090d030b0d30020d140d06050a0801020a0e060307020a20060c07060210061409040309080a15 70
    0x1e8a2180180501100c81c031000c07402c808024060390290010340320900d08580c562500e800941c0e982c40d0f804004901039820070140a0711170030580248050062925200e01c403803814281400000d01401d0f521200b001014081d0a0158400388a401d1195001750303501c0d102d4003008034103036803100084003510b421035100b8003c22100d96000300382d0064a410a02d03001c00d0110601c80050300d6150181e001510a841150a40500b2595002e4401046105001d1011620010702060343c40d01c0c0c51001000101d120007545031040702c0588014140740008500c00180e80340c46201103881d04100c1d800045483c1e6001481c281150f41005484c0700010040b645070345149041c0b0700094940c2d044a00050070030f00021004042c3c02c01c454209168020701400041d12040e80e0b6200700c0c3d0f649054440d10015000701071203102d13110081d0107608213946070213411801c00100d0405000240c20300402c141c00b0020384020104501c0001d0140000b52030055400c0101d2825001b01c07074084070827450200181c43c4041c56 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 855362077 1250 855360827 855360851
    0x6120c030601031e09060e03180f0d141b0411030402040e030409020d090506010801020403030c0b073b10020304030b130212030c1002030411090402011e020706081003111c12050706050a 81
    0x170b4030204e10280d6643c4035a00281000c5950805170150052100304031181c0000c99a01c006030de40c803582c0d1a41e00e030b0482c042e031603424042154248040f04940070020000100941007540040c40c2e020814421246441e58440d603040880e0480d444006d64582c8550881c02800010040c0c41d000d00718450085291600d156009827940f945010001c00700c145007400140414011800f40d03829503e8200c041d9040c030500581c2e07004060034000e0103070310041c55601c1c0414905010001c00540501c07900114501419610340c4c194160008101b001507540301250400143c480218544c40b00503104002c507101c2199954070790800c120f070a4000452881030082002081d8a06800f001030340041d505060b041d2160300040700d0002e40070440445007011004003451030766000034001c00702c440c90391f20701480c0d4840c440c3c0034090307207a1440003800c503501031124000d55180075410328840c02c050250104d01e050180e95654110107003406200040343c0003103824010310443d40030300760780428868010800810ba03c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 855363327 1250 855362077 855362107
    0x11104050a061101091e050f0f1902120312010e0c070c03030c031224060503100311180a050f1303020619021b01061406120c030601031e09060e03 64
    0x44103880c00c0200724012080681c2c0b01707500c04880550003041030110808081c0c8081c00074102c8040171121032007800621203110340d01164108552a0080c0503200c00021602201e0700a40c0c02d40050341c0c010f182c020801d6501070104010081041d55120030402176151021003018082c1c001e007144181c080030440c580020b071000811006903513050500c58034024041c00c045841c80c030b4482141601d58a040d107140c507a0402e40440e81154000f01403900700785601e540040380c0d2804241e505160380080320106000040b44901d4031150b0480142c091040b280c1c60f007031105040c50080d24031042441d0340300302303028525a24412080c0e01c41090343c1b6180e8000320347d41c3e0081d680d1400400c0c05040e03c103000001d1000389085c0d0110b5101c070080d81c84220340105616881802082d061040c04a8811341100c10700b01418800d046d16000d0000f040070701c0d4141d94541414415600082c00d850400d0b03136840495a007800c4ca03840d08071241004010000700d041903072400c90229a1045846007450f030041c840b5010034548a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 855364577 1250 855363327 855363329
    0x60807020a20041a0906030c18180a08040617010e07140d020a020304080d03050c0a11101a1003290d050312040b01090203010b040e06120f0708011104050a 68
    0x1100100b600021805403903825200100d6038164424140307101c18414510308145440100030481d100012525440101680d900e240b0350415089814100d040454145100f40303d94089500309610410104070092642041c061410071504c482003c201881f4103644400c01e4428a1942400d802141d4180140c2c88146d07500144448200f100700b042e41041d020303181c42a289107040880d41551107085440000c0d48039085406011014030400c0d064000c240d11a02860380035440704645c0c1d0b442c0911044003101c00c40b0061381105094441d21982103040905480b0b242030111040d8104949424124100200440140103050815003842c154032191010110728028401e04c150b8990340305004400844d5130090085000342c1640000b00300042c1568400f84164801d0380b195504001a03a01ca00b64881240801e020f041e404410034001400300004d0000300c1e680002d002048101d06154000100b45404041a1008803940122800b0000e0050034048c10001101c990442402c29060401107004a010303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 855365827 1250 855364577 855364583
    0x504030c020d0c05060c0d030b041503020904081c050402011b0203300703180f0b04030210030212010f050f01020a0209040b0705120c1903090308060105030a06180e0106060807020a 79
    0x20b5042c0d07004005841081e0300c000d01c400362000e500d03588031206c4035440d14410603d8101003401d20b566000146891300c141d5403010035480b100f078041d0742076400380a0400d10085c03040368810010050009108160301c0d04010f50100b0440c04941440e140c03000500407403914210b83c45107590401b1400041c0d40200c1d4003c0029441d40d121b00f8600400c0d0094807604010449040c514403001602d80181944441000e1000324800640c069055554042c0090300805111b1010040000d00c01440145014041240c0d03d814610340075040031356100d00451b2190081e40208500c002c2c4040410142c200000301e2000b4090900280203003d90507000f15020b00d41c0240b00900500d08000080c055500a406a580240641c0c41d111054548000018810f40c8640000c454041055001c1003400748030b805000b655a900d9a5007240d5602c0300c10056806800162906030790036181e280c041000e60981c8400c00c10894070002c049461080e000c801c60848425804c600c08021680b0704000030580c0014034010600d034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 855367077 1250 855365827 855365839
    0x4180c0813140309040203041112060408030412050405041506020c0114030a110c1e10020c1b01020708010f0b0411092d0d120315181a0a06051206040504030c02 70
    0x1070354032480f421480307504000f65001c2d00c0403080c001800011140441c0e4000140c40b41590f80c1e0055241a9484004850017408103a0410000e000140000300490b9079520506000381410380300c000007400e03030703c2001140600300f11040040109581c104040264038401303013400300e80700b50700f114141c0c0d4503c801029108929121001e10301400d02900845110381c80202c1a103501000803941100040c290b0180c0d00403500c2054061020a0000c1c82194111602c0c0c400400e000b40800d05840384580ca21920750341503000310100000c40356070038000c030280303403485d00000104010703100b042200300c405039030406004038814480c2041549451000d11144a16541030300c50380b00f0610314090412095030705181c2c110700c2030454201006072405003001128a181c605206848020010030081e02d85885000649103120352121440300d01e984c8621101e4100d10f03400c41c0a601ca80e804104c0311032840d03001d0300c009100002d103c8158100d00403da0307003240c4119024080340c03c154400410f0398080e048040d1181e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 855368327 1250 855367077 855367103
    0x30e040b4b0402090a420903020d0f063e040b250b0103020103140f1801061d01080d0e01051b0a050114070f081303030c1404180c0813 59
    0x5510852400300401e00040c5103075219600e860307130032168035031002610380064005c583c00481d42e000c6c0e460300c1410701d416916450002e2641c0c007044041c540c05002a210a01d4280700705001c9441c0317001d00c0c04101350850702c40ea90541c40c1c0801c0c0c3c004026004140c00300050710399070300342082e03481821182280e0008080544039002c0b0154849c81d0000052002a01c008041e00c0c00d040101c49069681228002d807020030a0790400c2e42841f82c281c000b1100c0710804010f510005000d214082030104002c1d01e01000041c015403038001140c0400c9252a5400035054039000402c40f0324002c1010b0260b85026113492185c065404001804901840b0708002d045801c1e00020340300070306c0c00c0082c01d04050300131000b07000c04001e80c040b070803202e90103440307803000070350002402c0401e02d0186065034022404080780e180007143c7c40e14110002d05894005004222111141441a06070a405000901941c215032083c403400340c580002141c0e10141c10005203c0840c0810003c1102c000d032154107590402c91208505d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 855369577 1250 855368327 855368329
    0x5030414030c0d0b1f0303032018010318050a3210020913150303120c02060408030c09090403020c2106041b08030a0908060f040f030e040b4b040209 65
    0x801000e08040c240c081178050001c2491341c90b800045020070b50b112007030740c5240382c0d2120f0b110760312032100b00381600302890041c0a91035209500000582c031080e0186079030340005030350380c40c00e20500c00000d1720204400c0c508443c100781881541c1d010008040b0380038440304628401c0a8841c40740512000145a022a400c421500c45401290720492010403c01c00310690401201254490340400e40000d0396080c54450341b19510312482c00040341c03640080c003481e0750b15074070001d0b9030740010130300c0541c1c441c1803001020300d80301d2080d21409284250085c5c05007a40600c00d00c1400c0d05901003c1c2000140c041816a02110206210b5009a04074400160300c181031920f400e2410010390080c0d002d440700040d40d00f0301ea035000708814290b40c0b1078400d0b9011500e032000350050807001620068582074405001100190244401e1340d0305600c0503102280032408040041d084240b006c603d508480320034103100d5580850721030402c41c072001d1030219207598003000c05440d06500c04041081c1c021076001132041c510b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 855370827 1250 855369577 855369601
    0x105040b030706140d0501080f010b2d0a081903020d03140c070302010e06090f0c0609061606060e0103111002060c1c181b151409040b090405030414030c0d0b 69
    0x8101c18845c184201c0d40d4981c102980c1d410516a0b00c8804d51901c40101c2142c5842000c0c646031100030300894980b0001d405414122000e5040e03840d5100440140c00541a00c06122043c80200d44504110094443d0300303000c0d040084101189041619100d03480340082c1500d00e2181d0000e031100c811540319803451a060f030050900e280c251030503100e1031040004071900018010800d84000d004e50f001c2c9910481803146900500c0305e19644118140f21103081030309090121032005004003c08138070255500c548484500081c2c1040c0e640c00c049500c0700d0042e0415600706651040544014809d43c41d200c02500780394000c00421601c2d20b860070721100511545d0b6040f00400d0300046218044c0041545404010309400c00403141400489980004490300c68501034a00241c842e105e024a8071040720605802d58445200c41394065036403080d031070075a2034907040180324030300c200e00965a030740c140145030300b0840c1540030f00f5220b03074030400b1802144d07260319080d90039050340310001000c661280411044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 855372077 1250 855370827 855370837
    0x804050a0212010b0a0b130918080a03020d11030603070e070201270203070e010605030c0a0903120327110907020109021f030c0306051f050904021206090105040b03070614 75
    0x340c400b507804070031514410103621010200341e048590010803030390382800e6803550007150702d02d082600402c941080310041d55004000380b6200d003480714861454568580b955034009580300d400103176001c907804201044601c1905081101d40a4241c214074006001070380d0f0742d41502502035110401c0c0081189039000350030403031aa00c258160ae4590001c0e05802c420020340d0010181e220703102d01000003440e924031030f95150507981c16686262440e41ca035410300e06541d101c500080700700101c0c1c80700000455100318801c03411a080707071b40110704091a681241c2040156160240c1400d40785408d1a00140d25a1503600c8007640940b030b64807503039680360310603401041c1009000e5004030741408410550903d400c00324800da81c40e03840404c00110035440c100c00b02c520600030700c0e80100c541058410360b0084040141d072003601d10300e0614a003800d1007000c03c09a800109a9000b82c14845040c0aa01d180180000780509800d4408104401d10b55002954400700c80c03044030184424901081400c011180440d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 855373327 1250 855372077 855372079
    0x140d060e0708101409120c0307080408100b030601140906030109060c0f0906030911010804050f2409060408070b1519090b03211b0106120c240804050a02 67
    0x51100c5075036906060f01c0d42210103d14041c1440c00c60390366001e00403451410300850141000745030400d601014085660301036031503d40b03648030030301444000550020042c40681101c1c8040c01102000c0100340060b03840b8595250f10942060005010715446071407040035250b41111040710350340b20f4001082c0149040d1202070813150404252181c6160002c0c2e040720000100c1d554039121035942c0200710200d03001000000c200b010700d50903c8105621030001c89030064007850a40300007103603d0b0b8405182040d28020003c8000d180c00c5424541a084444d10b903002c0c01003009484242390503a80d013034542c411900001c01006036000820305a034070111500c0003542001d041ca03801031108403204085080c0c94403c0f452040d08140e414175181c00c0124807500260300e880c20940310701d03c41d001c220040d9004601d074811103107004138034650600000d010340f60003042c2400d903480001c1030030300b00f60a070031a06e9000004030001003030b02c0d410032a50038415010208090300d015042602c6903c0d0a0342040d4540c800030f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 855374577 1250 855373327 855373333
    0x1104020a090810150b0403150902060c071e0605040f050d03020f10050402090c190e030c0603100f0b04230a0e090106050a06020109080313033006050a140d060e 70
    0x40fa012103d9a010804040381541c4903c41e107607403102900c01a00c55408020716565204044801e101d045421152090703100519160400ea00f5456042c5040c0f581e40c00700d42c00d403103684011500c0d00340d01d0a01c61f02400e41da00e40b00f86040d041058065100c0b21030302c40c4a0203403004609580c2810b1007840035040780e1443d00d0545240703004421181c0060a02607500740d11490000c2c002c90821180c0904079120f2682c41ca403000031500200c41c080c1c2c5c011a484540f1030309400b41c08840002980d0304070041d44038241c1609903c06403800c2c107800184616107a0003403440054100b10620184107000c0b0440070000c18001d01800d40810710000c181040501d40c400c00c0c000459000340002c0c0b490640001c02581c0c810b4a141407855a41d92049080c0c643c8a0405022300904002086c014001e101c01520424024100b00d001d18019a141c0e01e07880c0d40402c015511b0708504410304041c50a076000d0240240030403212440124140703450141e01803210b84074148501481c40c00101001a59081003804c81240c80076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 855375827 1250 855374577 855374593
    0x60207051c080f0405010e0901121104060b070f0b0f0106021e0106180f111e09030a0203030712110a1502031015020304080705120c010f02011104061d0d1104020a0908 73
    0x140140c0c0003401741e0fa000c2000100381d110241800501e003412150412100f0403c0100d030b4440009818040280b0b41d0030980b200c1c0e0118140c41280c0041aa5900c01c0c403003404030039454141101c3d0100068514044107442c400100001640025a8208100c604070500506844a011030b80100580d92200805418100c511200790a040c1e2001c890400d0620007804054240e2a80c02013500c1803441440183d1298442c000460304038001401c0d58403400740403100304003419000285546c120390000c8491869101d80351080c55484110414040121002410b008150fa52400890340e010500c0407540c0c0e070701100142000c201c222043d80101405000c1010005580f030700292a0341c05401110b000384620364000855083c80c101c955072440111028120f2100c000004495007a0160141000c40d0749540092620040103001403004000c2e036100c91041300c580220803240b10340411007091140b601000b8107030204260061105040780221001a512882d404060310110310301d0f04010030a11030340700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 855377077 1250 855375827 855375847
    0xb0105120c1f0201050a0b010f03020f040b0409091202060108060402011b0f06051509010f0312090b04090c0818100b030a0605090706140a0c020603100e040b011806060207051c08 78
    0x401149030302c05950003400700d81c3d20000c400003950082c084040c0016251031400f44190b1181e0301909214801510041c07401c0c4da6000075508a420076002034943d03660f200d0b181000c204585100001003003c5001408540d8545100592100c0d0010710203414008044200c2c3c1c1c1c6040c51050003d1140c1e44440300c001840d400d070030084018541215200c907000c1564030000b1141c0340030717010703107040b14149441403040e44e0031a5a600c0700c0302c0100c6222424000150404146c03410071314050f02c05400152400100686038110003000c1c0103021344520103240c0c00c0c6200c41d020000105850801085000c40420b108103048042032a01d840ca080c00b0304840d01d17160074060710140c04600502101c0c410303540d07071080d5419020b82c06891b110b6024084d0120310900c40c0d0340300604001c405507a200c0282c0c501c1044c0aa9229004846070100300c1d0b0460740340001a0060110740e400061040b502c15002030104203079400d00401035500d44480c0a03e41c171490f012180d0319290142c01004065040c3e1040700651a450410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 855378327 1250 855377077 855377119
    0x6041503050a050a0c090e060a1a15120c07020f10050405030d05030103110906031e010f0e10050a0e030922020408210f0d0c0e030d020a020a09090b0105120c 69
    0x1c0440d400000c46400280903c00c6000e0040403805a1f0701804003500c507414141c00070405012180450f4070700c403440c4201c40e554155111018a0a40c100d640e0b52010060710420f152001414041c1d036107400d0100c200540c480407610800850141c941d02801c0091748015940360044e9481107906120b0325a802d00c03400c0c2e0000156040702d11941d5a111141070345020000e01c4001152020342550103055a03640b2030300c400c441032200d94011000000c00400e80c0070b00c2400e0340c0c110000c00140398401c941a0209550b148034056001c03000e00700810a88041450b641d449200f0740d111184180e14101d4100641c2021000581e440c040c3c404c001c43d6110781c0d92100c980c461440400749050380408000c5203c20740031400c00c95804640010360b2910f171150b283e100e0001004c41184560030408020139192140d10104004030b04a44250000c0200c403800e03104100407411a500904540c604250849000030324407034259055840c100c401d40905111156000c0c50190908401a0301902d0756406510405d014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 855379577 1250 855378327 855378343
    0x18060a0203010e0103030c060f06121401090302120a11101d0606010e010c0c09090605090717030a0c0318060e27070e13020a050a11010b1e0a03060e0607180602030306041503050a05 79
    0x2d0342d94036080480e003035030cc41c3c00c0f15507100024001d07800200c8103000e649080c42c014100b06a0034100384082c1c6510344240c92a0043c031550241c106541e503110607111140c441200410714131f00c24024101c030301d0b185000801c0401020341c56814841d000c0c0400c410081c0140003007001c5c0c138120204002d0b0080328141784018280540e402d440034043d000300464040708038141c2030b00c0c1d100700d40015480d10511140481e6142240482079080002c0405039620310092040e8580090180d0b41e0750b14040b4140f082000714010ac1d07800040761100c1d00e2454016840d8450085c42e80c0451507041098807680010081030030041c07106041a08544000741c0046490303008030207806036841d103903a285181c00c0424912400c071918a2102540320075004000080798203001d40010010300050042c900e09a030300d07600d520130b441911150300c01581200c0b00300301c4450b510541d05c2c14947da0744030080c00894980200079443e403101520041c0220340320a8150f60705030400a1910046500c20b08440c861011800c21980352040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 855380827 1250 855379577 855379583
    0xb011e03020f0319051b0702090a090b13050607051606051f060c1106180f0102011506030518030a05030109050a09240e120d02030405100518060a0203010e0103030c060f0612 76
    0x341174089000f206100c0d0090900d40002d0024a242c288a078007006010b030001804000c42c1500c91007810001020980c645005811030218055071168030700d4528202000242400c0822a090000448102c03c410140c00c43c59001040040c0a03100c41180e20010350500c400d000400c1a420310001d5034984c003880780072100e030007402030030b00c50010710b0b0400200c0c0c420840d4918440d144102031403a40c5ca05031349600c0d1950014000083d03400d00031082c000c0144156801040401e80d02c808000449543c2c2c8810303404102540061441c00210240140c40303400180950303910b040c3d03100c0010740310790055804070f50030903000640698001e000c4c040c00d00d020b96a1003045081d01e0305001d54140701117000107100886c03109403441641802025403c03c402900000d00a071510b00c146202030009000911566005501c02e011a51034540b00c0d01c83c049c0b400c3d02c098003204160b48100f00400c01451140130300d90640b5414a0070320f251100d241021009041c011102ca40c080d45800307000144030116405070640588 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 855382077 1250 855380827 855380831
    0x90307110a030309061d120c0108010b090d0308040c0b030a0b01201b06130602010204031a060a052106070809010b060405031b120714040501090b011e03020f0319 71
    0x51040c20300454162910006021444c1a401440f909004040803140008481c860f00490600140001d807941d000e407242d10f02c0307500139a50902c21941c3c8590107902400c22407520345c0c40d05400c1c501040052010380409002c101111000c10200052003000b50014101c0b01006912418140301d400c00030700c8504a00703070114104d0440c2c40001d408030144070012090300701c0641820080000c000843c19035a42490380d11000c104809408bc00301e2810f604003901c0d0f158001030301c584c21881e00c1208030b1034401840705120200e200f003100503600d00450506542c41610202d10403440380c0795a50903030b8018040f81116000c0d1900b0408901d130320505152180070407030003e00c1900e0820061218620540c0140c80d0103030010702d0051207100d10031201440002d8043c0200b50700094509665061a8a5400c00500040100d0240905180500238a405404240f0040100c01c181d0b1002914903c01c0180e002040e8041134441c0c0071050180c0e0580e91450800e005440d0ba92a080e110100302512000401c0030084c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 855383327 1250 855382077 855382103
    0x403060e1b010c0b192316110303041101051209060906010911030112052107110f01020a0209070306081b030f01020c060705090d0818040c0323061206090307 69
    0x142c4540d0f00d14201e5a040024a000c1d5201c42d9241d0840a10b40031001c008a5201e403c84c0d81c9a0b410b00c10154603a4600000010440c2002c10003944075210f15040d52040188131702d400c06204002004880d08a9402005030781e9040e2407000503113240c080c44609021110440041010791103011035928410079540c420344442d41c0c0c0b0703100400d04507403c22013280c1c4021020300040c0020031040502200c59805042207425400c3d44440d842000c000400e030300140c110010075000100b100030400032080f00c4003203c01506000710070b070000b90b59140d608806071060b101e400c0030441ca24025402800070b8010f50090b03c11444541800c00069412000528082d00ca14a00c0b10201503041c0300341c60b4806d24013006030002c1d4551500896031500b140c841a9846644000b0305800281c415000b061280159020318072091180d49c01c00c0100d03450701c3c0d5003100741410700300ea1603880660700358075404113002940d030f0340c0e119254a800710300c007000c80098801d0b4500c03a9406120b40c45c40000040c10300702e403144400c98561 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 855384577 1250 855383327 855383329
    0x60406030233132c0118270602130503070b180321030a0626010e070806010b1b0a0f0506100e0403050a18031506120c0e0c0403060e1b 59
    0x900c202c10504401100711501402442015004e600c036202e21000c4c01d52215140c0b4110a00601c8281d00044208000d03091082d103816181c0901016030401841c42044030304000300b10380d40c283c51810000c00c81c2d070303000529107200c80c19040c8039005840e014003290040341d00c8100203d1181d015a8142d01c5000030840980c14628002801c02e8021b00080c0030003004038000e160340c2e0039541000e0811030055840e010b011580880d6000302c886503107850000700e01881942030042c2e0071200003502c80078083d04201c0061001e00e600092082c1100c03040c0d07030b4080e40d0340c490808101e00c1c0051007818000c2805502440d0f0f003030141540310120030500034010b41e41a912a500b5820488446100d80050a81d20030f00160210f070040c40a001c1c01d008600703080800007030403416081b440f40b0b99002100d24003e2a941c10540401e2413003010050513100c0b40c482840180e580342c0f0381f0685001c0c410350440000b03030800200e0303605010013940d005651000b010300c0503c0351914941d8030b4048000340c0111031100f00c0c00007130301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 855385827 1250 855384577 855384679
    0xf110a0506071704020303160f050a06060f091505121e070e090303040f17300a02040b03010b070c050613081006180507031e02040e010602030f040e0604060302 70
    0x42e9178020015450f2441889064500a182003020790f078100d524140100070410502840003042d04c503007000501c00d42089aa40c02c81c40080d040741c0b02d418600f1100e16682c0d400c01c03030000c003504d50803980c0c41c2c0f166101ca41700a00d03190000c00c0100800195548900f0004d000041003070581f03500d11900b1005668039a40540e407030000303d40103424807501c4c2030b0190109400201108601a40e602e41d42d2034840d0850504000c281282a04c480d90207403000c176081c1c40d4464816160704040d02c801c0640c5024a48918005140018055a001700c80d000901c2c00400404418940090201600c016120514034044884042072889004203c0c010040c0f803100407034462141a0940d07028000901c2d24852103d0354000800f0000c00c540b0a141daa60000e00c0180781c002d0042011106c501005690740c0c2c00c0021245031030780180d01400c01e642c402c0c0034240d000000340044e64140c1c0c25452a82503240d840200042c090101032348007942080c8c218503501006171034000c803041100641c000009403040a1411001c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 855387077 1250 855385827 855385831
    0x4090c0f050a030902011b050d11010c0207140402130f0612110f0922020a18060206011e050a0f152c030a02120309120705100f110a05060717 62
    0x40010790070808540c1440c003d0380304e64010740c01894407944030500111009100c440d00b0348251101c0e808044103007107182d8054080d081104425000b070258480b88a03020f540e0f41c03868014628103100000001c031141c4c5542e030540f91000c00c00c2c03000440d00c0d0760f9a0020003070f541c03190140390001003440b40340b00c068102034050b85141c6880d0110141c5410481c4454a0312034000900079035008400200c40302c640f00c0042d041c0f0409414074000140c0e10701180a01600040306d000308a46616920b0710104046500490900d044541c0c6400040100701d12540c0c01400d03400c0c80d0030040d48040c0c180804542103a1070b22248049c0c1e00c02e021000e90300c0348410001e0300d4500d1040e2000c03152a00941c0103c22041d600c41c0704000b002c4003d011200d10010660008182d508a82c0d9484615400454071502600d0041d1002c41c0d08820100607011190401000c1031014414221200030301142045450030702e88681500e15400210100f622011a9140f40042d1121800d5600d1000070710b504104410050040c01594 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 855388327 1250 855387077 855387107
    0x22502030d0503010f1202190609171c050f0c070303022d0c060d06030501020f0d050708090309240a020a14030c1b060906040e0a051518041704030804090c 68
    0x29294514200380c1b210391a400510032070f0000140320504241e41044003642000e46156184c2c4a8090f0410240c804e8075140d00509000c3e03940400190155400c0545410002084074a40680d403580f030364540c000140b00e40f80201001d4031a613000042850b0b4085000211058030b041040c4509201d0600c946001448482042c043c0c0c00a1051610a240c141c008061415100c0d002150869490f2100d9003241c01c0041c8156284100080329402c00cbe034076101c0c09600c0040c40c00c00e6059410848a210b075240107007421503001e02c2d001840c0c0c42c11107030034041002001c4541e25041e5522200108000d45522112400f250284a03400014080c0a000303c02d079143c480340e8800510600c80c2c5000c0701c1403040211015036403c841c00308001040e5448090040c40581510742440700f01781060300c994011100c0c010302111421009510303a440079520050000c052800900c08220540c485062405080800c1c0c11088482c080c00140041000365140c041d0007241c005182c1001603000045003a1840a407104c462 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 855389577 1250 855388327 855388349
    0x3030c020115150804051f0203060a170a0b040f2307050a080c04051801050c0414030109080304020d15020d0c08060a06140a210204030501152601022502030d050301 72
    0x40250b8403800704e40341e1140c010800c075143c1c07044881c054100c200b003030080610516000401c0161506003510202c0042c14510b8029050441c3d1070071168079028211801410000a80080780a100b100d03914450f041c0d801c180c0b00c4e8480c00c050a110070080040c0c5642d6500303030003280400520392808020502c00c850000014126052208080100404000700721100b40b443d03203e1484000a8240b0415118906001103155900e08140d41e00310442c0b02011842c0c07080e03041a00304800603214405598016034140c803d1031030310105107854050401c041c0304040000d403002c1000c061242e0301e504a0a58100c031910340d071895442d4401840b1058000c0c0c01120041020110b1940c05003503044001c01c4000c0491414140d058040d40c0300c196080818440d007440241c0208003407040c0079003031080c42e00303613201908070b645600c2c644110820003821b0b10011910002040b4500a03440c2020b4048418a100c04200c1041c005c0080c14180c0d516900c075101a400b900c940c0707003020034050003a4102d90503500710007d9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 855390827 1250 855389577 855389609
    0x21c03080a02071e0503090321040b0f09040c03050105040f0b06300f0709120309060503090a0f05030c070510082802070308061903030512060f0a0303030c020115 71
    0x740406980109411513000e84441d5040402003a250031840909200f507003e140c0e25481002050b2802082c4801a40201041075004104c44000c100300c034201d40a00d80d4241c0c840407140c030150800c1c05558400b030b4000b400c00101c041050740c95448107058600854003013003a8000c01300300e0800c40707034030190f4240c00070300c1040070681c10755511010b0341d030140e207a20400d80e4003a02620031a410000542e500502850328400f440000754021515601501c1144450b0380020343c9924001d200464602c14041400400001705c0d032140000e00c1b40000079038000403400040c0b50075251407580d03a4010a00b00707801c1d00840c02c0200e5503141c0319600000c00d80c4541d03260407590725106443d485c18503580c0c004941c449514164000c4081860010b000c03d14000e4450f184649000b605024605000d2120082e40d0040c1c400c0c2840001e800c2000e039a10440c945040d50000d43d100c0300032503003400d82c046c5000d9002c4081000002050b500d900442c100030043e50080c0914441140f5804411105004403040303d004858 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 855392077 1250 855390827 855390841
    0x100320031b030304050607080307170609071206090903020c0a05041815270c080609070902090a090603150605040923120406180f031a070519030207021c0308 69
    0x1c8000208070024140c1c3d240039540c4c40080c84c0d80d4032100c8121690b02c1c0100030041c50a81082c808803008108624107003140c40c04000042214000a19072001d000003099000003001c023550054002d484d032a80104100d10141c01d0203903031071055070f2165100e40ca01090204460516004221104200c8042034260440aa8a023015110424a6504401ea90b1018580c0001f8400364590384524a91401441d42d04103051246080030305402c10003041d44a0002c0c0510080000f9007401140c250000051300c40f100c800c006910f103800c40d4045070001c1e003004004424006110004201280707071000411250395603605102c1030340c9503548041d0250120801c040c0108d803080710307404404518982940e1780c0ca08240d81d0a42e17560081e03003200000a11456803400340c0b45403000b9240240043c401e1602c5e18070310710b03540d031030480041820860510300c01902050b9070b5400b450a590344958a0900284282600c1c40001d000b0b40103040d0903407050f000d00032803052418554408803000f40d01582e401c001030342c9401c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 855393327 1250 855392077 855392113
    0x90b0108160203160305030610080c1603030b130203070801060e0d02150d090516080a0503030612070305030403212c0a03060e010615021506010f050f0310032003 71
    0x8599402d50004000f00203c60f06680c40030010b5078441e899654481c00d00e6810310900c41c5459102d2028420780c0401e0100b00305144003074842c031261940024940030340f135141c100e000e0a0200309164010440450780708050704103401443c818801a510080140e9031448100d0300d02c00c400c40402e42100880c47c1c0000903081160b07240702c00791050303840326141c0110080b00700c1c11114400c0003a0350541019a008880d601c02a0300d0034024512040205002c0541d912210380380d210180003644184031302c0d98480f1950074207100003001503802c041aa5240d940e01e007081d0138880384c10031340019000d01c00749500c90003178018690641c41189041c2c4030821b0801320114207083e20000345a26a0103140c5407400400104070303014071000d00d00c034680040f581618042c2044c112841404051040d5001980402d528044681c101b680c00102464200b0380300707400c050283d40c035205d0312100040c0641d0010811003840355001c00b540849201e0005298205080402640711401c507500c00c540c507410009420302625040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 855394577 1250 855393327 855393361
    0x1c08040311030703030e01050a020702060d090606031410051003120311040f060e040b09010e040605150a0314070609180e010e07080d1d0a15030e120403020901090b0108 74
    0x1908001d2100d240007428140b550304900d8080f0002500c8000b40706020b5401c0c05035036080300030200c0950a03c2c0345540001c00c030740100c002091080d40e48540c0f500611250307410100003950082488000401150800ca03140e100940c404c1840d5400c0c0400700f011001000c0c1801c003265017060303040700c10111035a812005441a440d14901d142ca0520000c00e21808822500d4010a4291940d1000006403020703c82079a002c13081040c461910100108001c50a414a2661040d80104002001d41d1411141c01c249400340b90304940150905070040b003004010710091a084a40d01c1c100e0302419603960048403210010300507802800070807044004142c0c05604a100400503000020503864500760b000d92038004954407803c66a0f00c40b81d04211820340000318078400000c07418182c12402410390118008540a10500b140103002900c1040e611b8402d42c06a20003401060540f0001c4005448040c0b40d90882d020a03131080501d81e00020b10043e052051526898040e1240304540d03987c100081034060710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 855395683 1106 855394577 855394583
    0x1710030f020919090b0601170606091002030903010e0115140d080a1b03120e0105090a0b10090606050403031724040f0204030b0411031c0804 62
    0x410304084000d074050314800d6081c0c64085440411466040c0102041c03440e201420040140a003045030140c0800d9840741c00e110b41784981c4a4500c603003502c20b298400c81c2040121014100540c1c0e602101c3e811740166410a203040300807070b003903610700008100c240e5511300d0703e14040c0074412042e801a101c1b01100b89a800d01c182e001c40e104044980015000d0301011502440e0a4410b5420601da03141c00c007182440000c05281c050f00400700b030f02820480501380b0510140b4034605200d521f00c203004450090200c103299445032040b8142c080d020314514101004085031001c12402140002c050554403103035907a2a40c03c0042640d0412103404c0600e000f4282031001000828070000d454242c41260b20310075901000010b0001c0c0011021070300303054000714002007406001a02188124003400c003100c2d03e0503004e0101503c1d078004000364038110080c1c2c120003101d035205141c1c09510501c = true := by decide +kernel

theorem cover : BRFrame.Cov 855215827 855395683 := by
  have h0 := BRFrame.cov_init 855215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 855215827 ≤ n) (h2 : n < 855395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
