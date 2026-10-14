-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2589
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:09:19.676662+00:00
-- url     : https://prove2.me/submissions/d5a6a8ba-c412-49dd-8b3f-6d2e73f50dba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 465467625 ≤ n < 465647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 465468875 1250 465467625 465467627
    0x6060409020d080313020103150506120a0b03030706060603050609012402010b1009030b010e0f0a200415080105330903060103030903140307030f08060411220b09011e 73
    0x1145158a0f440040c043c0c4030315200100480401040c0000d901003400d0500c42103040c58281004406e50b0002060320381880b52030103c4000c1184001d0485110035034441200c55156010000341990520406020031143e042660040c283c61015128a00078111200140040c1122103024a4206905d0541e5884000d160300b04038054414200515001592442e11101040d4400323424010350303019084441160341d80d10130342500001d0480704201100030003c04034100f05201e400242040035000f180e0700b507a800c4044400706070343c865801103e0064200c030480d0750164001c0c00d410300501c000c4074400c00491000d4070001780d540b0114615024410203202000101c0005403e0711020107010702240d04940c3c46c0c1c64060110501804260350611086400e0b01c24441d00000b1104013680c95a924209021840810f0781ca180f006800307698000d8643e00d0150350303c68840c0c054203c0181d010325101200d00e203400901c000964540001c145480200301d01142a608080c042040403200496114406001d40c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 465470125 1250 465468875 465468889
    0xe0706082e120b0f1e0411062a0604020102030913061d040b0f060f090411090703021b070803090108100909080d0b0319080903121b1e0606040902 64
    0x41c01400301105000c0100d80411035140403421140310b125001c51545a21542107903010f0200c510505020032204080c0010030255022904140303c1c5103141c0d920044600021582c0c0c200110030a14045500b2150842e24011a04149400c003d44050700680c1040c0d00001d4803481002007060158103c9100c09529000582c4804000d001044503170000541441002e06004000d441c29505400d500c4040380c0c0c0c4a4000700e4443c040c46d4010704101030030501d00140b00418038002c00c02d83d40e41c0c030348482c040141e0312503030501403080c042e40d900180d0350b80b9150f10610a07084100d1700c04805030b11801c03050000c0000001119444642402c18080d190358921204047d1403298000e590342604002c00c03031041000b000c010b44040e01c0032480c24464201d8000c20b25554140400318811042415403161000c01d001e003004064004014007543c0a0550500c0110b13001d9101d003d084040701200030122424010600840080000d852030200716410482200340e83c2e0b01010705502d124543c1c2d2101d1004640da610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 465471375 1250 465470125 465470191
    0x11040c081f05210f03040b0717040e0a1401140105041806080d0e0405070e090f0402010e060a020606090108070312300203070914060f09040923010e070608 68
    0x70a000181e50f07144892402c3d0903c1c01510314030520035166039940e6080d0110039101a5903860f2001410036819413a00c107030400d41e08a162074100010403021036501301ca915101d10a40d040e000100d0216580780441181c20f105a104800000c0302203402c070450f82c1e0000455007216600d1100810f29906130481c60000d111030351185000c0d02c6403082c1000c405400480d9103040c0f02c000c550800c040d680741001560440d82c61500076a004680100003805a83c0007440150040d00614241003076840d40b40100306a40d006640400150303114404200080c41d02250b007074050b0900d0400303445614510781d80c0451000c0203200400c04e0085042c80c0b0505a6540c9124040400b007036800c0c00c60101192040303500a501c1500d00500090003450003180101c440314890307504800140109160081640046043d50002c0070441d030f00c41e8a550f080d50205518256618052100220001083c1c2103509101d0031103002c40254000c1d40c000160030404203410007011940300354000b681056004d40c0c04a141e900b00005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 465472625 1250 465471375 465471379
    0xe010c080325021018020d06020c0c15070204050c07030504030321020f0c190b13060b040501030b09060a0b1804060e0d050307021908040504090f1e11040c081f05 71
    0x10b420800400c81c2d0024100001051000c0200302820310b503103501ca06024684000b075000898a052900010240d038020301d8020059010340f58040e20f807038009540d1040d001050310711142c0114040040d49414451280c01070100e0191501d00511907a01411600587c403002c0d081c000e01850000c08007014070b0340e1103044d000c28001195200101e801d8141190400320b034540a41c03049019440e02203054000e10318000f5001031608100d56180070078140c0d0016003101c121020f41c0c0702c03078a40c9000e0310f4038040c06000c0c42c030890b880d400c03e01d420200c0c5031401600070800f84003641440030b904031948500e24003100f81030340c2c2c007007a1a251b5500c0c1041000380008521254030391061960841600b98440e011f103004881d039501f52054801b00301070031000b03d40003a2002c0c090041c2000100014a09540581c980d94441c220590703400d60f0b507131a080d030401d40c10b00f40503140032129800001004807404103000c05d0740c004ca804220340240303900014000c0c4d10003030030782103280142c8690b6518201800c006100030400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 465473875 1250 465472625 465472681
    0x2a0607050114041a042102070506130306050615070807020607050a0f0309060c050615040605061c150b03061e0d15150b0f0f040e01120507060e010c0803 67
    0xc910441844603421282640c403003965600c0208601001d11480c1c0c095508098410300001b204580074031181c48200c035080540c032402031b000a580c2c5408015020048070811744086a45c80d505014043c1d40005245030700c100031003498140000000010344010725001411340d9246d00252003c10554401c0100103022441070715150701c20440c1c182c03181088544640d07140784201c0c0ea210001e175004200708030010301c29000040069003500d01f0801803460740e0002800418a580d80301e000c90840d134000841000350300ca4410360f10411081074002d0074000010964000340080c50040c06070031502015042c90b1040d40c54010050415041ca46868000103005042c00c58684680c0f0b482c050303404007040d040c0c1c0780310b0801d035002242440500302e00003124101030505141c419a00d00c5040c0340e07401612104a00ea030f081c00013062201008034000d01818030012800c4032801181401403404082d98880030410841440f030900d56644180c9814142d40c0c405070450f00c9480b80d2511000c0c1c8029030f030402c000103035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 465475125 1250 465473875 465473891
    0x30c05070b0f040221070621091b050117070f440105010c03050c0102190305010311090402030c120f030a0216060804050616030f05150a06022a06070501 67
    0x196440610700a900c21604204605a00d40345c0c4d00c1d42030f54503004c0320516000020208651401180c010038003440780d01c3c801c88040c80a01c000700840d0b0070000b040e544030381c05d0a80b0340980d06526011030050f24003400c08401002441500440b8441c000303140000f0044c48041841c84107000b44020b0303038051210000291b030300c000c03030700311513030514040e050190000214101c01c58113a610110540c1a03400c107075180c4015410544040c1c486030b001102c640515982040504d0b00d1a084000390a0404c03d541e502003855451070603c035101081c0ca1030400e00c282101c01c1400b0040ea030014200080c00b6045e01c100000c00c4405000600389480286060100e02000504010095000c100041180c600114060f401c030745482041b9002502140c0c020b0a550090012540c0812082e5030342064010307d240106460101d00340781000e88400ba00c80c00d1460395007002240c0d15140540e141d00241043d88001c0c010a04501d03c41d064130984440e03410200d0f40c00718071400007511120101c800d140c0c2c001c030082c0001d103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 465476375 1250 465475125 465475141
    0xc03060e0f010f1b110a2d05011a031c11030d020d0605041416050f28110c0a120602091918020a0f0332041e080a030c05070b 55
    0x107101302e0804400b1848072550400c2c1d0003011004101c070128002054111030130303a074240000440d14602d04034000c4c00f46e403011641040f2600c48000520460020606d580140c000e460310038120103000c0c0c0f01e0340006024400e0b00000a5108540c04103d00e040e65001408540c96803c620520110241c00380c000641d4060403003440e00038104503a02a1020083c8070011200c5a06410301911243c0d8083d003250010000c8603c0303940030b000c1c42922502414607100584040301c0301c188070390103039601010703000c403055006030342202c2d5400d41401808090048000c06500007003940b10b240c01001203090124012f0011300c030311a03044e1807591202421522181000c0f043c0d801018030035115180f035513a04c0d0103002c10309021034000d9136011009a116100c1c07401c00c0c1c50301a0054401d464444805004121115114108240c600d440e4408000c2c1009420705250414285252110720320b4222742404081c4640020761260480720000510701e80024003000c58441103030280b103210030161000a582c011b01c0300712 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 465477625 1250 465476375 465476381
    0xe012102071a070302040e040f2108090c0a1508040503041518090b0f0d26070201091221111608190b18030702280b070c03060e0f010f 59
    0x1c0b02c80200c0240907030703880000720182e00c40e030300500c80c50300c1c00c41c0302080010302034280558850b8450000d51001c0a0000e8103882c03900c590503040c40000380440c0912a40d90400c0c0603500c3c6d100015108090111b08090070b07549250028a928810080c640303002030140a4140140d13805080c14030203140001125007401454407101c4039039418011414000018081114480e02410150192924080c0001c0004110219445c42001d9912218901d00800450361681d1450144440002e005807504003a0000408103401d0ba0001d040001844440c03c01140c81000303144904100384401d140403c41d21841141c82e4181d180030140e061041801300307443d0b00034a1000c0c03020b460200b41140c0001090701c0241c42030703403074050025105d43ca255021401c400103d1480681c40e90120342120b1034141d465012070441d40d50048880b503042505c0c4444590b030440f500e4090000d00d4a8070840e81400d0003902c5500404072240f2000b0103480c0c2e200f58044021605019807081503101b000200a0305052503400006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 465478875 1250 465477625 465477653
    0x1c0f180309090e0d08070e10050d230109051015120c0302090f010e01030e03030c0909091c0f0903080a02071a07110d020409020d14070b0a0e01210207 66
    0x419441c200104804034180b09000f14146244020203615601c14020703101030101915540812a49240c182100d071102040b842c1c016800d50341c0d0f140e6582e001840001200c1003140c49120300007200030350354920829030802c50f054502092000030369465000c1d034034500e00c0700b0342c5c010409542400c1e44007178030b540c025584011124070010300780940000e541d0100c00320301c40c11540f2076000c0c941926145c079951141c1e80340290140181000980c24484142040c615001214005080c03070001130b071000c142c185664966000505000104140c20490030b10340a50303152000e0310810000280c00b114102480344900e07100854118040070b41e03031141030000a40b07070303041400785404240307500c140301d034a030b54414007220a9a0781000081c941202224204007480c0402a4141d82c06502c4203543e80150b40c0300c0c4a038402d02c600c1021051400301d01008031720b081061640c04030640c0b030414444203080d00d0f00888003820909091820040250b004181101d00308070b1036945001340c2e84040b407240b04000f155528644 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 465480125 1250 465478875 465478877
    0x5120702070503060a090b1b0c010f06090c02010e0a0b06150d05091b030c0d15180506010f14040905011413020901050d0f03050a0c060f0b13111c0f1803 67
    0x1307850340c0d60140d4001600c03251140100000d000000142c0200b800e00c0300440510b4100010b2498065a00c1038103096948005042c0000c45e41c035001004070607698440e138040650140003d0158010001a281d01c941e080c4001601d601c858000090095442c444035040b12003601d00285e855600f1280150300030003046540050b90311507890003000070501c0e400307842c4080c07500030b00420a411124080c00003000c5001c00490b60070250311060070354441e660090208143d407184032541d1001460070000d18005042e0701024000f00743c03100034842110402002a0803100980300800c0300c44141c5466070040043c09e8038852000e00c034100340015407078200850250940211400c02407070f41c031102041000100c01000034500b440b1207440c00006030245018080b00640303410907070b090940036254482a10f2460744201c2c003065803140000b51900d41003070500380741c51800700200311142712008c0d441d2051141c0241e5503140e0002c4404009001403541290300900c2d509203003070008400340c0540d0400b00540b01e9040b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 465481375 1250 465480125 465480133
    0x30d02030a0204090e1c0507050c090103120f08220f0210080109150b09090709030803040f0b07021b040506060708120f092a010905040507080106020705060403030507110105120702070503 82
    0xc541036030005151000040d04d0085549003509246c0035120b80d8002001202e0b01e00072881049031580e00d90003018000c6008090110085003541001808000032041c850240b0050b4400e00c1302040d401e41d40980d00071000040501c0100d801d08000c800501801d84c02035209003030f41c1652100c0c41d40941035604035047e000e010312800842c00c0070074020102c5070081c40c0101d11b0a000c1841c132032600440380e5403c03249904249000549a0303c0d01ca07829030044400342da141c044040120108580007092072382c004035600c041c0c012030311015418400100540032281c861602d40000c40d4083c0d40d0001211a01e540c091741300c9070b40e5503414000c6140c40e4400c030f808640e036443e003400040803070070089000001501c0c07400d40f0341005d40203108082102e2a5603403601c0c5c10800c0c0024086100d44135841307680e01441c8140c07140380d00c80d03240c0701001f4901070303480d08645d0160a050004000098101e019545265482643e41c2480000b03c80122110300403140e22502038000001445171258010940700185c81080d0305407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 465482625 1250 465481375 465481391
    0x50705030a0f0e0f010c0b0a0207050d020c030c1c020d0c09060f0e0a0504080f0706020f03090318010f020a110301090f0c151409010302030916060215100e060111030d02030a020409 79
    0x1900e64102013544c0441e0060f40f458000520400d48035501c17100000b00182404403c4e02d60500c9d20003562800c1000d03038000034034003400785070410891150020440d604d026541c0208580481200c0200e8000e008580c0e1581c2101000034410803231010f040440801c000c03065480e00c031001080081d11480c01c410700d81d00d01242c810301b583d000c2e1900c5140c01c240c0c454a0005410041129584140c50030745800382d09020f0340103005030000085010b4000e040046403907140025004019800c47d42d640c0341800070b030b054031503c05900410761807401d80e040b1402d000c04014400200c1d014195a01c8000c100c41820016941003100051100381600c581031203007400350a5829040e5100910448103140c001400e200e031500b10361003034000f941e0040214090701c4070803d004100d90303049240f40d0080c002607003003840c81081d00c00310612000e0b8400a0b00c098284918074065a00303000e11000741c00c1d1b90411415020003611100200110740c03406801500841d542d10f031501080c00250058040c4001480c105004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 465483875 1250 465482625 465482629
    0xf090c070c0b030c03041b080102070c2120030c0901170607020102040f090c051314100305130b0c0403051c0e120c010e041d0d08060109150c03050705030a0f0e 70
    0x90f2445907050302462451611241c5421a2000c0c1c00010390f1200900d240c00803803841400e00103002640d00c01c404202d80309003003a82e880c844078002c0c1110303182c525408404101003521001001104c0300285413015401807928040703414111302d021a650000720748400010588030100c9020046140d100c01d580c01500c1c4d04030224240d10603842203890004c1210800d000044207540941258ac2d01400c0151902c400003c003440010403960000034034140e01c11041c0e0440c1044042000c20307107010b14041216103400c1010111f64035681102400b2042c0890000b8075289094040310f02a40d0044216440351a0448450864954518a2000080520304000550304048140640c02c9560f18040c100080f220001101c03406121080c450703100741c94500c0d09103001c11100e850f2003007050080c058000c15500803401303010a580a032000f0704006013140c04028914102d021020750b21350a1400b54984112410708484501a1007000341c00c40c000009c409140a4000056550f600c4c055250b0300611110501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 465485125 1250 465483875 465483877
    0x2090301051302042007030518041d06070906050301030807060e0625090308070b060a090908041412060f0a3b070b0a03090804080105040b0118060f0302040b0f090c070c0b 75
    0x21501c20800b81c207003c11030000e130080d80278082034000700da00080f03c0b01c1184001030954012090103140120301404980e1a03450520040e030f40000c29051094203545040d0000b01300c0c0c401440013170124140460070b4400c02c0790035044003c0b29910703401101c0c40d0381094031880400410385140140940103500f10540e103503000340d02040c100c1e0f80000c080780c1089501d4a500d040b0400003032055500820741c0d4000725030311845201d40c500481c02004c41a4681d820420800d423410300e60340342c581c400c3c0c101c88403c50751024000303022035200e40e11140c1c80e2015110304072048003074503c42070b00480f08104001100300d280c984681101075040c0710340d02d6440f0100000c840d036454030010700690403803610411840305a2130194022018051164217130358230303160362080030302e0848406603401c84002520400411201c5500031603880d0b0295881ca082103c1d904e81581040c42c00030f18031000780030f241c4401c64006070b640c940086044405000e82111001c0c43c00300b09095565006031b0046692800905000c643c0c1c82c5100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 465486375 1250 465485125 465485171
    0x90501062d0e011412010e0d031508010b060913180803040b0f0906130302160b03010510050903100f0b04060f08190b150321070c050d020f06030a0209030105130204 72
    0x12044204d08440090050044800c04004a1136484011000d1240c0b000c118101e00d41510f51740000742030f901c0750894015503000c0d07031220301c450b030400300064203d9480c50125140704004485003680c0c038210351643d401038420f01c0c00d6102c0e8500040c000344140000c50340190b11a42c403035501c1100d281c0d200004041103007000e031105409a0700120008035040701410011540318041c4c0121880c2c288000ca500d4043c80c010307040901660400300040096040814603840300d01103504003d4100540200440c0d92000484180142581c464550703014110a5030f20000c00c00f030340078005010040e02c40710b010070084014070449196210360f00c1d04003454030b20400c1c064125075000c0e8603100345803128612000092560510355506010b0340d060b04d06000003840f081791411a80d0444c89480744e4090074080e2201041754402d40c061a5840f42c1d010041e17a4800c03100c107640318125081900d03a26071143d40d100034015860b40c190150301e000c0501901c030190f000c03050815442113405009034000745003c2440c04401e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 465487625 1250 465486375 465486389
    0xa02040e01060804110f121002120106050c1b060405040c0f0219021809160f0e0f160809030f07150501050d020105190203090d080d060807080a0303090501062d0e01 72
    0x605480c080f501e003001e00b2072000ea000502c940d580c00c410f03902c408d00348240c04e00d07110001d5600095100500100300c46190040449050440c1040c00c600d840c15100c80d149121000880d0000084072243d13650201580d024020141c010080260080d03005441005d400800402504caa8001c003111614000ea0750030f0f00d0343d4041c0850340c01400c0b042c24003060100203011400c0070b0244082c8205030b802c1006200008000f201c6010410701d103010244220a00041d10880028516200f00140480d001345480c821740303028171700808190381d84040f10382107000f1401d41d119401d40c009404030500030840c1c62030700841224842001540d03aa401002103107442070a0081c0440c400748441422040c503c3c1400520342c000707005a9281c449814001228043c00c59411074485001144001d0021681d22416015048100007010400d082c00403441d0340b45008900103041580b40d403281c04c10068203400c80c030010641c0d11122414444024090346060354805481400100c0c45440003480d4040341c40111304076154 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 465488875 1250 465487625 465487643
    0x2704110405040e0a0f080310090b01050301030209100803040b0d0e010b01020c01120608010903031b0c03350c07020319020108071d0307180c020c090c210a02040e01060804 75
    0xd080c007840050400c07200f003000c0c54000c110104001c64003210305da905503440703080d446503245405400f4111400d103a802030902580703410329952003640c0100c2102d0550740c0448080350783d9074850b149000e40700900e812946a41c000071500044225050018001b004d42c40e01c000d228140541104900700c40040003504d00603841400018191b50056010341080821100c02292582d12034041609450078507804900080e610003401c0000d501003030b2841210000d40c6044040c6200540b802003154803500402c800e49268524003540c00311001c64010303209008404044242d00d0041d1002c1581e4108000070707806402044510310300302d102d40d00c003001515816180d044154403280412100e030700030250300b500c220104600c482140da80401503440100780110805d40107001e203800c0070099444407042101035501a0040b07500c0d9070743d160b5165520420707980b803c0740c40b224059500e8015032191410740c4c0b40200c2d40d01c1401480c40180d001002078036500c00304143c6a9a0382c5108903084c92048501400c1541e07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 465490125 1250 465488875 465488879
    0x206070321020f0904060b030f04020105030c130f08070b030c220302040e010605190e04080c0a020d05070801110412060b030c060409050610050f22030827041104 71
    0x1000e102a035448070401c40d101102410506068000c0340d1143c00070760841d107804079401c01c861a0a01405001e403030700e89800b0381541480c200c00343c10394801500c02418843c010002460119007030f0103607000c00c0904060110a140d0b13841641c2d8107007065000c1e1130483c3c020f17a200465040c0c20b00044a0280c4000010f03e40b605d40e8608150380a003903c070002c00d1045c130b6a80303c00400369480d40034000f94030240800000d149403518041007107050548450300b404d580384000401103850038401075036001f40c0101e40e9550382d4104a400e47c0c01c00341d0070380c40258042015050741d03041c02800940f800c1600c084400800c00364035804407440f1240603500c1541481c14a480004000070400c2c0c000e1041e80001070200c5104000c01800a022030300160407680c0344a0b590b60401c0a1841c169050212030505801d101e4070340f0b0095210f6454a1007545406200d4422142d018403010301c04c64403c038025a00b00c0250360310b5109a6620842c942108800c410f030051803100301802e1441e061150940301592203064031f107802c3c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 465491375 1250 465490125 465490127
    0x50c09010f0c0f0c030b0a050603010c14070c080613110616140f010c0c051002090f122109041406090a0f0b030a0309060809010207240207120e030d0c02060703 70
    0x2002a10200d840d400210030b40c3d00051201d40e0340c1c40245d4890b07a100202460542d041c11304480d0000c040502c02c0c0e040a0b1081e00480d080f11007031004041c0306030764603a03607072081c14000d03100d0a02d940500524801e950070441840d540c0f440924485200e51043d416001420741042094028034605450b410000010240054400c1503142a0001c0c82425030700789500421140d800c407070242100c20007003481f8003d04810010b003071198007400101ca540850030540070380c010a10f030580c160030f02e6004046074881c03128402800c000300207110b200c410a2003007400c0380055050541d00b200c15002d002d54103100d00d061180d0442c14125200c2e000c0075000d6103260341c4642040b0040c050405000300c44aa0360b80c02405140c030140045101680261603900200340381c814014400c3d40c0c010209603960b4070601400001401030303580410030f00c0e6512030640014100e81c05142c001e10034a20000d004400c0789150200240d08002d88031040f110843c150303920b00101034016038400d0b021150082d44444200f002800003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 465492625 1250 465491375 465491387
    0x40213080d35090a05010905010b0109121a1b0a0e0a12170a090e040b010501170f0403050904140403030e060112020f06030a0b031204030c06050f0a030e161404050c09010f 75
    0x4140030500320740c3e080c130080d119a42103e00c0a0400d480b10f9448030109081c0e0f58016406000508961903200607844913138a580003c00801300c1070010136150800450030100e440703107001101c0e1078031480e05c2d9a5010fa6003806401c01c4a4203500b00d002d01c001540000702c145080000d4050305401001c20f80c0c024280400c9022203500801501c0240802040081500c4409541132445940320f02c0c10302d101541082d0025044d907826441b140c0851129004111100010003592034006a050521030345468440740050050f103200b20980030001004402c02040c168190000a01c09c004203040e0384c45a600d44020402805040318065001900f56406036003a040050045901400c140307400036540c04d035900003a0070181d07508035090000700042014805e05c80b100223184010041f40c145285040c200c03007414040c500810480c00189552401c4030005481c4c01e010705003c015904841c014203035190500c44007942400000e140c0907a15050000302a0700c003000848081c008141c480400ca6013010208982c4c3e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 465493875 1250 465492625 465492631
    0x11214190f0606080402130606021507090b0309010903110c150c010e03040305060906060901060905040c180f03031e0519120c030912090501050f09040213080d35 71
    0x40c965600c8070403008062841868090640c80d50b68001d9400d00d8010002d88502007210f10181c40d242600812949070009210039845030045140701301d5944500090750304075015807040321000e40000070005081ca040d8491540d0030310a0b1194803100c1481122540c0e40d0f41c82062143d0000644108880c28801070405032070840c148500124038a00c00f28a4641035422503481150306501c03030030920407001414400150302c4030301a070b00441c4540c901500188000290310a0502907903850140f1003d003441003417400840604e0480f400c22817a0307943e00c41c41304035400e40b00540005540c440c85000101c1c24400360304c1701000c541e803800d041015203034103440640c2032b0348200c00500010301814016050035000701d0031049850740b0300050120042c20020800241c2150b000204100135009100d547c0e0840291101035084c03514054a41303004102250092182410010702c02c0701e190400100f4210004105108400581d110100015034500700c1d000701c4010310038005201642103075460b40b041c061400c554 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 465495125 1250 465493875 465493921
    0x20a11120304120b0117010b090c070f050601030c051905131d01050708010e0114030616020f0a06050106140304110904060902060d060303091505030f04030207050a06030b011214 78
    0x110746030b0707604500b292a80030f0080844e480d11054004200081b28490018004440d00c0000c2c001d14100f00c0014014400c014105003000348040b49420134003088122001c10264440304503030540d42c403800c1c64001c0a0607403144078800d13081e40007800c005010130b0102d07400b11040a005580c0d07886c1c0d414031690251441c840812113907941c1d0142c5180b0040d090152a01030038081e103610025504100144480210507082003e820452700d110034107940300064003980c000644024480d801508120407410308040c01c01042d501e11504c112201400070903841181282e40c69224a00640c90b0302c15040c2c0c1c9c0d40011940a08184600340740740e000c508106503601d9000c2e101c2d03400000c080780c40341d001075041d4109115480c091a507404091081540045900c1c01070500108040c1d04010140c80050031031100600c0005220300c507c020a0400d03008120240107050000c1102c4945030319036100400800444204a000070550340801c090041d040c81000e0301e005034500d16004a81e9400b2411188140a8003801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 465496375 1250 465495125 465495127
    0x91b2202070b0f090d170f0903040b12060f0a0f170705060a020a05010b061608070602040504140703150b040303051602040f020a020105061206130f062a020a111203 72
    0x40024014824442c82084000d03e4081e803400d00700506482c0c801880c2035403050140403c9400c0d0424010391020342d120035140f01c1010302e1750300c002c102420350241c1d46c0184000040460032801e60701c1d1003000c2510402c1c0507201c045042900108205845090f41b00d40708460103000401d0021142c000d022403807849140003100d030015900d40c08607241b40e105c1c080307000c01a0092150841040005c1c0a40c1425610488601d400e00d054440307101074018103440c0040c1000b0f0001414800c0042d43d4058074018000108100050004d01c0030040c0080411541c81c00020f20340701c4100e01c0510a0100c0c04241c80001003610b05040c15550141c03840e0348000c0b80c01c02e0800b00c0443c00001a40c0c1d030701517401d82c5d450303641000d83c40d03110105000e425601c0190180d4881d0560400d117001c91030b4001485580204187c2c4401241e00c0c0f141084590061141d00c064501420035442d1900031600b0303113200000841c1e144180200300e080c643c080340c0f07800a000d4001c0500b4028290035025141c808602034450f0800025a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 465497625 1250 465496375 465496387
    0x9070c120309050712060c020c010813050a0f06090b18030d1d1204080111041203050304020123040e010510090303110313031112030c07030204180f0b091b2202 70
    0x50702c0d043c601d520500e1034044440107942045181c7c0201074010200b800203140781054000003901c0d5060040526038040c8941044600b03108080044900b1247c010403072405e00c4000381000d2000c1c0c0820b070002ea950700490b01c0801c081c45036812180c14803080b081c1c082c600b8214509641000b03481d84084e4003201414403400c002146500f4040803a29400000c40309640d00d282c0070040742075a51038188d2520508043c00308009628801300381e1a040d40d07041c03900a8be01e50301c0c0c4c80140d4409141c0500101c01c1150380014903074104500d802401550000f010340e2005a0340c8030f0400c121458400900ba001501031a000c00001340101028619801d180003968140071201c200000c2031241075209031825030b80c1c3c01c4159410305150390040f84001c014000b5624140d6a107000d250354a40074030000b80501e03540c200304004002c0007000c4128030380d8081503c3c1c482c82201c1c1040320b000703241901c0101a81c05121241200c680300d205410301c1164006d40329190f840180c1d0240403800e113488a5501480c0d0b020015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 465498875 1250 465497625 465497633
    0x605220e042a05040506041d0a0c36151508010e0c09130b060c01060519030c03110112060b0a030c031a01140d052401181401090506040602150609070c120309 69
    0x481ea0b6234000c3d0310000d006681d9241803041301100d49500c01c4843c600f01088107804492849200b03801d8940c6040003106000230712822000502e00b110340c4404100e411100400d041c00103000c20ba080d55200d980782d503150390302c80382406902d850646c0c0300c0c0070303006040141043c1800d160960301c00d000c0819400107007950021011480302d52100e0307524102c595645030140304618103094440d01c0c89030b0050102c0c08d040d0541e559801031100d02c2c08080c0607040c042680b10126072003821502c00c7c11014000c14481ca41d03903055840311a80000310400003281c02d00d203001200906c40c1c4030358004805195229417100c5040801034418000440d18644441e03000c1044503045221800703124014005803000b4401184000520850224815002c40c10800c43e000c000002b0300710601d108060b241d45c41c2e020544560b1074801a2040c21080e4066500540b0205001039201e4000c582c61a40070945822283c843e42c2d81e0b803c002841d23800710b503c14003007940c8410100200d1f07032107080c141a18066040004207040700d0b480b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 465500125 1250 465498875 465498911
    0x5190e0306070903150c0203070f061506110105070f0f0311070803090313080105040506061c0204090b151f030506010c05010615030f14010605220e042a0504050604 72
    0x700c64001c155680f02c20420000c80d07038030506032807411318005c1001c40c0310b54030001e460340308002d80502540c10400003401440b80540c040001003c52202103030398681e84220140c2002c008401c42d010365403801001a82e0103005070303041d6149010030750790064800301d182d005400414682050a10181081c80b403403002402090055002d158140010364031014031071200c00840880707801640300360f410b000038000090302c006010b5800c808100d40e100c00510860701c0100c00c510101e100079500508090103002481800c800060060440384809910408442e0034030042aa142140000340c21161802001c0144240d000d80c0d08104145810800c448081d2601401e6034070315000080c0700910036002c2142c442e0540702d500794000c040f000602c280104d51100c1240440144201003e01c20001084a0f2510079490501402c0c96075104034000d0302d0f220100c21903219021a0120707200c2401e0410302c6e4100c80c901c00e0710070b4207461031160540c81c50300308001d100203403001602c0d060704503845510b44900034580700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 465501375 1250 465500125 465500131
    0x32105060904290a0e0d0f05120a1e0507110c031e1f05070206131e080c1501080f070e011a160614060418080310051c140d05190e0306 59
    0x14085645c45860090a04241c00ba060700400d0000800c04048010f802c60165001d500c0299808289680c071720030741c4406460003641c2d10400d550441154000102280d000034080c1a1541d1003a800070b00e84d81a081d6110b00100d18254554031040110782d55200744c2d200204898042401e44000b5000e40405c55007110700e5205401583e6140c0e402c10125079810454268070203c240c4040300400e08940783e200340d6415101c0000e441e07440c25001001400b601800302c803c1000300008650302ea07420394441c40580c040a004161442c020000124010400010f140007500c249c03022524440c2d10b484140c000701c2c031415071080f0184005020340102c83c4142c283c4039071540d006410205601c440c1444688241e20014240c6218516114500580c1c2d6101d88641403002e6001400c15a2522010204440d40301c80e03a02499200741c003946c101da8021407145100740d0041c40740c00c801c1401481c0c0300b98a5154404c0006a01c00200c09204042c540b009a000c4410b0710100c80c18951070240112000c00d060803021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 465502625 1250 465501375 465501391
    0x20a020f2b030e04090213050403090308030a0e10020310150c200102160e06040207030e060712120216240f1b0302070807021203040b030403210506090429 68
    0x70041020506811051049102c40d04907420014041c0e561b0000c2c40354032030303003140c18403d60340d92001408043c09480f820028541011002c0d0326881c002965201400480d4420015409a00c0040c000c1e481c49009880c0103030440c0f00d4614005003014074012303807d11100c2050003005900441000412040b0100c040702c803140400b07001c0b18040ba40006454003800074403544206401200070440c86c2d40312540107802c000700721005607403000d02d410222008090114066400b110020302101000b00050401c401441941c4030340641c1c000e41135841c0201e0050f0764070202e91a0000d2466000034094071036082161072883c1440d0b14103904040300c0b00031a40f884194003030141d07941050144501d005142c0e45052001c5180c194901313040c03983e880007180608d07400207010350108000794180d01800e01c1030700c0240140c4480c02d510703494142401050301004826448070508115625001d10200d0301a442c4104c402800c0b408103601d441d0743d02111005401140440407183e044840b45030312401026a001c2c2c054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 465503875 1250 465502625 465502699
    0xa0209061e090405070c0309062f0a23070e0604020d02070c08070515090405090120090a090c0e010804020303190513090c020d031116150e0c01020a020f 67
    0x2240043c4000c544001d000d40741440301c00c2d5030060000e5401726103c0e05507021403800e400c07a031041031600102008101010014014107416000e120a000911521aa4021600c6d506085410090203203405011a03000109401c40c070420311890202d138141e01d40119000c0c2005282505102d203040898201800131118017803015007c12403060308121a00150000f01d4011482442041c000d84440c0300f07941140303011f143c0f541e0014460b01c10a41c03050f0b902c5d034000d0b0211072003c10305c183d08010703640c806900b851040c080381c1000300d04840e4521418907110407644032201e414100d0001910001d600401c101e9240c0b008001440c0e41c0d8150b1240b00042e5540d5844040e00c542003000101c4201c101034204100700c615002034a541558000303413100d104203060400095800f00c008031a0414410001d12060028040035100704109001c04240c03000030351803500b003001005101940762039852062a590050f4041449040986050440706c204858010001118041490515441901d00c501801c80d1548 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 465505125 1250 465503875 465503887
    0x1205030c01060e060a0329040302030a0810150302072f01021203070e090405070305070609080c09011a09040e0a0605070f0c0f0b0c09040911030705090402090a0209061e 74
    0x1000b40908400750507030b1003000d01103260101c04208014424480900442039164150300190b0704524007806036401500c007500d8900e0301d42406952035003e6180c0c000010703101c40006000c580e40380b9082c801d492400b001c02a0b0b010b22017a046010750080d42c01525031000034141e0381c00c0c074030505a0490311082010f02001d581d100540029081960411440c03448060800822141c0c95100c40e211300108011669020161a913003449440d20406802c010301620460380086420382c0c101c80d202c02207901c0e2500312001117010b44140101e24400b8464040012001c070224156021b418028155400b00608000b5142a40035816458000b84441c107807071807a544e20601600c2a4000d07030111441045007030060350000c0960b102000c03030b03040f0300c0041c00c00251a40071421100c0c00004850301c600700208107200c0b0705c00c5070604c4e076483d1030310301c4030740b4071900c141c1e02d00061a06040b01103c0c07249400030003c011580d20840a50069480b40722007a0f0302200402c0709040c151841013100b0902ca240e910342585030380c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 465506375 1250 465505125 465505147
    0x50903070306150e10030b071106091501050d0b15040b0406140f0901081c09050d03110d030b01050d0b06090307090f110702031c090b0408031206090403021009020109120503 76
    0x440d40342c10515076410304c04200314003400600214012294041c00401e000d039100c031000c0b10020f0a80c0b078088001c3c000d0300305000400340300050f161501d8106030000700c5181d998404100f0008500d51004081d0105140044c00001e50400340c403890241c00b8001249140d80c01000400300e0b140c0c4e4100e400c1840e04c5030200e130fa050400344808087e444007600c40316801c1d4103107a01c4650b2001004a0340013440301909007403c2181c42220390800502000d01044d208042c0e0380703009081c910383d5010741d880511501c7e5862920703901c6800344800c0c0314810307110382d03140803c0c060004014281021010380c11120820246210b030b10100200e6001303207503003000001c41d04c0001da02d0100741c4041040d01c08a811007885608096a40443c00d006400c2e0240308030940001c0c050404d4919074810f03480102814404200000d602c0c9000c402002400300e8030001401d169149420454001c10070b86011300180d01004074070019051640c480034409005052a041c91035550711104106101c00340119040c0d00082581c400403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 465507625 1250 465506375 465506411
    0x6090f080d090b0a03020f0403150e070f06081e0f041703041101030218100c030210090f080c1513050f0d0e0d060e01050c1e04050619050903070306 65
    0xd05005805400416035600303005050700c045000d060341c440c500041c40100c940c06641203688604411a03000d484960740e0130001d122158542c150031816041c84410720000c2c0000c85c006040e5141030b00da00031190700f0424106e41081c402001021405c01c1c60403c40120300400c501c8078071640c80d0742c0d9070081601d0a80b8141c1c001c035a000c608058503a03024010320001030624001e03070464440a28006840d1106e0380240780082e880f1000b901e8200040300c0760b800340c0560100241c00390900035000c41b100d19841c3c01080040b00c0004001400f141400090500060f446d00c00405261126a0881d810302d90341d030070300365404101510065032b05089811114100309080c080c0000d5842d4401c0a0a980144c001015280740c2d04402c4040c4550350b420110740800013a9404022200501170080245182440c4404413075407042001d500e40492000185000b242c00600700e40941e24003504190070071841c003201901c1c05d10304020740707002d01c44144500c0c00030b0384081001c4c20095000312000b00341d11822030024540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 465508875 1250 465507625 465507629
    0xf0504150911010e0105070f2a050901030b070504031b05100201050907090c0207030f0f020f0603070507081e03071805030a021c050106050a08060702070626180706090f 74
    0xd86414201c405001c41c1040c00c44151602082c02e100c4072a010480040304c180c807501c00c0090680c240c070020b907410f206201c000801e2588400c100d441c1c10b10700d1040807144003003017846032603840401d51005000103444901400e8200700b081c20704034102070b100e5031004203500c250300d00d013090310400c2c2000700440c0c541900100103145160000b0009404c104040720303159a054002c002a987d1a4030284500c1c40c8200301000c001e4fd00000a0542c0c0300c0035140582e1881c02020b016803280070081ca0310078892401070b00300c9004403003903101c542c03406909580d00c55041d0460014080c203840040d120350101f04030100114070910742a510300011a9002507000461485030700031600031b900401003100140c54054450340d14245801040e08294440c0c03070001d02401e42500703d03581082c04888001415800015074500410391a001e0b1032240c0e8aa6a04580f00140c84104a480000c5a0354294690070481c0d5002d8000c0f8480b9145900b1440c2c1a011519180e40e95228400141d0710100801c10303c001091030b600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 465510125 1250 465508875 465508913
    0x90a021c050a0f170c072c0f0907050a0902070b010f12020919060f1502060705040e092104081b06270d06021801030e10090212010f0504 60
    0x540403500da15a40d000d0b4500000c0c0001da0503400c0200380704c2c10010302c45070340780107441c400d60303d4000c0680c40d91141402e1145004590001c5c850150800410203107007a0614500c440d0031041c1e0390200a00c6503820b001c0c003075800380d00034190045000c1c1c4a0710301503406007010b0140075948a01500e415048500140c1c04060701c800c24180c14000340700c8200386616260380454038110140c603060381042103460550803200117103207402d40001e54a205101503204503044103501c80c51030b1201160070303a1200001ca4070340000031700410007807050b42d01989000f03422071900400c5511002c060745622140303c2c41c2c4041c1e04100d0401003030820545100300100c6031034460110f0380c000985030120100310140900141848808290a000c0711808200d0516500c0c0080c0240110b20005250800500a50181e800d0840b80005d121143c41c03554028020244044041070007014900c02006050b801081020000c03030b4403c0b01c50903181c0c1400024060840b0148041c0c0d000100b034142454000b0086003a0a901700d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 465511375 1250 465510125 465510169
    0xc0a180302030c060901020c030d0f080901110306060d090c0605250825150f0e0a1a0c0d02040f050108090a030807260a0c0906020c06030c0f12090a02 66
    0x80010b840124101860a03004e0f2141c0e034950303131708500503410040040e205070f0301440750005400301194003030300e03450661390140c0750000c0707645131012000e00342c500d42d984550f102c040400110702d040c00d0003002441d22141e4460f000840000c165913500203200d803940070600140700400d4001407200c0c5080840d8800c4590082441607125540e2148282d0203190520007c0e00c2444bc0d4014004041c01c0c04115040d0b845482c50307406482180a04c0010011074140e07088040ca44002000c40f410b0000344160040c0d0810103410345038030089a03403001c600000f8085515000b00380f0080f8981e010500141010b091101903140d160b0381003000040800f6801410000305e98031801409020941104510742c0008091409070041a1b0117100c2c07125803c0901c4c03148010b036042404001001c1c00641c00003500d40c400740d4a0f0b034851075407544201d0307880107582c46480e4048003c0000c69000900c00009088110340e0f4248507045c1180b80c0f4a0310000e00c0d04950341d00454100720020b00071880d01c88003004900d030f004407100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 465512625 1250 465511375 465511379
    0x60e010905031902190b1908093a03020403021302040e0a11040308030403020a060501050a1503021e07050604030e0103090b070c06091e030809030406022a06030c0a18 73
    0x2551140100300102d840b80720900c0f10020340d00d03099005144054180c4412a07001d07a01e4a03298502d6000f00c0c609010b4034240328107000454441e9a0f094024000c003001040d00400382d03480b429480c80110001c1140c6401c001e0500c0542d896900281850010350720010b032150300e503006000c000c400145200c018248100401c1c094401c0c0c7c2c5010a0704110750a000188917941c501d51921a481a50005082c1c15004410041016400695a4400d40c803440b014881a40d8900500c110203540d40143c15020448411000c030482c440d5020345002c403c07001b42c1c5411950301c40d6039a6441e521420055800303412075400c00060603000000b00d8215002860100203030b160907194050040409440d001c05c0144c074017090800d0000c2c4c0e4001e101c0c1b2030b0304601080b040d400d4076504a03074403065144089000c1549040061410080030050b101260000d801400070b00c0d840480e01404c40d501090464803010303007440109100d4843c203001d9807080b030860b03000300e548810440e0040c1070000a841407849828080d041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 465513875 1250 465512625 465512629
    0x2806170a1b05070309050a0b0306040c0804050c011215031202120403051507020a06051f050102060c030609060d05010f05070e220f09050a0c031101050a170402060705010e07060e010905 81
    0xe0010300700141e14081d0b884072030920b8121581c3c0401d6200c45e900400311030000c1541d90701038000b14083c1408403410420280780035416110030340100e82c064110381001148c10b080354024850851610501f0100162411030348402040c9502c194005455103050b10031000c88054040000f10722980c88903403064101803550386c035980e850b681c120130340c06c1d00c032201804100021b00800c108118154804402e00051070f11115100b03d2500c42200da120101000000244950010405c940a1103554451510316a103030000d20448080241001d034014041d4810000407420030f200d5500c2c9403008847c0803a203801c0c40d090042511508100480c81110740760a0304290040d0019055260160881c001c1110136031042c46c5002481100703806072041c0a080d00c014100040300a65a0503030b84200042d520010008004507100e006d80c120200c045034040382000c00f4083e013903144130790051004000350701e40407081d52039a003901d152400d11180c83d84141b23014841d254200901204c038000c2881d10400321850140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 465515125 1250 465513875 465513911
    0x9060d150b030c1f0315081e0606010e090a230405030904050c0f0d05091614090a021603031802131a03030c030f03040503040b03010608010f050d112806170a 69
    0x540c050034140d0350021b800e024110101a24010300c240010343d40486080200300c9014501c00c0c05c0003d241c01000009683d40d070040d10a13224601018002d4600c4c0d9450180c01c00c01004607031819000c8608a03040401003100e88419684a24401c07009151142c80d42020f002c29140050010311400e201880340003051200070040e2103865904010105250300d1701400d440c145083c0d40741c1d0480c4074110240105040c08910483e810f40d4005480e0803130b441e580d00e0040c03000ca0088901c455225442001e401340405e1090700201c03a0041ca4541c1507000c152694000b40d0301c4e0090b007990318506500d88042c8848003d41801c0c2d8200300c642903020354076202128442d00d4403807280f840b19079100a40400480c0030f10008000f030b42c01900004000b01d549584410000e040c144c024030034000307240c4524502049509159640c11510f40d8021080c5080c65901c1c1c080018030202c05004d43c000f6103403034410010075052511110000e0102d030715074060103094a80c554407940c4004001440441c10700c040100900c034410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 465516375 1250 465515125 465515179
    0xf080408190f1b0e0a091502030105060a055208031f05090403170903160602030604090c090b1023030601021f05010501030c0201140609060d150b030c 66
    0x15486000343c1e60b049480a000320708542220030290b1000342000040009644041d009074040c088074050741801c5840c0b4001d0b80f00c00d0241e41d030889010301141a200340039002810358168240130401c03d0901003032442c5000c0c640480d90103026101d4030981200c21840d00e0ba5810340c05111000300107415601e486503062407102800c40c2498610f000842030300303103e031a017640010b810018805040c1d03080c00d040040c91402403401d501c3c403901200c804100310b80000000c8940015160b0302e0340108000f0340d01d4280007500014281e6030810707103400106000582e410304400241140031710026402c12143d081c881100030032000401484100c401c0f0380180e00084110032502c0f0035444942c0c1d80d90381c814004074244000650005110311180c4201440b440031034001c14180c0d071081ea0200700850340301e24101d003601c00b4200e420909000c110003003001030030b00e5400558433010241000e00c15510581d80c580b4240702c21f040b40540d40707640c1d082c60f100c42c1c42c082c4240c800c5110b003250f0905005501000e0607560310021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 465517625 1250 465516375 465516383
    0x7020318090c040806090a05250303050310090c02070f05060909010e13050d021c0302031611010b12030d0b12031204030306090c020303060307080111091c0f080408190f 74
    0x40c00002c0040d820502281c002d40400c505590315402c00301149695684070150031109402a504889440d004e00700e00c0f01400d0070540c90715a6254a9914180c43c42e900103401c012080e00f042030f011800c4e42c0030f8003e410414a040e801000354070310b00058a0003900c9503800c424422181002620126500c0324020f9054501c441424207540c0c55000c080e090404402100500c1c80c06415400c1340720a0b004622180c1d20828014090521100c030507045081344001c490031a05d8110b1035460a070030921400c00e02c48411492000094030f50b2110300010040200d02030110401c0c3d0000402e0000c52502d4040c3d4484168141c4040710880201d17003080b510b0f0301031403400c04e440780c0201c000107061500c80d800c10801010302d03101c01c0040d411913a000035100e03070045580502030721410400291601052264015001200540b05c2c02c00800c1e90410182004175041c50b04288860324540001c00d500c0c06100902034492013083e99181c0c40c01080d0b0b42000700e00e045054441c00400d51410200d40000901e4011540c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 465518875 1250 465517625 465517639
    0x403021c0e061c051003031e09061d03060108070504181718090a090b060a0e06130e15071806140f071a09011413081c02031e07020318 59
    0x1140e5004003c01084100952180d040005028424441d041414103413030003607840107204c8092016070f010000130b54490a000945012007040b032284240a62041c0c00e081d0a869900110402c0c0001c0ca012002e0b0040c1034150000f00d41003220749414851400a014803411082c0d42076999124100819050300641e41c1d080c40004072002c2c00710a2100345401c0c107070000e18a080380d0074a200040010405000c2c100e40e070040c00400b05503035142480300901190040d4a034801c0703a6a0740814031422128041c8980c4c843c54480c2c40440150300d00740588000d403041d13128410124034005400421425184480c44044940c4007018003145501a60304110b000003600010342d511a458a01019403050210140c1103c44134441c0380740b2407a101503083c1c043c1c0c0404001740044180c0c800d0111449500b620110142c00001c41c80074005052900540360100103403a540032090400d0310244142c1e03108a5000050400b50000003d903114024401ea81007c080d1000794203000e0743c40c5810214504022200380705401c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 465520125 1250 465518875 465518887
    0x6030f07021603030c170c0d051e190f0c030e0f0a030204050a09060f0b03060115030902030616030c051819080d12060501080712050405011407080403021c0e06 70
    0x10081100d001c402d9948040040119034a0600800501c4000c2045525034403499801e40c00c0000c0c8000d6421610a032409042105030780301c000e5801703922065100002c41c4850451140600340c00010f0229000401190b00501c041d094000703200c0c2d14000300c0ca40038811400004008a58015082c0c01004010303900ea00000c415400060421582988004cbd405130402c1c0400a40c1a2176030004e11019100f102c0900442c082004034609a4402100c0643c1583c03003031004001b0f01c45003a1490460310150f00340002d44040c140c002c20700384001200d0fa0b0100340f0304042e003000c50503071501c255001c0c12910320303000703080541600075601c0b040c00e182e090307503c9809840c50003605100000d42020091480b941210308002c158078001d4010300182800079034aa00c1c000c0c000540b9401410400c0c403c00032559440b0712082d80400f003500812024205882c50f658603c98000c203402110001401048643c13103294161500c0e160003850040200d940300318503110a0104c9200c55002641c4c102c02c42001c440d95a1540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 465521375 1250 465520125 465520127
    0x4050303010e130803190e0d0c020405130b010b04080c041802060306040608100e0111070f030c0804030609030512090106030201021c03111911060f0103150209040f050702150606030f07 81
    0x400301e0f2a0142c000a000000c0c00f080c05c41c0402d107015819140503081c008415500d02098407204400036110205114111180061806600090384a41000b004205066050301c40841400f002d03001450030000018084c804841d0400010551400884043c00412802d031801001003e18020090050b000400482c50a40e6141c0002d0043c00500040f40c02c1300d200d19240f071000e4481403641061551804840c840d20714050401c0b601a50b411500d4460b0441166408684181440d0000d60f2400000e0001100040103409000c0300c41c1d01950b81d6944440c0360700440240d1f40c0c8090032282007030b07140020402c0143d03004103240218180300b445480d4818000038040c0c000c2c00203802c84001880001584600300074078072400240149031541c40c07402c44014600c03a0395848000369649030b04510040010000a0410200c040406150b14005420f02d49041302007019a00c054102c080115201d408104000d90f0412845450b119806080003031030038240081041c901c000f81440300202c5500300029109 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 465522625 1250 465521375 465521401
    0x2031608060f180613142d0126030c120a02030c07080d391a0a0509011803051204060902060423041a040509071706061804050303010e 59
    0xb48014207201810800070000150092080343c4803407003a5008595000c01d40480d200b003980f2003001d1760440d01300d5200d83d600c03500d40c20001421091410b9071064030600c05503140c1c203a14020b0800d0a0182c030a1114402c400a804450f00480304180d44148905215014000f9131040080500d4a155981d203034251000c90a51003442c005000fa882642c030001510980040c1070194110144e0300c15450500840d07103c10017419801d204580d04490340328203442e071040c14050382c81040c414202180e5070200000c0e018400e9404a80d0306109070f545e0020080000400c1c042c42002040d4140b00d600440c400d039401814600466600091188415000070100b0900b50300144241d07400800f019115a564074003441542c640f00f0002440241e250189205410140603001c0582010b1008002000148081c04020040208990341d1441209800680d00022042d0003040c0c4000501511b154900036003030002c1c800020342540c1c1d0b440d14043c2000080740020041d02e05644030300808241ca500c40c10110201 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 465523875 1250 465522625 465522649
    0xb040f0209092802040b0306041107051525050904060e280204030206040b1b01060e06102a050615011e0519050301170c060d0f0f110c07090203160806 66
    0x10031300c001004500c14241901a600c101e4041341c3c184450360603036030084601d0090003c000c0445c0d0004640308001c450074003000c1c2e03200e4050614008000e400302a48046e0026071a40c05003c0f84000411008606041c09000050107400b0050102810305002c104114415044180b60580050f542c0083e0701c0c079540c040f5001560020302c410384903034450403200503562020f01450303024800010740543e151410b0040d682110810280c045035079581e00180320322030749841480350030020310018040501c100c003540c00b0b507000713160603a90b80104024544a480d00d0340c090034405250b80040c442c44013581e0300000483c0741c901000072000440307000e03180c140c5542c004d45e81009180503003030226190707065000c00550f040300c0c50484606507499506000d05c0d100c1094000454000d42d0030407416200c01d0080c0c01641c006d007580b400000300c1e28042c03a460b00488180c651020a69180021012001c10041014001500c14440300b10301d1810151081e000c00300e4020114020300040c0000100195116002c03400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 465525125 1250 465523875 465523951
    0x1101182706060e1809100905010b15030712020c0309040e070f030807020906180a0e0a14061509150d02060f0711030609030c0312060d080a030b040f020909 68
    0x1282d1602000740c0301c2041c101c0040c0c0190300e42c11074640d50740700d021065806102c00e0300103050540c00f4902e411001d840c0c4c0080a580c10340d02d400108040c0d0311040e2003035401c0400c0040c0f0903240d0034112030040800a281c16045c050b01e00601000c8100000402110940e58003220001402c49560300b0b03807820590542c0c882102c290f080e9a0000900903844014007200703100300c070420001d40d502c070200030319040d100801200700003007400084c0344003400398094000d505080d0304460010100d50b80750b0981c0400c0740074402d11600103005119034461140c908400d54001140c52410914104080d1142c42c49000e007800d02c80c50800e8001d0085d9200c0a044500700c4000c90140c940d6452f0900341000700d6850743c0e40650003440f4000000c0d4a607040030007074817802c90300070b8003441c542009005038a0b80c5050107056198060840300d1040f0001d25404001d1091014684010608464070b000f04001c41d1003540000042174010042075603141d4801ea405030380170410114003008986c0d55880a0030180320180141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 465526375 1250 465525125 465525131
    0x7120c0305030c100b01051245060901050c270a0603020a080601050a050702151902060907080a173105040b0d110d03022811011827 58
    0x45000c0f031010811000b4101d1200050103800c2e0640f0044030544100510250030003c0100460030210f480012024502c1408a40318101032258042c0caa07007080007030450802d12124201001713070f540c013440f1055000003280000c10162401403c41401441032692004150310401b041c13500c01d0740c0c42c110002c4061006030040c03002c59118000540254007001c0060042400200040c400b98400c404642040d40b0b0341d40e425040100c150700784000325035000ca070300800c840d007403290050003414010105440105e80d0300070907060034095111401c3c44510703008403402e60407035041480490045210484034505403114141c0e10326682a40c180d42e1003d001900440401600c0c50f200700c041000c100d541503600c111020441408540d08001099404041c01001d00d02e44400b10240c51130030841c480c1696000340142c44842d401c1c0f101c1c1001015200100f406c0d01d18214446900b44992686210084d01003824450764030b40075050700b03c0e40c0550b180f01d04842e5a00700c29401076200404d4880a890050f106414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 465527625 1250 465526375 465526387
    0x90403032307110f07051003020909040c0f06020d08240d0503180405010312050715051608150a0311030f010510060f020307080403030e121c0f020f07120c030503 71
    0x810008001d60300c00e000a6440c070140c0400d0301010030384250304c0800e400189a080d00d0b013018031100c5649540d180052603070a01040440d0340b106101d8a1041d0320803250b480c0550308140300c0040142050700803000b19030100303410200c4190040d140030b410400da00314400807500c1c40340d0240b8000022140b03080d0801c80f02d0855004111002014054241341200200225080d11003400201c1d90244000360680007400100d18a0300c1c0144000c0040e9400394002c1c10222081046070816640242c0c3d95100441614104502544c0d03c940415084148a00c040c0032070016180040c1d01000d01d4007003e04191402800100c0c035940401c84c00e44414600b07030003030145140c1103150703156000c003510540c8046a02180d10401c4c1e144084216903400d98840925406c04c0e0440d24211540c0c0181c41045410004020900e0030041d003c028210310441c4038980654624803250700240031000c158161425540300d00044000703100702280c0c00f019205841d280515049460a00d07042c1c8038110f07440642940000606 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 465528875 1250 465527625 465527681
    0xf0e01020a1e1d06070327150e090604050c1b060609060607030807052b05090d08130308060d060203010623030403050a0f020c04020408101107050c09040303 69
    0x4140c030b0307030200003200d889078600010040da011520010819002405400210800e01d00308000e8080d50303009251061a50340120f607850310f400c610000c854611811b000c0100120340903007001c0340b10400d05180c290641c000800106c1c5009070050003030340c0b01c1d40d264070004651030411010740c0c950400d0100403010403002119101e44441e015100d050240c146c1800249103030420030222111540d05985040e50341d0b459103000c5505c0c0d0081183c0c90380b1510130340c0020104041800102c0070742118042c001886040c0304103454680b0300c40e0034000c810702c24401d040004980241549100311a014104820305a80301000210801e021005c0282260310220020606540c01400014034a40c0f9116482552170b040500e03030030310b000481d0020002001000010070303492240080e400325100c0340c01202d010000b07101c002016138025410035865607001a10703c3c0030310070441c0128008048481d441c185428125102c4503201d11080c224280100d1416011908251007076012030b00c02e42461400350400c6500c400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 465530125 1250 465528875 465528887
    0x6090803070306181109120c060d0e100501081f02070f05070e0a02070507061b230c060c0a0303110f04060203070303050c0a1706060d060b0c161203030f0e01020a 71
    0x15444c0303e402c8208448400041c1ca104140714000d10324600c500b4410300c0e80800070706410912180c2e043d40200700300b4008688402002d007140551041c404078010004100d0f00d171a0071400c103028030031142003070010040c010000c650085540030580764a01c0d442e002500030000b80c4910040100340d02150340f00c00043c003c000c100710040d41ca00e400303008051f482d410040b10076805181d50140c81a00b2a0b0800c1040718010100c1810b940725110041602d111503845090702e40d05440a0140309050b46140c0c11002c2009000000c10040200c607000c0c202110390003025682e03403403880c00074141651000002c0c4010221400c0d80c1807480c814004507540c42c1c440a00035100d412001084001c00d0400300442c0310700c45002d0548901c11a07c1da1101d8a103800700c002d0a031352a4010340b45d29080002040381004072401c0340074a45c05448030701101642c401641003110300e0302c20120340c0d0340c840290310f1348284944004038200064841c0c2616001c034040740b408103144014450138584003055031000420162040d0010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 465531375 1250 465530125 465530129
    0x23105090705040617060109030b070c0c050102030a080109270302070810090809010c2f0f09010e07030f020f0d1a040209010905010507081b07030c060e130906090803070306 76
    0x250301412161110340c8141c4242c0030303c0c01000d021940c40c444c982e030004207007420b040d40700005260402e10150b0300d80381c460741035006881850010725284070500c140180e010f080d00003004203100441c0340403048403005004c20380600a1940c3c05858980c0e0a031988150584110b0303100040f0f010104250301450044d648103004d11403000c3d00d018104a25100701c0280c030503550026008101c0610703081d544001126601d40104084070448100a071200010391005071000514440f8071019201c00250410040b80b070f4000488503125044840040c0201d610941985420045c14140807a50064510501004e402021038440b442e18000c03c81c0308075500304d41c1111005100c00c2c05a01410a29981440141e114110900c5d022035061042000303194442d400030000a4020703902d050603c08400c01c0025040b108080204040c0d122807820b000380030320903554100504035428030001c42c1e8010000b103075a0044032f0303e01d120707560f030380701603a07414041e01c0e40151b891b145c0e0090200d80d03a4501000050010907640c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 465532625 1250 465531375 465531379
    0x9040f120f0e0405061e041104180b0306070e0d030e0d12110f06071b0b010905061507030e0622081606020114040b0402061303050303190506090109023105 68
    0x11054600050600e40b0130f09001e10800703026005a0300d914100c609160720f20300440350300a9940c0801c0c5074084000005032014006801304258041000798410b0151510741241c5442500120184511681c011002c01054241aa20030290b07c0042c2010344000d012000296008a80440c8a004000c400103e0500c4c003500354580008110890b2400380d601c00041c0c0e0724894960050300410300b0359008680d00c400c07100c3d403040e545054110302c0d40c2d4620b400350b0aa00c0031214179116800c2c8081854242c000e80b103601e0300c101000e4200794079614024500700c01c0c4042e01d4001c0900058081c150350300309659210b900703008480b114029a40d80c0b02c842e070b034010840c0303c070042042d2031901007069807060180704801c5041e0f00041401e40ca86440b0111000e4014000301d9000c0c80c204100c04100c0d0f480c0ca11b400085005001660b1280780030f00c141c5403580031080503800b0041c42d03c807c010840d0f44103001c86054071900d900058440304040702040c007500c1c1ca404c000390f0000324801140f0010412a0300503003034802c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 465533875 1250 465532625 465532637
    0x180c0224040605090a051b03010603080d05100e041203021b01091202061e0a020a050405280e04080706050c090301060b030402040e010501150c02030c2214090a0209040f120f 76
    0x7804d640103407141e00b00180107009802800808000718404280e280310740a000b40009891030362552000700c1e9901000e565801c1d02e448500700800000c4000f640001080070400044c070503d8140d4a4188004805900301d041c075a0200c0c0886640d40300c860000065800480200501c0300a4241512180941e0f00840014840d52001070f5180481d4207440803542c40155401c0810b44079040d42c400a9004881058100201071200003419036661206800400051503100032009001040300d154901c00d41001d0348803107200c818040000c0600080750700d42508180c00041d00d45a1000c00c3c82c503441034440255044d82000c03030208400c1015001540500d1085070b0070400350400660041c2640c00910911070b60b10080c40d0f048180600800410760254401815100c1d601e00e81000038110340600d20240c100034074119940b400d00d1140c0e1140101d03115889944c45460f20b0300100c020360b500358842c0024000c002d4100403034108030318500c00d01c03020340e4000d0480c0c00c2d0700d1400000800e030ba01490708a40014007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 465535125 1250 465533875 465533881
    0x406060605090109060e120d180b0702010503040b1003050106180f050106090324051015090806010605070503090312070201090e040809040207031116050406080601180c0224040605 79
    0x1008204440450300103844e0f012440d46000c00035108040700040d610340140303028000346005002400081d0315401c9540b2003d0040341d1a1100d03840720f504540220369103d8081121101603070304101503a0703100317074440a1600e4954440d9007034041c9900b554002081d547c2442404612560710082240c4032907408882001400c00c045884015184e0038409e040c0840c00500f0244041100d8050003004c45541600820b1803042d1500000102c0d4030850700070050746904902400b09002e20031003040310245501c1c3c03c4062031308100b020b0f502ca09040c0b1031241401000121070003048024020b940748058001c098030082115403040e200b0b181e0000004070f001a1b0354020100e61a5a40b80d1194000d41d08041d4281c1410900000d000003940541b40036814009410540c1c140c821040100d20b8541d49000300191610b03152500f40030943d071842d0480400e54200200501a0140c44180741c80b807542d0807200454001030514040c0c3c18030240941074042802d03e140079500d102c2d1b8036880740d80154402d250800c520340d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 465536375 1250 465535125 465535127
    0xb01030c05040509010504020a051213022715010921060605102712030c03140c0c040b0607020a030602070c0b0702130c18120c06030902011205151804060606 69
    0x2110b14060258407400c10001031040c0e0a042e4090101480c0c0f0741009440d00603c4518a0f940c0c030703801c46464852101c840c880b0011402c10503841403103002103055062115421440409144100400c00810200c0403140b10a42e60706c99299000109502d9581102919112410252414a94030181d13000da0402c200000d00781030910303800510b101543d948200980d0b60040710315140c18071480001001d44c0e0340d140071444e070309045408441584240c44011440449240160410000307514040400000340040b4940c1c10000c00c4c485d00d0040d044400044a4803150700054003802103290107500b10110645c00700400c40c030343c1e0003813110314041d80107000460342d2820542d12510460200a411026018524080c06d00070380000342e0189480c1809640d655160104410801560780074002c000c031941500c0041c8502e034404900a8469484c040c000b07843c060b0000707031810070b620122509440d074a0340014061039201c401d0103a082401840a0150644690b580c458060107440580f451132608100240b45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 465537625 1250 465536375 465536377
    0xf06020c032509020318010c02010e1504050f010516111207030503130204112a1f060e040609150b130905070e070c171606020309031605010b01030c05 66
    0x8000c005006011941e140344804028408007035a01d00150709103030001c40c8246850028500c0740c4501e8480324a80c04a050f03c00d8203550164030000b05591414281421817900440c1c9008003460000700003529449500d0700c1450000140c123a035846d07510744028005c041740320904507110346103140c2c3d905040c0804101c8150710b83c02c0f80d0700040c0c0080c000300042400280144065540710f8852401203c4200c401c0d0049001c0d14009114010b822000081207600200c071403030805403d00109401e10f05500c01d030307030000f50788210700c580ca241883e0a12007080d88144d4960001c001915070346000508900306440c01002400000398101c07900040b0b040c0d8940c0c107580c24804c0d4034003404000d201c050060020380e00f420050071400b40075103442c011054085885100d6108440c01001e080e030762071040810500380a9100425408000121042003103680301e442a1036410098003a044040107a4945941660510350712482da0b640103146051070851045c01010b41c0603841c0201c0030388040c0094800c1207002c40381 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 465538875 1250 465537625 465537643
    0x3050d091d01050f130e010f06090506060409050402030a0f0506190b031e0c06030c030906012309100512010906060f0612020307030b06070b0601020c1509010809120d0203010f0602 79
    0x450407000040060385410076049100ca08090311441c80f0650040100064500045405900780c0d11100d40803130604180c0b003141e00802211400b003245041c00700000d1620b220303622074515550740344d00114042d03603428044040d01c0c42c3e000d0010b80000d0100e24103d41c482c030040f15142c401442290440031029401c1c0078503590890010013070101100b07041e40d030600d0801e080301d900350140304807032110a15840c0d9000945c00380c540d1480d515105d00d004030900b464400141c200e000c40328041f1001101075410300343e2003041c031041155040d181c4c2e41c1d091030052401c400f5a01c11580034080250766003480006607c214400c5028410510056440b1900b640d440429489200001b80c50300c5d034010040615503028580200b0145000318a03d141c0780c001914642180200b558040003400601c480c0303680421912008220540e01d500803112510700b001c6440c010346160341d040c0300c0042c0008044080901c0702400310789007548200d40340c0c0003554015001b90024003914041c0311038240d001c40d01e18000640584 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 465540125 1250 465538875 465538919
    0x32f01020d0807050d14270a03030b060904050705280c02090c13080d030606020607050306040905070302030118030806190612090c0b0901180e2e03050d09 68
    0x105100c0308841151140d400a100c0f008205083c0103046030382e1018000c00d007030002c8400f0403055905051505510031455071410103503800d03100b2000b40c1c2265000c00c020051640500300001d05c003c8081c046903403031203107600441d0300a18120810901740d800c8406170002800d003001898900390012030303e503015180c03100002d01107650000640e0051404480d0540c0c0200c0e03000b03c0600700141403010160808040d0007108054004d00001d1520365458171690340100103500c003d0240703003001c40c4040d10601c40500801c2c02a51a200300009101082003064000d550240003003109001d4100e1805081c0d201500440004150301c01090301d901c1d1441c0380c004050b0380d100c0504022403034004c0540d14482021302071a07049403110f045202003403100300300758021b10700b0060003940c07000280e000401c03150030209050009148144280503a02e040010180d000500c0500c03900e03420b0508210a45111500d10700a104501103403001c001c00c04049003000c601081602c402041e140c4800c01442000d0004203c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 465541375 1250 465540125 465540133
    0x403031b0e0d020d02041812020c1c0503071a150619110a0512030709061806030b01021207050c18191107080c010507140c0a08030402150301032f0102 66
    0x4541c03840d020100602180c0b004000030300005041d03000c01c0540d08041180703190042983c40501c103001e0541600c0309a48035503c0a0071841c0031480004400d00c0301407040c006900710100c0060200802001101c9581e90401050b090550b01c0c9030842c991084119106050754107621281591414003c0544a03c0f41015810080041c6251000c4440c501d4080000404d4445c4c41d1110000c03650074043c0c04140c28202c0c0c0e503183c0d00c1c80c02030f101400307080701640071801f00452207460795000c4540715011b6081d03601c94603020541c8041140101d141080040e074641d9010320021300325041007400a40080c094106a9200c10900c1d034500801103003030b0080320584800d0385100300049001c02c41d0382c8401e0010b04141e031070a003804d01070744410116400104020f0102c4e07541c1e41c140b1200035088100c004080405d12042460700034002d03440790b210704140c0b034010102e0401101240c115580c41d4101114000c00d4115542c072982d40f070424070002c0040c420361080183e04a00c130800c808084022001513207006030018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 465542625 1250 465541375 465541397
    0xf050105182709060f0106080603030a030e030c03130e010618030f05120a0f0201050921030604060b0c1606032009040b030d1809050114010503090a0c030b0403031b 72
    0x44031000540070040b40800da050b4900c0e42400c0c5403032502500503080200281302515000391885103001040e0000b505100038001045443c0e68001b040304e8030f4050510b000304481440c0301040d40341d40180810020140408192020004501c0d000841104c241e01c1a40002c0d981e40c030010b0303c441c003444140501d01c800340b0100740041001c003030418503d54459001c0b602d442c0300050108505400031202140041c07407050f0350002e090b609019a40d04244098050151130341c5084c4020800100f8001001c15211301000080d0a0794507617002100911440b15000c0c0e0319401001a29100c0e00c4007440f03405510901100800e855100b40b140d0302003400214040c03501114100700d060107a40081c0030b010751043d1180c0000c0e2003a10f05105511a00115031612042042c035000c0174500d4410a81041071a40d243c100100302548649101111440342070030a50741d240c076503a002078140507401c0b0002d0110711a40c4800410403600c004c14604c914000c0d80c0402650a11004295200b105000c1c2200011865145 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 465543875 1250 465542625 465542629
    0x5092115180a0807050f01020414120d050a0c0c05030307060621050a0803091905010b03010f0b1e01020a12051b0d090501140403020a03060209010215041a060402071b0f05010518 78
    0x20103413940190304440c06200b44404407400da80c0607400010101c140303980310390100e0130070510b1380c80150507841c050100301c0e0b0465030040c4180a15480d003410480e02000720030078068400e6004001c1c0101509580e965a1035050820183c102403207031040c20010400110f40c0003403040400740c3c4c656440b60240c24070440c1a04c842509410140480d850382c0118207a0b48100c481140355502d54610a000200d40e40d82c12400305401c4400b260ba1001c50b00e0b060080481c22540c800800c1d286070700411010f030006000b8800102c0c58000c0c0b0460040c800c44c100d2000303070238068100006d081da442820100303003010042800516120351105200da0301040080710240000c2d03000d01c81f04000350250101040c20705a89400160303000c200c0750b1041d506542e0000314406156418401d801d991142d0b03103001440740c245583d907038a000204e682e00d4144043c0c0740e80410700c541d40e550111031686070000306050941c981c0a0001038148228072402e410700840500024055001c2c00548032400c1201410911b14920001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 465545125 1250 465543875 465543877
    0x110f0303070f090b030916090b010e06030403030902090c092b03120e0706120f050408070b15121c08090c04051803040f030605010902040e010605092115180a08 70
    0x34202d024040d0780710340803640302e00101c06140f0506440700113000034810200110a02c5030320b40c1000001608101d202001c590b0088505a0030802c19110303a503030b96840f81801c4000b8400c01e08001d5005240c4030a20840071a1040981002c0781c04039121000600038104192280c258042c1134045410542c0400c6c011a000301d00558842920b2100419a4081a0840b9003440642d41040c000b240d030322903103825040303401e03c039103084036243c2ca400301714a040948230420503014200d0024183c500441c0015034110780184000012100900780803402c2c015807042d81d48a068039101c102a84451100c0000c820f0720865129000e48182005000561f2030003003840050980140903100c0a00c4040070342c00f90301800c00040c0b00805080080b0040c031415071401c070b41a500c06030302955980f03005000034409108241c0324281100d07281d04200343c3e2054a8808160320021480804103100740354a48a040c0d440081584107000c26003011403a10b44c0e0b24924502c1001999408055903548105052000144450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 465546375 1250 465545125 465545147
    0xa050a021e16120302220f0515070c24020a120e0303070b010b0c0706090e0112060e0601060e1c0512130e2a070b0408090d06021207110f030307 63
    0x30814110801d980e0300c500f004030680324141e00c002540003c14180160a2804c078180b15503e5003000ca02107481c10346a0b0500c481c041c040d241c86542c2618051010720010811140f40c0c07640600f0400724650703100c0d07c0910001700e4948030304403018086070380450188040f60584d0703c80d03406840e1040c1c131610003a0444851100009281d09480104203402c007298000321124003c001403040a03a940001232a039030308001d002d0380900103200150000b84004002e031000581511180c040c0304144200608044c40a0091440807100b140160704c000309900d5440700040f206803005a4040f8003144201c0001d0f080c40348510806850350f000b00d84a070140488a0005020f40591989007803500c40d12815000402030050b01e8403c00740c1d201741c80e880800849003005070114998040c50504180440c0c0b110440d552004100030506070300044c0010040c1e891482c001203980e00080f0454940c400800c521681c5101aa5014041040707503015810b9004002200ca5419545034003079400d540712844107846c690400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 465547625 1250 465546375 465546397
    0x12030603050303090105011d040302060a020319150608060118090b0f100c0c05011d010c031103120f010b040b07080702031912030f020c19050307060606080a050a021e 73
    0x654400404514200080c40c01180100c00005155161039440300000100019250547c006a030801000c29004507800d0b500602c11b000140c1d8039078030384503942000f0702d0a1609031455403812450b074600ca05000801026150280ca071540f45407038100040d1210f003284024000e440c0c0d8a084140b09030820b076002020341400184c00d02c13800f60151000640c0e1000710500c00303c00079118403026018031991100c0800181403c0c01d2412401b14007102c0d11100000401d00203044c0030780011810109817262a580e0750201c0c02c8010380b500c4031a0010744042c500703016100c001000c3c0700030b4004210007006e44101e40031030b0001c4030001d1801181e95a03000d0a504052000d907803600540d000b401c0c002c0c00d03200d02c611501e4403d6070b01035007a034081d00c0042d00300d580c0c80c03100e40c7c0c00d14411301454480d070000041080000100181e80c080316409407038036070710b0340c402c81c50000c22441c204900042c0640e04850a1402486034110070b200745d81da0705149004a0007075010789465010000410030070089040c1c0288030030040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 465548875 1250 465547625 465547631
    0x30e030105191a060304210f0509040e0a051606020115081c09080102041404050703050601090b092803120c0308010909021c03080a1d060403111c05040303030b0415031203 75
    0x50000044131608201d60a0300c4401d9940c00c00e0b0400e90315200c0700e04500e14035090604109102e510b000780710740601c24046000c0c40c2d4400749441c42c00800c0107660807182d4000b0032500d410000921581c0101003610442015600f0070308543c075204c100e2450102580c0918006081401070520070b00d09600604040b14144100d030400130414100a00050010703100e0340c81c00c0b5088414007801c1c0b1003203174001002030007050302c0d040a10100303a90192141084440c1e81c400e10303448801210000e2034201586a08984400c003400c6ca5460100030107032a442140d00850760107400030120303036003920304558000d402000282404010711880d58541d0080044034009009607a61114404902c40c804040000c16000b03d0350700410070034070040e0b1b40200e000361003603040343d444d44018507850150f484201500080c140b06c00203103a05a820401c021054900301080608203810958100107030980d030050105900080c240351858003181018000c0000361548400301491052035900c0b1003000e8140c07c41e843c420592 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 465550125 1250 465548875 465548921
    0x1009081216120c0308180a0201120216060b010905060a23040b0d060e0610020a02040c051207080609150303090d0203030f070804080105090708120d1103070507030e03010519 76
    0x200c80c0300804401640d448501d43e080c0b403814081e0100c1d80c01003800903981c1070400301030610a004690015025030a080c40c0100f01d100c06620300103805410f0103220491522442c50040c84040d4100b25603030304083e2501c0c51103c2c0c94005010092141c240c0000114542c4504002100100c0720320340e41c0e000d1a80c210f5418680c82c0d102ea010300f0303440001120350040d00c1d08000d018100c80f6140190b0010320880c1d00c0d81c40c0100d1400301946549420501911507540c6041c003111250181003240c02d0502a40d20b034980c40d143c03d91015003005025100b03103001c0c60590000440c3d58082d803282001c020310040c021800c01001d5002c200031400d04030300c120781501040c040301c03e0540d01a405004c0320b40c41801510348807820400c0311400c4820044c500ba000341d01841c810002c1900100b000c02e1801e603028465540d41030032007100070141c08950454403600e0000810442155402005412900d210341e4528641030312079010542038031025600391000100b54100e0035001d0044d6485090581e49204400e10710113 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 465551375 1250 465550125 465550133
    0x61617040b0d0e030a020d0503040809030618010509012a0c060c09030512030c04030803150303040603090302010b1e010f1202160201110102120f090c030d020c1009081216 75
    0x40c02550108940c188041440000e04859002d400b4081881030015802e0806884000b56210f1140c104a000c0c010000082810701003d4000c17211010009000c8031160f0811115408203580c82d034069000070752802c1c011682807401802410100c100b2280406c0c0c2d1030851494071184d209001c2030200c00c0c452b001948800042c100d026002d20310045d41c40c0c481d4103601c0c505016040c105801d01010825804004200c3c03400e02c00030695040e030303820203081030703d990311040d440c039003100780c500c0507030f41840b020400280055140e04950752040c07103940240841e00ca18014800401c040c040b40c1f40d15100c0d20541c24040d544211200b04989049141440e160140040903034200d034032007001e05400c00001d00629040d540c10800211001120300003c506d40440b0b46104000c00c0d0000d405400401e03411804180421810400c0300c1ca40da800500741d600c001d03098030000c0d40d103004d10080c0c0d90281581e0702a508045001741c002d00c0032501320700c02919004105090803540e991140003482804581603003040c02107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 465552625 1250 465551375 465551377
    0x601110a030806010e040e06010b090a080f010b0f060306090a0f06031703100602060702030a030c3e01202a030a02010b0f01050d09061d030306100806061617 69
    0x10380e000b511a41000e041281c00140008007180a550046051400c032044091f40001c1560460300b0384500b20743c40354040400141c041200b42c5c812507181c03041440840f0b000b174040d0320001d1400c408540c914a403041020602099010869050f80c0c1315104000140c20445550403056400c0c0e4140d90001d50180c90f07030b85014405070582c64600100b5004030410071540c8005003102c000d04480c1c0014001d80c03400e241300030364900c55040218101030300c502c58055490700031810784080049002804408200c00811481e29480160b440200e24000100711a80440184a031850701681c41c81500f80c880a07508013405ca5038030050311b120032100800c0e400541d00b611001d400042006d004055541c60440c10070003802e48840c1d43d070a034454028032000f54042c0c1c2e00700c0e0460744004854000452032900741c0c1803d200400c081c0ba1085186205005202400d590100c0190f10500003259803081188000f4000c45000740c00300d400641084007003100700b0301d00c1c400c546500502c03440740803012540c40c0c0703044040c510313 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 465553875 1250 465552625 465552643
    0x40623130b15040801150e07051303120305091c0f080c0702060703080702010c1412070306080f0a14070f12050f150103121701090e0f120919030f0209060111 69
    0x2c01011500b4065a0f0703082c092035800030180c04120401034100f0040d2802620080c2c452001d104000070b840b0a11090380c2042001990880015010303041d0000d0b010380501421240044140542d42180802c124401d0800e8480780040d070351141d40c280c02c01010344000e0406028045c10800a1041c01e005039603400080c0881840782e42c2c1e8802e40d0608240280c00d4a10030b00041c41403101c00c00f030745528040e10005079030702c02c100714a580290780c842400507002081e0741c2d048042640101c980700c00c0f4051002840a2042d0300c5007000002a2020801841d1204414010441c4030b1700083c0382044070040903011550413900840a581140890050703541c074209911503c25107090b0b4481c01041403211200d48a51401d0850a0400c416080110b101c400c030030301402042030450b52450032010b510b4013004640d6109031160115000d0404002262005400441100d40310319a841c0050005000c040005801c030b0b5403000340e0a0000c0d06a90030804103c20040603241002007440c00b40310320510130000b440c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 465555125 1250 465553875 465553909
    0x804140f120a14011a040203130b0c040609090204050607080906190306090f050609160309050601032003030c070b07060b18060103050c2104021801060e040623130b 72
    0x20051068a440d40c036031900d240c44190f0b11303451310a40d00744400d0240443c181d0804221001680ea030745940c3e52840c0c1d900c01300340c040c1080b41048200404081d2110003001555007035224040c40c25a103c0303020f01640700310b029003900030000780030701c0d4001100d8202800c2c9002004002d80c1c209007046140c00f52049414032110002a210801006410000d11808030b454901690522440c174001000c1a0580c0024051001c0860a2032091500520079402140300c1580300080d039065503928241125840d9138160542c2c1d81d1082d1041036100340c40c00000301ca008040f250b02600340c40e841c03c050114146c00c0a0130540700d151300c81c40c030103c842e6074024651b40e003c000600345d20440d0600d4800102194801030411b5021202044150032480b2003070380012248254115550141d522480454103042c52420f90300070030a00c040021495076040840008070b1541924100141541d821002070140c0d940c41c4c0c16110040819452919410300800c0c0c0d207180280c4c090045030748890a00400d4000380c1880b0524 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 465556375 1250 465555125 465555133
    0x21040303061a0d1a01020c0f0a090207150c030b031002070c0b0301080a140105010b09040908040e0403080411030a0206070b3c0a020405100f0233130804140f12 70
    0xa11640c1241c401c4d84a504d42160142081100c00000070b541e502c100010316114030302d00c17005441daa5403420000006002c002c1d0045d501c2c0d040b80e2030481c1c1da811040780741100700c904000030a0b60540c0300c2d00c80d01c00c502e01300030002d003500200030806034004e50040c442501d02e135944160104881c19001c0056009040100040c242480c040c1000b49404989001504480e4100001003080640036815110792010440c0c0018808419141682241c410303603101440b048100010401416042400e46105501071107660100384000c0003050b48442034401d0095110500303000320004140200041e5034407400c0ca2400c8181441884002100180d07132004101e0168010b0201044e84100c0c0b058045d0001515001581881c0c01c0500140c244082061035404004001d8a03101046200704042001000089001d10106041001d242d4114000807640c42c0b01508820109110722180000d001c8915000000c0303031b05081c1400d5203081400300d110002c96100303d21400d40203569552620b0140418044c03030080c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 465557625 1250 465556375 465556387
    0x70e040203010e011a04020f0d0903030e28080a110715030b09090c1212180f03030909010e06032a0f1c1e080309150a0221040303061a 59
    0x25007903e4820b02c4a1140ba41044421101000c10120f8046001c0c0112405a12081c031004c0400440c068040809243c81c1401c2c0755205140d0991f10104402080100380e80805a031345490303481c005001d071100d00b0748917105d002030320101d044c03040a400e00541c5460f140ba03071414141c5007549005026003044241002a5880300e168503010700c2a105007c00c2554100158a06150704548850b081300c8003038001d483c5035a4950744000c0c01c0c0488840714054040090302c0b00c154042c1d020120f0402e0090320300076010805c01b0b10981c903001055032602c400042620b0745580c01c1804114407a4006402503405100b0308416080102d40c81090340710700032203401559104507038842000a2251441c2106004400e0405580541d500e14500003807200d8000070400078261503c15049144119440054154800801031081944002c1080210070040c0002651691140f40180d400c07445118405806052049447c90b014150000d41d181d10500900f000a0340701d540e210180300680401c944050a00400191 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 465558875 1250 465557625 465557629
    0x30060b07080405011805060c0f210d0f060b0a09150c02090411030c030d02030d0c0503010501140c070f060c0209060103051501080c09030102040e070915050901271404060b1e0714070e0402 82
    0xe40c000105404140750030ad007044044080d40c5100360b0340390540282d1a214490400441d0350007680041000a48c000d54801c9651001400814280619002c6414000c016078032248282202132500e6002001c1d1071854459540e20b00c20b1b1b001107000f498140c091083d0404d45a0b40c180803280c85c006082e005142e466400000c403004640320340c40a001401410301c01801241d0b4030000707100c84145000f05460b51030303554560051603d1000d5000844060b805080454411b82c03004202d007100d4400c0c0c85504854542e00019010385004880303061008404446200f12503114100c090f400082d41140b091820f10140c011900b640e1050300900f0b01121100140007040713510201340c40c000d180c080c0441203c003280403002400d44c07042c4140d150410924111440c4144065015101c219002c0700510f82c030f080d41d84240c082c281d501c81520314451490281c002a5a025642c02c540c8590300c401a51105040044c00784017040d003007604107132150303041c1c84980304080c0c104100b0040500703500e040401d850319240c41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 465560125 1250 465558875 465558883
    0x61801050f01060212070302070e10091808221d160503060609040b01050c010606090612090506010e100801050408040312170601050a30060b07080405011805060c0f 72
    0x9410904103a41d401081019404106034076100c0d1514203a55494a080c20201d2600c40d8640017112500952000c0c000300e040e01d220740f0411951582001c4c00302080b1a41d070040540010040600b44107410407500e10156000344080941581a0101041c5681c03505c6035520145910b440d003002003680d030300500507511a8041d4a01d1010028a0000e18614040c80400e805000307000240c0d005940742d0722000d4142c0e00550955108203040e00c020001269207110060814160744545130200789032200c40d0440520b03500420210a40081c010005a447c004181d096010000d020900802e004440896141c0c42070103214080d0380502400381d111411404d10036200c1c8a654213030070501c0201181c0100c0fa40710494002e500110034280035071507800c85e40066500301032044c1070a038070560038841c9141c0c00520310f00308884142054000c0000a07101e440000040c0303d400000380c500d0b071052004010a41c49002d104031054040c40750303101480d5960b0301145c61038000f99408079240d0890002d210285200304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 465561375 1250 465560125 465560131
    0xc080a170103052b090b0901030e06070336140307080409091506081911040f06030506060402030106051602130e030315150459070f0c0303060806180105 67
    0x2148455840441005041d0441741d1007200d2040002091130a41a0b0085c1d0154000490f40020f442d03d130301d4003110080041c207251b800c1c1c00305180514a0081e000000c0c00200c1c0c100c0c0700341e920748500081c480d20344e080c8207074000012207010b2004010200000d08628007500c001d02da400004654420680b501c65081411950a03041a91504d94100f000d80400525110600a06081309410034100d0404550b400b4070248229042410032501004032407007a0b2000044078041c100361125500ca030010002a032100388980c0340003405c02d20000c5a01540d00f8921a80f1a1008180a821941c405c1e40e1109403007140b01c04a500d60804001c012070f1515241e400c8203010400c880090780c0e1313643e542103003885002e540512000c89003685421a0300603e5613900e26410f5890ba1210440741d07510880b2980d80c00c514084007104200043d54403c046616038400c00e0180c2c0b210745541c00d8840e05482c0864189035040001c0d010107444210000304103c060102c14018030040784c01f1024020340301c8143e4295500a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 465562625 1250 465561375 465561433
    0x703020d150c0509102303010803041d0402010503220f03080a0f060b030a150e10241e021f0c350910060603090c150c080a17010305 58
    0xb007240758500c1c1d840345c240f1048007420b400d18640460b41000c86401885101038031465000c0000004200044000013810865009603a16650081203200441c40200b050b60002d003c0b44080c4081144100706032703600d02e50389220070188482da28054541c0c030310041e68000c0a8000c502c075901405585041c0b80102d041002400405000c5c40346801c40108130f0303120040101d8001542e9111038200d0101080c0d10308020120150002898140440001007110f4680b0030034040c40e10b1916181075140c007a014034460001f0326100c03458407030b4019105400d0350f8440c0064a0450141860b440500d400300141002500314030003000074551154440031300550341d1030751002d800c0090b504054003800c040150000710301040012030141911020180b5140281c0c00600030300440c00c00001040c1c440c0c1c1a40a02c14150040c1d091010315950303503d00290a80c013034070315100040d4016207000c0c0428411002015014104e240c540941080e15118008104e020381086459070020b0100c0c0c81e0b07950080d012035154100d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 465563875 1250 465562625 465562627
    0x105030a051f0b0d08090f011404030f030c0b0a060e13240b06040e0f0a020708180616151a0108070c050703020405130b09030c0c09090703020d150c05 66
    0x150784406a070381070780c2d03030702c02040b042018800004450340d90060340c030072100a42005000d82e41c9141000013a0003400c0468002c2040d00c03c40405503104611070f0300303400c002201c42c1e07160508680314002003c1c0c40d25020303018008198280d43c002000c07401203502c51101d2200000d001410141c100f00b00c047c1c00b030400000d02e80c0000201010942d014559154114442c1c0c50187c210009000ca50103800703040f02140e8014804a00018101d01c21038489104421203210303d44603039103851001e0100d019201c0050604a001c0c00410040c1402c40c1c52500e4401004100034200300d4141e144509213400c1402c2200c69a4000700d19101c10005400b500030000410300d203921060030000c000a0000c2c000902d910b003040301020114091100c184150000f860300900f00707206c14505170700e842c40030350074001d41160718001e5040042e0034048044281d914024106000d480b0080c98070040100003031001c5e18041460044080010059030b40c2405512400e120307040914900b844071102600702c0700820044070034440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 465565125 1250 465563875 465563893
    0xc02010c0509210c060304030503090c060a0905060a1e030606020c0406030308070c03030615081e091b0307080f010e06070207080c090415110c010b063c07030302090108010503 77
    0x150701054075650125a00030b149880d18500700c0c0704d18102502c10020b4100d08000284024140c3c028000c61251030702c0412202c204031011306102031f6106900c03144c0000740660b24240318910f4503c0c0144022034240c40e0115036109004103460a60030f88000f0100820707540c440c1000700940502c0703442e0344103104441c100040f0703181d07441c060100c050050240d4200400050707484100760207684014041c0c03400c00441400750391450f90291039541c0503101c0382601034490781d05420300005003c28620541d411000f41600700100e50f400010151507959080d8140a83e103008190070104010102c0b05240d1800003058413202c001c1140e00740580030f424001190000c0341d080c022414000740c900d00da59415035050000d640c6030300b820182c16543c2a1110b8000e42014014940c120005019091320751a99008121760408402040214401c100f009241441380c0c2a104058400200300743c80b00080401065905000e22120440143d00c240403c034042680464040c5465034030a40700b5001d804140c0c01440c0000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 465566375 1250 465565125 465565129
    0x203040f05010507230f0f06010509010905150f0f04050c0a030e0613110105071a0106020706050c06161809090b01051215060a0b07030c1101050a0c080903010204180c02010c0509 78
    0x10046195010b2900c4601c424011900010412a8011a03814050707407810428000042c1c8c44080a10506105003120170000c20b0401041c45800d00074403203200d0b01c0c805500e141060054484003010010752004594501d01c80c0f60f1164015580300d0009554500d80d540b032910030103811120504002c600c0755104034200051300b108652240080358210110000c00401503004a4840c403d0a0000342132241a81e20110041e0380c45410034161211902503800b03050b20341000300c405000c0d8a49241d51a13004101041040c81076000c3c6909141d00d903d84140c200c42e0120640380c1d02c00c440c0d400301c0d04d040da4520000c0c080c400d910150a015000031100c480c45401140803469032010f0f00f0180201e99464003001c0741156480d008040014030762511007585810b03003424041c200151804003920552001c000d0080c0c84e40c030680489100082940750b003045208181c441810a41211000c1a0075641c01c01002c9080d40000740c155200f0b5811714004140c0300540070000b030075224040c148500303000741400b140c0b000d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 465567625 1250 465566375 465566393
    0x5010911030103060b150d0912020d09030206030a020705120403060c0f0509010302030a0e0f0d1701050d0b09070e04121205040b0114150703020a02030d02030c0d120209100203040f05010507 83
    0x680c0c00c007201090032185e000000b03c3d0101c0341c07121564150000164040080b02035000400020700079801c1106403505081c05a0f141d6898062031400981100300500c01031a01c07002450300f0880309a0014108070b00d50791400d1401107100c000c65103080d40491f0810400800f40070340a8140c00901d000c0c550003040800240980c05001c8070315041c181c010000450100d00c69210003518402c7c031003114924603109108944403480a03800344000f46105031000d030072050003c40c00b4120b860240c26241a10800d1721401036015001e01083c0540c099607000040d81d6844685840c000e500070a044140100742400180803020032004040d01641418100000b05801440c82e50449915003100144006080000368100c04d0f038901c0c6204440e0301284440c14503038000384544400e4425000c68145068070340003039989024161300d002e180d5010010440700f5501c07030700140004000590300541403003c00c2c000680000e400c00104001a030010904009001e20b840301000105400e00304946010503035100d540e82 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 465568875 1250 465567625 465567629
    0x8010605130e120d0f140109180503070f140a03020706030c0807080402120c041a0a0b19050a141606060501030e030d0c170a0b04050c0a270b070503030a050109110301 73
    0x10020086040b240346865500072803134105d06400104104694800744800d101c0080c041d440b8050b240a0404003120480c038600311101e0303004401142001080d0b9907030450b40c0c4800300c0464140d60a40b40b0341f50300312010009503409510030b8010780000b900f0510020201c580003c0103004111a0000340702c1a590401c403241e41281d0103503609648211b05a003003520341982091030036000b920b0b0554003510b0000421071079109034402c482d806409c40d501c1007419260302601c660360201403064070080018071f000d440180542c0341641080c061150a080d001049600140803003440119030030803901c20441c3c01c3c0701d10009007509003001c2198080180354661351307002d01d0f0044401555101c030045210b074014443c070418100d01e810f060205241c0056040080c0103003802072401542040045840c40082106550328284030b035580c240702c00f140c105c2c100030050300800c0c80305244503030800c00f0940110642c01810120301600c000d5659052000ca004e0440300141e121200311444c28000f9101e07126800110b0341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 465570125 1250 465568875 465568903
    0xf231b03041112210c07090e1203060a050d120906091208130801020c0a110f011d18071d030304030812070908010f06092307050c010b03060108010605130e 68
    0x19650340f80e00f0300070b490103810b15024841002450044c0404504e01002000d6041411007515001c9640f000c421080c0c1d83c0a1081d2119908007841a000141120780556400f4000600005401d907940b4013207031140a0405003503400b0400c3e48c0821952540040741c0200401709440c140002c1807405a20b2000303040000b50050218400081188103600710f01c0c42c0e000070705403110013103595030400c403192036640b842c60344200d4011420103801140341c80c280b200219a0300c0b0603102e503244007a82441c0080c0c20800b00c44545c1c1d101d40c54095030f0300030100f0600400d00c82c45080d00e90416003c510010400d03400301c2425207900c0f0754030410081c0002060002600d12025040d240700e80705442e0200c0c02e84089005030003020080d841e06c10440e4503d40c1c0c64000c50101c0300950000c10001d60320324030204103100130b50306400c034180c5502c0200d00360611550040000c80f02000000848481c5140001d04102c03080c0c0c0541075980d11010240725034980071040040204054404021100d020030245850701c480c100207074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 465571375 1250 465570125 465570139
    0x8100b0a140702090f240102030306101101060314190f031b0f030203070b01060503091509010f06090c090b0c06011202010e10031505060408100f231b030411 69
    0x401005a10903240143d50082206034140740a032556160318030102d4070304214182c21b40b100b42141c0e050110048000e10182d0296203035651b0351050010030007851108104100c0c003080442d081d040207220350b0019520644000000740a86406145800f00441c2102440d60580d10048006144c01e11001591941400e140300d1081c42498901c0303d80d50316403405801c1183c0b2624a104040d8040014006140b0507210828541d80b00d000448450208442c00c1c00c1385d03031007203220300c007866005560554840240030020401482c80d01e03001007690400d52000b600b41d5101c00141321001d8024000c200a0148100790508000d07810b04142e81c1e0b0f404c10310403600380c0c0c00805003920559219111200c1d02d40c4001d0640d07400f44205010080080202c2011380301d0b0b600c51701e503000c40c00e8682001290226a002c900420311590210481002410112620740040303548a05846403103c6403274030144510078110703600d5402d140020700000505c0e540a812400c4e09010010080054012042025603101c10342d066 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 465572625 1250 465571375 465571397
    0x20906160c030b01030b0703050a09050606090405030405030d09300809010504120b07080c0a0c0b090c03010c1206090504080304110102011104080706020717030412030507120801050108100b0a 84
    0x100303041d0015a08050001401c10002005101d00c2003000ca0207002c241c0c0e01000f05a88808414007142e151351401044c42c0c01890220310300d480c0424100d030f0010b0065007a20b2400d03941303030002890001d1240c40400402c0344180c04100c504292181700c2100200301e54800c0714040741162a03001385030850b00013010640042030550761a486507050340e001d01181c01041c212a0303072504000031003141c11a0540009800500018185d450120658007104c2460308c41140b4041103a0b00c11b1006803004210003450310440da40803100c0d03039090182c42200b207201d8458448100411096101303841c1d50780c004400c514240818040003842c00d0084a600030f40001c1b0020300c01e55100300403405454480e40000e101840810301290484000c81e0345011076481d030f021110005d0b583d0300460309607100c60200322107a42051208115002c800c03d8400c0540e4031a00d81640350260903569a1440c0392203042c51400122030380014003032560031801e83c030f800860a00040c5100703860003120707403640e00c907000031801001303410004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465573875 1250 465572625 465572633
    0xc1101050a050105010819020d020417010f0e030324060a08090d050306030307021c0b091c020c030604170c0f1b01050c060127020304112706010c02011e030c1202090616 74
    0x64849089c405202550f545680705030b800e05600701460a0142ca5291005090082c0428414070007880601c1000e1811507640050300301015031240141c00b6010400584c140040d95180002d20018085490301038076814201e100307030310780722800c007960003401410414040c9594000040e1084641e04840d202400400000c0582e4403110001000709114602800c0c800c000d000840c00c0503080b402250f4410724044c40c0c0100b00d0f40c274001261000c1d00754000801040128407002c4821004410191403149060103400c21140b40500d0b40c401ca06040d00084844103c1800c2d41103411903004003441c1c00c40c03c1600c490600d40c0c44110600c904070050355028030740d6050000d440307204500d074806407400b151a407400d030419030705503541104041e11951803034901040c5100000d04429910300d2041c080305841d41d80d01c005480031140500700303a0611100c07012082003004076a1107d1704004040c0d40216440015a4000d042102c10074004410540144080e01a58071103c2c103440a0f403000e03000c0d1103032071411420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 465575125 1250 465573875 465573877
    0x617010b071401051e0a09020603060904020607150605010906050415081b070606150309050307060507020a060509011527150302032d01060f12020a0503010c1101050a05010501081902 80
    0xc030001c0c5509160405c0100307036903242090340800c01d03031484c15840e80e9040084801c03501d500d80300a50000060000c64100e0500010b21640144050500c0d807404007180c0b140718040340c40c02080207660b40c9440c4280041e581c4055640700610450408509050800005207142d00020768080c08205112000036030320800f00349104804400114215540c6242c0c1c00c0c6040078000c1802030070441c030f0040007150700c50b0384284074880d045500040a50700f003120b82e07550b0002801006c0c03d0081140308084100011075a107101e82c90007409d215000151000f03070f01003000d214464503031180301041e45c40c4100c90907003540144042c200d88658140004e40c010b12918210a40d409600040d4040c03045608031604542842c16540c3c414001032640107400c4140f250b280d0aa901500400c810508600f41c00c11905284040d0300d00c0c914401001c0500042c0c841020a00312401c0d10f2080000400c00140140201c000303200c2e807500906047c2d000c0c0070365814080040d000b0b400c0034018581d0100d01d8594074181070b099078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 465576375 1250 465575125 465575153
    0x304060b0a1d0906011d0405030f13090b010e0604060f110d05030603060903040b041404020d0e010b010e09061c080705030a020106170d0801030201030e0a0501140a060617010b07 78
    0x34034008000b501e0316282c4084190084550038145a200d0101e5480c01c0c001a10904980551801070740001855024201414000d0b20444103440280079018481204401900c43d10344c81c40c450343d585510780705080c02030725084d51219041c815205e645246036150b800844055a0003401d12080b0160410070445242001a400e240140644401e0707030035441e4080d00940c01480120100d0b419500da82031160b84a103d00e10a0000740380d0100401c0048145034008046250340042c801428050710920400586003000086540c50350b4076144542d280d80c002404a079404415220340c000e03450000040340f840c0d01d01620101040c2c00b214000010011510202ca507580d621000f501d8880b501c40001134060281400340c5c092400a042c0301011986000540f1500c485469035420260b91031a00190010b11900e030b41744e02d00d400341340402008600e003402507081d072001c0c04822900b1450040c00b07c104a076032940102e82004013400444021a41c00c5010030b065a00a07480c090f540c402900d0049400608a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 465577625 1250 465576375 465576379
    0x50f030a050f1c080c120703020d020d0b040f0b0924030f0a03140703052b02040f0f05030303010e0103060b04090210020f01050f0c04031b0b0f0d061a0f0304060b 71
    0x940042c4006a102003828104940c0b1500302c0704281c200498161010b21301101c40c80034545040c402101c40a140b00071079034010145050061034503024411580c1641d109011040700207483c4e040d070841c00d003020302c650700800790100d2041003000344100000c0d100c11710107411008a40c02d5800003181d00500c0d0b00c10300141c400300030201c0d1a1920810b05503603c03140d0700107003a800301b400d908116130491102c1c400c6802c02581035440b5031800c20406074001c020072070340100d1018030850303034440c2250924510041c4090420b40c0c00600f03916142000f443d00583d81504224007070740003800100030300f64120900d00c1c196540004007037200c94600c40800c000b0000c10710060741c8814140a0251425004181d54000c007050000034056135817940c5000c03451400a8880c90001d4101b0001000032407091001881810458000034804550b20720100c110340d000480e40b0752140f500054108040d680d94441c1100410085101444d040014882e189480c0035404111801c50350010008040250542c0302034620080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 465578875 1250 465577625 465577633
    0x5101202040924050d0803070309050c03010e01020405040b0418021507021f08251803080307090609080a0f080904020d06091e09080a0507051504111315050f030a05 72
    0x24124001010414030482400fa210401d400410702d4108000006002034020458503d10307241d0443c128000c01080e0b070150b0302406001e8601070030380d0f400c0c0100e00c00c181d4903400241c2c5a40c14503081004031225618404e102d20725000a002003103c030300340420308890301202c500e4200404c44040340c50b28410543e00940c0303e0003458000a0300441148403040308c107075640e5000d50b00c0d51007500601c40a40102040e84151610f803410300d41d410f21449503800c0d103018089a2905060b035991355040c0c0c44e0015103035940445c2d504981404000d500840081c01045081c0c0180304141550301c6203038625090100c0038003a840c00003403000c00394072a9012200c0001c0000703810411680d843c104600100f0220011281003200102c0a01c0d155155010710b014081c0c0204000b85003c0140c0c400755603607406960211042d000b45210b2084401208a05e0ba201368000c500c1c245c0c2c00444101045520840340594951003454414481660716121105405803107041d6080c2019002000000e4504000320030000c3c01031107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 465580125 1250 465578875 465578891
    0xd09080d2d021c09150e090103170708070515060a061407060204080604050106061e120507090503120301090c1d010e0103060f09090c05030304050102100f140702012301051012020409 80
    0x54440c0311341c0112a45012140a415001d250898042407000b81c4141c0c050288401440814241040800d085480b42c0360280340c034803d80e5a540e0103402c08030003500d1a4001e50164516121854281071b03004c00b0444128000d5800e00b4070190074000c900546280c0c42c00c0104100c81040416411074016001e4207040b2000da190a01d0680c1c007814142c060100040c0034100394044101030400148210a1982c44015141300809075004c01084010203000402103500e40c00541610103206210404800c07001e840c2e07a96051100c004240c03120070803d43e04020f102c80d40c0303503640404e01d1400203023540240303003112040031a280128003400c9240c00c840305081e03036600d0004034a0900c0d0b0120344250712450030815582c1e59201003603240e024034401c10380580c0008481d1034031001194407640407a54410707400140303e16141c0020703004810465095016039076900c40141213400b640804440607546040303c00306507040c040032840a20a080c00c010071b00400014500080b0340c90740668001e4030345c00c001001604 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 465581375 1250 465580125 465580127
    0x3040302041a2e0503041110020a0302011b0801031104090c080705040e011a19080307030e0405060f01120c03020423120109031b060b030d09080d2d021c 67
    0x4412a0452489591101e030800d14030302107449002c805120f8041a081d040b0b450311000d99569200a0086034500c803680d015580a42c0d41140341d241c3d203666540280b03103400a510f800707400c58502e42d4906034100c15070092610401d03072001130141034a81c4a0803604c0420702c0c40f00854040d1400c103a0040850040300d00101d8080b10014104e811101c1c21502800751284240803036080350702c14420008100c003106000d60440c20a94441400440c203d5000100d1130365403a000303800e40d004030344200d0004481c54241460380c9001d014031500300e0801c964204005041c03000203031002d0010001410525210405001d110f4020f0741034900a005035012445400d0400c0261416642c4150b09188141c3c6a071100031003076041441841d881e568140c80e11681c419801c058000316401d1781d007080b500551a813a000c0041d4900f40f0100e10484c03205d0703c803510098249801213003440360710341c000c1d41000010301038050444402c81d8000b40c030403017031401203550380d0108000724207051101d6000300d560f8290a001031642 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 465582625 1250 465581375 465581411
    0x150f270a060e071a090d050f010612020901080f06040605150d050304080607021c05161a040c050d02030a020603060d08160b060405160e040b0d08030604050106030902011707020304030204 82
    0x581442c01602c800a8460090000e18a14032807009041c2e141070001a109007000700c4103800c01070007003044a00d0626140540b0f829500950015581c49a291840204500300444440e014000403005400c0005405040544e940c5005001414003600c410100f5003040000414140400001d080d2248650386400d10680c0d9520501c01e2301004e106500000701c5840c4042030810500105041c5e110785503600c001c003150b0b660003401e5a446100d004000d1540020943c1c0c0550b1701d80c07404a9007080781440c1604003c101c1400b00e60000740a0800000111b0050741c000c2004140240e0490b4102c1e141e0f210780e00440e2211401d250010301030a00060060000c114558254078010f10403401d0020341d59901003032000b69081950f20301132074501aa2502c4509028000307103d010740e80a440010f40c0d80726030300001c115520040c0e0560720050000244075580c1407900803140076081034101444400c2c60355000030500064040b118844010f40c0300422799643c802c0c801c031801581c005006001d6088050040104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 465583875 1250 465582625 465582641
    0x10f020403230d0f03111902070b03150d0c090203011d01090b06040e090f061003060608010b010926010f020a08070801050a06120e010c0e03150f270a06 67
    0x80154408010705402d07090300b110b81a03880101000d41245400e0040550720b08000794246000d140d11410b8104d02d19038017002810010b1088080000c5508030301c14007030708143d002e03044a145881e0800c2000000300b0240c128100c0e42c042620840ca040c6c603a82401c050009e8160442c8512500020001541910ba5881c2e280200b44a242c3c915007640e036220384404640c0031070310168108030140020014202c281080c41d5005083d40c2c1540d200040b0018224103160303003250082c0000400102c2030090100c00e201d0917000d800240002c1048014460020340801454416aa40d001251303c070a4280c41c110b04c40e564a00f980a0300a1020710800d6403140c001c0c2d0070440328503000a01050019142511425401c1d048034805000c02d101541040e50031038801c01c012420900c0e003a15492401956142403180810f208001d50351500300d0f100c804101800d010009404010000d424030500c5030340305220819941040301380c403400307405e0810002c81c00d0360040e40d01c400707003028041ca1126100b4031903580c1214103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 465585125 1250 465583875 465583883
    0x114010905040c0f08060105090c13031b09050603190c0317030402040c0516350a02011103011d0709031a070909090b04060b0d021504051c050d0e0f03010f020403 71
    0x1240c80d45499002d0f000407551700c82c40070f076540b01400410903400c04c4021746422035400d885052800c039513001035503114900d5500840e0600400080c0840000500740d804015080400c2c4c01e0289040c03080000c1e69901121070405c40780d013aaa0100d20420202c041048019540989542040c0c90201007103103154100f15400ea0049041c45006074445108604440d40d81b940008030300054011030302e409400010042c0c0e0b000740401c28807001c82002c0c08115181c02c55a2060005655402071303070000900791030703060b000f074002d2800a2006001004203d814038004103990510500107585040c41101c02d1146a4005802c01030a032521200c80340151064900c201c0c01c540b9684103065503141801c0c01c0750611200507100d032500e5004200090125082051101e100500c181c0010170180c0001d800880b0900c0c15540c1c07a040014100b2a901f80445407280c12000d6106d00341d0741c20510b4076090344030041408070100300a02c0b10070031202c65881c0c0d64450440000500200444d107400c01d1240000e6005d408251 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 465586375 1250 465585125 465585143
    0x1a030c103605090702060a110f04180b0301050118050406060906082b0e091312020304060f092315040603020d0f091a071110060e0f0408090d05011401090504 69
    0x224050403c030f20780c079004140c1d540c002c110960f621040040140902e2400040d05901000760f0030901c03030649d0161000d041da524601400c034454a00c01d4080b25070340c080d03143c02a41008010001c440580d8034055406c0d121100c04142913075249080740c02041d4a8001c03200e25443c06c603021131043d000003015000c40101c3c00e21041000121018250b8181c000402c40000400f070b6008507096090a00156030030140c0c00000d550280d005a41340004130514030306c6200180e00c0030900300b00e00b642c00b801c580a8a03c0508244602c18104242224408006900b854889207210404001178030303241c280386403409010f0300341c41d00c41da00c07590018043c0d4040d0064003c202e00301440d51000c03d0051140d030200f181c0c0300241040b10b1140d00130106240c1c800030254418400b008014490900042c07004080010410701c001900c9800c0441d405501070001c0e1130f0714407201c10341e01008009568031b030032102c80034000c54000c0c08418061800d01d01510940c00412034605080000040c0000190080c0e070085101d15280 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 465587625 1250 465586375 465586379
    0x306010e070807170a0c0e130905070e04030816021e010501060908070803120c0d0504060c090801140106033b0607020f07050103020714010912031a030c1036 69
    0x2111007410030078004e0300b4070359000c0200b001c0112541c4100318181c03660400301250724071800000e03840c40082d15030068903525010b070101000b6060040b000034141000c0e0b04645400c0c075481c000d00c0d46d88020b0000720307a0b4811515144c8468001c110290024a80300c2241e90301c0580700c80ca480c068102803003840c0105191210115031400049840c0c010b549a00d0020342c140000858449000d003405406910a1076003000606182612401030500c00e0340114004250131220400c010f04120340c80c2d010000591502003148101035800b00c0740c0d81102c14615001c505074081240c0c4e4a040344140340c20754000500002c200c00201001c00c1c82e005489002d00c2920042e07528150280d031034210004001c0c3c080d410030308052005601903400361001030b00503104049036504060045084408001d4156442c8405660400d5940c1d4103009140c032901d100c4074196610030750103000c65603171121024203d2041d0b40c2c0c07100c442c0754603204918031145041c018080c0e86030401c8136508e98624040c0400ba07924101540200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 465588875 1250 465587625 465587627
    0xf230a0e0f010906080f1503060c0702090622050711030c0f0f06010303140d0f0905031210050a0308210f100503010203010b04150c080c030909010801060503030a1103090306010e070807 81
    0x65030f41100c10701e4540d607100b0b0350382c00003010752194000c10348070052500b030b80d0601454800b00000b40c407400d03034401501c0d507440090041005000c0000c040c41e114007036246402d09041c5001144459800200f8004036098541c540156059800782140d503000c1d1002080000c060341000a074580380c00c04240960b01c0c0745800142240c1c035400c09000113004690900b041148428841004025080407608001507400080221400340d489642081c1c0e4650320118000b034620300c21a1290b0b0b005207400031089002441d000c00f145810480d440050711021000c11084034000c03c2c0000080da5150310031341d94171245403070108290090800d482c5a005405045000b2902e400c05200b1a4160345007840c24a082a141c0000b141039040402c903110300300440120342d440040d2141c0047c01e100800c1a024546402c1e42d107090003041c0300143d03c01c4d2401c1e81084400c119a0700d021040394403040b56444c0c003e0301c0707075a00f17003043c0e140d0b00c04d6510300398140c4a036900010b55100f441e00818041c0d102941d5000701600c038020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 465590125 1250 465588875 465588887
    0x80109020d0209100e0a0e1b0f01030e010902060304050105010611010c0e0d23010e010c03020f0901180e0703050a0c0c20030106180504060b060a0f230a0e0f01 70
    0x48000d4115101d003030214058074021144940c01045a550301c40302c640c865101890b0401c0c290f079006441500c039085407618130828070810060010b02c04508030141980000600703842101c1d05a181070542e180301651024800790408144c070360b009004559242018a00a8020a424890100020070b811204400b114042c010101030f10007545c5d40702e40c500c645000300300542c0c030b801030100c5030300d03409048080d03102004020707818060890340c00018034644040f40c1103003907903403008000c804c041c4100300c410400f044072425512080000c0c601442003006111650992610541242844440c040d003002415030b8103801c414424010b03c001400800060401621700200c0f00d0360080800c0c84150f9404101d05d096210019071540c02000030906d10358410064101e06284c00307a845440d525402000f0621085d8000c00b0156002582d00c1c40c603000c0e800c0402809900709182c003004000d003240b060b89a1549600c03110015440c84503103940d036500100700c05010030f503001c1502030103060b00740b900d05003d40c0904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 465591375 1250 465590125 465590141
    0x8070209010806010317030a09060e010c0e0111060109020c03090a0806042904171606050f0708010e01060e03010b091612270203010e1c14090a060f030e06070306030c0801 75
    0x2072900e9811006d4202c0303000e03050304000c0074a4030030340e95030b142c035004240c1c1c81c01480b050144031800041c0c0c1d0415454000d0003407244d84082414008817a03001e4038030160000b0034030304440d02a10b00603160000c5c8404a4154400c4443d92540101c2c810700c0810450000b04980d03018034466031242030000440d40340d00c14083c1003117405043c1541d0580000e00030802d042c20075040000700b00c20070b80c90300d528800121a85408240c054dd021035440082040540c18940242e81180d45418101029854070350703075200302b1105000d20340c20811407209141e160f84003508014070201c03004084202c0d81c0340440590f14002000005200091840d100900d17505029201d4224122030451007004052102e22030402d0f01043d54100326003640d45c48081c00d03601d10051100c1002c0418400e41110100c00c5004020710016080307508400c50481000a03030001d030342da030080c003003111070901f48504100341c0030100341e00518000d9440d02030b5020311001c104546038182d020328183c901c0380c0701c1a8030f02e9803540b011901701c4c0c5100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 465592625 1250 465591375 465591383
    0xb0c03121311091b0f0414180105100e04020a0806040b01030b0f060703050403120504081209100c0f05060a0c031514280602060402040c0309051f0b0d080702090108060103 75
    0x10948802160400400d0294000c4450114000640811410140300c2d44011441c04c5c5108020030140440e240c092044810080101e40c03070380d0703d020a07004800d507004d0107110f050320030300441a80d0001180215640b407109803000700b0031034444682c60710281100504644040c411403800c5254282d5600038131a541110744042c0801204c0120041480802d82c07090320700f6400e00400340800030000c3c50a4410b2241d00b20715907103903a1983c5c60300c0c03c441d10b4690310416021740031109020140c240d44900c3c950150103281c1c3c0c9064112107a50f801c01401007010148042c00350300a00040003410740c840e03044030420540321340c0c00b0080000450b640d81c00340d0740c0b24010040172840b42004c6082900e41100c83e40c02c6014030000d0f080c20510810b1488840c1b0a081e031000300541c100c5070070002503103424441c491185000d8141842020070315aa5561030701c04105990800c0d02401014020814855100b4040400c0c05030100b503010009003029162a0070100b82284110300e4000041500900410300504a07a40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 465593875 1250 465592625 465592643
    0x3010b030a180b0739060c02100f020d0506010504150f050903010921020f1e031309050118051315060512070e010f0b03010303050f071707060c09061d04060b0c031213 73
    0x650381b100040d003806000c500852040c041c01c03120740007851042040401c00f0304c1d8016618050910220141c40004141905001d410700c400c001149a46c402c001d92000c1074600319603101200801941c60303000e0266229010341ca0040b105080204240f1003074500700040300300320100c41142c90100e9540042188080181d08800c040c99118035219840800c042006019039091881c030443c000400c8920341e11900c3d10303584030001042040c40d2082c030083c0360044480144058075142d80302108800c0780440c020842c040080d42821028803070344c0b004024140003002c00340d41201a0140e5030b65a07160380224210459000000a0410b81a0315171000b1030746a691502d007507a04e59241980c064001c1e0007100c1210b4400c01510000540301c520901551000c02040c5482c1c0b003d5003080da00b00d1300b240c0540310a005810704288a401e411164551721109004ea400e9605440307003021402820b4294400040490007199542503050080302400060215074000c90003a83c4400090110514002c400b030103600c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 465595125 1250 465593875 465593987
    0x1b080c0c060906160507050d0302031201050102190213060807081b0d0c060c0606030b070f0318030914040b030109050a033e01020c070906060306050603010b030a180b07 74
    0x2e071008648481c6005c0d0f070641e00061b42c0d0b6000300c0d520b0810550210300513000000c105001c001c030542c0c1e29014110030710040a000035402603000740c010b030405010b88500031000d200d1240320055000030018080940588100550303c8040c2d9a8600100459946506980400d07407a036040c092503a408050f040b00c80c2000581c9008419101c0500c0c510096910586030800030000c2034055200901800150f5220300d004d910707244004003180c02c107400402450502603080c1000c00da1060343d003030640340103902c0010000e100c000010000e240001c510750309542070075040d0b002d02030082118015280a61244441c0c540003850600191142c000007201d10b006861800f4600842c4d41c40c0d1441c200680030005180c410701c011311506c0d100f40c0768400b05841e511008240000c40c4d060140c500103100a1b503100c2c0c11541072595100035400300a0000c02100c3d43c41d40c20b4200e050310200b110800e10f42160040f686070134111001800000d1140103086101c01c049903040e01030a80c1d80d21019103a1040c001e0050b010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 465596375 1250 465595125 465595147
    0x5120309160816050301140703111608030411090403020a200d24060f09020f1204140d05030702030304030e01030e070801090c0807180c1b080c0c060906 67
    0x2400180030282140320303001c860200300c0005085500604401001066940310b5404050801001038101501a90500344038420102c0480c45a030f800c4400c40c280410a584060843c01050207030303405c0c600c0d0525922200d8410b00000f203000f14050f40c0140b0380d200100b601d00003440940801542d0060061b8498800100030810354804094004070700c20a40401158031000110a400007060956060503001041540403070028030700512040307021020710a0342d20380000006052044c2c420085200d400240b00c100095405007280c44040c08201c0e8041d590815085c07011054001580d03089407403181441c140042c42c0600b041c2c80c4606050b9000b14603607a55582d04441d80c441c0e803800742e0b040c15112184070348000024480c1d00301924a0400018166050b8100035a020b080366104800329009a001441940c2401c00c48210358515010080358259907603000300c450200e0082800c10074580344c2000d204001418005009800e200c00031a16100b0151040150310b00c1468801d03544100204000a445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 465597625 1250 465596375 465596377
    0x110703080c09090a1a030d0c0816050616030e010902100e03010609054023030738060d0c0305010207121b0b0c090d0f080a020d0503040512 61
    0x4070188403070441c244010400030032280c0c1420358841c2d2a81d911442d02c400d18101c840c3e01d020504504500070298181a480041c0c818241007501800a9400040d0a04010303414000810181e9102084802c245801d8422500d00b0004080060001c0e00342040400c45001c140075082600350002c00b015060110b84800f40e4280d01e4180040344c042d500c42e800058011020300c600d61240c1c0980c41c080c0c030424040f0007041a40194030b030056026402c00103000d18034100301c0c21042d001a42c441c500d00c0710342c0c41c0c10004080020000020010b81c1c480050b0b500108448010700c281c2d0401540d441d0707421a48001c0c80401c03641050143c40d03a0318039543e0002032991905681c9807030100e00440101450a032261607007403c0e80e01450065030140e4a0501c0400c4590340a04440c03002084820b46c200500d0807036413566100c4002030090786903248041188a015640c0302d024282d000d60040c4050040c03540e42c0760070302e440d03003149441d0005409001c1e20000d4003070080c0c0441b4030403035110010300f8160070100e080c1426 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 465598875 1250 465597625 465597631
    0x5030c0d090f06021308010905030901050c0715020304060f050313020114251704030b0402060d39050c0a02190b0f030f060427030e2e0311070308 64
    0x140d25001c803000450104002901c20900a41d8056524202280e141240380190352100c0d11a80c942070794135002c180c01005a5030520700034600315645100034080e481c5800f040b034000103c0440ca29656506481e00040104111405501c90002c1800b80007015580c03400103c43e40c2441846822110b0015842510301031034200341c0d081d403181802d09060049901c5010440d42c0c2c080d20186011400030b0040340c03695002c6030740c003d40902d13140504503940c0d540b2403100940001c3c019440403d02015100b2241c00ca000414008039007a1001400c90614100038034002138402400035411089015152041d0100c880a5900b48010400c5181c0c42e400c0c00004054880c40303043c0e00c503a00d1004101e00c0c1c10741c0020002480c0c8121440d449080106210300e60307403405400b141c401c1b07290400d007202206103041032054981e2524840c035262800e5040039131b400b820703150503140d00582416503029002544440003c5820354500e04460614400c0010380072141600094280741130140401030003c0c1c400c803082d1794 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 465600125 1250 465598875 465598897
    0x90c460806211905010b030106030203120715020a0e01030b030c150d1113080c03060f1906091d01140f010315090206120603060a1a060a11190201090b04030305030c 72
    0x655000100c41460500c4040001c58240d118a241c0420074401309001c2c0140c0d501c0107c00800c802d520710b6001907540c40852080b89400c450108008080c842540020380d03018881840541d035580400798001c241c1c140c400c1c044e50110b440c0130300002850800040c0210307441340190603a00708076007030801c0c14076070342040313990201d050340352010700c88020603880c007514a08030314400301c0d42d800c0d080c04030503030820070350700304241c02544001c040101c3380ca682c00036950800e0f10700c0c203040700a40880c0c00900203004c4079006040d0706420440001c00c0c5c4020200d074580480c05e81e4000708003501d041941107400e25401d540c04410310079004014004100c220260501464403000001180c6100742e0201b490350708a400c101c03072241030030020014581002d00000c1d5002d00c401504201d0311500f0328540c0070f07141a42c02428042c500204402070064001c0c40000b08011102040790b0703040c050010b01c2c0125075464041240000c000402c005100caa03641c06807030659601d510381c80d00356a5028154980b542083c070020b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 465601375 1250 465600125 465600169
    0x50f040b03030c0f1f0e0615040b0307060909060b0906310909060606030c1202030717160e0d1101030c120516090b040b09090c460806 59
    0x401d070707207508000704604410b05a002d8000c0031741e001c09044a8507244500b40100070b0504211501c3d0110204660740e000071402510b00140c00c59101040080050f0710075a07405100302c500125041340c1010180044a0002c001401016201c0d030500c41c40380255144950043d8051000703920791120301400c0e11401c006002c418003112480b580031745d81d00d200da911207030703d5a41d0f03004c030ba10070f11a035070186101a1115060900c610001000000c0003440c120318208650303540800440d5010384240d040c00d480c644182c906c200d850500749155a525100d0222a1000c1030312030803012140e040141e0b84c6142940c0200b40d1a80c1000c0b0701d00158064403c0400e041e0411010b4421140070140e1449024003401440a02c046041c60f4198040c004c03420036005001002030512003000409a82000c44040e9182991840410341710300c0e0a030b03081405903122403840034098084213910002e034584000319610024041c0140081c130000924100d50b00202c60b100000e502c00000b030b10700d041010500780d044050600c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 465602625 1250 465601375 465601387
    0x60f0702030c0d030c230a060f11070305091003140f0c0403021804200622170615010311070204091109090706020601090203070503060909010b0405070302041707050f040b0303 77
    0x10740c80305580f4100b100420345015841c42441740e0002c03203802c50401600740b0100c032402d020140d40d070703402000740091070262111000d810301c0040d40c0000303107c1b0091000c5140c41d40d0440c41e014010741c21240d80c0034015051202c01064a5219014080105100e80c90701c40041d124500f41c901c401d4001008800414410480000180c6032065100c40b10601c031901c000f418107103450803c1c000340316500302d04c0521480c0301030602c86589e04412100d052140d00100008000303c030801c05140304042e880780404554031601c0202c1c1660108815100e000e6154800404583c02c50040d0f040700c21040b482075404209001d030f8801414a93b01184d00d99000341d410302400401000040d00084044641c4000368024200402c0039607010840c40f409403c0c0c0c00744c1907040d0300d480c0000421601004044611403e0003002050040400798804a454400900148158a0700107005400380d802803151640301c6848038a8007481003008902c51064450050000d1100c2c02e42c0d00800c0b01600d12a0081c0364140010081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 465603875 1250 465602625 465602629
    0x4051525060504061d0309061b07091d1209040f0914010e07090209060a030b0105070503030a0203061f080105130b121506010503071707031d0c031605060f0702030c 72
    0x1444a100744194400304140c41c080c6400701c01d48190b044103640140300140d284114200110680718a594240c0c2c1050311003049404145200d084122425154010b190b00440d0043c038540040c1501c450030080d80c45180a07003a81d841c2c0c5c5211000c0f410f01c0d002e00c24005101c0c41d141071f4018000e8001d040c9004a64012070380c4400798499a01c0004c0c01072699034060903125030301d0500c01c1400401246004504000c142c601003852031060004420070503648402d10940caa0103a01070312801a040310460343c132854070620410085d0b01c2550698880d10584216201d0440700da0200c4c40e6007601c83da5205416441c24003846040e04185c580405095101d035001c0c030994454030030306071b242c502d01d00c000c2162a02c907403401e4082c2c00e0f000c2d1085042240410821010329001303506910780b412800c41d210701c0c90352403c20490050540300c58004881300b00704000d80711540f000402c4c0307070030380b60840944001c2c103e1013541041c0f5100502c911a00320b20144604242d41400c44090103807540080c055611701c5240c540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 465605125 1250 465603875 465603937
    0xa030c062f16050a031a0907081906270b0a0b0d0b0103021c0c0324060e04050606100e06090301060812041a21071112091203040515 58
    0x80c11200660101d414594110702d1030300b00500400c3d081d14032202042c21515024510303030720b0080c000c030742e03a0840000c24800c0c0c8040003150024481c000c103680500c04051781080d210501c1c1203040d01c105050890300d0003044080184801d140e00502c801e05000301c580d903101c0d18603140c014075101d8042d6a450200b84580c503001d040c002545e101e03061340b08040d8110710420035800c04600c00d0300c405030359003040300f800914507115031015660840d8102410328103008024ac0c00d5078403d501d007240c65040000001d0b0821101264500491154003038409070383d211000e00402e0b910f4421044000342e07903040300708aa41065001416006030203800416003035203405055207880c484909107925500001002c1144003800d840c40401c02d10251441803424040b03800c4055504a032003035204020b200c080118240601840031483c6009460055499540900c010008113410412280d40114000f41110041000200c121011b45000600e441041110496402d0158100702e800c00418044a200b00350703140c980d45 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 465606375 1250 465605125 465605207
    0x5011e03240b1c02130e04061e0c020c04091e14120405100905010f0302030c19051b0f0a08030c1201080a020a170706050c1006090c0206060a030c06 65
    0x118902c0e6200420500070030310102080f410354440d03205004158100c003441e030802e41224203154000c0c0058503207052010060485158a50f0194000041d800d4200304a81003501ca0780c80039003d0318035030395140d82440251070400f10002d10100c02da074800c524403028000542d42450152840c210302d2503500f0fa07c10b00d468426400480c40c444086010851071406000070540c00d43c0750303e050101d482c40e11002818170056100c1e01c0080c5034021000800b90003190b42515040300071410f942c044100e06c02c4014010340e002c0c462030110001c140c40001034070f010000e114050380c8070400c0202b07030051094032401910f800180103861996800c1040b000406103000c0b102d0302034446c00018018461507441003003281c40c8154081074102081c07869040d41c0c50b4001c2044030480b83c09061082d41c3d0b4194010b09820080d031001d0a00b5007518003000480c03161070551210b544000d003a001c6400030307103404040001c0500b191000a00c05503d0030070030b004003031052520141001c1c0305104954464003841e40c10ba40b100d014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 465607625 1250 465606375 465606389
    0xd0b04140a18080a0305060f06070f05010c090f031e020a09050f1b0901030b030102090d030e13090b0c0a03150b2101080a11060c03030711010605011e0324 68
    0x1110a0020103426840b90507504030840803030031000109560303420590b01030042800d050603a1038000402a440304001d919404100404165841e8140e1425080d2055280426030b01c1d50310303010421b01c01600032050f080c00e0326035060040c00380e10310715900d10303281d480050380d105010843d0001000c0180c50b5000400007801102c1c0300450740d441c1408818250300300c01001a104525501203002c0000c030540d00300e6400d0300d800e20f000b04071450300101081c064803958030b5560300319109164400605078048044144800e00322000820001041c0c011400e450100c03001604001c64032001c00c035448078400042407010118200464903c000340c103404c0750300b82d00340e01c1a009500005040164544040000d40c10080d0fa10010000f95041940c150381c0c600202d10b00801d004001d080c840c10a0b80d46000f0340e041494417004980d40c0e8500580014100c60072500020030541c20031601140c590b0048002d0304144446000d034201d0000c0e640c030100e002e41082402815070340d8568844c10a001108441e243c080c1600c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 465608875 1250 465607625 465607661
    0x9060f1404060b1e041814030c060a0605090105100912111206071409030102041e05011b150902060c06070e01110c0a0e0712020403060603060e0606010c02060d0b04 72
    0x5801c2c00e10a80d198102d08510462075580406800c01c00d8030148070124030103940000701000000714445070380c0c01c0e40c00c0c05021103049515440e1407020000081c008140c4032820340d50682c03500c5441c0c3d001d50b203450140a5200000000500c01d0742010106190240d01d01c0c03034101240380c1c0c0c0d112001a44956400240d81c24140e00c1307150b00b4203040c1501d2100c80c1c1c0d1000c01c024100f034500500010500f1702425150700b548039001070440c0c1c3c556000d4040c0c401408000051007079080700320210b01800010b600c11107000c2848001202c0035105207584001c07600e50420111054082c014681038001c04050300708a82c012414401d50441c410100665403069020381c60b03514000058030000f400000c05461005041e90040405190075110014403001700c9034842da014580e0f840e80d80080e00c400912420900c1c106101140010510885400c03a00459009843c02c100e54581001e485032150710844069002c04c40c004200350060a1a2004064035080381c2800100ca000740000541070340e07a081131845425003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 465610125 1250 465608875 465608881
    0x9070f060504051c0f02040b010c05010f0b0306090f030a0e0a030807030804020a0911040519030b0f04120504051f0306090c091706040201021b0a050607050a030e01050901020c0409060f14 82
    0x200342502e921503072807002e51304c40006040e5550b000c050407403420090103941c9a078140b5425900511612060590040007403041000d0701c1ca85500030300c2c00c190b4061091144a000c41c0f42080c0200b40700790704401040107903141c00400300e404d0b82c40c102e0100e82c11360020746404002020600841c05482a42d209540d80e501a0a00380100807800d031464000340907261800001c862041c103a5012182221000d54407036148a003c2e841245c0f03403000c070380e00240001d040d0100f08000c001400b45840e02c03d600c01c0c46040c1340f406440c42c049480b4001c9004d020b0b088028a50300072040d038190b04941d110014580380c0402d0082d100c070310b140190b5101c00c0d120004110401e1092001c0c0c5c090040d019024040d2a00a00d043e00e040c0c0c000075501c0841d0602c0903152000d1204110040c0c40d000800000383c18003038800e036038a0450f850207556403404843c040e4005501200c0c0d01400350b1140c0f044401c5031405900600d00240902c04002c01007908950444049a43d002c4c245400381142c060301c15a80e003480c00c203c11700d10b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 465611375 1250 465610125 465610129
    0x70f02010e0901030819050922021b0a0b0c09100e0a0305100902120a0b010e04110a06080f0a0504030206071115010b041518090b01051c051608010b040e09070f06050405 74
    0x240c40c031ba4991003400018000003203035440d801002c0102c460034180f03045004900e20300c2e090003807080417405400d0b9200740b00010858803002404080c0e0b075100e4492440541e03500840c0460a0107400c401e0b40e840380300f10041d20a100e11403500500e1305036000b054440c1107642c82d5100b501d040c0070f140e450807019032190150025490900302e41003410240c9005824280d5290707403440b410080c14090701d070010980c84046018807001000c4445140302c090000c1c0b15587d12214050b02c084ca044644100c1c600c41440090000c18103030080e280a00d07415001004151161003080d201007a490a0091240c41400c07014aa0a580a1140380c002c00c0700240c402d0740e45082c115a010098040c001100038418984e12544440f42010945021100e02600c0091a44100380040724980700701102c4800216500c04c100351901100d0b4080303401140c41810890081d000300c0d0081e143d4030750901c107080b2000350602041101a481c2440d140d03001262400b540c01e41e540780c07410f50100001a42040d0001040818207100c94 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 465612625 1250 465611375 465611407
    0x1090501060f120c0515120108030403150b0f041d3408061504060302101709010c08040f0309030f051b0906130b030c04060321030e03070f02010e09010308 68
    0x1900344000000c0183c4240d0721407080b4100756110301d82c016180500400384954565081d900543c3c80c8110000c150b5940b454180d40d00d0300203000a4808810740160b4200401d00e40c0300d003200020b400b61001001c25250010003000708000c1180d205640c0c000c8a008502c13030401d011143d440400c191151610b2201c06494503113440c03101c0000002c2c2e144a09060000751000106180c4c4412480b0101c0340c0300c000200480c02500682c0c2c80223410004403010100301c9030b00101190120001e0170050300d0240e551407991801c0e2210702a050010860281c0401d01142081c105003814a0080c188610026682d035102404044d05203c1621150001401c41103420811030a13103103054012102c02e0124109800019458074281203281c881c0b954402c1d400d505602c0034864011a9140240100300c8503a0b281050b480820300040040084508010014215802880359092183d46140210300308881d40c2c1d5440813801d060b0078168140300c000580601c0036034a00c80000d002c0c520640c20162540c4000e80400a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 465613875 1250 465612625 465612629
    0xc1c15061a0c1902031b1908030712140702010806030106030c030312050109051509070201110408010b15031b0f0909180d02061603020a0302091503160306051005030402011101090501060f 82
    0x4019010703043c4002603580003e00b03285541c0400308100e59500081c00245540610311070700105510000800154800044003a1071001d00415010540e850030031412660044007a800021701d240030b204000140d441000c500e039102d04040c0c0002800c40c0ca0741c40da02000c41c4280c0c4100e0000c2c150100d9180742c907003903014107401440f0348030b800c0c040c604188007040303003034021010502d0250b07000382c00051429100350801c4805501d00c14040c4e07902d5480e030a03c2ca010b8160740d1241800348040c0781c40010071401c200100d031311807070b00c0a11071020311610410150941d801440c0c14440e210003800140f4182d40c03100c583d07501441241007200c1000143d11903283c1800d941483e4a001e41d0040d80030030842c0841c1c0200740f0301c2c0b4002490016034895403004160000e0103030b0350710305405c25400c489600c00d00d02c1803001117004d036550042d50074001c49001400c0f416100700340190b40e0060201020103807524041d002840d00b00381305041004042810204071821114945010741c2d0b103a450710b40c10090f2007000c2004c400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 465615125 1250 465613875 465613903
    0x813030201120903020d08060310050115090b121513051f150f08131e0c05061c05070c15060e0601020111071e0803090705030c1c15061a0c 61
    0x4108010740f000781d1502000b007114420f010040d0005500d0727a80034050340d114070741c58107400c00c000d5840e9100343e01c21256601e03417040492880003020801819100a4650820092000942a0342d92100e80c980060003801d40301d42120358240c805c04494107600450b4400c210900060091102030802c80004450760b9008130091800c10410101642d400740046048540c2801c041c1a80d885002200d6040205690701400514070020355140385a0180c00078080d90b406160b48100c0140c4540821204d4030072121708083c240c10b040800303000414607401c0b8a40c1f1507103030704015003070403010384810410302401010641c010f5561001400407aa041c0b0440344c0042c020b03c003c0015443c0740309480298030914601030001105501450603011420600c9003110380d005030b0135071304c9040c484d00305c994840c014041c05100340110000084982000c6261507401504006c41d5a407048054803a100420302c0c10300c04068240e103075000412064201ca03140118854100c40440e940c0081c411400d00b864040e0940720 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 465616375 1250 465615125 465615131
    0x60d06090c06020f0d030b0d060506060f070506150f030d1809021603020d2604050a02060c1605090c0406030e0c03031b0c1f0f050909010e1614030a09060207081303020112 75
    0x84880c1c0c860704900b15208da030007600041c0c544c5a91000a0f86401000c940d1f006004000800104000c00404d5041c0501120300003000600441400c0200044603200d01c50b070564400014030180610a000814001d602c840f914807d01d6180c031081070a030391110320804140b080d04c01c001030805034100400c000074642480d140149007900009038192030661400d1200c00750245000c2400d0020070721000c3c0d0060b900820403966801600e24082d200e05002592400804141100007020700300007031050300c9190f030080640d03e01400c103c020f4005000035180000640300309140e8070141e0310300304014040180440031103415101854203075850161074425050080605003c035240f040742e07160390409100420b0420081030b03c000c00701201d00e400352100316544a80c4034000012580d007082a0a0b00514120069201d0140c40e090296221110303944c1d8440c00c3d0b0400c000246c100c0b18103a000d20b000b507102d29400b43c600748064440c501076810840922036152200c138410000c540e00140f00075040000f0b05028 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 465617625 1250 465616375 465616391
    0x92214250504050118090f05061903020d06020a0e09090f010b19060509010c15290904140703050111130f080a02040510050402030a061a0c06060d06090c06020f0d03 72
    0xc00d40c0c042c500c00d0905110010813040c1e5032108850722503025000c0e030003080006015444024001e04820344001d070148040c0d9265101e03408824a05500340ca0b000f4000710b0b0040b4660f5100e1000350700500a81d8100419140c0500b21561803821141c0038006000c010004507007020813050844400c1d2010034810907080700803c40c00a94890702074111812410441d8580101c400141c03003194141800800d007442c0151201d0b0000969440702c4150751174a0510b45071000010303501d11180503070440103a03100130a6800075000540d10681414900150300c2540d40362681ca0b600e06007074aa20b40030f0400f0845010403141c125280d4243c070399005000441c0c44a072114603024074540c4444003108041d001c1c2d0f88503c009038003080380c064890010a8007070000c569078500800510700800103030003100d00c0c40c1c0c00c2c0e8040c2c90107950603030156980d41c00500c1c0540f205032900010030a80c44503064003181d00b60344882140d000305900714030100082c103660300a00400e0340009480750a18804c180c090b402d05141c07004c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 465618875 1250 465617625 465617627
    0x9150e010f0b0d080c0102090d060207050c040c270812040512070302011227120801050a0f060c05120a110d09140d03020a17071a060609221425 63
    0x112104560041a840d130b1714a00d0041e4a4007900c00c0c2d6190a4006501050b400100000d50f40242281d50041090740d14042648041000303495152541e0320005512855480b04684401c6d0408080081c01344c401400c50782d600380d07460400307084e00c8546d1582003011230b0030001c9050480c004811a400c0101504980e810340e40082c080010b04095122000c0d507176549441c6941e41e480e122042c01c0c050300342c0340f0076540d540d00c3d20840c4022541084000980c20340d00008450600046500986600140c0001d245081500c102e07810b014142087d9201c0c840c14881c0740140352080020720b242c3d41c05170f88400c0003545003052907140c01003140904080100901c3e040003601214107200c80d5885003200d650640a40c2400c00320301e0301c441d00764040c201c104000c1d01512030b0004040280b016910801788880c45140002c592603c4c480200d8000d07030800030030405008640f40142081e204201030810740f8049810300c0c00114129115811501c01034114001840308480e0491820248020303907004d4541d06003407800c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 465620125 1250 465618875 465618889
    0x40203010e0c0a0903050303040b0106020f0106030203121309050103050105041e03050403020d02031006060807262802130518150105030c04030b0a060512160605070609150e010f0b 79
    0x1402c000c090011814065081c0b2075020741c030041d07810000700c07612400c080c204020141c0b4288514409441b134041c00f0021a6018001c00701101d40027405040890300a020094140e88a0f0543c495903424110012030920039038400c5c40c4c040c500a07000001e8516091926a0141d400203200c3c092107031000f80d100000a41c403a003102c0071340780d050b2420710100c6464404039150401002440202d141420004129107034400c9041b44200c0450f910094080e1114590398108400c400d00d04800050000008440d0014201c180000074400c904201c041400400c2c44002c1b0303000512a20a034003400c0c0740401062911003102440c40301c0402081c092030500780908090380302d0300b070703400b07070501c0804000030f102c4581c001d060394000e60700650048200d1030644940c40007000203011703076486200106030045408500042192a10342c1482510399040d0a011003524079400c0001d00311111504d64100c0d000160140c92440311040039040041030000300d100d180f9080d42c40c914410207a041c504004d0780b02070390740ca603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 465621375 1250 465620125 465620131
    0x904080c1203131e0204050a0b1c020102070306110c1c080f01080d030903021e0604051e12090d02151215010509010c060e01060605120708151e0301150f05040203010e 73
    0x8030030984c1c0140d01d0141c07440f05111901030750091401d01003105680d51600144901501101d02d8000041140306961502c40c0d00d9001900591048000380005591940151019012300c404c0c0c6080480e10a9400d02d40300f10a81011945001601046d41858100d0300d00c9402084000602c01150b040c060010342c1c400394080780c10100750b00d500c206001e05001784164080e000944092454000300d440125581e40c0c02940c04441503c10034440282da100d1040d03072500c40c59200c40c090710349641900c44440281c0c0009011a50104800c0b80100c01030751908441c40c036024004000700c4d107555010044c480000401091901c460318003c507409041c1e80d114045403800e0009003081340560f081030400d54011b004020320004150b20741003020440c2038201028015205c0300b40d0701c01c07207079568035001105e000300103039030550b41401c5951401c00c940c03a000c08803482800811034004c0000b45e1810000c0e081d5428188005000680c8100034410900c00c01202c1010f88820380302581396500d4600c0b41810a81d0003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 465622625 1250 465621375 465621383
    0x601120b011a12101e031401050f131b06210b01050a051b0303040506060319020306070c03021c09050f04090f060b06040315050601030b0103091713050904080c120313 73
    0x4540041d682c240f1840d0380d840031700010340691205058221412603911340030b000694030704652010081282c4014000c00d8440d00c001001c00300d1a40700c10211000990600000301c3d004070782c03030703007a950f10042071401017004003400e60f42da012081514820294030726812464044a03820a0760324082640c102d01158039449151516507070310b04014541c401c2c481c031048294101404000184018007800069041c0182c0c41103059841145034078000c283d0024683c40002d405420810004204a008000d0101d070030f0700a005950040c81c48420039014078030904041e001103540032000b0b00440c2001d91400303254410075501040059210380700e041c0180e50075840140340580f581c8205001da2944410781d00259400a401c203c0d024080d510740015100440f0468006031810043d90503642c0709000d450001a001044a44203e4a900a501656201d6617441d0144103001c800001c0d02d1b00c0d19101e1511490040490940300c09003584860b040240412603000340004c2032040c042c02054015500821581c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 465623875 1250 465622625 465622657
    0x140a030c1e050102040f050414090d1d090708041202010926071a04150b0616030509031e0d0e010f030c0903150506041103011401030b0f030601120b011a 67
    0x300803101800c0300707015000500c03a5001080000e4450160310182c1c050769021181800a15000c1c0c0d4504005101204d10051035800a5030751003005029141a2404000c00d50300100c181c4000ea020462000040d642a00090828820041807103070018103042034801a200030710203490705440d43c1c00d44460000c041c2c074503600e620040300ea484168100300c1d11129841224203d60029040241c480d4440c120740541d024036030140c000c01038240d5423060741c07a0410018006402c1c00c61512801c40c660400301012401e1150400181c00c850760200b0180b107103000480903000c55040d418040034207003445c11000070103000c03085000c00500c0e038210004039241c45a615001422200c6803c0480e0865152341c0050841d150000c407180080354290040c510401c000d45091000e43d000158815040c03109120711414200c0d042c0c070800b046c2d0b11940209072042002065100509003107000a42031040a81c404206141c90101c0c640402907010700e070f140100411440000e0680d0410000380390351203036035568041e03030030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 465625125 1250 465623875 465623903
    0x207030b06060c0106060f0305070905010c030c0f0b0112061b021e0106150804110901051003110c1506180103051002030a0f0c0909060b090d0b060328140a030c 70
    0x680c1000d5403d00782c008802032007550b944c2c0202800300010a0801c2c0d00003420500000c40507801258030004403034041c1e499540526140d1800c81d240300f00740e04111002c0c3d40d01d54410b07000c5400c044125028000000c20020509090b1800700200ca603c0744c0c0c0307030345d20785154901d1415550700807a20041800300003002a640c8002801311500402042c0c1025100c8040e04040d0840190b018400501c618414a0720280c01c001103030800c07881107002d01c81e296100c5840d5007508003141c42904242d000109031b8038002d003130260842000d814104980844a0306003030810410160b458001c05e039524240c4c0c0807104460310b50454880a8035164641006104c95030000003240141e031f040da1099201e03410b0f80404100c0c0311046c0c180180926810b1048010715400e1540100700080722108642c000320005007041102089551441e61002c402400f040c0e00d8016001c4d9880c007089045181291009007125203000202149000c40480030501c4444000307921441d1440c000940080d42900200d400c6903028124113 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 465626375 1250 465625125 465625129
    0x20409140102070f0308010e16030c09080303010e0f130b01030b101508040308071b1401110a030203061f0c0f11060d02120105150a050a0203161104050c0a0207030b06 73
    0x18090325101107610008a0005100f00c0c00d241079800745c442e0355110b0941e607840c1c030403210f400c1c025180310711071020030007a200745c1d00d00079844101540010304004030660340d1012001d0a6800c01d900038030310400030302d0820200d21003042d0703403652060030003249000c04591511076080c0301c2c0b014000100301e0782035000426070718100d038010720b4001c0c0b401c001c089400b2408680020004a8240c1d4224007090440c401b060245000d90030102d90003c0c08008480c0d0540991035038030b00380300300c1101e2081c9035507580036039420240c0120090803030011315200503941342171000502110b0240e0106204081005070400c010003036120a101000c1c40d0406503054a686440c1059a403400443e000c1681c0541c00081a41c421129600544000014258040b020360303600c5041c8804c02512051130b842c046410000880c03510701800161081020303a1040301d00f46404903071840907125002d0400c2e109034007800d0820b1640d29050207041c0c1c1c00001d0311000750404240d400043d40ea0011400b00807e09400200014031603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 465627625 1250 465626375 465626393
    0x305030924031f180b01030e06091b04090506010b04030c0915180b040204080f0c0d0209071101061a0d050714040b09010201020c10020714060105030307061a031c0f03110403020409 79
    0x20b0030404003443c1d003161301034031400014912490038901090030320122048481d00400c1691160f21b0680141503102c4142070500c1e0030f401c41000d4960b0003030792140c590700400e00030010203029040c3d14050503541d03411400c1c0109405055070103100789a040030f032202c584034850401e0904444814820040c801001c1000c0d0300503109908070603800603c04907000411240008510316090401c0040c0c4500754444802c7c0642d00062441c00f03900041030501182c040d502c0341500241590044000003506078507010030f203030a020309110380b1254100200d00e18149284900c40e03150010254145204849814900861a4022032091005600c000700c0d4004a90b4002e404840039a102401511030140c0603040b400000d4016041c140d5218500a0f20252400030010703003141a82c000600450034401582c3d903ca01505180e10340394104180421032203000c0e00c1c1040205016210720380344c2955000c0c400401055140c49416980c105800c20000c02c4d9146055001c80d001d0302e0301500c01007200308003401c00c0925 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 465628875 1250 465627625 465627629
    0x31418041a0415050f0312030c07020112050702060a1103060d0303020f0f040b0706110a02030d180f060c020c010f090509060d0c090504170708031305160305030924031f 74
    0x115042c6208299580000000c0d402500c0044945c88650507075002403650324420b1101c10b82d40b030502000450840c038404c1c005008150320501d0004032400390040b181d02075500a0791040b000d40e2200702070110303600c61030042000211280c0c0b4a0750852034910000780780000d003000d0240a0542c0042d13040e001031200402c403044408962042950f50343d8030245c102417a400b01c00c06490b4540307841d11982105000c24121062100a0390045080c01903e800c860010004c096001c441302400454000c000340c8e040200310030160003500c000600302000e01c0d000c0e01f00030a440c201410080c031030b903030b000c0343e03a800082803402c1d00c2c070503103104c06980d8511012440741071110f0b20103845c0c80b201c03010000b00c600312034200c2c9210314421104c8118080901c40d5200d41c9002e9034030000c18004003880082d407025406c040d02d100c2d1a014200312070280340150f01602001600390002d880c1ca8000042010709410480b4203034102c0d000c0b0140c480000444003202c0c2c2541d000c05008001d004a009041c0021103115000ba040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 465630125 1250 465628875 465628879
    0x503130e0609070f2f1b040519020306180117010506040b010c0314040b07150b010201020f160309030b0a020403020a0e06010c0b09030408070909060b0a051509150a0804031418041a 79
    0x10f0b901d0170f0b41c00035617803100501c9030300807240400b020031140342c20540195405030080b0072080301c40078595000e40380690401070606402108280c5c2d02038600c0e80700141c80f13008004640c0c40c04110325405040900f55000201401d0085041c0012040c00783d0b44025403644d000e4240c94001d88240001501140780d04c1f40d90310454044c2130100c1c41006005948001d40b2000d04050320402c9005000c00041e401d03405481c0403080100814050124840e030f084e80c58180c450310a10701070000545903074494010107019141d0b440c80a034003007420300850a00b80701c1d80c0301405462101c03074080d103040740000b40496080303030b001000c41e0007400c00b01d02901020400e50740074003010800c0c1c1e0095034031070b400c2c5001800c641c3d1042da0714504158152074141000b08001c015204081c1107980700040000041155030f01c104d0300d4a402140d011004c0b0721040e4550003400c608642e5542b0780b2814102401c0c020003940300102d20580e4201c04100908441e0b9400c503002002c00b4017a2008284984c20800e070043e84505820256 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 465631375 1250 465630125 465630197
    0x1050903060f010e0f010b030105130b0405250203072d0f06090c051f050a0207120b0711030c0a170c0f16080c03190f0503130e0609070f 60
    0x58402210b6041d40e058036011a0741104955a021044101100c01c0c4039a210518003000180705600741050300f00954860480701144202c0c008020504581c0105c410864060019420412401c0032210170402c0780018401107051151a46a40d980002c820801c5030500f061081506a44204c9103aa158540d07003152000c00101068242240580240c90007140c01c980d820380041800d1900c03194082c17024510303081d07c1c040913000d148207580a5111140e20420b42c0324608000500c54075a00803007005502c2502c0d4240581015180503042c400a503072540b0b541d40080c03140704030f00322001800060540d0020131403181040310100c00d00f4540700c3c84e841002d003402406100d204028000460f0b04100c64648002c40c4107030307a40c030303c0703542c82c0c201c900034140e40341e00003000e50381c000101e8008a8811600540c1c019803070b080c0a40e601465640091000140700d2400003007009100101d000240d40700d03000b901c0859283c0707082c4100500000c1c07130400003418002d03000c5030182d051062085000e122101c0f10014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 465632625 1250 465631375 465631381
    0x5090a12020f01060504050c0d1d0304060c02091b12060a0909140d1809110d02130305060109110a08070c12020a050c03010c020616120203100509060d0209150105090306 74
    0x351128402d4000405035800d0280c00121400d292260a2003946060b884504104144140501504009803072410451148010720322030741041c00200300520040d1281d200c522100e205104480c20010036030f0f07008a90100b012803070b401c00b00d030484102c9644103176018100e80d1007900003860017000740c0141d85040d242c8240c0b60300b00321040e4401034030407802c030703040b144400e0b03e18030211407261004101002d001503205041101e910f183d08504c480d90090749001d410702188100c206c080360000405030000b40010101002403040034031500f405000c11800174821002a00031202040c0302e0402e10000b007007d0003000889003485001000c8596501610401020f984002d000359182d400d0081a100e5004600c0b4600c1a440c0510030301c180b104040d00508019940d03050314466002c0c60003108002d1084817000c1d003042100d144000c502c240308210070364400505150030311a02c5100248850300444903200c074280544e80e048032140d8022482d29620a0b041107480c012240f038000c8030300c200d415100b84c0c018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 465633875 1250 465632625 465632627
    0x8280302041409010303020c0f1507030503070807030924020909042009090a17070f1a1303090905070e03061009050705041202090a0212270f1005090a12 67
    0x801c2141d031003030700c81d0100c071030325400300482c00c4028440240960304c404080c4400d0b040484569111000051414a2482e00740b400145d140e440b00104400180d400010440c3e0650003600e1250800d4591904012380901641c81d03014503107003440355880d044007269121003a5402a012201c80c1200584803034800d051074944079044840704807003850200341180c00000c4a041414002d03106848038801170443d0301f070755101c1d90440ca440d51038210701c100f003c00c141c20115180700e000080f2544101e0a08018030140d06003045500740140020124030721a44190b00070a41c081e81e030f40207686000c0c00005041d1038030403003034411000c00c91440d40c241c002d1000b0029151001c10310502241c0e00e8060500103503481d100220340e948168016440c405401380002005400d1850105610680b8950b0043c40d00d004414000030034881151000c50305d40000008c98100b0856042000e5440e04020041204420542096480d080740c1c01c8035645d5541c0d0f034000610201000c20007008055084440c00307401203070703d100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 465635125 1250 465633875 465633877
    0x6180209070927020d020d200a1e02070e0403081e01031a0921031e09060c031902030a0e0c0108160c080904020412030305060f09060d0614010b040512010509030708280302 75
    0x5102c2461580c0b104200002d40440d8040340c80c002110340c0c0d01010141d03540c80052b40d02c4e0301c095160f01144503003800443c44115178801640030302c3c002d460704036091130700804901584914200742507445901000420011390201781114000403141400d81c85940c601d009145440b00d9540481418402c100410001103118801540155894a80c2e100740080000100c44450760548140180342d000c2400540f10f04024405948c000e103080d42500c0040005480301c1c41030780c00c142c4201c6210f9507124042600180100400c2c40400002e090000b4036142000c0100c0402503e0040c80c0c090140c032160803401c200d40a0122544120b00030011920313152644d8030f03406d40100310f1000300c0200c6d151a0102e07041d850204000c034040d081c02010501150b50744004c1c000f0019080c00c0840d1180c1e01e0380c2140841c1011081c0d058040d00030340303c4464071245044200030132070040314000410350b40340c14244045420040b0031100701c16044104a40d440c05030035084c0002030040024985450000203c140082c0e034950 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 465636375 1250 465635125 465635141
    0x518030406050c010e0601060215070c0f08270f01031109060706060f06021203010605070201120603050d1202090907230f0316050a090302040f0906180209070927020d020d 75
    0x110003040717640292425550340780d20a0003588056403001005041b91283c8400569000c150361528404404491b80d40308500c54408004803275004001c9a1215921403117183c24819166140d1246810400400410609004054198100364803405910b400941d8142203405000380940b903d0381e03609250a002000f040580500040c1002c1c0810004409200069a18941200000845c556480c1c048213440a170300802049040c011405030f0701031410300038802d14006500910107055003510640300180182d450702000b4002c58814070103858640c5450340b9440c1e0000c1c107800c10458890301ca0302044141e02060711070042c040c00c0012012051741060014500690704c0b501031030300000103c10300362441d00903403c8030303000504901d6040002d031405410a135441031149500080c400600d80b28901a41e840c464405202c8904001c1001141410800c0c80d500050b10320b004180f0344d003031040300da0783c0c40318031080303101c41400c245640c5e00c0000ba10382c100c4550b1403c1820440d0344061000818000d44500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 465637625 1250 465636375 465636397
    0x80f1207090e0c090d0812010311120a11030a0b090f0c011e080703020d02041e050f1305040303150e0907090203060307061206030210170c1c051803040605 68
    0x10802240605004490407800d45441d1a40001c26903104010000740f60051201c041c0d0140a44040001003055000100700c41d01011101100c1503055042045080c0d031030501f41c1d40a03080701908600c0c00c000101c1c121b40700c25403140411598248807000a0301c0c000c4200d4014042948503014020740d40310024200205184090985800d10300c410019180c3d001d00e00780003c030240c00f04501c40e02c9a0321070740803141d0100040c1801418045202c4000080b40c00640081c052124008015a0100c058014580043c202141e1810283d40030f0b1011420311461840b0140c152034440c008281018025004040c043c400308a503440c1072035407030300c4002800d0000d5541f411103016051003c1020f04890080f684181c1c40030b001403a40914054003261142c4088601003203036a6105004001650381160800901c04295695003204c502000e601541501c017510b0f004540c20100700d88084031490241d00b807201881c00b000003c3e507a5030352102d0a43c0c11f00140e01c00075507000005010401540000260003000300c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 465638875 1250 465637625 465637657
    0x50d020d14090c030c0d03080603070b0a020c03100615081801020d0605090f01050901123026040f0809150c0d0201060e0c0a1206141026090109080f 65
    0x603103001e0549030300581780001d0300164003040b0240881e01440403d40c10520160481d00099981c45c54080c0d103170022581180183c0150044004d80e180800c8141999481003800b001180e10b00f41a1004d050b265202100900c40c2030382c00a03069600c0d20200d05240720250009640c0c44000100d004002c1000e805241c0c0305510801c003247c848a10100150305031140580403a04503400c040c5500320319840e03d5000c030b42c4000480312061027110b070b209845c50103072180c04c0c0030480000c5440000e44190740180005000e20555141c02c2542c001465059401039040920320b043c4c00718900f070070742c201d04c41c002d0030940196008040c4443e503c071b15801020450380c0c11042e56106240001c08a083e00c4481c41107044288103800420381065a02b4000d00043d102400e00c0b061200040d02c4405c1518030f203078880c4006000d03031141d2000c2d07403d00320034815280c4624a80031400b500d030546045254500100345200b056901d00005020381403d5200c83c04454122041d10784580042d030905c042a4007132200c100460f04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 465640125 1250 465638875 465638893
    0xc140a091d092d011a010207080d12051302040203130606090b01081609050a06020f0139111b100c0312150f120501060b040b0a050d020d1409 62
    0x1120366a1140030741002c038094400706066400c500c10050811115410b151800d51200120840902c255058070103503505407120403420600281c00e150031507000c0c900503081124040d030042da0010075940d040361340d084d0019041c1c442418211114080f030310002d400920020a00a615848c0780400c800783e407140c03000340003254a6424030740079143d0000d4554049902c000101c0c0b0310b0302850004103c80c0301649000c0400c26915800601c5c0c910300703035210300056002216441040b202c20b004141c4020f8000484190201140000310f09181c04290b4000d0086140007040c450381d8031440c0c0484e01c0d04411801c07035046201078520401e0012081c41c03494880c009042c042c617000b40c041d14800e890f19405465506040e08581849400b9011184074000e034044940d20101e0000e4018000001428402210480c003295924085003152000e810200b0398100902040121100b00310440f42082114a8001c1e250900038948401134082c41207036006084c24002c0d074041c0d00e1094061035116150600c11288401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 465641375 1250 465640125 465640169
    0xf0109060b0706020904090204060f0608130c03080a09080313060215130219030b0a020c0d02010e03040909060b0405070e0315070c0b040206070506090c0f0f060403060c140a09 77
    0x921036100d601641c80e0306019400c007140ea0b0307a000d030812010140010403402580c1d8005001c9135a40d0700b02e080343d81d4120790705104070b607403104296a10245c1040350042c0c16010341c8a466011040744030061810b00e00044004056210f00f240200401c03180d003c49446200c01850310b0446541c601a201c014412030340d0030425500e01004941c01044001134680703a2031a03d8080c000c00b44010020a081260119800400a0741c0000058403c113299080107840780103004c0841e00b48091200b8070011a814110381104a030030200889085410061000845040524207039015140c1d918140e94424502404c12803c40e0704600303240408038048082d80c0318028219503546161030260703104000541d4132080d83c1d002031f00c0b5007551500030b4001010941064445d503500c0b450503000b00c2c0c0c3c124154019229803d028188440080d20140044408010110640c0d0210b00c45001e1071001130306481d1941d04500025000c0d40d181c01082e0760b80c480701a5a09240e03480030301100c2561082441801c100c1541c00006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 465642625 1250 465641375 465641381
    0x1302060d0209121b180a0b0307081b010905100816020a020d05031315020c1009121112120313060603021513090501080316030e130f0c0503040305160309050603010e0f0109 75
    0x240c209251790070055103a80c05804020300c1c00c00c84058142c0300d010000b2500c0002040350b01e141042144d90b1049945900d40010203c026130391180b2300a2a05100030084c0c2c503007225140d940104c0200c90080c5002111000702d01d0030951290113500300d03041c140142d050040c084010302c1100200080a8030007503071000f4002d22400c1440000c00143c1104003107e4041c034044041c1c001415440c038018410a49896140941c40c1e1201011a00820b10039004400c50801548054030801610003900d07840c55000c0074014184001084400c01c00e00311440001002043e901200c09581c001c2c001003240c00c00d41a4401c2541e06c88140c0903800c06011f58001189040c5010703281c142c80c150b50186051515031911086490800e90044040c050000da07100d03d030742c442c46048040d03204443c50102c2c1d8005038050b80c40845101c0410036003041070400c10007021030341000846a100c0301080300c840410041e801c0484080c59950000d5900c01000000002d080d902400d1481c00b995100880c1c04c8181d80c2e13004801c0031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 465643875 1250 465642625 465642649
    0x607150b0105070317060d06050a05070201060b030601091202192c070f1214070e0109140d0b0405010b041d010b010c0b01060e01120603030507030210051302060d0209121b 75
    0x2c02c43e55404e220b0b0248488040c0d00058040c040803001010fa940d00c01c241c070382c210303003c08ac550f07076400030060f0f6158240503c200400b2140f00c103514505101000034590070550140030240c0d0380100d10b80d01192a11201c0a00900c40307022010030f21601c40d40543c01611543c0c541c942d9880100c001000701c14081e60741203004100640f1280c0b040340c0140010f55012400101d000f10140e69481168013403403070848020706c00c024079070700c1d02c082107074000014048a883d504500948507000d840390010f40c035140f0084201c280c0012800c034141d5554544603015246e580d42482d00141404a40d207150140c8841c02d001d81902440281709240b4104011140c2d48039000c005410b20304450700420901c1e0040c1e021a079007417010316100f0840d50000ea181400d0362200e0b03200714000f0340001868011f055041c01500e82800900b14144400d081900c2d042c40c0314010480c01030b111b030341e002407805a031175100c0d0304440c0c014901400d29440e81a03411f2035140c8805050340f00028454400e50310b40a03510784103901e484 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 465645125 1250 465643875 465643877
    0x411040b09151317240a020c060c0406030c050903250b0d0203160e0306180f1203070e060f0a0f050403140f2e0903020f0a12030c091d060604050607150b01050703 71
    0x1021728204201145803000541440700140e801c1111203806501404154411000042100d5032185410401421103401011120810009118950f256075022030030288091407180012052050010104050000f9522a401000740040d90481c01c400e59005507205482c10b80498400d014800c1d0151080750b130000c4059410340088002501018020200040f1216610101c88804000c45000c3d880d00d13043c40d400c0801400c01000304940903a10031070040c407000d402e032040341c04c0032130901071019540603c41500c418041580d58142c90079114200780c90045030858034690034254003c0c5550f44805141c00b046d100d0380240c0d19004030280380e160802040344403542c00b01c400742088800510090a2000003102180111242503c40000c20070021002a01607258215442603038240541100c80700ca209200740300180300708120044070301c818807176007010030184030381d03a0758868001449a210f65082540d010002184210174000f040c20000d440301d03490350040240a071614011341f02d81c025100024 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 465646375 1250 465645125 465645163
    0x40b090106050d0e03130618060212071515060e191404020304141f06141005130f0611151302060d0b0406061d0411040b09151317 57
    0x616080c00759210b8401005101e041e06d08002ca014840340a420480c2d0040c4009216151701c0b52a0100c044059001400140010002c840c0c041001c8002800f5240000d0030b0704403881078142401c92038ae08400c1703004031019100c122064a0320400307011500610340d100e0280c11095041034210080700281c40907202c8000c103185000e203c69040201940c0014000c1b80e00054100da250004041001802135101c002c0c046502510460070a000403101c10741c0c4030f810f03000300c080342c1d42220345c94800148504401d1441c10a40d03d001841240e100200310368013549904218400018141d40d000c850030034802a040c043e1000c4045280340c059184c001500e128203000302c41000342c0b0040c40c01c80000c0c05140c0e03180c8800f040301503506000a04591341030340210041000420f800501000c990036071100da0300100c400f0040c42c440700000b1100b5000d6800b40c46595400040d480b82a9070703e90039054a4002e041c101c05039280b0410300e16611000c4ca604c2042c411141842a0490b038500c04580000703080324025503a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 465647482 1107 465646375 465646387
    0xc2104061b050f0307120e0a06060f0603090503040b090312030a021822051801050411031218040b01030f1503150c1709032205040b09010605 62
    0x1c004120042142605160a0382d0a880e0401e82500d008070984421144000040201c40121681403052901071410070030160092030503620360454215030b05545407403d50130b4400e4040300a050340c01c24002403051000c1c400c01380c074038803000408403003084030840b065840560041c1d41c40bc005903000501d01501c981070f0300d89030402c4801511542825020340d000c01a0303403988014840340183d220804103440d10580f41e006051402d0300d600070011810300c0d180540301c00c007a402c1c80a02901030502c0100c0000c1c03140c030030f0316201750f42548505404011101044010091244510305259862240d25a195024442d150030701d030000020321656419410f101560131410040740a01e00e042c5604400d025078461400d45010b005440c0452290b1258041c45056004003108860b1500d0089202c60271080c142d410101198810b0b02e00300100f0500101340842b018090080b000400c400b0000 = true := by decide +kernel

theorem cover : BRFrame.Cov 465467625 465647482 := by
  have h0 := BRFrame.cov_init 465467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 465467625 ≤ n) (h2 : n < 465647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
