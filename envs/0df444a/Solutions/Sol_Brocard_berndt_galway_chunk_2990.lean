-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2990
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:20:20.069217+00:00
-- url     : https://prove2.me/submissions/30360c19-4de2-410d-be8c-f9a92c6c65b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 537589928 ≤ n < 537769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 537591178 1250 537589928 537589931
    0x160b0108011817030a1122080601050109030311010605091f0b13210b07020d0206010504060f0b0a1116060f090608070e061213050d0513052e12 63
    0x80850310600d42d5801072101d0b50010099601e00c01d01054405a900000c00d03809601e55510319201041a0f00b0340104071008600a84000b07000040c00b041c81d2024182d00008035580c00880140050790f0070121510661b42c0605042241c29142d02910f809000b10f03030041504201e2800038401002803041c90b10f0748a201440e07000b24076a444003d80039660050100703101d0740d100072503010042402e010450703901945001c0f845251920240c0c68484100e003058894400503400407040130f101c1075061003101e01501040350700380840c0d072900d40d40d907880303c040d0700443e100b46100040410801d40a00e69210b40e10000005a845151903001d442400e00c0301846803102140034110310040d024466105041503511940320352415445d948000c07240c050307480c00310b1a080102004012a50310910302c0d13461094960f19809405050186001401c184040030030009008080c0010480c0b002c00c5150401581c0d819590b04446240c14194031891401a03814210003200c400c01041d09103500183e410f5988854500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 537592428 1250 537591178 537591191
    0x91109040c03020a23040902090d06050c0414010908100c05190e0406060509220e160602070605040f1e03021e09130f0602071b0611011d1e0102160b010801 68
    0xf10105c060707900703910107103c000c010402071201007078070381c003a001201000e0300c50380081107140d50b803004640c41500c0481d034000e0b0200c4c0800002180448840d0841e20a2a040c069146481e03d000e80c1c031000700e0700800c481510740f04000303209407040307096410310511120144c41070300303040030b001d800748040c0303403001d40034030308007040440d25602410480e01c4c0004003901400079560b0081c3d035103074050140c1c100c414980b81c035007840e000c40c0c07042001041c0d804030745810601180e62908102030300c4c0400c1580024248502032004008254401403810115041040d8110741c22400ca03a002d451481c540c3c20082d0b01401c00c004054000700c1d1003200310801241a03071901b2079519041c41040007000c05050040c40028890702d14400030300d85801821031180302d031242c90315400240170111182d002c00e42040300050240550004209000d000b9104035415010400302c3d03681c02400841d41710a0794030000d07075841232860216000758400358104c030143c542441260045043c245000712101d0030031b2040c010158204038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 537593678 1250 537592428 537592457
    0x9050f060702040c0e130b040605150a0311040f03080a02070f081f020d02120a110711010f09080f07030201030b09100e09030403050a0b0703150302030304091109040c03020a 76
    0x110009880040140314a04144196080102411079140c81008200c3c80c4400c0002c19184e16805031a80781c000000401e02c56526028042210070603032046200d0090741ca00e0110080c101400c880358003c0c2c03442d0110b840d5240792840d0043e8400d980c0701e42410914208000180b20018002d880d4006c038660135140250341e50b100c80320213241c8a0003801c80c2c982004810b100c041000c00d03402c2202c0100b0903800342c101441c0000001c12600a07061400c2c3c106a5401001081c0c0720320f100303007440780e18943c02e003900300815601e48102d50954590b44c503051144940c142c401b034900882c070410050010000710f030188600c008103a62205e15a00c02240407a0800e60008a10301e40303c140b0274070420005000071801460701880000b0660040d1a10b5164001048044003003031040c0b10486050740221210100c03400c20714801400c5480c0e00080300d00000084105000503a004821a0200c07088144041038101385c401c1c2d416510311981c1d1a41c1d61162402500849040c0c15401800070080162560700c0d0018101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 537594928 1250 537593678 537593689
    0x203010e0601050a06110a0c030b0403090603021c0f02070624080303010b0f2d030f09010504050601091d0f0706020d050f031308071b1a041d09010e100c0905 69
    0x20300815503c1304400c20280200742c0300d10204820750741190200d131241c00180d261522441e0381c070f42003910204600c504010505410a40500c000c0059103800c51412001d4809000381c044204050030884d626042c03096a001a150180c4d0300075508040d0030003a2004510b010004401035001c11100600c2c80c04001a41c00404000d40b4101c0c5c3c0142103003450041016000310791303684a12a040351151043c5070612207500303408003801003503d04441641c0c2c0da04112443d411000300080c00b9049580c1088100400104045070040c1150300400010900309118034014054440c1e42114441910030b07500e11310f010030f80001d171400841c0c0e195000d07070380119024074040316584242c1150303104031003042001c5540344442002421440340141c5506050410756595585c1c1d03a108040040499004c20b0400e00031341035124149811400b000014a107003910b01030040000c020203840885080710070340c001500801084d08130884460400d0b0170794480908001400c002400f01403000f2000030315a140202d80b90800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 537596178 1250 537594928 537594931
    0x80c07050606091b0301080304050406050607200406171f090201020a0f0303090611070203013602060705060f0f090a0206070f1110050a030509011503021302070203060a02070203010e06 81
    0xc1c2280e65602d005000c0098009880021003030444403d40014082e1040914041d2119070061940c551038481080107880c0d69411051080f842042a000003c007200403401d04203c9003228900b14104120000b0024041580008519001d490815407608d00c0412007410f51403a000300c0843c0040341a41a0301103800c1e1040080c00360f440383d280c0b00046071800c400000700d10b119280100c0c042d143c1d1f84d5480300fa54240c28410011900109081d011442e00703020b00c40350701031400036031080c1658107401c100c41c8001d010320605120407134a110340295251310003180c415903006812900e45040040c4a0000c0f010b007210402a41107202e40402e00c022400314a200c80650014030382c0342407001c01d44030804100c14110b81101c0c902c0c4030802029a0751114071140240340059140d890b110000e00c400681912401080c0d03140e03d0f40342a4a05c95103e412884602c00d490301a51012002c0300140000e000901c1006000f1307505119480070004942aa0380040801c0d40c0709030001d1111320b01d90300409540c0c2c0700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 537597428 1250 537596178 537596183
    0x2130e0307080f0702060d050106020f0105070e0607020a1e032105070308091005070e1011070b07020310140a1119051e160302070f08070905060f090f07080c07 70
    0x2040081c1d0000c40d031040050591810810b8045250460590004099510080c0f4488100c0c0d25500100091901400b2103c0440c105c1802400549400c440043c0228082d04e41c040c4140c0021170300e001991900c624410242c0310701c501000d400d00c0610301d09003240482e44400c80d490807a0502c100d011940f18040740c80c0181d05915810308204a60307a013901c400c60014691902c43c410300040b507080038098029039024104945540100982ca0403d00110240c10900c50041c42030220310443c246500065690450300782c00d6200313440f2506803000030b05001c01e960308070003642c0c20400b42070001e481c0c0a50340c0303016060400f010040c2107000b030510703803450003081c00304800e4040ea09003ca0717449004100130a60020441c54240e00d0b0040403502c00c00d01d8221045440b17030b500c400d080365000c141d01005200003401c200100c1c005001e161030310352a80d03a101c2e0b0040182207a02c1d24082155902d42e0703001c0d00c154a83c0107158981c286032000c000e90322440200d0b040e200280200011400b98490304c0101d0350f840381c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 537598678 1250 537597428 537597433
    0x60c030206060402030601030e06040b0714130b0309150c03010f050a030308070804060608030711040f110d0c140c160f06050d09080c0a050a03090605040e150307090f060302130e 78
    0xa9030b9008000c02500014001414103448000000484005002040c0702d148900411080d5040c0b8401c01410101880d1548844107020400e194181508031660b408a0b1540d40c545941c070b5880804d276605008110035495105400b0800348001104a140594161429118841c6030a0382e00e0040008901c954800600843c1c0c900300418021031040c080c0a40c424000d44c40820a140c1d00d034240707441c5501c051030548034450302c1036541c130840c6840d009030040505c50030f0091001c85052500c00050b886440076155089a8420505003410f0003410103501601402105640300d04a07a65295128405402e2070701e2008041d05000c0340e802c1081807207a06807004c40c3c1c1c0d041c0c02c240c405070401c0c000385121002581c0d000010b12902030316035420400240041c1c4510003608109401785409040008030340c020000b480001d100c10b010740c00103c1100c96101440403409803c12980c840403d0070608660005030310719051041c3d1a08030b2a042d00800120b0303100b5183d660a05100d501e100044814258200c03040b82c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 537599928 1250 537598678 537598681
    0x50c090106051218070602030a1b030206130515010303210c02070603020c0f0303010f030c080f0616030b090405030c152a0d230c0901021e070e090f0106060c030206 72
    0x10400c3c419607a07009021150303e9403510600740c01c60f4078000303040e480f070001a0b10001e001402c55900c680842da803c022801c1d103402c07070303141d035500070f503c0d1140100000080240b0b882c1130001c0c0030082001040f08015003180c000c2950316800c00604e0303c3c141421a803800100203810b180e0303080032441544412a000e602500445007089000c034060750000151034100d02c035100004040c0e44050001b14002c6c52001101c1c1c1d003032850b510b0184508042640906210f40180c1801e020401000c909140e01000b12090545920b941c91002d500400a00451a402410b044100303c10004000b00401a880099080b84c0d00114030700c950300940001103840c54043c8200b00a1181001510309240c030001511041c120b060035198190b440c2222290a042c1100d0700020071040d48203c0401801904a09010216460901c0c42070020399113840314083e04c0081381c026144201082d106000c46e10241c04840d0501d280740c20012800d55503001c0401e2040482d518000c000a0103c2c00740c8505034119a058001c0c1115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 537601178 1250 537599928 537599947
    0xb0105210a02042d0b03010f0b0904020f070f0b090109170a0306180f1104140904240902030c0111060406020309010f0207031d040519020c10140103050c09010605 71
    0x994002504980c461030b02804003054920031500100281d9824403580c445958542480d060f60345516880a810400104014000c051308407040310282e949040c80300d5a1a0030610108001340f054046100000c48046401010000da00d02541d1203207018050140c21915151030080c2210143c07800142001c0e01e001c0c104181440394400390800e080c140c10300040042c0e48920903295a01015a1055810350751110004003e80c2445082c40800e008a070f1981050f0512031201915449402030070f108041060003e0700708520003d13000030074076462440c5841c01c0041c2c0b068030003501100004070701c43d02649802201e10352103603501d106000c458900074a20780d200c43e04d03514025440a0b002c00215502c503d034588451352907000424030980700b42c2e00d4200301e0941d0306100c01c842181046d8940302d58102400e0101100100d0070225002c14540c1e030051381c0d0700d03440700d055141c040d41703204141c0b846081c07104c422644000b00803c2e5040700e0195080c1c41e503420f0004100138486009016680101354181b00e031088 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 537602428 1250 537601178 537601237
    0x705090f03010b0d03020d02061f0302130902030d050c12030421170708150406141c020d0c050a06030207050303070c050c09010801060906050a030f0f151107060b0105 73
    0x120090041c0001841d042034401040e5200c2d800581a805648281040c0289540c1005065405000782c8910340030001c5502ea125611801c610010b84103660303481c0b00b141d50039045d91101480950060445400b00e40f43d410180080d0440c5000501a0060505856800749031000302c0f489180d0108011420f040041c2c422180706020071408410005861200207102c0e1000c41414028180c2c1c0c1c0301c0560610741040e80d001944e442042803402182444000c0224000d21a09803250031411280956010030030390640394000f00d009006540300e03484151400600420101c60010340b00107072003800704180c50300001e80c00d910607850300a01960082002824161140d14000c10f07080c861019161407080ba1400502035507000c5c1c11800040e55501c0c2c0130004035509124078001080107881e004881499512080d000d03903042c04c00541262a18a0300904000054500d501c04260900042001e03130000c01c045030380307500300e80c800302c0714145812421901c40d03000c0d0301960341c443c0d0a80070128520b410710410f601c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 537603678 1250 537602428 537602449
    0x1060f211502031906060503040b0106180b250f0203060f0f0402060d060b0d060503010e1504080901111203010e0714030a0905031308150619060c0305070b072006070509 74
    0x2110144e000c014120703080c0b8580600801020940e994030740b80e00346800c01030004003040e40800c0611048903081003032204d04400e2101214403d40740c098481e0385900d50340512600101e5194042040e80c984541002050b8075003100030340c020750442c0c483e903076200e0030003080090a407040201c0c0c40d0541c00040051a01478001c00c1d810000100204031156192003018098100340d0018003103644549040c80785040900c0790b1300d8001c13404401040030350800900400150760140010744082c00000c0c20b260503900401c1b40c0c0c3d41d0305807105d048596031801840582c5c80c40d0020300411f04c100c07006a0205000507c81e1010300708600d9a00030191560f120910000c005141c6100c04544078001482929909400c42402e9401419040d020309a0018081401458810024181c9218490042c480780ca90140703032032100195040381c109000e00b8601805c007030b11b43e0300840d40005c06c000030b640e04218642d44e10030105c04e101c10b00c408000d01c40d510318520032500d40304115034050020b4024803481402786403d1030401c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 537604928 1250 537603678 537603691
    0x1050a0506030a060c09030618021801050d080c0f0d0207030b07021f05090705060d0b010e04050c070b22080a030c09080d12020f04060206010602060c04061b020102010e01060f21150203 81
    0x7403556542c1e0801510b580509c48001102c05080c02402c3d07083c5001c2d1a1518080d078401d503a0158100380001d010030005500c040d095050100b2550341c0f448041044080911965003222400300075000d000b503650a5500003242d0440304000850001c41c00010a08111401a000f00c1071142019085c500185001441034000d4442c01030001040d481d0503005284010260ba40411480c03101800509001ca1f4440041d01503460182004402d02c1010103403a5080d034000c00e00f01180d140ca601c658040025611001c40e100c0014850400308058040204002001c0f500c050160000c950026070703116100d4820500303d5080002d844920511610344010701c0b00052000604201c000c0303010b41c500360010340008015031300240040c080150100402e55016a90308841032805040c640024141c1d40900d41003000b07071410b103060008582c000e41000c14041c0031400200500c42c0e075091318440d400348620030545111810340424440101c884400d004031a00700c80c2021110a1031071240b8029071005202 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 537606178 1250 537604928 537604937
    0x3140c0c03190908120f040e070c0b0a020d06062115080a12091a0d092907081006020c0904050a0f080301050901120f02010f02010f060602030c01050a0506030a060c 72
    0x10b100c08041051020399607030010ba4a40c40140d040100070743c0303041c5c42142180c80403501403181000724000a022142680d10700405103c1d25140c0d4201902c44c40481c5c2c2c401000315050700200f0007401178590140500c2e201e01c010030300060b607807030000361144901d41c1d80103061102c3c00d804000b40310100d41c01001e80e504c004290541e0507a51003a03e01c0c1030000021040f1460010045200d500c5588503160001801100341640b5888203c1052258544640e550340500035417903410102c1880b402a652040c2c071140e140c91404510414107116140790000c84e094408202c000d0b010800e00710322542d4040c10383d04030760020b015600c142c0701085246100100225a244504c40c50307000010490142d4000082c0704c1e0315a41d4032541003004011045105800c5048501c04a19150011070a1002c20114442c0c0a080070780c0d07181c103045422405001a1134030300424500b0080006001a03001000b0251a24600c00030800b0791910900c050070b9550a071086603142e40040c2021001c101c0030385c028083c4c6a11401c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 537607428 1250 537606178 537606187
    0xb120f090c0a08011a030712120e061602010809031303061812020f0d02010b010503060d020a0302041b03050a0209010807140d05010e07020d020d05031503030c0a0506061003140c0c03 80
    0x290350400d9604100f000b039440c1d407034050824170320f034101100484040380034025803410a51541038a001c2808050490020b44040441c0d4a010300c1d4500c818450241c2550b40d82d800f5103904404880d50b00a0482c0002d0007200043c60703401c804001e860b0340c3c4400c0307248440b81b54a0b6459031805004050300a07070400d85001983d0300050200c2800c140c20419580290030403004c945c103094184000342000006690505621b89403aa0f444401c030780d80f004e401c80d000151481c40c0e00105584407641c1d08029006843e049421151400d10038640c04449015a07042c0301c1c42c3c0e14034210310b00740d00034028402d02040c60350006c501c5043c00707922841030706000410305c20b060240f40200d82c800d844080c0e2286c8240c1da5070005100d0840e80c18082c401300c03980d02c0d000528826080c400000c00301d200041c02418010901c640c0e408550b40c040c0304884030801d50706c048850001550601c0c44c1c650006a51080c8109001c0c1500c40405000e800b070800d052007440300a03a450781d06c03c40c1d4500513902c00b1000000c0c0780010407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 537608678 1250 537607428 537607453
    0x80a0905031903090b0117060115050c0a0b0114040e0c040b012d0e0603071205071b05060709051909020d29010306060504080c040e011506030f060b120f09 68
    0x40a80c4042c0441e9503000c10b6400c1c990601201e86507040c0c00003c1841480407111000c80800030302d003811508a400244851082d041e01201e440c00340f0030a110541c0030b403007142000d00c40401c2c01d060581c0c00854000c00e0070520a010441240e0b680ba031405844e03005070301c0100640c81d1540c8501812501030601c84001d05811803440b203180c0025075009400b6001c801a081081e0380300d040f8007d07500051710000e155003000f48c0c000c2c1c15409071100c03010b282504e400009000038440c1c9031203000620903032200074803001c2a01e410351300c44d401241c00c50006000c509000940745002c000001c8544207003c0848503460508900c0800396001843c0003c0c45078941c80e6980d003041c1102c45c030007000d400044241540707540340c1000600380c0c0c2c0300b80d0100381006000d01c014404003402080b480d03130001040b40e0021300e00c510300134111302608420f0000c0403061411000040e205802d500a04c11010740c50000300034075610342030710011900580e000f149045401d180054044c200300b1949541000810041381d4084c3c0400c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 537609928 1250 537608678 537608707
    0x1020129030c120a1e03120e0f03070c080607050415050703090b0f0c010506040e0c09100308120108010c1d0909010f0e0a060506030a12080c0405040513150c080a090503 74
    0x30440880f02c0d501c032107040380501030701140318012401011740e04102d014050700d00602d0521000b20580c00d4580c0c61001ca443c0c9117042001100907072550341500d8841805040c00940802188540c54036405035000050590340f00e0003c6400b078448a0b1151060548480380440341900703c00422401c2c00b40700040032402810220161004401c1100a40c2d5902d109241803800d440014040d10702139810100610303d40350b00420fa110f00800103840314170003a43c076640e135a240c0700c56540c4050b054250024814803d031280c1e080a82c140d0722288028081c4c1e003d50361084a0740c4070040c0e1200600303030b080b8841000c10726021a0640d0406521400440d41042c1c03502600e040f620136060640403503200d11950420850540505076100340100c014003003851a0780c42c1c60005000e80e0410500b00000d6800103040f410101e001d0b540600000740c410401d6140684a90f00e04a409042c16030b00d1001e40001d18603010050700a03c0400202960307404c040da01c80e85100e034050052001c0854a60209011616010101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 537611178 1250 537609928 537609949
    0xb151e1b0312150d0b060105070314070506010305160303231b070f050a1a0306061b0a02040e0319140d02030f01030b0606071a060a0b07060905070501020129030c 71
    0x2216450b0305034140410004481c14030748000d0b50140046140c84004161010f507907070f030301010038200385030758018a290449544c160f01c000c8000c22003010440400b80100050014180c921075411112a203140300c645070503064042c4030060001e00d901115031281c120b41d04010311529020362805007000c2c81034400300891a2140000720460388081800c0007070144064051006100565034608082d061843c0018818400c41030110544400800304a2540340d4004a404d001108008a1a200d240c1440c0300c1d100c0d1102c40082c2e02c154280044500740c087d011040340e800c40552504234140490401080c0c46900e030092400300c007141c2c2801207a001c40c5c0140001d62060000c400258071541c194030303203648800000740c1954040d09050003144009034003011988401950400301b12420f5a505000811a0030705801c6840070b0340000c0748441c10451583c2001030120b00c03c000703a501642c1c8540049080380c2b030b05801c1c05080c00907080e030f0140c0c0c071081c86d21261003501c000c0c058460900c4c3d084041840d9440313 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 537612428 1250 537611178 537611197
    0x150908070803160e1905100c02100c030e040203130b09030408011109030706080108152a09040e061006030207080c070303120c020c012703150b151e1b03 67
    0x1041038424a10b40c80b4210101d06a03080322010341340250300101290340b007264042c072805040d1f40c0030903181c0103015060300c0c1c0c921940280380820130408070000030410241d45000300c011448006c01c0700c200e8a014001d4a11482946d09100d58422064507020302c0a070019140071046d010420012421503800e010309100301140500e500e42d202610340074175140504990291080002440c014005803801003003100812410755120030568903000c000c01c183c642c5d5581580c110800c000c480c8124503941001600150302c04a03020045540c0b010002511400c040b101d61500f610340e42410300002c0e02950180c00c0c40b60007000264203040e802d05506160400c682c10039000714140300240c03981010f15000c1d02280c18034a02c09802141440d8001030300d0041e0081038007500480d400301000710150150102d06c000d581201340321a0407104d03200c0080040003403007041da01559424030840500c400c050100c1380d5132403d203240554035006100030300580b60000400b0a480d010b80264000c0600400c00140a1025 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 537613678 1250 537612428 537612451
    0xe0f10140427090809010507060b06040f0302040f05010b03240a061716050a110109051203180a170a09080a060c030e010903020c040c05040906031a06030307150908070803 75
    0x10604551200b1072503003030b00405000e401c0201503400610707264190781da001001c0c04c01c240c4856031803a040380030b011060038080e08003001060008044540607410b034100c0b4000d44003042404030144240d010740b41c09006482d580c003420000b0844400070101e1b010040c1d03036105120441d5010038030026611980503448000090001c1c0c13010303050715500e00091074102440515a0010380940e540c080c1c014007070000f100050010040786d01e41c0c2e1110079000050403580c01816111400314490640b201074100b92503401103424011403a62054200180b118000c9070041b440610b40040b60910140c10745c0500c0301d0900300450303e58002100b100c10056005500c0c80b440020603900200c40004040328110804003034130f030b81040041c00c0880e4000c1007895a825082c2e40c0824000b0250109892522440d8015a00140303404000018041d00c01c81040058400c010341203030720f884030020181d6034062004040c050011082014010000c0380d0311004031a4030400200d4200325640d00c1d110700c8c507001201c03101044d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 537614928 1250 537613678 537613709
    0x14070501020f03041209030c05131409100e030901200c10031a040507170a020c0d050702031207080417100504110102060c031e060609150a09060e0f101404 68
    0x8011a003e00740f003481d541c80c00a02847c41c5440d0b81100d18900c0c400c40d805481107280c110420400703608010303500d0b440070b01d0f040c1542c141020555564904454183c11003854000000c5031400080201d80c5807060507501c1810002507a00e5aa91100544400c1c4001c2e01c070b100702c04034098942c03221081d406001034038002240e440704070b0340802e1820035140052180d45013204100705160080320094989600c034107009040d03030352a81ca0780002d119040c0e044400f4811010301d030038200d81c070500400c0014820307003c0d10b480c01c1042d68850181e01690740b004101400600080c4840b0041416800f101c403048000c8480048000f55284119a0b041d030b002d80c1d44089800e402c14031560100025a0045409810146945040d009140d0041c0d94900c515440c02403600204400e0795030710054900001c0000d01c0c0c1c00c105005e800103039803d0b03031211601c8004145018800076880c0e00421140c410740c4400341400304c041508104020078042910f040b01c0603c0300341440d400050440e040a80050043c0d8840c41404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 537616178 1250 537614928 537614933
    0x90c01031d19031205130609050106230109081203010302060d1e02030124020c0f04390e15160b160320190908060901050a0605061914070501020f0304 66
    0x490030304d0000c1c030500c0c10303e401e2200c0d03242010340b9411196081500002c5413141b610b001030250000303501c040c100e50070240b0410b50708200c00c80b5002c24130100b62610305026a9880c0c1d0281c440d05a4501c1c0d8840d540180010009403c04c00c0080c0382c4205040000503500000340c4003c0d81a070b0081c2044200700d5800302c014450074018003a0a8204403022108140c00202510b0096840f031108801c00e004070020000000c7c503480341d07001030b4011640040102d20164408200298403100005d650805001c0c24003e5401c26004121502002d1805850701c07600085805010600b0b900c4800e410300303107010f184025070218400c00c02080c0100d034020f162000c403400c00003004041d103010041c2400034041144c40072a4800ca000e084403010755880c00314034424100e913034064600f507116900030600d5014035030400c2903903c4190310541c842d000706001000910f403103100340602030080b0b810070910000d160802800080c01034501c049040d107002c84bc06d00c3d14110760780c1c05080e41c0120800c599403100100c148000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 537617428 1250 537616178 537616187
    0x801150501030e100e030d020403140d081302091b03040516090c090302120304080a0c230904030e0a0504180c0e0c03040f1505040506040c0509090c01031d1903 70
    0x8250034a41400503448024025850300544c210b00e091032070313807420310710b041280c1070007030f10205441410115201c5a80f404c200710110410030f030b0a0660302070b407501d503271035240030720440b40c021030740043e20152034491582408000140035000b45003c40c2c20f0030103003441403019030080d0321032403144c00a4000710700f0100b814070310000070b9007103000d8141c10700c0740c60240e003a0711615807801c6a4040f208a11000b10803003155045209036084140c1c60b000f006149001d11282c810110129040c1100c01185600e50483c00c2d81110001340045034800114004500032034441c00360010030f8070700140f45407003242d554000242103c04881d01e852111840000000502111901c0c04008083c1000400203d18001c1d01d04103081c40000d2006160b0403e1080c42c0045c05941000314500c456409000c22140c1030a042840c0d85400464048070302c05100134010845080104299020b04070783c0c00205900d0300a400190094206150070076105241e1030307003001c1c400d00e04010303200c2c2c54850344446142e801c132107040040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 537618678 1250 537617428 537617471
    0x313090203061842060706020c0601030803090706090506070b0709170d020c06030601140c0c060403140c040c08070e0121060510170c0708070b010602060106030e160501050f130801 79
    0x20100381030f810000d040c400f044c0f00c00c1031140780100c40355955054107203051002409040c4840b06584500000407042040800056019104210440d0760080d42c4003000c880010440c022160405070a0000700001607866080c960044003504091803440d489114580a2002900400c0340b9680040d102c0e0703440d29010f1148080007181a11500d2030351808400107001802a5018415400c1c030001d50800c0001061101244142e002440c0c240da83c4d589003005101c09481c100c0c14050b5004441484c5418078203842103001003500c41c1c481000750b80c1c400d0410b030b4940151002440c10701030316840c540843d850755106818504404100002c11b01c2c1040c06010641120185100901910880441c5080c105490707003a4003a00b1920203d5440180b4035060a8900655000820f0094003500109099402080090507034107565003c000c200910000240e0b0350703042c1c07807003201d03002d4040c0001d0106504c900c3c02000290440b81d0410301c2c111500590806044007584000016591242d5070b03500b0400d41d40ca000b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 537619928 1250 537618678 537618751
    0x10c06020f0d36170307110d020c040b04092301061802120106110a12090302030d2c130c0311071202100221150307080a020a0803130902030618 63
    0x80310074607425078070200c510b50600701d800d107404c0e808000111340500c10a0880baa000c40c9405903000300384c0c1d181000e55240840c03400030b407003107007000106841c508040c17244d00985900001140c50541409009a202c0c9c503050f10700b40d42c0741d52101c5000c101c2d10780d00c43c0e004012180141c0d00580e507414148000b8400e24042c5c020344c00700400c2e00e08142e503002b000524158101d070401d007054a811840c1c4c8003600c2400300c40d030000350140a00e01c111000d090b04084599034000d0980220001805030f100004075200a00179440d40c800341503035805690b000c0e203611403003030005d5905000a0311324030004040c085800800044806501944945404680c1405002100040160217609040319050408185540c8181074281c004a1100284014088401c08020742c00c01030240c0b04076544a074100d5850701c01580c030030b82c06641c2e1000001003800c800811100072071031702c0318011010380c20819030801170b40c40504900c0d8040d070a1100b1941140c0c2e415865402a20003c1c8001081e60008107602c26003051151030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 537621178 1250 537619928 537620021
    0xa05101e03330302090106080901050a0204060c030e0312190e03010506010c12090e070302120c07020a0e040f08040b0a120510065306010c06020f0d 65
    0x41503544005040c80c1c492079224a03807214000c0241c0425202c9100651020350b00401e01000041c0e050340060000307000e127000c0c50003031100ea03445c14007081c00d074480c91007204001060480c070a40030a129000380c56544100030305862340c010400300381080d00d40101d06803414040d00c3c043e0703005e03045801c900304000300c070000d500900488c54400c0001e491031000c0380002d85400843c0a038490082d10800200f809030841c0e01c140320447c1041d440060094000061507070410b2005000f242541e22008180d60910303500400228003a8140690001030842c00380007110410a2182241d00141c1c403000a400501100080c41e602c8030581b2a009152294a0885005042c505014021411040c9142070152086401c00944080e07140030300c6040c982c0303c0c0c92120b14000950340c80b0300441281c0344072181c0c440d844555030003203586072104043c446002501d04030b001c2046280501c0026a45401406440a04c11b10642c14a100f4010120a4071041411061101c0d101885075a405482030310200300d003482c0115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 537622428 1250 537621178 537621191
    0x61110060b04120602090d380403180305010614010807030207020a050909031b0a03080708070e210a060501031401140f04050109051626060a0b0a05101e03 68
    0x207019006116034054481920b038010b1081c001c0c005240c0440c1d880e1507024080c219004000d060000010a60b05030342c0c00f40071800985075056a014000780e03400414014400c440a0f02c640d44c00b550404140700e0032000314000c0500010205000b8403d40008042441080013a06841800109280e4000f001002490710511400380961180c13807204098840980302c19156450b0301d00380c41d00d1401203458221180440e480c5010011802244243d2458401d4440b8480c0740c807580001d81e130302c0c50225041c0340010f0324024420040d00c0c1044c03d2180e102110500384864402c403064075420110b04000603200030b41c403800100704210202021448000003e0000c20904580541c3c0d2545108042d02c0040c1c40c10380540400d003480800e41c44514902d500100303c62400325041d2840b101225a0b1044035800003c144441d680e004204501e403c138140c18601401041e41c88e1440315004081182c0c9042c2c015810150210312a241e0a000c4154492591a041100d94080103c0400f0040307141c5564101400e140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 537623678 1250 537622428 537622439
    0x120c07060f120b0a05060f07140303090613081201080d020c04180f1a010f03030e100912030306030602130f0b0403020d141908070506090703020306060103230106111006 74
    0x80c007008520400e07001041c2c25034000d0029100404d1600400d0380604002421010000d1010003480300b9489100f001003c00140140da0b0349a010845802c3c00d290400c82c0041c0c1c0204c1c0d007010301c0344490300c62190a410709203402c00c4070380c07681000d07000100e56a0260760a144003e03010858140d5607001241c007886805080301c440e92900b01008402011980e4841c80d0004005900a00d5500b0840c5e0000d079803d02c0da5298008103400890b44415000b007040c2038820140b5060051601020042c1c036103581340c20916000307081000000c6403106a0130582d035045e011000407910700007040310380361081c40c000b241800c1112000920010358081c001c0400200420001a114040c8400203da0085031800c0b0504001d000c407400c1101050450390214080d08264003000203460291130030314010000c030740683c2d40398000e4650b1103140d07000c0654103134130400c000789803503100741c010520401015206c0d582c041e111002c2a50492800c0e0002c0e404101b200300000c50a4030b04000c41491142c0801c801d102044c98007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 537624928 1250 537623678 537623687
    0x80411030604230c1008040218010f030b13060e010515011107050f030307080406083c2a030a14100605131d06090a0b1c050f120c07060f 60
    0x2c054018081516032400360046401d0150007901513020b00584032135500d800c0014060070b41103508074440e4421003d000700e103114103050981070700e170003c00c41041d030b90443c0c81311031000d24001c0126581003000c589983c0010418080e60a1f00000340b00082204c0c1031018214184807540a4401d040012042c0b40c010966400503681c0102e590590b414412071041d40040b900798070420502420084000500060380c59010341c1d11481084c2e084140d804140c0703178804109440035110041d407040c1245c2c200004400d11041180c135003207440d01740b01e002a0041c001c60308112103000350100d00d070000040b08008880942d4020608003401c0f5414200c2a80380c0081181c04040d4107000303110070090007084680c0308a800f1b40c0514080c1440e000c040001c0070440002c41002e01003161a680070341000c80200f4425503541c010004441401003000c1c00400044a81d41c106d011a180107841920030100c164000c1e14040c80710f144401c800840c201d95801c8001030304c902c2d04c4002e51281c42045890301102c200203512 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 537626178 1250 537624928 537624953
    0x71208040306201803160e04060c03022217160b0f120c0711010302130302010302030a0b060301060f09060e0117070212030a0911191203020106030f03080411030604 72
    0x240000b9452040c030051524610300d91041e4180c0703503000032601e607060300f04071246404820071000c482d18950002c190b01c40c0300800c1d100720307c0400341140209001810f190815580001c09282c010b041c600f14910071907840384030a440c05a051074079241408451800450385401244c580028401c14500c25402418109140708800202c0b90200310320310381070b403a9822a0058030400c2040d207000d0810300d81080266120000071909a4040b0600c515507501034020380e0640c50f140c900c404c0d041403440d0019000f03940300500c00c0c403105503140c0703141d41c4a6440c0d00240d80604125920f4002d140151100076006803526000201440303800810701e11584e07070003414060a088031b01c1d1901c1c4e454a80d42c400364640303000140c0c9202d00c503c020040090b40300f00340c5d1106410502880301c1034041d10103401800320f183e011110030104a142c005003448020b403100c2c01ea0306410f04c2480002002541e030748030040d031b0710b40e500800c0380015120002d000500030310030401c07111810128080d02050a00e540e448000c000c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 537627428 1250 537626178 537626183
    0xf030a11060c04031a190c03051911041406040b0c0a031403040c050418050a0302033406020901300c030b030c010e0111100f050906010303050703030f06170c030712080403 75
    0x3018000071103c107006c0c04924901e90b4500340500c20840c00c00c1e0040d001e4082258103408409150000740c03d9944c40740075042484211949807031503c0d041c08038104004440c4051f16412590802000a8070104500189650b001480c00344c420f013082842c1c01403240d000050002e18000c0240107000c04106a43c003070704101d40c012140091220414083c96a800500306800390075401000091000d054001c0002d142411b00300340300500364900a07142c05440780403d1501c0da04010442c940c0b1000030b100354018101c800c0141041e110000e0240038040e466000401040c9100c00400900414000c3c3c40c00b581004000d07a0a061100c49009008250798000054001b03042000340881181280d0080c8041035503814a102603c0c1c08014041e401409031480c4040990103911f4100001c01035400864600d05903541640e48600d0540e89072403c8001e0695612515690340e07035240700040039943e4202905042d240000506080342a40f41054244070055001e01d04100300303140c032000000d2107131341218180ca6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 537628678 1250 537627428 537627473
    0x6051906050f03040c05040c02010905010507090303230c070602010207050c090601080a0510050d0615060e0603040b0a1107032c0d060522030203130b0a091401020f030a11060c0403 79
    0x1991350814081c030454580c00a5041442c0c000c2020350554190000000140104024811034aa00788221480c01103440050b00081c1d51880d6603811036040e200b11801c050f80b20003d2810242251001401c0481c1a071161f00541e50014a00c820000248240c50fa26030f0101c602c400c2c41e05e003040c00030f04500b100500c0c1482c440c0c0e5850016550525400b1014068000074000007c280c0007031800e03800910b56608030b0001c41450450009847d4440d50515100b94405080c0c00d09585550f912030b40b0f001009071840c06e040361502c0c02090640980c0e409041802e000340c0e5070f0500001c100d40146210a0f070344d00c1d43e1207480141c0403104510b494a400c0d680f59141d218400041c140e540712081c842c01690216440781c0b95005840f07260615030700101809181070070424130840e9a903980302d49180d0744100300100c4080341410104100001d4000c1032411401c0381801640c055001c0103054038150b9000d19071250103d5402e500305000c1d030904000b515030040714949042d10740f90560711107030825003150081c0703130816 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 537629928 1250 537628678 537628681
    0xf0a0c05090708070e150a051308012a0e09100501111203130501113601080604020706140f0109110f07021513090501031a150f0d1506051906050f03 65
    0x1a183c5643c1c0c03900d030b40c0b0140642501c990720a01c00810b40c4d0702c4051092a01c527802c0d140451200720612400041075060410a0180285504602000c4012000c040240051184a0070594a8035510240b18046c850040c0d100c4038180000581008071424006050354450b403405501059504100c0b90004644404c21440480c0341c60b0941c050012406001107211003c0f4502540b640e0b0b800124904202001e603118860b80d602c0e0f00c0b0321070709407201003ca000a0b0300707001240c41130401d40d00400d00e0341d0190b03d0115802030f084c01d402d080c3c9203050700c0b88a24600064010800740045114140b0585440c210082c68080740d0200b80c5410b0055840181c41000c03d0640041003841c01c0080b211100700c19a02190034070b40d00e41980c0000d1034248400c0e50858580500b0b0301701d222091741554410f440030305491000101d5442400b40741d000103908150003000d240d001d0b01c04649448450013a485024001060550805042c0441200a800071890f0b51610420074008150880f06881e110800246681d440e03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 537631178 1250 537629928 537629957
    0x30e0918071e0801020c0d020706021204050118090c1106010f0b071218090605040f2304080c0f0309120a0210050a03110c03071a06030c1507050f0a0c0509070807 71
    0xb869194004100c544c80001d84113030942e00490518a1080c081e002d4030300c11613079900182d80301c40208041210f482810001441250f000d602030498500d081001144c5c03d0303031103000190031110f030030b8600c070b005c10404413800f5840c01040000c5405001c1c0d40350726070446442c240e031401d994010401c004184451514405050764418500e0001441074164009205541c0d00c044400818450140500450808a05040e52500c0d07024242d030340b010498625608180014029400400241c000c80302c26004200130030b00410200140c601c06840c01c00a141d46046000070040140851300c14901250440382032840540e403007548800b4a40018185665616882d0000302c00901d522450303600200030100d01ea0b58030b0000000a400d07658820614000c119441e0a6039050708102210055499800760340000d01504141d1904022288501c0040e810805103544803800d004200d5108006988440788030700c14800b200d00f401d00104070507038991440c1c0c2403c1000600c0a0f6005086800340808004503d05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 537632428 1250 537631178 537631229
    0x9020301090219090e07050a050105130b0a05090310060b030606070f0f120f0221090307050a1706070507020f040e0a0507030c0f05120607210504030e091807 69
    0x2a0300303500420310b0f41c005003550584034010501c1c1c02030000141c43c0c01090a4884400200507056482c000c140910441c5002c0044929034040c07152010002c150420002d0344a1640001e0605000c90303484080d220a0980103141c5000d2008a491541c0c5042110800c00082080201c90b008a425500c0d1070303491341e0b1130500600c114020301c001407102442c010b4040902c864030848100b42c5480c0e9071620007825106c03030700300d940e00c00260300702860a82003020309008040440040c100c0080140564601c20741d6103000403580b000c03d82c001e440082402c50f65608522052100c29408201030411505100c0c080d008201c540460781000380c002c0e0b5481c00030410f1640b00304900d81d4080e502c08100c80c0704030744900e45440c12040600c18140344126032040468640b40507481044072035184002402d50759200c0c0b00c1115228540c4090180e010721805d10094001414051280720314003a4450030000f40b2200c0a010101d8030050469402a4081c0100d0300d0304400800d607901218844480290014011644a031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 537633678 1250 537632428 537632441
    0x2060c07030c090207140c18091e0c040509070b03061306031209060305010f06170c07050a05010905120c0c1003150306060503060708010609151403010b0d05060f1309020301 76
    0x2082d01c182c6507400a031500300d80d001082c08610800218142c81c000203c0299142e00c8641100da0003030810044400c030000300c016aa070310040c080c04503105130a0b80740300c8900c142001140b1060302d4008180941f481d04041c0a11600808580d00600d2071b41c3c03030039017091841e0201030022032081e42011114200fa240c5a04440c0141d60031600f21300c03444078110005018810144650800710307080400009512220304400320841d04031340c4880004c1024108004411140104201d031450018411580400e03030030400300c41d00c14032420000880c01007034101285801340440c8941c441250400c400d542e268404a01544403407025500201d001c00da980081c0d0182142d014600707060b07c440c41001083c1320050f00034004488084c1c00390b4a0544419000b01c4500100b4014040895070b81d1404120103104000c0704440b00120b494281d8180c0400b1b241010682e0081c0d0000810031804101580345003090b105c2d9a0300300c00211007200101100310b0114500000d10f052407500b0391307940c0d03400d0425501c080d007108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 537634928 1250 537633678 537633683
    0xe04060302041a15030c07030e120f0325031b0f06050901020909090c0609150c0a2a081914010912020d0306050f10050c0f010b0111030f030402060c0703 67
    0x61110a40404003c2440e002100c00c6600c200d041c43c03100d80c00441254102d80c041e40c02000d0032841d03c82d0b1a2410f031001000c08440c0ca812030f01c0b10081d401441010b01810080c0b40c40580590383d502c01100c100d60246c0d0071a40c1d03c201a000400e9404002508640704405010500e44803008ca03a103581401c80c0f00844d622000f600c500c0c01c25043000302da1403042d4020802184e040319a045d5907201c03000304a0340e4824000340960802c200300003030655440e00074076074441c818103409107502d0282c12212040c1082002d4100f1110741d83d807540c0284220283b943e60110046401d509607080c81c2c80d01e50301c295258500101c440c07a070011002181c00b841107079103440805070805c1c0c00034021200c2c0303454016504002c0308040b10040c050074241c0002588240202c0044070401880344d4010505082088049000d410400c01440307410003c02d80d040e003051052040003c1040c000050307220a05001400300d51820400d29043d4008000c04095449a201542c3e0029010749c0c1d03464079040b80c250090708e81032503904003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 537636178 1250 537634928 537634931
    0x40303030509010b0d050c0a0f12080c120a050702181014040f1a01080606190e121902010e01020109030206010909020d200a1208180402040915151403070e0406030204 73
    0x5050900c840001c0a40c840c2105442390303c0f0140d45c0b0311130350b504d100c0c15000e0b0a100c0041e1a02410104003101c0140810403c040c050718459881c1c100614050b520126020010075004158402903140c0317402481705011042d81035440074a032450414110900d03d000e42c01c03c51090040d20000e940310382e0b102894442c6251401c00c9070005044446d14280440d51400707002507800e030001005410400c01b561640b0072140311001c0c820807946021f46d01d55401c0d410303183c2c01480700080c007545000100700140c00800002448907291005000040441010007021419681485a1000040c0d8000f0b2941c2c11120b10103070000c0c4c82445440058003004801101804074600d80c001c801804410110310407101d00120750741c01500f03a6030381c43c00301103050440c0e019000800501401861040079402810b414078014001481c2035252160481258405800700c104642d00c09400d01c10042d039221802ea40c0002800c0900c840802d00f003c1c4030741440010641000c010680c032615401e502e554218a0145600910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 537637428 1250 537636178 537636199
    0x303040620120a050601022d010207150c0f021c0e06040e041b140f0913080406020d020c0f0904080a0c0c12050d140409150b04060f1205010b040303030509010b 70
    0x1420700c00b1440945050407050f24050102c2c04560001510f4209040c10318802c46030140081c5051020010b8081c0f1091955020044903001a1200403130513203a15a0500000d003c49000c50001c1420340750142c203038199803206100c0800b0001c0e1904144880e116460b01900808010010803400e0186600071011102c2c0c0100388410480c000300002103500c2c5000d41301c032a5a0360380034070304040000388840d41c6d0401d04081c2c085089040c0308004c0d907840503030b25020f0222180d00755501d00566000c2d0f0701c10320041c0c204992001102c2c1d814054001d48440480307203402d892031110b00146441d40f01a0000700f20103400685441014054180302800b41d030840c0903024910b1303031410f50180003600200d003210103008070004079003824012030401611040000c040e600741401c15035220000c158144030061441a20b980001da02d0902000a0014104556038041450031912010301500d002c02000003915061070014001002c1d0401524222a058a000308031500c4142c4200d0040004042442c0c00201401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 537638678 1250 537637428 537637447
    0x5030c010b03160609090507030b102106140f010c08030a2309060705030a062c100e0f07201e0705130e010605031519020702030303040620 61
    0x40c0080788004040d402d4982007089507591581c0d0015500071100480d200351801c1c01082019402668051040d04000850100c0980003920341c8039800e05810000d050595481d282d03111641c0c00c80003203003c500c4280b0005040003000c801c4100041a424042c040c03140104002e07038454079103220000d4002d0701c01e56403401d00c2c56515020b40300484a9010002c20311501106a543c9800194400c250140281c94962100182143e03280c0c0054081400c1c10380340e08011075500107a48160301040c01345181c95100f50103000c20441c1c0c0388802040d03c00c120302000010003002c50144007699021510140051040c0e07101102030340c4100d20070098841450079a55940a6000b0014100d042444002254030f0f030640d2805500303940c1c4c16a03025054121500f000515a00404ca801402c00408048000b242040d01c0d41c1c08249051300107525000c03540c2c204003c0c404104180c010650031a0691841035103004810b401003035903803201410040c84117980d800703011928400d84402022090860a503565280c0c83e15 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 537639928 1250 537638678 537638681
    0xc09120c0305250e0408280e060a1b020f030d0306090b030d020d030207030320030901050a0203160c05071a030709080d0509060c101a011101140103020d110916031503020a051c05030c01 81
    0x381c7c00c8000c51002803c1d0341c10380c90000107071070001c41e083d07542901c120300c901800007501400100481c1c100c800308000c1602641c080c8120180c1d09100d40d80003601038a003c940000340d800b40d82d07116010303410200801d6040c55000c03030044409030b0141005070783d990051900b14002c0180c40385c15201804280f50505d080d041c06001580500d038102c0080c48a511582083c404a110540d002c2a09a032460b8110109034042c54507400c900340541c0684110b241e83e0008003240c2d14845e801e2103002c0c0400030030410710641240d182c002500b0780d00001c3c6030301800706501621314801c420001c1c0c8500e00208036101c074100c04010b028411050084188403241e5081d0b88102c0c0071030748220a5000c034600745609050540144501003900c00842c0d40d09000341d20359001e00540100c1001c6c180e90000c001c0203c9070103500c0e054006409a4140745803101e581e800d015008045440510a805140302c12130720400241c1d40f010b07500300a4036012100c2064259130610508002000414010711a02010a198941c000c06 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 537641178 1250 537639928 537639997
    0x503160912082a1e0109050303010306060f061d1302090307060906260609190e150106180b0f120c130605030f04060c09120c0305250e0408 61
    0x101c80044103100354003c180315500b4501501041c039540704020b54510b0100c0c3d41c89103449070100c44000a40c805640d00c41c1404e40d442600141d880c01d407155000c02c01690300d5420007000300002d1402e00701074405480755503010300a03c1c0160f44204044008050b2500305581102c600e10390081c01ca48500c0e41c0c0b0070000d040d044080c8611401715013201c000200ca8003074109980c80c4c00b0540c2e04051041d555803010000364040150000c400c8034000c20400011150901c140a09160300100900c5101c1900b48022030400d0305030442c2c01080000d5012565045903106c200c3d0503942c2105a841d107980640d80b4182042c01303024018903041c5911014031482c02a20030060410309034030340f25480c00c01e4449009603110b1106640180340e1280f030000040100d1001d42c08503105059a01c1c100781159038580450741d103502e403100c3c240d42d01d84100c2010420410200020180071000c0700f40c800c111007508003082000c040398840d888818441c040041c3c100500d03401150300360b84030940411100651403203280d444440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 537642428 1250 537641178 537641197
    0x11404141c120807020c060d020d090807080301031b05240f0406030209040605010c150911130506041b020d120b030601080a0c0b0405130b0103060803030c071110050316091208 77
    0x1001c0100d0701d01c0384046801b03092103001420081c80c000c0b48002d03020003940486454052603555461010004404400504004d400303509419144c0d4110300340a07500c070000961020150814900421043c3c45001143c11401c43c108024100c21006422004181c03042c2c4c0c240c60240d44000402150098155003c0d006007841038800300f05841c0c07650010358103c0a0b920020f403c840e480020100e119645820a010491080e0303c40385405500700013052844040f410100000d603126420814036041510507415007071112a000b040e80130300700300003a440385420510305040000d81556084841d0140d080a0350a1201030101c03943e40d80d480b90040d45542001500320b4900031000c000143d0070251505a400b070724001841c4800501d01d09800c0c0b4010400e806455041c56144c0780002510f21052015611907072120b4002640e80340701d450022940c2c0706807a10184107048009000e80d203954041d05513a401072101c40d16004034620030f1825035143d6519400300c90040b074480c0f081401c210354a0003070312291a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 537643678 1250 537642428 537642437
    0x30a030c12020304030e060708070605132a090b01020f0a050a03200d050702010e040c03020405030709050c1210150c1505150f0a030f0b06010e011404141c12 69
    0x100c070000544280d01c000d41d005000900200b01d10030240c82c16400400340f49100d040e800c0c2c5002c0c45a601c40003940c0c0c0071201101d00e0349502c41c2c0e407418881d03241c00b240d03091113558800707040d0001381015818400250340609501607a41e4200e6255a90007002030302109401d2904454481c00c852502d1030307840001001c110300003136144d11041c0144001c400c47c03000b007840c440d0103440307000e0340d005003118103030424130303050b07040105c600e444148648891051a02a128903900540c3c0e841c1030600703041c545070b0030b80e100c40c12040c50b140c01c0003911040c02007520100c0200d07400b2003030f9075100c540e03410700050210b820161520802c02030f55a0400c0d000b00e0f0500490344039403d083c40100c08a002d14080b220100c2e20300c0100f004284124426160031941e880502ca0024141e00402c1d40b00e4403070010040c81644100c2d015200301c0c060150310768200070750720082d150900e070007100304d0342c03903401c000b03617030080744580340484080c828010460b03900c0465150380b9448034401e50b0404110350910a000080c43d054150205 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 537644928 1250 537643678 537643697
    0x4020d0e0109110a0303021c09030605070f03150503030708180303120a1802130c0203041a040306111c18060c020c0a05010908030406080a0f06080703050607091805040311030a030c 79
    0x50800c03550203070840b901500600b030421040b0a1140c400c0300c03018410b404010101e8800720020b203e4cc811035000d800503a135200009691004040c3c100c07489803840556090400f24100883ea90000c100c2c3c014560104400b51600402070051410300d645120013541400041060429a900002403a01c2141074010034041001c0200d5141c041d40c1e13410602a4010035082e011506289007500407500070703041441182e1074240e5410300342c4c42e003590482000c62400c4000400700140f01d01c1c0e01500e4001c0101108943c5010f01c50000144590f0700140c0c0900c01c1ca45a9101c1d00c1d0f01000351500c49a02600850180f0022000381e4009460792040d443c0703076124030000040403545511940004040d501080025403a044c140b25051782c9030702e00101003030495030b1034156106440050380206030040c120b0400a005040c194907006091000007001c40d010440403000070050440151541441559030002c0085c03c2c0d115820100c80d50000b44d030302c4d03501c0c922000900501d4254103a102d51060001c958605110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 537646178 1250 537644928 537644963
    0x1d06090a0e01062705060a030203040f0210050a110304080604150f0c032c1e0106050604030b0103150203040804060c060b19170f0c010f020a0c090b0a05010f0212030604020d0e0109 79
    0x400c07190045c01d0b000b41c4140300b001d070350501035802160090f000e5071015002500c2c03940011041d014000603440001d07008034035040c00e550803500c0d14040c1900040030718181030812041c1d540d1303904c0080000e03004070180480c4041d180d0203030b8084259503d04e02420b110f031354401c641c003030040c000c06201801101c080850140d4441e10503403103120400780c010042c0900c001c0e100c80403101c2c081c174080348500c41e5594000003d002e0381d9070001031009520030081c0b1910366140d400c0850510040388030b18811580100100400501003204840c183da5080c00c25460840c0c0604002004084000820b0703084581620862a405520302070b10088506500662042d19080c5d046640c651400a11030410742d4000c0100b21215030080702c2c6031588c0c03000d0b40b04480141d405515040d144c0107245d0301910505d81d070b0781d00d0100207080c106c40181c00791200703081800700c4500c142c1000b0b50350110f284d1359029448c004008900244d650f50110b41d0345a060102c20b114003070845a40300d00800c1c0f200d40031a0500546100a1034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 537647428 1250 537646178 537646247
    0x60903020a1e0e0c120f040c150203070227040c050a0603110d2a030e0105010b09031b0301230f280c0c0f050a030f1d06090a0e0106 58
    0x42c82d0004410144460745000f16030f521851001c0c0c4645080710080c0021243e40c0c05041800b4400c0c1c0c18105400c00b5814903040034804042c554002001082108604243c29500007044075030055040d1034001c00c500041041c00300098182c0840c0c40520403901c24042840030380600001030300c408a0341140d5a40d56001e0541c00ca0701d4000042003840b009000b004809080c0798441c44446071141404100e1a4000e80f0060f8658211a20700007c079075181c083c41c00c1141e09101e19800b400c00f11302d03018603040c1701030b000035900c2010040c107982c20b100c1d50700c002c4601d840a4209060314111902581c029002030700c42a03e0440d01100e03001140300810000441041d001c204441c00c1d00014500d9000304e1000404500250500742202d03024400359600001c0050003120030910824003c4004e8012400a071070010503641511031207001b000161000401a50203480806800803c22180c081d80d64210002060707940403103511015440d40c1110000031020f422461132a5056013401e4070070f00c440c4810b1078840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 537648678 1250 537647428 537647459
    0xf0b0a0e1813060f1815022a15040b06061806040602030403061b0c02060c0111030a0501030201080703090b01060f1206080304060809010e03040311040207020d120f0305040b0c0304020613060903020a 87
    0x80d1751805000b403800800c546210140c0144440800945080050244100100444a000031a00300581d0044418900c1845503e4840191810224030350905484031070540710090321040c46400002820541e40c0000c0104800b1420090007c5840f0340e9509000ba40700d070820b11054032581d04211540780d15104d1102c01c410920200c1d110181550312640a000d419000949484803541d40c0e0603494409038021005584155045027000c2410340c1584001894240058101c006041c1010761030000560b12107a51810344034a4600150002824202124143d440c40c91503900e4a281c1070010440d00c0c2c000c0014001c3c1c0e0915128103c49440b240159402ca4441c00d0394500c1c150002d000c18800100300c440b80a02c0c1c28030080c0094141101c2d6000a0314482032039004a130703901c3d603d41c804040c43d0b8200001110803030b01030a0800252816440d4141a000010f10901c181d12000002404540d00c0c801914407040503806c41d0310398241c59200240089406010a92040c401c0707140028420040314844e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 537649928 1250 537648678 537648701
    0xa170c150a030c120f09020f040b0d02131811090618010e0703020c1926030a050702030f03041b0506030405190309090207060f060f0b0a0e1813060f 65
    0x152400c000110101d004110f9210a1010440d542c0520900c580d490300514840c0d59840500007281c06aa2041050b20080703404414010390800c442d0b44090b0303452181086509070199810300c0000100c0a0140c014500005e1811010302c0d168800c005010340e0804050020406685481142d101e0008001704000800540e109101741d800c01480aa03807451f40c41604680c0506001d420104100e119a0403c0368208840c908070941d1b83c80302c8280855003900881001d11503035103076020b000c80106200c480c84020403562809848002080c0d2440c070800840701d1520042d450716031070703042074500f103039a500050f20426074481c15294046054a04a81207130300490b80500186080820001241819880340b242503050210004c0001092801800101102c5114401c00a030707400703024142008031441d81d00180400d0442a405010328003000c0106c40e60420181040c945010105002a1124245041c2c0c1d160050f2030301c1c103002c81d00580c0c020303110450340716074070070321190011000c0c003070481d0910480d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 537651178 1250 537649928 537649969
    0x304020d12030b0d0812070f090e041a0405060f010e070801060305070c0203010f020c120a090b032d04050f0a0b070e0105071e0201110304050d021e0a170c 68
    0x1401d490040605869142804151440400700054020751146015100540d000400d8003209075003c0e0510703801600d43c184080741500190004048003000e000e02c903900311481e0003080500030120504101c0140011510540f8501031416071313100c00095860012282d00d40300003182d1004102c0c6030750310850890b540c2095a81c6401b10460181401030000d6051141c610b0880c00540c60030700901d40010702e13280300036030358200a0410511300343c4103001c200d40d081010300c41d02c0701050b4085521022a2407070300406840e619144583d524084000c04d400d211040490800000700010f00d079060b01c00c500403004d81d4201d00e40381600b552240120200104880c07424030018010900491b6040306c44141850041e050a00641d181c104d800b0305a0704080c0e40c02443c4404e5003c669000180d1365804181801960405280001180e22944800c00080c410700184090300d840240d4040c08140d195401420799001135650241c000000c0612443c1c28842c2c051082c500d40f040c10032208a000da4007079800e6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 537652428 1250 537651178 537651199
    0x4060f02070e161205040b09070623250f120507050606012a1407061d04020f1c051b04030507031103070e1f060906080a0e0c060d02120c030402 63
    0x2407020f040d12811040050005450702c2d888452218405c00d445107100710224035040c1040b48040b803a200d9079500943c104448090503100c03020190082c8150800c0c1c0c010201d848202c62055141140030410131034000e140c5007000d000a1003410360190340b44a004402d840c1c40c403000180101c6081c0b1440e03030701420503400350b400300f461544180f0321101c0b44110412089035000f401103000400c2d04800e0700590301001c8180c1044198081400508001d000b1400d218990040c02a4a12846550a021103210340e0303001c0b030301c03100c4035500c00c04541c04820300a6608246500341508907004010545081d44942030b004110340e06c400300c1504035000e03650010000d03c0d403280780d507070f4000441c02e50066403609402010300020f121058410003e0061035002c001c00c40c0f1220b8140020403052981d0300040420600c002c08204a50300181c00a402040314107000c1010030307552110902e040180d8010503000b80b00090000401c200d6580078007940c1a10040c00c0c181611105d501e00001c1c001980c0180d4031190344070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 537653678 1250 537652428 537652441
    0x406030f0b0417040b030915130303050601050712020f0609010c05091302040902030f0405010e010c140d1104090b0a092318070306140604050c030a020d0b03010204080304060f02070e 80
    0x40040b94814407514101c02c80e5408640043d80941055000c6241c00c4000701c144050000240044109041d800c454891035141c440c01e08c2d000f003105000c000d414940e07218040f07a02c5920a5080700c0a840d000020141030f201b011000942d19002041c0c42c3d0303201e004031804500c0110040c014020240895a01c80b403d0014410404c07014458100c9060384c00769003080001040902400074620603600300c2c880da0000d00c1e0a04120742075541c02d00c02d5401d180d14240030001c02c01d4001559248840d5809080303501c41148101400c000c00381d00b0504035080b130000c500090a440c2580105480c030074195107420f502035988030640161683d500d50340e420102186032040d00d600c4100e42c50395202c4148151005080f01803000e0a090004680042e1612074982481c806900802c051481d00305800b078808000c0e070714240a105030903020141c41e2a040b240c001402000c0c0285540208107042c0000b402150365035515075046680758028842d0002003036000d90b14012090000c25000110b402c000340710301040c0e680a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 537654928 1250 537653678 537653693
    0x61609090f02041203050421020a0b0c03092d040608030d09051615030b060703120f0b03070b0304020a0b0301140118080615040b100c120e06190e0406030f 68
    0x6024480307640d00b4000000c445162024220307410f0701035107402e0b54031401c104888030000d4601200311252804088540016125a0110411905000d5801e52251b2146011238210322480a15580c00480c680c918104010900f42c0380030304d000480f004a0100f03207030b1014403040e03800600c030701040d5400510101c101071940e6000810f09500c02d400392010000c00402c2490b2180301900040854032255100c900d1503a0035225000c40104129901d40c184200d91383d0013001c0350080103500e214181c4511403c017201140303802c40c20b80000010309448030f041d10746240c0189500101c90692050450040003d6804031050842c3d050b110201048203104100d0001034500d500b500248588218503690300165800d0140081030055920b4404104003202120420081e10040c2c800541f10f00f2041402c900b01c0c40d040040350700a07551001500c8050000c00b8410f403a20503030390702150b0304036074000780c03445188100d03201326a0310714030907201d40041c14546020b100858007640002803500912038001004180903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 537656178 1250 537654928 537654941
    0x30a0212092b05161a0403020102040e01212d1401050a06121101050409020a0203031005040204080c0904050c040203040305070605090706050f1c020d0b0109080307230f031b06160909 80
    0x146a000700102801702c005081c0d41c004a9060300140d40c08130f800e000000802c000b041c01010031400c140c0b4000002080561480c00000000b40340407903004c45030001c034440b1119825800340000031a513512005003070220340710000100680080d40313040c1c0003c5050141d171140c1c2c4251207160b000240c00903146c0c1d0724039401025080205050020500c00022091034a00091004c1c000306e0f400345403241001c140742407101c18035401ca244581c1c0140400d0004007800101c5c40ea241c00c0031200040c05840310300f000d60070059031803400c030340040c000420401031540010040c4802441514104141ea0303404107007544640003400303410009001000724407904100b202c0580690082040c6503c1c05500c0c045c140822680100c0308500400e07100d050420380340d03810145150003050058040d626103602c41c0d58154440040d4102c00c207400c6240705a8062a120402130040940700c800304881e950b0340c4500030742200c119071017184403081c495840003410703121101010000040c0c16403518050b8500300652400034004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 537657428 1250 537656178 537656183
    0x3080304030e09070f020c18060105090613080d0809030a0207060c1a01060801051203130b130e0114100302180108070c0f06050403020c03070605040506030a0212092b0516 75
    0x104803680b11241d9142c2c1c0e00c05014510755115100d03056101000a07041141d00c4401d14850f40290002030210003aa5500b5a8488024070f041b41e520780201c0c0008009005031182030090100600300483c0e2003030300007095807403543d06031200c210035070b00ca03940c03030b40d4a1040c0d00342c000040c1c001e2074080000c0d602442c0c1107107000b841070004a4a01c40c0b8801c0346103400c80260300c03c0c2c2c0010602401000b107803c04203a20169010003078090351a1045240c0381140813101c520407040030003400150768409a03641269100540035091160415580d20340404031840c0341d002200d40701e5a440159103100d07500903c2200d24400100c07120940c411004c10040d50803207001040d41d0207006207448c0c8800020403201c09081036602c40c6000081500f06402e0092628121105c41030207540681c0c814001d5607000800d5500b161412500b8036902c0da1940700d6803010b40280b0000400d0300c00e9940c1445032403040410301c04c541e0044400c04d4075544207141c015100908170310030084041401040340001c221000c03805012940d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 537658678 1250 537657428 537657437
    0xc0a0516080702130f0c09050f0f0402041d040302010c0305040b180709020a1706030f19110a030f140606061c020c0a1b050d0c261e070518010308030403 67
    0x7001d4021810240c0401d40501e2800e0f5035114607142644180b00381745402e2058034021f80d4003030600c0046001a00c840c181d06100c0e03510703290b000f00c07a90b46640484024103052103c3c510b0740400c0d0f02210840c103c02b610100c0155007010307039210801c1d01c00c0c480d1034802d5403ca120907505442d1102c101c403480f004400300f840d89020b0410b010030000380d1743c0003c02103602c8982e00c419580103e030008060900c005084144203030400c0d080e290f0414800590854461040340321500c460b02980340c01003003a040307145e40c01d4000c035125500006220b4921035952243c0d008101ca03050381c10325010901c0d02c80004607511175015005004580b03d22402d80788000c1003500b0440010300c1d0466009070986004008502101c220940f01c8410800d0310030034907078100611040d180d82c1e044480356a00c518036142d10b40580400724214001d103804445102d00000e8150044c5001d9079402c1300d01d22004144055500e40800351885880c10000303a41c1010740125250458a02c4491450707400c41c1d8400383c266001400590030030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 537659928 1250 537658678 537658687
    0x48191e060f05010b07021507050c1003020c0d091d1b0c0a0507240f120506010c21090803181210110301050906030606031506010c051002030f0c0a051608 67
    0x5100c10302c101c81c0600700c0d40c084652610120300c10011645001480e201d80c0d41f01c14000310000840006030820034003800c640c03507520f015009004500a0140c0104001036214591420a075290040031480c00e45000050410f260b500341945031941c40e0098030042c0000d0340e0304501100c0242c1c400013500e0001d00d040107a030191021503e8903464051580c01803100300300300512043c591416011a140c042000d402d00d002a50304444000d04154440c1c40c0340c0c2791150300c81d030024546038410100041001d034410303094003403842100030b200075008110390000f010038030084003c10155000800d5940101c840f40d2188140c007109428404d190740e28000d880302510651925900d94002801200781100d55021059100d61424080000a60b4083d0025020340c0090b010b11049450108a6285854a0301d1680701c65407255001292800545040507281d0700920030400000d6a0b1600194011a51a030201d00c2e1a112400701c1043c62080046003000f1036420407441c007808280d01d00c40e000721802843c4a6007003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 537661178 1250 537659928 537659951
    0x80c0709060905060a080706090506071104020703020f0105090c0d0204020c160602011b031a120316080403140309010c151104080a200648191e06 64
    0x2600c0040c1c000b4542d8a483d00304001c180d040480303244004002c2c0714010404c036444d01001400c0641c90380a16402031400050003401d010654400d540760420180c8110766030301540c20025269040303407510b208154204004580c0c4c8640001e600000c1000040c05a020b200040d804c000c02580402e010569a001d4540d0203568151103010000c0102212380000c40c0e9540d40180784514408006418401c0c036140c00010325040044000c00036520b5000e40c0d403102c9407202240d04900c0c60146186111500d86000c40401c100820040601b00301c9100703107013070207400603a164110381b01d000710180345001429006001c00400c01000070068486170040000a0040c1031103040807459102d070b0001e85c156440000110100003400d03034044540280c5031400c0074016070480004a0394441c010f5000c480d003503140c4810340040c104147c02010700085902d82c00e141080180c900c041c0c0701c06200b60222034000d40005040c40c000c04c0304544001584402c810b02000e07002018486089048002540d81690300d0010001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 537662428 1250 537661178 537661181
    0x20d111005040b0f09030a05032e09060f0902092b120f080901060807050d060b060d0b130b0a0e0411030f1b04090503030103020405060d080a1e0804050a080c0709 71
    0x154029980c40f00d41e458442c0340000441e401410401c01a80200318020699500409494104415008594200c188102208408101c2c13a071810720105000f0309c0003c13180401c1d48085c003210300c03054404c00c1c1590390300105000ca028000440344c0141c5000b140c1c4900c07910b520b0842d00700d00d10b1580c10354540a019180c4c00581c4401d000c0207008901820043c4010f48d40000505034041c0c6198001e00c6194142445903444c0d041c58484c0c40c0c02144c100ca8101b00b00001a0440c40820902801141d254188840c484015000500389940181d0120301503145104444c010381c10070502c007038031140e0300c28075083c10700c12070704c40007481941c4440000c54050103a03902404510040c050b100024030a100c482c02000140b00a110f410310f200d1450081001e00203000481a84e044940403600000c0d9980ca1078007040442d0781d040e0008021000c00600040440e4001031080600c0c0010a0b04200300401d5400923250b007031041d01c0c090721039030001c4000c200013416480100180c0071040c06848500740e0b240d02080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 537663678 1250 537662428 537662431
    0xb130c080309010806040b0f0907032909010b040b030103201f090f0f14010e15070b15030a150209030a0b190912031a0603040f0204110a020d111005 65
    0xd110340001030701004940e80301e4045600240121820044000341800240c450b045403460207005020040016907002c0c043d0f44410001d000e031400d45a00c02c600903503112101440d222601e80301d403664a00100f22409294269400c1d6404002c0148c0303542d0071a01c8203c409030700e40301d15061442c41681403251507258042110401c8041e2642081c1e5000c9258002d4082045a0406150b28000003000c0244070104203407901103d8050303000001003085840100c401c4800c0050242e0060100c1601e0048664100c1c003c0c01d840d07009540004c400d4446da1140001e0b2501c030400250b00d6417060000d80c0114405000c400f01101d00c4640051030804120301007070515035010815107a00c441c43e0104950001c1d401015074039403c1c0100d080103051300c01da4890000b00116400c847c20540e4991a103c0350bd041d2010030b000120004041c0741c0c40b0b1805241040502040e160201e0003181814800304152030101e043d9803444030740350060324240325002021074070071128201402d9188100c0031160380c0c6000610629 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 537664928 1250 537663678 537663689
    0x702060403030809060601050a170a1112070f05090a0b03060112050c0a0206060324130501060b0c0d020714060702010c0204090303020c060c0304020a0608060402070c0602030306040b03030c06040b130c 88
    0x30f000707918181840d1828084002d141c1414401c0130010604500c9c5c2c404c681c80c41405401068031b480781c6800340007800030060210011100c10700015009402c89800003100d00c50550360395900e400c0c03143c142040390280101038166400c0001181305000d07004034180a0359200b907042c913040c46480c06240055050310b500b6580b0025190000410100056040c041507174050f0083e0010840300a11600500e18441c1c8041d403a500030000e01c0105084804000c103450005030400024440107440b240c131180294040c0d40000301e2445040c19032540c0e10300108090040341c045425103040d0808031014003441d80d1018900300c1c1044a00140c800041c1d035144141010345019540041c0c8407003407068010716004001e45190341c4100c0030f004100060b03490714000f00c25940940303003c0038103803502d41c04a80030b405031380c01c0184000c1076072002092166000015600c40c040441e000e11280c43c400051540701c0c42005001c26054100c1d0700020003150380344c03403d144c112001e1b000c109004003550321401c10b4540f19401c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 537666178 1250 537664928 537664937
    0x9100507050a020d02061b09060f03090309090601080f04060f0b062101120f032d080411040e0319270e0a0b1c052503060606030c2003070206040303 65
    0xb038402030342d4104041840200207000400d4103050032001d85c40000845d003110400d1060020700c12285494840a81d948541c034001d400303440341000d900b460b0712a0088103080c0e014080f030300000345480d8810304045009210f44150441d071a125511204040c140000c10300094644170328450b0540d071106001000d0094030019400c4214182848800403102c046c0c1c406e41401c00350018403008501101d03048415076070701d0700700740d50703200d819030b200b422040346140312180401000c0d105502c41d207801c0030b01f141c4120320400c1980140f003044000c110440d62411100c00c3c20740c0c010700561111450019000032485143c0c1000110103140080e0040c0e05180000c0a2008581c015010044002800000350b08201071310001d000c1182d20f4070100c0c2d01064011019200107220041c0907051040900060140160f212440c0036200c0c040d0f00d085900c02a144003c43d1210320b02078001810038440c0c07065840c19620b0303507140e160101c1c60743e0702e03981c414240c01c088151170302003045204c00681d0380f400240021840303a2103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 537667428 1250 537666178 537666187
    0x323070519090c0201090203070e0910020301030f0b0a0c0530040309080105070c0809010318020402030c041d070f080a060f091b030e2805010c02010b24030f0910050705 74
    0x40078003c2d18205590350080d0382c1880360038401030340c010550105550281c0b02d01c0100b991403520303040c80e000203038601e818200e00c0000080f00780a090030840700154040d1112081644604d990842101c08103181c0740700143d000d0024143d10354280b549141c0104403880591186192501040010366007914100e0203e0804d071000c0003189000c0c000c156100b9150300340850f0826140c1c44941c010303c200e2645d58101691003030510f20344501071400f1040144c000d40219124600700b10003210315845402281811085024001219072941100342d04c2441c0756651001d62900010051f602a84082c190748581c81d195640861002140b0302c0000041c00a040b0116259044907030302640c0b088100021010103050801c003482d10040003801c0b0f090007034508010301140011800d690400c10034400024019424410342d1918039505402246450008032845407000c658541000c006070f00007259402c0c400c00034000150f00c0c00e005c841441c1d2060704001900c602c0b414410180c4211081214030b030012840114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 537668678 1250 537667428 537667439
    0xe0603101a030f01090c11010c091e12020d0213020309160b03100501050c0c040509010603030e09071b020a03050f06091c0203040b09060415170f010323070519 70
    0x6501d081d011080712801455403d1031290404542414002c440c2c0311606c031b4200404c0184921580c1d14500482002004050030700040200340d200648502d0358285442c4019104501012050000701c4280a0003000d00004550a100d412080c0c0e040a0307034808040c071803446009160340000c40c0304800c1d5101400003070100b0021441d0042140c0c00c8989011802d1003040360f041207000d15541562000d00300541c68102c040940c610b07060444080750341050401061040c0010b0541015090340e10a8407114008080356040c410b2019086903480c00160310101c1d00e0074030002c104070340c20344580058490000641c80c0e44502d454051203580c0d5403410b41c011010001c14990510004c1c074144007032183c11001c0c40140d071000750f907401603010719506480f00060001c05070b551141201c4c020420555508500d100c0d110019241901e07103c0c42024850b02ca800161b540266540d085069035401048a00d010110030700400603036488141c500840d00c01d01d2004107150741da040080d80c0e54903042119060981c21321 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 537669928 1250 537668678 537668699
    0x914030712030c02060a0905030c011434050307181d06040b100e0402040e070c030e01020604080a0e040f0e010207060b0301230c0910110c030c130c0e060310 69
    0x102040201460030507a030030f00c0380c0d001c54510b402c445c2120002c56146040c0c200103066220f22079240c0340c29131902000c10380048800c240c417803003001c013440030042d0701100c1c0701441a80f0072144003251112610710809a00e50303025201039904100c5919101c5480790701ca200d00003041c200754205450200c8400d082181c48402800100d5004000b51420700c0309002a601090302c110f1903040c0001030007080e03200b6150b507455682c1642c00800d6140040d91042c1000d400250000a009205400241510500c03c080e54000030352640600c0e40451014a04030341548211071604040003910b901640f9161180f05080740c0313016140e428505440010307a55451445d16108035903a2600e43d42c02a4140000c500071015208400307481c0d648032080c00c4825a0f00c955008c03079035101707510090f640015170111031185280c0c81015105174402e11412959401d03a00e0040547e11800c2c10b0b44180d00c94a003c100803848112900000e24011090803e000b400341210000b84a6420072110a007200d45052410019003111 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 537671178 1250 537669928 537669953
    0x60a081f1203030b0301180b13060f060f080706020a0305180103090606090204180e1005060303040f12020901140a17010608102708090904020109030f051501080318040f09140307 78
    0x24100c1f40c180d40641d662100640001030040e40019243d402c00700920249801c4200541110701c000c10a2546980600701989514090704030507214049000c100300d800000c0e031401c1a5055221142040404150b1a0880000001840c1016215040e4030b000481c0c42c00307070101a011480000d40c44d6418864101c5903800c00504180c601800c0c03010900510202180e00000c0518034000070542e139a44101180c51071081e60b01822041c24800300003c2e105c2c01160381040d010340301700c5007250b60740d0360742c548425046140e0761444d5000c0100401003010712416114105072540032400442c40030750307901d0b01c1410110443c03980380e940c03078a60541c40b0460f8580708002c0440b1460154041b456041da440f4840e403809180b0445011703ca403100801c00b0f6a025525102c001c551101207007007030f880503141454495862140c6110f100f41c2c1c2d82d00100b1108000300540d940c07440409140d1b1941910f40003000003800034041110045541d403040c00c0d010030700d148044074010340310800a560328040c07031030140702070f010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 537672428 1250 537671178 537671201
    0x1b0a030c23030c09010507050f070317030610200115090b010302040612020904150b0a351f08030c250512070803180f060a081f1203030b0301 62
    0x9001c1c5501c00480c89520580c0d4001142c0303100243c80703a07605030040c0c4961140703550140452082d0f090400340c2c0c410000e240020f8a11a001211001541d421503051600003a02c0403a482030900841c0ca2001c3d1141c81c5141001c80310551000398000c14400b520300312210f8120b08035030308803c0101840401d58030700542413441401e1804518141c42d14170000e001400e4880c2043c51283c000030525020b580b1604034074000c40c0c804004045d00b542e18000400e03254065946034001c19020800004030704080000c41e0110076184160310070700d0b0fa070300701c000c1001d01c40184199841400742e107510799001000a04400038254240c0116a00d030741d49001c80340b6182e607407500b0f00301e80002403004401303c1201c5001c0404680096828414400040255030705000050300700444a20021412048445000043c49069a0191108070700000280140040c503ca4200036101040381900400ea21044c503c035507100101c10506942411922141c000c20b0307130003090000b5030001e5100c1900c0001c1d03140a103e030310138001c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 537673678 1250 537672428 537672467
    0x60a0e19141903050c10050403120302030a0e01090506010b1c060b1c0501052b0f06020414010813030e0d120207150c0201020c040c09180c11060405070e1b0a030c 71
    0x1d10350b66030313039030b460f80000c21580c000e010340102001038a000d1420344010310381c8810995244560792000400941084809103c3e1a00f85092511400410302c64102c0c0a90060003920b0542c0c00c003ca030440341c0e0311410450b1006504142c4007480c03280d03544502d10107802000c2c80156112911291104401081035072103120600c0d00004000a641d0f200194a02144a007107c4111140070307150b01c5403490704400e024240381c40344000f50042180a0b8000d0040d10740030183c102100344080d00440b00b0b01e8080f600d20390105031070008000030078010030500b44041401021407506100660fa0010461401400c00d00540c1c84400300344003100b000500707012410080d1801805920240c0c0000750ba41c0d0304400b01030b01840c1c0e201510762032548a0181c2c00041c0103188000200c008420721034034000d04405081030300080101c1c561581001c00416142d00070ba0700107005050180c14504c20245000c40a49040000380c034010b481041140f02e0800340a20b14200d40300010001440c01d409031407a044c03050400141d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 537674928 1250 537673678 537673729
    0x20405011e1e17070906021225170c16050d050c121006030305180103050103022218030c020306220303180c082802060a0e1914 56
    0x40d031140c02d030307091040030070690408500c1e041010381d546207541d0b90301c0c1e0580341c0c0391041040003900505d001e411a01554226000803a00c9051780d21030340034490010360440b500c0d801440b03004000003941054030b0700585908024640c002304051a1b40e2000f04e480754aa0401c1c5003040d0008076580394040101020b0701c1d40c2c622074a40c0c0c1e480c1c5445480f00e6143c58490441d58240c5540311404222582c00422102c20820a00740c40703040140c1281c10016041a44081d8601103002e1035219004860480f5406498042e50540000c41079150682c21400380c0346d02d907614101801c0da4100c561314560418000d8807003814030001401414140304005004180e00d680e216900f0301d801c0d1010700304060007905440c00149411421041c000840320307020000d09900310016010510f02404108291459948110707048c2510450081c51403030a00c45001a600202c00c0c40700341415030060600d50f8881c6c0d0300400055014044000c22080d500c110740100c0f0724601c20318a41c5695060800d04030261b04041001004407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 537676178 1250 537674928 537674987
    0x1107030c0c082b170711070906060207031205071209140312090607030c02130c02150709050405040201022e061e120f06060311011b1515090e0102040501 67
    0x658504103111068101a00c00042e0700f144900440110381424401030811030411807001042da14255865544500a40c400003400300d03074910030801115003540181090601d56161601d04a01c241ca640007440410401c00e400904a08056111310690b1703241d43e40248e0901c11428011150043c615000c0d50103d4410440201044251400c12000301c0e1882c0e85c0308501e01e01146c413044100d60080d0080110742135644012078580040041394070b0341d42240d100581020482d1181c000c107031006400304000c0b143c00e00060400350000b560050060048a401c0d00c00380724032150580960400c2884600c031490120200380d40c5004010003003e070384842703070750341003816032803543d8004148100310a10300c031007288104000410500787c02540d040441001041e641e030400102a401d94400f19000417007d5070b80020000d8083e1144510325048171081c50352504601070348008041030014038600380c3e6a5000040c0d041d585000d03000700d92a1300800907859a150100141090304c2c000480e140c10444a03091109 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 537677428 1250 537676178 537676213
    0x12190e0109021e0406091d010b012a03030b060304120207051504050607061d030d14070f2f0109021804080d020f0702060d0e0d09150e041107030c0c08 66
    0x1003c1c0d41e403401c4803002580034400903000300a207500c0700904905201d0349008029000e074034980e400302c0c0b40c0d000348071041d840001100d4444011407103283c4e0414003c442883c8004060180489920038207000445212050002c5ea0070340045504030f41810000900b1210a0b40c180001002842c1c26035014117000141031a82040d40201d02445001e0729010502d1800d0210a8002c0b2a8a0300750001d00c95003880300d00700d11034682d0702c04003100800360301b4445401c0c04209090032840c4103600a94541860300094001245d40c0200d1110354612069074568400400c102c1881e01081c002100000141e1802d03148103100d02c00b101030100640c008080400c11002c03c032400200c0b02124080c02d40181d8412a40103010002c1c001d804003e5044035001c01c42c80e01030800c0b68440c06010041000700da40030b072160801200c1c82220b6014a0320420b100b030b0815440a8000e040401c00c0342e00090010034030040481070540c46070402d10081c2d000403483c0d00f06800b80881c40742050040d10b0404060100e030107000703c0e1000e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 537678678 1250 537677428 537677449
    0x3010609030204020d06050d0b04170415080402031e031209060705340627020f27070203270109060f0c0b01180c0c0218070512190e010902 61
    0x34002d64002174003085032083c0e42d101202a010090200080c20301c58148040c0383d1ba03084904450444032010002c40d10348050040e0f40469824108c0413980380096001101d00f00c1014204a03003520800104040144030750f4806d40b00402c0c03188c001c60b110081440e4180c1c05840141911107160440d0b030034401032642c4681190850344031140d81188101d14040c491800c409c1881180d5002c003103012070300003003147d87d0300001c0380d1203002c03110480000712034905040c4c80b140122000b58071611003501d006150411840500306d48102c2080e160920402da071401000ba0bc00301d50440040e00006400d551b680003807480b540b00e0802c01c0b185c0d14400350203c1c00103482d01107580510000e0000128a00020b103116103407504002c4da200d0403020792035a6039001000050461031a134803001e41841e001c0411244900f003014070311900102458600101d426112440c14000b800e90810040300304030350700511102054541c0107040043e41041c8004002d01c01c001140c14030844911241d0404a240d005644c818420700c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 537679928 1250 537678678 537678683
    0x6030406151203020304030309140a171f0c021e120d022206030b040209150a0c0b15031203090c10030209040c0306050423010b03041e050d090b0301060903 68
    0x28074501c18101901d44840c1c030340c4044040a0341990000070198003002070300407644261100740d0782603141c01200e203090f03542c82d000030381007040c020040001421088070b01e8841c072008001e40b510650001c1c0522050400000e0b580a02d03034403040c444250030f904104465402c2c3d05043d42c03406900107020a1070b240d1104000100075103001180403807003e00309504581c0107507403450b0b203020a10001f40000c0c1e9050310302c0c4150b401081c502041000107051900803100c04100c0104081000551070f1098231064000c5007a80082102841740e030b40020781081905070142c28529400d0b01201400b408051800b00c1c855800c10303e81c0d900f44103225004000051040d00c80c44110340d18aa1500c1c080e008400900600b0303506940241819000850940c046d071101007503600680d81440038500d20001d2035800076080e180620154290401008803c6044010f9030300288161106140d030a031140c1092020701c00c4c0c000507159a00314110014441c1d410102101c01004117102c1c0c90305643c90800003500032030291001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 537681178 1250 537679928 537679931
    0x1608030f0306010201060b07150c03020406090e130f080d06050616200a09060503010f060f060c030509190e06090906060d03140d02032403060402060d0f0c110c01090506030406 77
    0x4070b03030725038001e40001c000341c40d4a4032402c0d110581410700003000e034241409041e983e0300d080044070703405100c2d00803901901c5d0152915030310340b80703000140c0b0030840008140644808c21906950000342101c2d4071100d545015a52040d29400100f510f20211000e550000c3d100700005c0207107030060003220080081c02c9801c03154a840d4103440076980000b6902d400c45880d400320b0342031000319030204290b00010035150f007500204030007000e0110101c1203c0c418082c14268810400003001203e1103200e01d4a01306229103030990a290000e000b04010b4204510508102415000140241c4000e000d40d1340d030050301158074a200d8103000e01600d1f00c0300f00c0648040d02034491002d080702890300a005400e002141040b00c41e0f0340d5203170024442d00075007041d1042c072800c023505090100fa24815003400701d0f148000502038449502c0d15801c0109643c080d42180d0440c64980b50036441801491143d811143c00d1034568250410400114030704005450b035886050005001c1c1c01d11554032118180c0364440d500600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 537682428 1250 537681178 537681181
    0xf0902070201121b020106050901030f0803100306020d0b0f04051006030b0607150605010e09090c2e030b0109050a08030403141e030a0f08060f130b040f0504051608030f03 75
    0x4980300c5521844940d41241440701c0c42030b4a400300303899400800c4c040d034002c00c409602e59041200007002032201600b014003000b1010701043c04000250780083c4400961203003242e803541c4003407d0781c01c40918402007694420504800d07082180c9040c0394100115020400c80c0b410790b4000c46008001d0050004140d9519a29000c1e51a100704a54200d0f81101744241100304490b083e1001e410f1500540d03000946100c1c102200b814464a0240202d00c07040252401c180700505001c8166031940880b0032408001812a80c8800d4444583d112140696404030760f0504040025010103540c0e8400744c081c140e04c04003002101000310540d0103499218803000c0182c00540943da1a06842d100394941d140412041d10380b40703103c0000109000c40b03803915002440300c40301c2c1c81503802c0c4200f210001c1e00700d102c00059070100d1403c0c50b280401300b90748030000a070f4520342101040c121004030946101c00c503a140140001c0c040c0800141d80b40b98520503224608a080c04d07030322501d80c001c214144801010110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 537683678 1250 537682428 537682433
    0x7051b03010b0415090e0312070305040206040504090303020c070803042102060d020a11061f0b07020118090c021516080c040e0c03070f090b09100207090905071e0f090207 75
    0x10840b908814004200b44801584000020307500041c2c0d2181a00f11440c0c104010392400c00802958400e480c1c0200180712581d0b2a28258090100104101d9000d0800c100104442d0382d51b108603403005019903001602d60f291a800140390280541042030190b009100c00c006c14800301822400c03958a01400d49189080d601c0400c200703005e0302c005481c4940c00400c2070108141d2000254456201c48012130700c058560254480300200040b10101900011400900c9131039001d10003410003520605d0300001c214022240c91703a4011454001038082c607112001d400e9550f5040245050881d0000e000c14210b0404030400c0c00c505910441c0c500c14030800a00150040d01d00d503043d20014032056000c20041d1810344102c08642d1320031100e000204524001c4a40040d214800600c2074070030503040c482c0340c140342c40200240c141c0c45120500440c0301c1c5203c04110444035004c3c624070140f151005000b5079007440ca0744040d0100300c010b140c2d490b0859841c10404210b90050310f07c11218880b03c01682c0d42541d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 537684928 1250 537683678 537683681
    0xf100b0d060f0602240606070201031a091018020c0601150c0f03030f1a010801031e05011401080d1701090c030f020304110f040e060a0e01060e1014040207051b0301 72
    0x107900c060b14400341d80c0c000081141d00420700c2044400348800034421520648070441503420140c4207140c0044c014412140154040c0c5c5c8040b10044010080100c44030001c80000c0c54400c044034600395603141203008200400007190203600b100341c101015800c01c850f421085507034000520813090880c42d00c0440c1e904407802404004416900101c59807003d200310b04014019000740e0070609080b6181007505207040c2054030405a90080595900d10607920350746415441c89030030341b920703100506400442c3d400035000344580260804219448480c96142c00511360800001c40141d07400d1050348800c40d569005094240340c191040d000f000114007440a204400a254500801c640c40b8800400d0006001a08a08621081080300c0b0200114245c8050000307031001040034959951100b004a03402c1c2d840c0e504440c00c54032410700001049039490304050130404d01950420b00c10540d45000b8000107028400500c00b13030038281c60951500c8125a02ca0b6a5400c601743c82c1803180c10b040e6100019603500303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 537686178 1250 537684928 537684941
    0x1b110306010e060922020123040303020c120d090e250e10182d12031211030402060319020309070602010b0301061412011b05030106080f100b0d 63
    0x502258141d68603011010075511040c0c80e03880c07282c81d80e540003c0c030214100c120a881c00804040d004000825640103450b41c09041c490601e21291304a00e40815403420006080218001e9000b850300d5600d500c10701c03800c03060301d40500340ca64104418007001c0d41d82207000740c000c545030071240c00c0d101e5880c1c9812130072640802c509611014480452048106e80c00394040308505021191b0351416201c01c070050b030704000151258004030b803075400c0401440c40400b6801202104188541c81103144111800f43c0594081d0003002c00c501c81c504552090551098032030300450080c203000c00c490b80154510800c01d000c0180000c1c0b043c400080000c86041100c003140c000304110103406e42d280d00709501d8003034680d0158001e0100541c82e201d22000700e4581409054112100c0001104000c0e80382c40070300c0203110003e81000620f640f540007041031210200c101d01c08800d001e5071040c4d10781d41030076002003071400082c0c203110b840c0340342c84240200c03009040c4040041741c0c80121000d540f404040c10f600085c288 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 537687428 1250 537686178 537686213
    0x40305031506030a0507120c0206180307020402040b120132030f0d02030c0d050f03150607241b080f130b010e0406060501050f1905040e1905010501050a1b 68
    0xf005001698020b0b822490250550b83c0b81c5028001c0d117816070780e04607039240742664011392008003c2001c0341000c244802c1a244032000780d0f0303d0400da940206040e41d01079403060b65102c8002421030b5048c44500941805000c0c4840d102c0c1c0070050342c030028401280380d007403085041030450f6003180c45a60704101e284034032000d0001795a04006002c0b000b07034803500402c80081c01030040812f101f100e188100c0c115422410504012400c64440c06512002815244035650b004031303041004102207000e1544640b842042c501b281100e600d601c50703164040d52030010300ca5041c42002544006015003100d607507a40040114030041c1c050b603c20036026008d000b4550040c2c0340c040003100200e110195403c0591140d80190310622860790307581d00468141c86030301c4003414180c406009940c14440c1041880414281900d0400d061a40329021001004020b40741000030003001d014107609907001e0700a20340100002d00300507040c084a900d000d010200505038410a6161124003a000c01c5000000201c3c1e405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 537688678 1250 537687428 537687439
    0x901050f0c0d0923091503011d0601080c06040302061b160602010506210703080711090a0b011202090a03060b1203070f050c09060604090c030f1e06120b0403050315 72
    0xc02c20b040604405001d01440a1300c6110103241d100c105141882d0a440b00c0b0080d03c191415074a1824805804582e102d00035415501d40c505062881d8101400811522190000d090554500034050b80350185000000303014000c140000c01c0580e40d1a01500d6050100d160036101e0300d105540309a0030900c103032214000b0251000004201700b03034150b004c14818030060b43d080041e0381c15003165000584001840c4080750340042410b00000f48040c0140102e0340c490301280301c16210190000300b0b03503c070071501715160f01d1381c60303030300c03060540c0d00405502c40105160310841ca41010310000c5075030401d003400007501e0036440700092801500c4500207051a10a581c058940f5480149454856008080404c0d1440e10480d00400c4081c5400b10400340a61001044a880c1901e4586118040c242029800040c141d80360800d424000c0940940440c07250840d03e003010001c180101c140032220181c00c0300d22450320302c450a000150300d107462250040c0d05418403903203c0c0c1c0e548500784080404c10710b0194125 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 537689928 1250 537688678 537688693
    0xd1703040606051906030b0301021612110604080702100f0e04180c0605030915011503050a2a02070602060103110603130f050a03261803040b030f010906050a0303050901050f0c 77
    0x2244d4113050301040c0c4899541c24010140101c0805082c1e00907031400c45c0381c044483c007108c80003031035444002c03496803101e04041d8044803920b5810707030070840c045500740c1c4c43d002c000495504514016807071889010740d50031301240440841c4401424101050740380e90007155200744504809031820140300c4d50075802500340c0307600c07501c4032002025070304251b96180961054807a003480149041c100e9906a94000c100303084094a01c0508502400c4050080e0b1000350351540e10307406030000480000b03841490360292551080c04c0e10300080c23401c0d01e5540608115000480140001441607480c1150fa00702100c159441e0744540508a50001c507100000b4a43c02640742004100030001c503035611200c1c044e8403845008081d250625100c0c1150700030042c07104801500081d01c29000c490000c48000c610b00072a420191106c00900d51640144c3d0108542901c2400421140314070f4011034001d0841540c008090510f5a81c002d840c0d4042d82500b10b0510001150900c64001c0b40419500f003c1c0c250700032108032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 537691178 1250 537689928 537689959
    0xb240a0203040803040f03050c0d1509110d1b120c03080f04051c0302101a041a03100b0a0b0903030301060516060c0302070606050405060d061a0306040c060801050d170304060605 78
    0x11001074801101c40d4000c0f88001127591504402e06038071170740c0100c480003031044000510002040700800c00c584d40203c0c920214220b80740e904804459a20442000b11004104802c010100c489a4005c1c5400318182050304000751040d100310080301c2e0702c0001140c450140e5542e02d0600d0156801c0b00741c005044001c0d0013100b40785c1402c0504030b6402502502c040344201c1000704140c079251108500150070003400d00082c3e0910340d0001c0d07260f0003582ca0000c05003184200107130400c801803a94108003921803407030b40103515040464000602007200c0042c60981d034980403c1d200c0c0414402c0e0418801c007c14010745180300f0303806100909510003420030205541000240c02500210ba0a8480d00e00e0514003040071308003441420b0003203000416001c5002100e658800140c400c0400e009590240200c40c4403854404002c41800f4511400382c4c20f021506102008000c00700590003d40f0414026143d4004110b01c0c0b0b48000495803024a1165269128180744015241540c091500001901c112000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 537692428 1250 537691178 537691199
    0x12031612032315010903050d0c021e030a080307020a0503031924140a0906290f090d03020a05070306020a02010f1a04051806070e040b240a020304080304 67
    0x148801a80701001102c61500c4446005a8241d020045111071030300412500420301e0416080e04105140203129a41c513607540c1c40c00c0c8440405010f01007501c00c8441021031410307011600391429071084001840c2c11540010b507541891100c0984007036000800314050500c01d100d103030142600002100c1e0359041041c1c203614000d001031042d00c4502c0c40c110b003070350ba0481818810112800080c0c1d070b200c85a030174501c080e40702c0e499544289030310035980f40d00010710100c0380c05074500030001011140e010880c203e84031740040300c00c406e00900c0800e0070001ca010b820b103030398140d4030310404c140c030003806940213490180d02d450600310b4040d21a00c0740341c80c0001000707000c0e0000c0414410a50080c01000c00025140b8150b0f00700c0c01d801c849000c2140c040e442c00e414280e129070b0b40044014404030703a00500d18181810800151580000140d40910140c180c3c07c080c011001451030603912000b8041c0001e81c0c01d0b10f003a07840d00481150082c005151042a0702c200300b524040d14450054076900ca80d034905944 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 537693678 1250 537692428 537692453
    0xf07080a020907020f0d05030a0b15070c0503062406090315100f0315050c2724160212010e07080d02120a081909050606090a0b060702120316 62
    0xd00c680c0c9a20b001648041c07000c2103071034503c0b00544c020000c1050b88030050381d444d040100f521a485940b501801300c80e94903201d00c40135030041c074141140e40e0251410130400c41409500b15900940c49507040c0714132030083d581c00c4440324075240c1d8001c41c90100e0a00040352803144a081540c1407182c69003081101116140050050b80f00c15142a00c3e00c0da954014520f2000c24070000c0c0150003000804003100a5035040303541d1001d888450b0500d481030590b006084016044590491079a50034044030080c00d11404801062160810015080400040c40c002d075205000d003c40403c84003140c42401c64070380783c40b11003c0c881c403070000380080c0c06d880185079039030901445117480394070030070014481850010601c11007028400f42400d1a04041001c00e40b0006400b5182c1c01044004660004e070140c0b4922503c1030062069003d0411030800e03c0402c1314a4601504035800350b07181104109169907007408441c031150303040d0f4040d105450256101419409000c0202080c204991140010001800c0060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 537694928 1250 537693678 537693683
    0xd24051038180f100522060804030f03050112080703020106030212030d110c030406110c1302120703110a030c030209040f0501150809070302010806041b030204090b060f0a110f07080a 80
    0x242c040402c041c01c0101c008880c401d81d40d08041403202180c000d0703104000502ca19075182e0b07900310050030030140340c0c00340c1d50050b0b01c550300041c28942400109603200e442586403001d24501407016505010343d0452584000c0300041503590009408402c06000790442c00046800074120303200d00003485011038884e40502a40d8401902d0040c0d00d00c1000219002e54a0311072114005506160500200b982d008040078441000c42c0f040c8000b0849968500400e000d40243c0d1003001740c0ca8100c11051050080809403120302854108003034503500d40d0717240701a54401c003810701d400329200c2c2080b80b00703900034420210307020f8009091a5400449041a070861412940031230341d001104410301c40c041354050004d81351044030b41c0013a0300400c0558480c054044e08000028400a201348507181c2a841003240c440404011a03004202007046903031a1040301031780d46065561500d8260100031411071881180b09400c1400040c050083c1840001c001c2c032a134104440c000c941180b0b0302c03024070507603403502c05804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 537696178 1250 537694928 537694957
    0x71b080c010b01180b030405070e10091b080703020a09030501023f0c031503030a090806010609030c120c03080427020f03180c0d24051038 61
    0x9400711544182961100c501c0180450803413075091110005c62603101900903503280c032a645022500020582100340640154401c00d0300240c03620035410184c0300e0450384991000440e040e003c0001e508103038600e900400034900181e40b0042c3d50815107402403541c0025007150310100d502d081c03012510945041074141044031500c2601240d101c4044504414011300300c01c40400041241072520300091500604050f80640880c0220800300c0d2031500300443e11070008040050411840000f40a1140542018a08441c4550543e240d104030301940d40b1078047c00003c0c1070781241c140843e1043e00b20107142d10400c8543c0c1e9a40d2200c801072030048458402814224080c4010b0302ca20407403013202c841c4500c5503034950960340c035454198200420000d101c4014080c04522040725030b035010556241c988101c0c501014601a5170507249650500c03034020021a00e41030502c04602e070200c2500d02101e40c41d5031512031b800c03aa4082c03134441c01500f8804102c50080607200c0046c1c030008102912040ca016880d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 537697428 1250 537696178 537696191
    0x140c0312060609100807030617060f07021b091f0b03070807021605011d0603070309060b0d02150a030207080a080405150709050409020a17010c0915090905071b080c01 73
    0x80100900c1852441d075403081303980c003901074603038000c501d541da0010440c200003448681e500c3e996a44400c3c50f41c00d0680765082402001014840452800d41040c210310007040d0990071075620070700b1100e000043c21b201c1d80349200060a83c6507400111301400b481d403514404840d541c2c582c6800150810748074a004070b2070000000d03000610000301501441d000b01c028039030141c540302c01910100705281d50059404400f17043d028103502e40c01e0040d4004d054665000412402d80d041581c00c64180001c001d01c109944452100980d440103080c07540d8240c800c4000c9d03070713450740500140c009101d00030008103004e001050710114103810070310141c4294054810b8600d4000200d5910740501411036101b00460211402030026007410761254905900c0603060140382601d03400d1010140101d890305052a0307466901b000c408580c80b0070847d0051059000b43c0811503030b61a4080c1040c0b240d401540b1009a4607000520760314420406032911444950320f40010404038285801541d04c002c0b48000b0039130038100f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 537698678 1250 537697428 537697441
    0xc03090108010611070e22050d09050d08370806010807031b030c0504090e030417061311280603110a09050411070b0a02030f0106031404060c140c0312 66
    0x130b10307010100d031074000607040d03950400160000c40100030382180342e14811459980c01c0c004032224903841080c060401000a07200d04440100184203a8108600072217001c41a00000303003842c03091b103075425140c040420b070480d002520b142401110b034402030284020204401c04090304221110b02400c001e980b140259910401c00307074151920381f81084958003800325030603800c51081c1d1020300c4256040c900f192500e80e4520901003900c480e2540440b80d500006000c0000120041c042c40b1091000706c043c080c039103462080540c00040b10320011745024120b03c07550013565604d4511030140c50300d094800780a005180709041c0c090724140565070102c2d1401c00007005444201080c0d60750b084550399030540e51401c00c0c0c1400060944a25052a000400d01040c00003c805200451040e0590040140c80e8540414040210601a0f015006141c0b91089102d68140c14401c250343c00758011001145541068030704950b100d41e840c23421600b40b003000c901c00050b145e02000400c03254410744444a841d03181c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 537699928 1250 537698678 537698687
    0xc010c0f111c05070909051b210601090b03010905060406050c04030609060b120c030d0e04090507060513090501030305030a051504050c18041119030212041202011404022d060c030901080106 83
    0x3483c080c7c415445000c40e0540c2c1c450302d10842c0281d9201074040150215802c1c00d401c0700c10400079240030140c001500601a0b01420310807014a50001c800030310200e95180c0b00c8030385079200580040e1809848200084480b52050200c030b0040d036100e0780400c00c046850500000910050044a00c0b841c0403400b5070090b00030000c0c45c1d07105003100070041e00440c2000d150a03542d030310b10340c160142c01c01d450314420700100b4414000003004000340c0d104c3c40d1b9904c158010040b1000d4603174000718405851b000050001c660b021040d00c0d48107050900001d01a16208040c0380f01c41c210071105a449400c0a0410001402603400717040c550b11500344040070759000e00100025110000800d1f50344840a0120795044424510102c01d02c03140c60600516100440908902a0104032019034940c81c18903046c2e0364440d82403085100c0442c003111415004d04050f4002441e400d051110746160140c10380700c00c180a08a00900c1e5601080140481d40d00c00700c04444644940092641d00d0124191900000d0b03824003a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 537701178 1250 537699928 537699941
    0xb0108070e0f010f02100501090e060f07051605010b030f010b040e0307080904240f150f0f12180b01030b0c0c0c271311030c010c0f111c050709 63
    0x30141d03282c80044000458813510212184e01c11403042c07440d1080381101521407940a418109030100300003503c64070030340c079104000d8410303110030801404018000e948030f010703075180240342e040c4541c2d0400c140c14504e000d059261342a03581806101003001c03240d80150f00480003400e0a59007401049040c50005803207009120740a80700301d034104400d1a1502d0f060b8842154818003210f4808490326103490300744a502c594024514088000c482800030041102c549424030711603140c105020000100000c0120148165100501a1101c200d600c048502e80081c481e130454804685000028ad040c40c01c0c004c01c0070701c4103548185c82800030034100418402100c201d0340504005104144105051100e94540503003440c0d49072190f0035550f2645103044a22030b02804c050910007400c03800e1414a00207078000003070028400d6000c201d5119080e40c014100c0c00301d5035000045103101c9000750500800d01900801c8040d17000c2601e031810300c100481c900301c1c40c0c02103015000b1103140c562595000c40071680c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 537702428 1250 537701178 537701207
    0x10f0c0906090e19090f0b060108062d0a090c1d010306032301060e0103050a06060806070c150209040203132901090e0a0b1006080609010e070f03110d0b010807 70
    0x10f00c4070024482e08940120702c20482070306000000c200c1801e0722400c52944060f0001c03142915035100b0300100d036a01c94501c0750850800c5a400d240d41c103041c40800c0158491040e041808071410a03004520351300d01e00300c9001401c507910203220320b08840c0710003000450102101040014444e150020301e501ca80b02c0d41d409e03641d201116086001c01c2424005a00c00003132a221525074a8220228890480d03110190003140f04900600d020501ca140c10300a84c0c103c2d40041c0201e82c8420f041180b400e6024540c0000f01341c0101c40b480341d00b00c1040b8690043d119180821b50494000410302c0315a807010034004140f075001d02c2d0300d840403469503441c40140c0c1e0401c807a0701d0f07a000ac240c0014007181085500036004041d00200f200c1c41c8103101e60b80c440e40881c2c221034880071044050301c100115500260400d61050044840e0205981012030b03002c18000d02500600400440303003a4480c0c007500a500415200c011900325640307035801c03180940302410100f01441c0c0040d043c00040307031070240a03d90148400070f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 537703678 1250 537702428 537702449
    0x40501151d160e09130f060204090e0d0207262b0905030d031a0a18110435070306090c08010b0f0105030c0906040828030207050d0c08010f0c090609 65
    0x10b2040c1001a041005405d0000104850146100040c6050601c2d00c1e11482680701503125450135001601b2103d412002d07038420b41254000680d80b950200e594070948034001e0440031000e0300700c0c1844610340c802501d81d01940c411a02042440811800000440700b1408000c2c0100201e614044403d04014460b003074040e400144d0307941c0f030540030350801740350703988a550300451001c0c0c0100000d40b0103142d58030082036103800004070962260607004020400303200940c030a107810714010075a0a0100c0c0000d0400d070181c04590903548011031b40c40b0070b900c02d120382c5e800c07220a191a03080110080140410490343c01031401000100080c042c0544000094010469011182580010746240d07000910903542c20b4400c03c00d8101c1ea03038481014001a00d1540c00426084c0c2c52000800d505089a002642c1210410903884002950005d0365500344c59041d0b40c2c480a9840d0388c80c00640d041d40d1038100c1708040d420036404400e0007015074056400d40704280d071070031a1181c0e20a01070302c042006004080014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 537704928 1250 537703678 537703697
    0x912050408211207080a0606030b03070519080f250b0d0c02010b06270d0b01090f090803040605100510051215030a08040303030b0a1409040501151d16 66
    0x204142451444401100d40c42a0f2a00c6110034020754144800c0f1341c010085070102080c06281911446160060846403c00b080800d03800070009a40321203901c1000c0c852100141000c2e03042c00b810980200030082c00d0125001400c9050b256601e85164004540e4442e4050900c40d00d0088400321142c01c40f0307000300c00f01c1e15010f088030308030002d4102c10021909641d214003620940303840f503500a00200d180012601c0c0980740010258200c005450300c00c52007486003004d4071010482801e00306044814465002440c4501c1c8945030003d81310100d0068080300000c002c010900001d5000315110352078024010a456403240704000c001c0104d41081d00000f07109124021683c2040b100e46900040c0c0500e0350001c1d440b030600002c0c5851101d210449840e0b2001c102002096014001c0910916040b605500c1c100d0420f1412103007104200c004c0f40c4120143e10105040c001d00398000910604441e52202860b07844d00004e8031311030104921000e05c66518000030f21032480c14042c0440414066a030652003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 537706178 1250 537704928 537704953
    0x1401060503070c12170a020906041e0e010b071217061309050303090123010501050a03022101030b01080709020304020619021218040615020c041e06090912050408 71
    0x340e040100020144685248400049181154140c1040030340e45e5480c0e40013a01140d00b4511020007a18070075066006011441d2940d80700402d40e01542e07522150310541032150b40e0b5400b0001c00b5980160303405042e500010810f1480e20780100714050041d202404110042c0904807824a48a90b00707604542018010881a1515550900300c80c1400d142c040b441c2c2c0456110141160b10030b8424084070b03036440c050401900b8044c0c0c80c0b44030350010f02e04208503d40c98000007804620900042204245d80040c1201104810000c004035a41e18201c020519607124034182c0a08d40d001e026410051240450000e207201140c001c0303074402c2e5409800d00c1d0901681d10036464284220003440000c1d402680d0188416106440261030f480000110b003002c1350700e000d004d00c4100c900380d80006004034030100a8543d065000a4680c0e2100c0041d14000745c2401d40903590307422250312403104490079061840001c2c0c25481500801441401100801c41d4180b560320160781601c19840381c003010b50001c1116624 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 537707428 1250 537706178 537706187
    0x230303063f03071a06040510060504030303110f0a0201150801020f0403020d0c080d0804170702010c030e04150303020606031b030a060203071b350d050405010905150f0a140106 77
    0x36440740e80c0450b800c2114a07500c0182c00c0f100404509001c81440d0104405890940a2190401502d1001440003403c1000041c01071140d400044d06050b2503488020b0920106c00851340d481e0b80020020347c03200200d04d4000c0c080c0020000310300c0b81a00750540031a02400610881d1380502e0101c8031185802c1c034503400d03c0b41d8141890006c0d64000c2c849800001c2c0d100d803e004840d0b008181d03a81351045403401e81780c250a0080c8054145003115014441200142d070852040e00c440c07901400d120070084200c00c000f50140000501a031800d02c44c100c0000200f40e000074241d40070340401c8040d034040b0041141c502200c0c0c00341d5146994158046c0062901156040e4000c42d00301000f440c2403001c5910000340c0306200c04075034200b00d8100803510705e07402c1a003141103442801c0d89800300d0700c050f5032680f400b42d00c1418007454440d01c00701d55491000c81c04204096203c218842c2d4444203480c018004600c400c001c4507001c941c1348426032144000503010b130340113100d2000070401041c001c2002d6400e00d08201c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 537708678 1250 537707428 537707539
    0xa0b0906161d19090c02011404021903020613060e0607020f120111030c04060f080c1b07030b09012007051002030705071b060e04090f020d23030306 65
    0x90445010720326507842d5161022407040403003840c6a4220102c2c50861310070704030b43c1a10066011649041407a868100c2080b4050b030b0800d07011200c0441c00300b002e1241809481c1d044e4002540305000090780d040e07581d0325125590403100c0a46a00051300700013814404144124074000390b105150074245036142c0340a038031012182e060b0100005001c0c01b0b144148101c0c6d03000b80d409100e044008103080241a500c0101e0540004240c07410390850b04103140d5803500341c00758481017180c140300c1c0158482950002c210001c0115004205d040d00d81c180a0340c41030081c64200f088030188030510310460080d440c800220b500301c540c0440205030888025000034002c0d000507011a042102c10084d840118562104c003c800300c01400f1240051403030400d004d801c1c8400b000c1c140d070149040840c01c43c0840e07031104000444e190161015a00180d041c41d009048000d20342c0d0b816a040352400ca003100680000003d1442010141e904110402d42814220200c40d0005410046101c06541010b00f60405a1101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 537709928 1250 537708678 537708707
    0x90c030a05070e090f0f03180402130311060f03043002070b0d0b0d1101020601120b0a0b010c080301060206041505040b1f090e03070c050a0608070f020304030209090a0b090616 77
    0xc401001805d8034140c1400c4001803002c015a10104009050f06112403141802400440d400c40c9410038842010886800d0341c8400360144003000c2c40c0c01e81c1c41d240c0a0450303c54160003281c00755a440d0918121143e0500e01c010341001c4c40c080d10a800f200700f2a4401d01000300c5281d00101601031030314100f0f200d550300031f111034505039854030581d10b140d0b120300c10510f04c000d1158109c0c100c0070011100080c54088160b1000286940c001240300c04520300980564000c101d00d00c02017804294100103134ad2120010400505008001000160311507000c40c009004070302c03603161001140206050310707060321004d6030041c24280c1c03801e01003013015030480103400c1c001d52407c002e015900d660365160421140380c03a48880c0c0642000907042c0401283c0319000d0060301c41210300c00f8515040c28001090744800501d41e00c1400b07414040b9201a0f8000c00603100203540c018044002454084140c94445100040c1180c03400e01c0d04021034900c0d180070070000c3c4a50900607209a00b201801c804540021001106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 537711178 1250 537709928 537709933
    0x60213050d03030c020c0f0f0d050c0a0e070806061201090915060b040602160e010e0c0702151909030b13060923160302130b120114090c030a05070e09 66
    0x14039032964080c026110b4080c1e1800030300f0003032075003000c0c0c1807001030303004207101d04501c040d20700b03059a5059480d1840c5070141d0301682e02222030320b021840c2c1a2041a116409001c028002500c40d2841c4006881040aa55072a0340d40e15044180f142c02d001703a980b245080303072455006101c4072000303502c44003040e4040c140102c01180b82c4c0d080c0c4004c60364240c10240c103440f4001030600000d03404200b07110400c4241810b00c441c0d940b41055129001e5410700611840001c4803020075450848a01680d800030b40007002104a2044465074580035071140c0c0894000c82d1001c081c85801f00d0040340320a08490b041201e1418903543c10498503803140768850110703602582c0c0e0540c0b4021500790070ba0140000c240c1802084104060644145400390b100a806961650b03107200f1b0005031280c0c2483d5012406021000c581d80800c840011010b05905000e0755243d0310301201c020602040f030703465a000b1001e8a0640b04461880310a050300c1d00148100506140d00015003040345038007a5032a80e46c00503a4905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 537712428 1250 537711178 537711217
    0x70b0f060409141006050306040210030b1203360f011b050f010509120708090f010309050a3002030313020402070218011d0603060610020c180406060503010c0c0602 72
    0x1c030401510ba100159072007960004c2d001210b81803140c852075015100440003000c0514007580051604041c1c2545c0b141056250000810503407164942e405c1a00390320303400e46c0c1e1607020070a03410047e4082d802070141c07807009482502c3ca0620103450002d044a40141401c07131031403070000040d9002101740030060301074002c4581840c0401c60901020703121030300c5480042031508010350210b18000b01c0345049400c13560100300480c00035800c0c2017282c0c1140c005650f944d50700c8008a0041c0c00034219084080c1103030041c0e40d458410040c00e910360824003503071400559140c410321002c1e951040038081019026a00400110b88520786003e003140065100400c05032400d4403e6011800e851091011505800880740051100d2400268059007042d2010701101780d40c82c1010000ba0b8920740600445c0c00340d0501c2201c8003205200b40b04045403400003802e07034161150018040c00c8103407002c40d01952020302d41500802c09107810300420501990360380d5201403241590b1685c0c002035011380200346a2505510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 537713678 1250 537712428 537712433
    0x3050c10050d0e06010e011a070f110d0809040f0204050a05010804060b041401090c0e011e090317090f0d03021f060504060e09011503020102100c050f0c07080d0203070b0f060409 78
    0xf5000b444041402800c030075403600e02c06100c070f680b040e08150340ca012412205680d450490081c0c41040e90050500b490301c25490400d1490b10b00214207003a04100114416414001201d00038101840c05a404000741150551550224081d9000f803940c050080202000300e0340c40340c4256904a40078240001c0c8105505001800322818041d10703880c8001e1030300040000d00058410fa2210090b542841141c14060b040001c008030014132003940540c9200380712810f40c6200e10043c03800b86034000303214040f40049800d44190740d04a07c040c2c80c85641300e042d00703c4650034407407521b1101c180d068000301136080d8030b40c41021204090419441c801e907a00c1c00001066919030280078020100361901940d82d00f00140c078142075a850b4803c0301d046c01145c400c104010b036400038104505603144400041c0c0c03003124440031215031242000c4410070a2001c20032102c02c040c0401c82e00107ca441d802100c004111400050381c40e4060002c0c0076204070411000110401140a9500d40c06203008100058540c0710ba03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 537714928 1250 537713678 537713681
    0x1020f0a0308071407020d0201050f0912010b0a0803120a09030c0f150b040c080c0901050942030c0a0e04053102030309060d1806020a02070b0403050c10050d 69
    0xc090a8002640c01c01c24402440d130000b940038030640e0707164000c52510105070040742800c0c0201e48000e0400400007001c8a0703100090f03054a070080c0340180012178818440741c0da240604a20442203100c0c4604100000300500c00208580195a02c20700f001c41d0360351001050001000c0070300c401d40510440045030b5000400c59030250716054802e003881d03a180716640080b03600b00d40200b52a2805940340c03000c80948917403c1090741c1d50024640020319540c80c0b40600480703890003646c0d842500004032001051031440d92503410b1544900441c010840240d01c001d0110041d948030346011a500300c1000402c800c0d948101c024800c00314582000e4900048030408141160700458800000c00d200c41200e880151040c0c985440070003d103440c282038448184c0009840e44108030340217128460018108030846003d40201e400c00215a0451034078030f00724103100010303500242030400113008452012541c850601d0944098035001002840c0781da100505104842a031044048144082840030200c024030700d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 537716178 1250 537714928 537714943
    0x1b182102102c01050909040311010e03030f0709050a0303050c03040b030702030307030f060b040e04171b0106050406120f140601060302041e0b030c03041a0a0507081b041401020f 78
    0x8660b80c0300399204040310644030001c80c00040200d034508840c0c40b00e2041c0e0713105050307480020040f14a500035846514059404d0398080c034401000c0c0d428800101c03030b902804030181d07100e82000c0c02c120300940d40b24002260b0000d8113004440d070080003440e092000c03901c141c010f0180d9808007411603107050340710000750825402c100c50b00c400580c0300100704013849905004440070090980000c0c04000c0c10504001858010b90040700402c0c501c520018007400149008c0311200300d100e41170265140c040510212050f401c8021206d110340c05c00f440041d55060600c17800040b261135180c0b10591282c0f613620074202c3c02c94200140d42d0302c00080c8064880042c20701c0628001c11180e240182ea031443c00722580300030b8104400981c07100c0007046040044c02c0030142125406a251064141e80f981c03985481c1e030101d0f50746a010a40c9200180c2003000304141648654050320712601c0f800e00070341d11040220108010075440c2c20705118107000c2001a24050074030021308800500540d0140028814240c2c5407845 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 537717428 1250 537716178 537716209
    0x18050c0703230706270b061210060e04140c01140904090c0f08070609080a0206070f050303310f020f0102011d0a03030e0a1a0714030a1b182102 63
    0xf622400c03191807000e9010000c01c03412145c03404d80040ca0343c0f0740720000c91640050032940240d0a02a0340c0710700c0c0b04e0a00c0701c0985000ca0240420002c0d07102d03040c079190800119001c039003141c135448000740740740f500003000036042c1816910910340c1e082081c0e181070f403500004003090b082502e46100800103050750762a03001800115601c0240c542c17500c5542480e0500984c0312109118903014280041d59000c20420040d07601914081c3e590708903813426401c1c446c41c100000e0003d020201c148150104000e0320a0704d07016040441d01019080704880713005034201288000d056100b000c011500504181d0b685140d6100140000520414403600713040030a962086c104ad02c0c2d0300300040c0035080540520800d420070000c80020080220b243e52201d1807907044610441c41188408001003c40d48614800c00310b03900300503106901c90906080c400c020742070503052030500f50142c0041c902414480e92040070715056801c0e14003803080c0b8280042480300e0400a0070051101429400c40c0503840e25000710310641e2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 537718678 1250 537717428 537717431
    0x1a0904051c110c0d031107090923101a15280c0f150f09020906060a090b03041e050f120403030807030e0a05070f18050c0703230706 58
    0x10040000e0001d1249100341803001e0014584088644100000b0703040c10001003074070140036001c00f909003920329944000a1032003520079090085000c02854014049251180101c407802554281c80140910541c01d9480c556600c55220808005c03a6500810305500100e029401c1100d505004500d504020080c025028680020360301c1103088a03000e60903264200c01d030600700c2c80380a1071000708400e02c4100301400b42d1002d410504244050b44880036440729082ca0100405c094045d0010080c1c400144161b120f800c1200c006805410400201c400d031041c07541e00d41c850310341080c000700c0b116000500159400c004441000214209492418051501800040407081a0340c00b0942c41c1c41e5055981c880c02c1102400104002904180802d800c52031500703000c81c50244881600307280603500a005080d070300c115540000d480821a1000050300c448024072442c40c017004112100340c1d1401d0b5080200c4040400c07141c40400d2160090301c24810381403c2202c0a00403503c80c00450760480881075880f075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 537719928 1250 537718678 537718693
    0x2121c090203010f1e05060102190302070914040302060907050f130204180605090702010e0c0d060b030607030c110a020a03111c0b22021e0111010218270a1a090405 72
    0x14840d00c0904017000311005414006890101b00007900c81802640a800b1209803035003074001c00d030080c07201c100a0f1600500400150031005c501c1d0140c100c003510103402500900021844081c80441c554090b5031015040703102003c01d42c1c050004003800c040260b40200d50074400881d0466010048003030a03501071101140141c202010880c55100c05004001036a1400d122158030360008101c907000d251003103440c0c3c4d8102d602400c1602c06041c0924040e41c0c0742c0110400c00013680d81651143d5a0240644d882c8507413000000e94807595000c21000c045d5102e0011f01041001511601030048036110207802c180340d050062040f8554151f026608441d4001c10804000f018506207841e0300900e4140c0742c01c1e03048440c590b00460310042c8000c4814400c20315030302e401111a405039151780c4c40c0c80c40000c000c55a030342d00512040406048004800d100d0000005558080b09542025119030700c000e2050714402e88800800000401d031031030401001e02102c01c29003400c1d6861203c01131065006030080c0021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 537721178 1250 537719928 537719951
    0x1c0501060801020304230c01030b0a0e040b2706010b0a0212030702010605130b010e09060301110c061b03062809090b09160f050906130207050a03090602121c090203010f 74
    0x1340100503468442e2020442d52118110000180c00a01f214282400510704d0751180101d401207036503800c903410075402d0f4070501c420098041d8515203c2c0488541441c1c05003554503024843c042000c081c0c28190380101c0c011320846072588000c3c6000f401600448000c22001207030452150011140100582d64450701080703a4100520700480e081c48069081022004500019001300d030b0710031100e800356644100080894500750b1100d416402e503e50f140d922413842d12005a80c511045481e02c0003501000300d1071403a2000720080d207000341801050100014148002400c0b00c0a150399a103035203079001000020f00101d80d200d4086220701418a50080d807030034400c5a841e01c00305c00c41400d005001030100700068441c020340310040c0c032000c5410b012140c95070000aa048502e200c0c40190342840010b20301c042001c0051640861480703512a12071869440b04243d840d9680750002c10700c030030001c001401160313454850007894181040800995a05c07240c000c0303400c582e0044e014201959803030004070342 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 537722428 1250 537721178 537721193
    0x406080a02040b1801020703020901120c05040207232401031208060307090b06040e13020306071b23060901060f09152907050102070201030c1d1c0501060801020304 72
    0x188449005015860286003060743d02c010702c111081d0440100000c1c8521500b03a1003404000300842d0010886030003561908240240044a210202d400303004000002580c2d06060013619082608a81c2c00b80c0140892560200e0411100001070300c0d501a801031220355042c0943d40d071020200340c007090003c541c110307e0881c0d08411500f002c0014809568100241ca540004803001907030318206002c00d2803c114004164240100c0d004410800030200810141100083c5081c0e00b8a00031011960b10740c88821040c0c038411301110044078084a00340e800004a00342d082076800e5150070003210b90384284051026403e200c403d0b00d6506050351220810030040b204444480098030742100101300ea880c2d15000300595071440e200399004403001500c40102c8002c0707101040b4070080180740e0340c0c0d910041c41c03410b103000b98400d00040340840d190000381c010061040f6602c4500f003210b00e0b01c144448149a0400c14108401c1d01c6450550751100558000200207028602c01041541c00160702d82c24580780510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 537723678 1250 537722428 537722431
    0xb0a09060c0b0604020f0f1801030b0a060909110706020a0e0411040e0f0c04030c0902070b0f22060f02040e01080d050c0607080406020d020712080c160201050309030915040608 77
    0x40411040e00c00003800b0072510b0b50400c1e007100c0b0407180141d40f908014a044058000c04a40071001b00000c100313100102142c22003920348070801d03030b020070201007040104004240d580c0528000503003071007014031843c03800d50302510b4007211a4000904018450360f07450140d0b480403240d80001019161210347e03500705409427003003036250040e03205e05081c2890846013107900300802d81880d0711071601c0410001421101164041d6800500701c40a407a00d034108000070b0f50141c9812105042c11600142c40307407021079229030082e241d071806044d040700785508141c043c6111400684042d80d880c25041c29039011440240000e00c0c0c5034149905644c902a45982001341181c00c807010720000304107140d40340c540032a810b540078400d402c2030070b10b903100c50904e1402400f42d5812548001d10009010f01484401c01c0079904958031750b07542a00944c0c85902d40b01042c090000030b1390b01c041ca5409041c005600850246521845110860341000e04010014010074a0015080d04035140001c05014103a40010181d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 537724928 1250 537723678 537723689
    0x204090923030a05031021050d080c0403061a04020c1b040902030a03110a06092d0809060a211e0c0c030c02040905010509010606170c12040f05070b0a09 67
    0x800d0100d084190390301c80c843d010400c420441c0020008004130220908800030303100041c1b00b4144c071080011540b103924400c400642d103e01ca61401040500d01c110000b9124a00320300c522400d240c61a40c80d0009031922442419500400c0c1c18000e00b103485a1000c0c00250400030700a10258200e41c00c0c1403400300e412a10240510f007030110400c007503200000d00c0100302d94035180140e000502070040a08054284c0d00c014403c49c1400c0401007400206103a038101c0c40744940820380000e12200506d020280c801800a1110700700f408031f503c09183c000042d10000040d8180a03145407140035103150058000014a07030050303502d111680c046654500244d03080c0c1c0b50f26004210080301118007501441902400604100c00400c213071085484580058041350b42c400b00a100d0f03810812195806403541307000e000b000034400101860035010b4120524003035502101920314040031006c5080040000030016071b42c40c81d0160070355000a008118450051207007803d01a120110800014043c0585a202 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 537726178 1250 537724928 537724973
    0x1b06090317070c030501110901140c0714060702280b031003060c030212101502120d050c0c030c0303060405180c010e19060e040501091b0c051002040909 67
    0x2031000800484031801190500081c19844940b5840e00502e10450384d0001891075003010121219104d401024000d242407d89440d10b480c01c8404903c02e5a0049060666040d480070008201b210144020350012030b10252800340703803401c20f8012402e0f0300340442d54501d00110005681e01c200703e200f203c940141050440300c42ca1820200368980ca0303a00c481c08041c1c40b1550340d10151503400d010f581211400000007400b16642d140c4200b140304100994410352003502c40070351b0502010740c408948110340d42d030000445410701040c140504010f11004100c1c00801004020400a8a808001504101c0038600c01140d41c1c0c81d00c102800b080d240d0240000c18030300b0882d110b6091030400070a4000c60a0320038604552074050003000201403081c0c085030982509449103004c40d4550344404491051801540c00307120340e0340c0c1d82c0b01a004541e40e10000c1c2401810b01e0b00d01c042094418220004d0305030241003214a0703054400080402ca0303000d584405085a654207107801044a441c1560b03501c08400841c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 537727428 1250 537726178 537726197
    0x40905010b090d080c0709090803060f150d0506120f0706030b06120109020a03140c0703020c030a031e1101062d0f061b0c090507120b0a050114090d1b06 67
    0x300f08010502d050040c49048007050a844408040010100070b001d04c8009100c0c400242c10a145298416605540144c000240000103400d22540c0c4c000510343c1d5151710b51a1020b040200c000800740a0003855001c9c030004101160844200130b03d14902001401034141c0924004001e021035501d00545402200188401c0d00b0303420341401198111020500003681d1841240c10031001004c01002d40c00300c5c0c0100710140085005080007500c0d07204d109808a0f000003003403c041544d64064820004c1c000340801030742507245000e4070070506c1c55221904101c820a4a000081825105690806246041c081540310701c800078013041c0c410181e034000c00044115040640e500301c01e0105004c2d10003404680888540c0c10081e0f045103d0002e5040800503200580b1800004050001520040006220700340e840c8200401449070321003500009107010351041c54a0015a105a45e114440c1ea800c03605100452003511040c1020300001d2188914010030401c005452110725003a412103810410443c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 537728678 1250 537727428 537727447
    0x30506120c060a030c020102221508040f060c111504330b060f041206200d050a0e010c0206091e03090d050307050a0305070210030b011209060e12040905010b 69
    0x804031503a0348910b140214a4945100040e1f000e881504072510002c1e500c1030355585a40381510341d00b4140e40210321030011030020203204a501680599001d0498040080c68800050050340400c402c510607013005900d041d407061450f07051807600c1d01c0c3c44445a00110030171081101c2c030715031620351030303000c40401320340c1802d0112103040481100ca81d00001c1c1d07515550020039a5620080d100a10440540103560b1911380d0402e42c50042d402000312441c60400c03521081e400d01030103088260b00d40f60301c41d09042104003d0707030101900780540300c68000c0340c0d902055413200070f080c05004110300c1245c008000300c0c2040c4040600d03140300b12040b441070400b42d84042084550101c2161005441142c1d000010500d07400e01c02e05500c524900140f15100d000708000825800a01901c040e81c001c0300c10005c4100481000e40030b0b1500540788500150b075040da01c88404102d83e00c01c08400d8015040028000030107101a032070214544001c01d03031014042000c00c480841c1c1d0140b1800b500d0356928084c00e022845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 537729928 1250 537728678 537728689
    0x171003051002310b0a110601081207030c060209121b0a0f06260916050301090804030201111203070c050f280303021603050705060f040c0b090607020907030506120c 72
    0x800301d4a00c0814a8914100030b0001c2d840f01002034680c59091580e207118001000c0d007103c2c01c0d2514060140030700e0000040ca1900441c416034008154034409151a9007a98100e4643d01031b160102c4881e0340c00d029007040c03500c1c0c6ea1210710580e1290380c01041083c860700d2800000407025114940300304401c100900101c10405840412102281040f0300742412003407000901500f0340c4c0c6051521010f010800103000303c002442892712440165415800d52501c080c142a135083c1c2c04081d14020f000c0104100551048908584030f1100100380ea484044220018134180d03c16910040080e00000002040c098284a160b1403a0400001414112503031801c0100d002c400c128000c1c0843c19403590601418045e804460240e40e500b0a40c041c402c07007500d009811600f0081050303450f40324a200042850480e02010381c0200c2e00080784104032841c10f8154041540410741458000e58180140f8005880f501919401040703a42c40104061400344140030206070041a18400c0740c1c052040c808040d2501e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 537731178 1250 537729928 537729967
    0x30b01090f271e0b0612060c1602030f071e0519030f02130618110306010801090c030b0603010b0c060702030403110d1a041a01060f12020901171003051002 68
    0x3101441da904409401c10064041c40404141d034203c0c2c0c0781007100c0810103c00141407140c0703400c94580124411013070780c00c1e40d5403004645a801c102d804220914000c0188071a000f4001d00c02011101032070010000c04d0306020413940543d51a80302c142c10a6030181c0010070f4100501402c0c4d076498440b481c10382c00f55652102e213200c054440340d41003810b0320030341d12545d400302041c8000500a1001956500360840024287c3c0030800407645801410f0240740c04000031039004c1c4070140e440140301d07400c2000d004002e00b100388902081c9540e0f6003211551b5142d000c06140203000c0300698545501c00d2070301d09400d126008242d40c04541040100303100041440403e084000c0c000e8684441b006518600741c41500203042c4100038041010041004112000c01035206c1402d0404241030a41da985000351241d00b040012400031407610342d45116401d10303a5002e040001c0741450404400e0300342c0541e15544e400280c1ea8100042d42c5240f0610612400300400860000701900c2180750101e50b0f20314690505a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 537732428 1250 537731178 537731231
    0x1501080402090705120f04170901081501050c1e010e0f15100306050903071b063203010b12010f051807030e030a030204060801050307060c080a1206030b01090f 70
    0x107410303010840f000c3c851010b4400100750302205080904025001c030803038502c101c800f215540041c1c1c3c82d4481c000324180558043c2d51043e10b0713550341d50700c0d45010001200070044200c1c1c10000305024110040c03c0030020180902c03c07402030408203c50320329916081d00d13610344c60042181e100c1c0c03540100304c2c036000401c50f2840440c01440c1c4010780f0703074004a078001c40300e0fa03001a00311070500d8103011540d500480140340703e51049450304100282a4510783c1e080c0224450500491041a40c90361440e4004200b60320180400c840201c145211500c03401e1242c200307804c000840c00d004187c00404080da208240e024050030201068004d02e0200000c0e148030206a0403a07990000c0340c0401d03c0e0314000c0c2c0001c0d00d169450419261105040d4100a00a40080c800c02000400c02c0c1e00001d528140400c0c003005a0711356588038550b001c160340316a0b8455028100f0f01c002c0100c4014401c1c81d404044c420400a144203072200e40ba01e5140110a000362000802d8611096145c07107013603c3d000415503140c070843c1c80e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 537733678 1250 537732428 537732439
    0x10801090510060c030309051609050a050402030309122104050901080f06070c0501381507030c05120d050406060b16030807020c0a0b0d050f070905040506060c030a030e061501080402 80
    0x50a1745402c070041d04a1840c028864410524000d051202404446040c4c03141e0110420a81e039030110310300d05a42040d50040c1d0150410002420f16042a030200042c02402c8401c0300d00130580042148210b02440b03190314140c84000c1400d01ca1403402c0a02d003030040203c40300500d9036a500784130054407a14094170110600040785100801c0000a402c0100c0b10816107042030702a00c070503480308950181801034040304041410051002d450038403041c0b00600000f2000d00d003882c0007980c05440d0812401c40c01e03119846102c1760480c112000c031000b0000302d0210400411203007084d10780803081d41c1244e000025038036014003c4d400d4002c4102040a0b240d13400d4600346010b502e0301d49059040802c00b80c0500d400c110722140100303079450210020101e108020004010b60307903d002d0b00f40200041504d0200c00151050020003507450207420058200c04020500c62a0180030b82c0d15500d546e1000000d00702007511040b81758112042441100c2d030246203038032a22411507000c80000c010702401000284181c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 537734928 1250 537733678 537733697
    0x40e0915132001030e193e0a030b1f06170f04150f0b030c0402040302130b0103020d05090109050d36050301020408060f2a0702180a06030201080109051006 68
    0x2a0b00c00c0c1c00c05107009200c03400742d46d10442c0600c00c02d203e00b49401c034140c0b091804070908103c070541503824581000c0c5440134240c1d000c0e581982c180903e400d000c20144d8461a100c0303003c001301e03035170700340640c0208d580c5c1c1840420005c584041a40250b015031117001030208006140d04449070100c40254040704010a418981e42c551a0001303d50800b1248005520319000b40040b0381511b0f13910403a15504d0071400c45088482c04410081a4421400300a404c240071030740c1489403c4180d00165081003050401504003003582d03851908450084442030301503034649180c0414801309010007410340304646010510310040200c41c10413941c641031809000190041c1a01c0b04070300c0070000c4009090024000c1d5035441c0c1c6d07030b0700c002d03914941511071040c008050404140c91401c0003400c82e4038010108a02c85003009001d0000c445a00b1400b030590300580d0101d062440c01d58040c150a00c9a100f41100040950960000420100058100ca072200c0c0c078000521140002070b841c2d4404a402c075180c0714821 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 537736178 1250 537734928 537734993
    0x9040b0109080609070f0b03013203030a080a0510152a080307020d020303010f05090402031e1b0105090f0f03071a030a0b010302070c1a040e091513 65
    0x401c10309901200490044909004843c4004152282281c2d6151048030016840f41c403003400b03c0c4420b02ca0340002c0c0342080f460240c0d9209034100031180200a460b01056003580e207001c49d0443d030040080c400003804020400031486141d10a164105000d80408810b1905041504000803100d6100354184031070401c1a0f01440c0303002401d10009198450404c050050324501451290010381f0100054040c54082441403440042584d0403607201c004c5201c1324901d820213111040e14090010ba0b09402440e4004990700c2655000d08120f0a6003802030a41080d00d02c01411407041540300a8100241040b00d1a11603446030400921118100c500c035500c1302204000900d04040c607800b90301081c0000c0780c4081d40038034210103180314054601c418401890300c0c0700118100d2081030350040031204032000130b005600b441d005907400f00381c0004040741350688a807020103000f9400c4615420325405214006407101d400c940c01074102600e10300142605006aa0b842030014041c0c900380c80e1071404d103024100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 537737428 1250 537736178 537736187
    0xa020418050703050a02010305090a1203020a1413030b061512090c130509010b0d0b18010e1905070b0309031e16030c1403030919050102040509070507060513020609040b01 75
    0x9660740401200c0b0880d80e2450080d44032154414181d01281c070348000564200e401040c101e0300b80d54040300303901c0818000e480540080d003280582030100040e604844441c03c0c2e002006040790b540c803a111204d001c0c594900b000d29040c000f801c1a0250030040f5a241043c0c4541e01a0f4880500408240c07405580b40c4c0c04852502ea01c83c3c0b0f80035032003440f06071800c1003000b80b6800140507004180091080390400010700034140e8200030014551807125000a00b015131496603004042400f00004c94418640d030552490040a42d03000200c04e04000c078114101300f820000340c40109803040b01c640c15441c00308806a100d0188618907204a081442000a00060481181c0c5400740482c0103240700401400c00900074090701ca421540000403082c10501e0407000420780e4412581980180804c80514451602c510070b90303641160159020300000c50340d07a035025000d80c03003452665500c61315800c5906041c010f03607030054880700c48a03210361901409030711848201c4024440980340840c040800800499 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 537738678 1250 537737428 537737471
    0x602151503031806070b040b010e01060f0503150f0303220f081c0302041d060103140c0901111e0102090a120f02061c060b04080f06090c0d08130602031b010504050a0204 74
    0x2801401c21b14200001c10070140d10312810390b160344d45d840d80c0d0ba80e242c103015150f030401404104046201440000e01a5502c0503444d42003201c0039000410380004c910110b86940c000f01030318102e1801100321010190289916807008141620070f50242c5440c21030441c0d1074208032050a55100c610002d4030031f40d81e000313404480c000d04081038a1102d41c0c810310103a50312481d081d9041d50001c0e00300350b400d1510840380c0d00f01c03d0040c10510041c83c03800613148010340354030340140080e00c0e481c0105c03214501c803030b2100001c149003484680005aaa0042c1d5010010740b004545c2100425010810040c0003140ac10b400c00c85040340d0585105a80b0500e0007481c5101085c1c50320500801400e015000c50525460000b800854110303008850301c0035040c0454030744404084842100c1035000e1594030500c1e1510b803c413550b070a801110030910b020014171010292183d15000800543d00c0003a650020281040186214901841c001c22207400c00e0740d02d041c1c580004100c003030300c950f480c2c0c10031031445207450701c050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 537739928 1250 537738678 537738683
    0x403021212030a06142e02011d0709050702030715021602060d060501030f0218091b0706050613140a0c0e0d1a06030604030f110106050a060215150303180607 69
    0x8030345074503045410f000641903600890400020009420409080c5185510304281c41b01440d004021031a20a100798462008071070002c642d21180040d14410308a05c0085282c0441c00142150a0407c60108144e44024040008543c010040c40d000304401c04410380c11a0081d560141c1e6030810b00d180e19068280c81e0002951180c00080c003840f078122103510841c103c0b182a241408103100400180e0100c0c01107000240e60f05000b9200d5403c0703807030901d0829a2110625001d020440d03007003a400c8503a90403020048500c15030720360074003405d40360070040b2804000c00030300103001b02d40b0447d080d0820520080d0480400c2c540f01d08407034025034007460a031103030400c0140000385402541e0416100000074851502e1400540354041103450402050843c841c5801d902c6007004103090250407200410481d0844815560b10301f4045420340e5124039410080150ba8003c1013050b030b109014440c4003801400d02042401800350160441c0c902005560b086448031a41e0010500c1d0200801c21900c20080d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 537741178 1250 537739928 537739963
    0x5060a030c0c0b010608040c080f030d09050106030803010b03100b18010c0311060a1514010e150408010507030603020102241503010644190204140a1d0c0604030212 72
    0x81042c43c0e20601c06d41c03003140591607201059545a003515200d030010f0001d81c283d5041080798141080b465048001102d1052000090941e0380340c46a10042d042130704100c912040010612070264400d5031840003034921480c3c0c0520b0050f0300c140d86c808580c181259107050010103103002c3e0525000f480c42c00c00f000a201d003512242d01e0512a41401081c03003170100c035040d100e07144c4007103400e5495540042c00030364180c68000c001c5c10b501042244070700365078207900c002030b4080002180115080c05032a00400c502c2e20086416401e41c8006401c3c804050990a1203401102003408481480300b40e9035008104d0541004041c00310002182c090301003070300000240d1203401320b08085500030b03007001150a02001407511085a41c1e200c0c0640ca00007074050b00d002c1f5071200d1400201203220995001c0705510061001134103141184090718001740480348c64009540d078441c007041c01d030712813480504182c0803100070300740034424400040d85c0d44c040c0c1d000181c020001c104107207a824104010710854a03100903c0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 537742428 1250 537741178 537741181
    0x9051e090a020309120c030a08180106060e0f09060901031103030c250f080d03110702040903020d110c0a21020a080c180124051606090507050a05060a030c0c0b 70
    0x41001e54001c0d5130f84405440341c06820100701d00b0a8094480100c10000992325041c0740c00c2c5c086410f0706001e0302071000341d01d60628141106100b4402c501c002c11194503005c0e54550400204184941c1001001e805031043e001000642d513218004107054940c400c509031043d551100210f807a60150010745941446901c8802101d424011917840010a039160614001920341d002040c420302c0f10311a502ea0b80e1f00204011500d03e000303410901740c0400211005003810350540001382a40c11445064015810000c5d44c030703607101e034040c540200c41c1c0e200308010401954800003080f00000c07144511140f603101c902ca2003041c512492a2a0740258004140344682c40c1c46840207a140e5102d1000c051003222641910a0700b6200408054101c03071100112011300a8807030384a007540007128407c901006010001540da5064503c035421165004800c0080c450341c42d071034a640f17000032980155100b2202401e04010303c3d51100f0481e03015002919010584c0c0c81007a0b81600d0b010010403005009070300060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 537743678 1250 537742428 537742441
    0x412141204030c09110a080a0506010c0c0e090c0a050f04021b1f0b0109030b22050d020a0501060905010e0402130e10050901050a090c3003030207200109051e09 70
    0x54103041a10041c60040010441071017a0300800d1144050000c080b80c02440003580000b2254400c907840036040c1044041642142d603401120201600500c01344411034060000c115410040c100100c603040c0c5171800101d003418005100d2034000100c01e0722450300000c55501d03800c002041012803071035200c100c4402d030075013800340b074120314054950300c10032403a00e04a070320998419a41502201d400059940141d00d400010302559400c020f01c582450800440503000214200b00a4408041680c054008030001e440d0032030940d40ca940c04040907a04107030060001603045070403660070603030440d03c50340c0500114050300090090940341e042e0038051440821b1500816801040c0f19545c140020050340c0d403984c00c20000c8601c909805490103a210100740200ca100c941c4200005010407404055944a400b0040350f800280c8000c40004e80c002c540001003000201071151140b81540c6101c2501c0c1d805400207080340d24500c1080e00c556540080405940000b0414418072036000d41407107400e08d0000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 537744928 1250 537743678 537743693
    0x20601240e18062e1b050601030b1006031a0105030601021905100b06180f03151003060c05030903070f060902030607030501031115030a05070e03060a0c020105010605041214120403 79
    0x3c4403558040c4c00d41c000754269107801e91002d40d5014100c8003040c031341e138141c4050440d642c4032820901c01900c120244d50030040381c400c0100314007c5204040c040da5030300d02402c0f40701c012165036000d041414200540c003608400c09208031460581d080ca0a151241d5550004034581350122800c012030025560342c54051207004102402180341041051124180c2c003c2408410b1280e17000d5146540c0110228004510302900d98001e90000141120100f804294040325a0070003503429412500503001c0400801c0100d0147d94503140003410041d0031071500443d1180c80b4030403071800801403070050141c03100300f04042d404520102c0c0c024080382d002d40f404100141c0142020700007520340402a012102c1326242c118400d0a242800071244d90654171a0812100030708805410141881991440040300751400c0010902c03c2801400205034907203050b10107421520183c01403030421900300028000d66206c08070071107423103602100d600e02003a0340b00581c1e824000f42d81c42420b40018006400010300c40031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 537746178 1250 537744928 537744931
    0x201120e1b0a170f06280915060f03050c0a060906050906040b030a09031218140a02030307031d010804080f0304061e06170115050d0501060312120c020601240e18 71
    0x20138200c0301a5141d581c0d4540108803100420542c00210044c6c43c07001302044c0c4c0120b8030040c0318502584080f09400e16000a40d4004c0e0080e04246034051410130078000200315541617a402500c40800f054181000105094903034003908080c0500040d500d41036849070300858009010b0545140d480f41032080245000e42164602035000821100d240c00c00780c00144a550b81c1c840298041010212140c1c0c1c5842810644021320b8400d801050362203c0541c405000402d005403195032611121003032801030700110400e0301449810084150b0800000800303039011a0800c11409154544a5440e072402c43d02510748811202c000319141a0306601801071500500142e40115403a1100742c0d41d54a2a01e01305d580510920342c071040540420010390610f035a04281c0c580c01741001041a645a80b2024016050342044200040c0d207849240f1002d5440d1080300d031049a40c1c0f0260041d545401e15689145c404813503002000901c03440e40003015402680000d80e032860140003c0c1080c68003c2d20300002c080c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 537747428 1250 537746178 537746203
    0x140a0308030c070f0606061227050f03070c05090109140417130b09011103091311040f03111503040213020313051905211602060d0e0a0201120e1b0a17 66
    0x244446400302301198090780d24030400d400c949200161102d45611105001c1c064162924060000e4814080d03800f400107160950054480200303032032404040c080802c030142d0020181502c1c100c0c03858800010394981580190700506000f02c1201468001070081c81591070034000300c0700d40c0400040c0265140040e20395403d00741c0360365000007108000030340c50b0b10408400a0f40b140384481b03244444042c69124406041c01e00311103a003041e80b40c104105810f100d5400680b107080000100c01807c0c60015a4070301c0d8040c0f41e800290a40c101540804e1021840c44408401e441d0080000307008061109032801c0266000421070320307125608084010f009900c3c07481549d49003e07682a0700c0b51159008113080e40d6422841030303549800c545241c4061410a44042207a0254003009220002050b9000300048400c01002401004045100140c5180c007490585c5c18110704110000100a8000c105149009600441c20f403d10090b0070009041d412160441411002d9540c8030749084200092040c10a08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 537748678 1250 537747428 537747437
    0x40e01020a030e060c0403030e191701050411010e18252d0c030c03031409011b0206010b040b0c0705090705040807140a03030f090b0c0c030106140a0308030c070f060606 74
    0x219401c5d000300552055020140c0480e0304009a0f080303509240500c041e400901c0c0707040c0c00c0719030703140c009400d424880c260a00d180c07a9190000e01003405403a2641004840090800984450964000c40e0140201c1980314021032000d00000d004040c0c00b00800001445049001310300f607586100181c0f00122806e002c001050484c0f00c0d08100700c294520840040343c840e01c503480c01605075582100e188a0201d400c070201515000591014005490040c1c0604440000458964201042d9681810051003144115030102c401000240420822981600d00070f04201e96103c440101061600c00184c1c0410b820542510400000c280d015014109450881080c2d4034006e6881140040500401e104603a11000e03000c4100001307401650160540314003410060030b065035904103130781141c108480542c1590404003141226103021711481019010061201c4140382c46c20300415925196404014207080c0c00101081c81c80202d5015210312540c01031004032509480d14000c00600840d00c2241d0106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 537749928 1250 537748678 537748681
    0x250e09010905030f03090f120c160501081308160807021507031e03090512030106020706020a11011413140f011d100509040e0616090308030f06040e01020a030e06 71
    0x4410700510032002d400030020350824000007510141070b440030b40000c0b42440b5100704042c08004c140501e07500012020000350301e921119061500f0301030041070f1050314031030801d42030105a81081c0e1b400c0c0c024502ca034408030445000c2c07404c4106480382104081c0d40181d030341138101c1000b21000080c1110340c4241e80e405001c00000215a4160040304001070200f15190708440680d40b2a44180e0804000c501e130114402265481c2c550804000c00c0000e440b000000006100c600d03010001c140003803882d80f00408080700c039a264440d0b0030f5113040c1d0b10350400c0740c0b981d0711120b018910740070f070390b1100040001a0301c542c2e6900d418500300c50f11181c1c198012000e0050485039503004000402d642440000405824011903040001c40c0f50305080302814410240303c0f82e000794569100310034600300c4c40c00050605007014200080002c001e2480d0b103003000305114052000400c00300940e0b80000c80111441c8a9844000025020300043c0220103207a61005c103089650300c0e4150007001c4c8c81c0d00301d107003644e80d075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 537751178 1250 537749928 537749941
    0x1403060a060e0a440d051606020a0e0301060f08060c0c011b020106030303050f0613052503060e0f04080d0f0b04020c0124080706080a0b0a12030806060315060c250e 72
    0x10001c03140d9641c801604100e071103854481c0544005c000380f40030f024079107c0c140b5440d6980c104903086000140000307035502c2c00c80703551424248036202c003078402d4907903404070316180004c2d856660038021300804600a01040b4280741d504250028540c481000c2c51300b0703810010070030f0b0003402000c0b1803105500003810000420a80d01d55185094000c2002400c140d1100b444087d51002904000c0c1031800c03050400c0c40307030403030000340034145480c00c6003107540101c2c24924014150800d02ca01030000e103e83c0303080c0400d1000081504044030b00c0180401e40200783c040a05610b0802845190105074005000203a09980c51340194003801e01031101550782031142003002c1c00382c09070303c505019038034050b40080c2c02441514041d2400c0b96000c0c6180e031022600c0c69510000c9540707001c09074060101e42c5d412010300380c00c05410444040d803000342a900281146010405001610001c1c03010b18051403001606800d000401d204800030740b50351040f021008a1f240c4910307081e903031682c85174081d49010a40400c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 537752428 1250 537751178 537751289
    0xf0203010b04140310020301060c1a31020a060906200d03090f0812040c09020a0c02211605040e0304030c05100c0606080d1403060a060e0a 61
    0x140c440780d0100e01e0a003418400c440c40d140300d042c100c0d56414400c541086017042c1d0f2a00041d0f000e000c240c3d40d0803101c00d503580750440e1f000315610380091a148040381048031020b03003143e64000d2070028804003280080d0014844410080d0030348041d4010815a00121f4026006454401144d0840e901c2082c130000d90400c1c400507942c9002506801d4004030184002948a9001883e040d4054aa403104170b00305030740c92200a6000895412030030005408100500a5a102d804020b00010310150702d03005c080f5100511101d071098000b44201025000d007101e59104204003840c0c0c4a280045036038070002c0700a5440a07890b944a041c1c4140e0400801d41c0174100080295412243d00001c2d000b2180c3c180820840c803100020343c84820440040003140c04036499018213802026024060302d4110f81b11000200303041d400b40c0007102282e004006100c01a04c3e0802030000302d40c8940341814140d1b000c1c1000501020040d070019a613500080e00c2281c80380710301500c1c03403254152200101d0381e20560080002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 537753678 1250 537752428 537752431
    0xc07050604030f11190308070302090a0f1d01030f02060a0903021002011a030304032f060d0506091018110f0a02070f051009060e0f0402030106052101080a0204110c0a12030f0203 78
    0xa0341e90550741714000040d01034240c1c0e98101a10b8140903040c0041e100120f00d80d141154003510030300080000801c100d24041459061091a010f03074a511503045440e00c111240e44580c000f1f00460303000034403c105920400f1000040c50b8011f00c02c882945104c40c000b8041c14090003a02c0c07002da915039106503545000811641160f0b4040e00c0128490907851089000d4400401d0800b068490500514404d5407500018000c0e000502400605800c00c1414041c0108004041d08101901e5642c203201907540113200c1c413084816407030302207080d54080416030020f0250424a0300030340c1c0c0c00301c3c018030115008501c490640c5c400c03ca11505150f03503034081203480d002d07055809002c05c0c041c9805014451140704003800491020380b20100003840f10b00428102e134405d80c40328001500c0403500f4504841c040d0306e448030703003400c881c1110203d5062483c00f540307505508000a110b40d69420502d080c801660050303c60700c6019500380c0700b45c83d181e030030b2400260b000c412100700064500000c0320036402c0c4500c00d03603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 537754928 1250 537753678 537753703
    0x91818070806010503102007050a03020708030f040902091305190e03090604120f0206040e060310090803010b0a090e0c030906090a0309050108090f1b011d03060a050c07050604030f11 80
    0x401c0346d88a030364110001010f2541404135404260103290f0a00c0e40450000d0146502c17039801081200316900b4000d0400d034032078109240e01d8000700154844001c001042c1c0c0d094038041000143d40300708000c00960020078091381e00d80524101020007685624128404103910f0f04c258090041c8031610b19a0758682c860000300d943d00030414070052040302491030b51901c207188600380c48030b034402c0c0c40d80028015412903807143c00008003a00411001e41010702020010a107061003e12003e0111795038492a07010500600501d442d0200c8c400d42000d00c41e2100320014210008140c90508008440c4001d0342e0045683e445103200300320104466074400034540c0c0c20700e078040d0385022009040c00011244840050003400c20340c40b4840302d1a400c01c80034407640401d07140d480d00c0b42c8404074a10340050301865100b40e0b514a40900d1000200468a021900303551080084074002001e0f6604001008076005096015003d0f04c105801c01c010107421055008950800d0340395031030002c2d146021175903100044081c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 537756178 1250 537754928 537754933
    0x31e0412060e07080303041209150807080723070204110403050303010302060721021b030708031603020109050715080f0114150408121b0607050708091818070806010503 74
    0x240d02184442d031003249480c141c0020f9950590ba9201c001d40b40d80c00c150382c10b890311580e00381c00303a003601c1d0026068801841c502911a00400079204c0c0900361b00d40042c0904103001e1042c00081d00c040c880c840d22814100c03031a00d85400175505444145450300b106a00324015441d016485902c2810300040d0740072640e000005500c0c41c0c0c2154240007954102c00d604480c0c1107400c1101480f513080d415403501e4800300390f030300402e6110300c3c01d030550080c0d41c03503044991300036003150f0002d11012401204540b62801003000d511048089840d04034018162018003802c0d070300490001040b0341c09076005d00307240492541e6868000d43c4500c6a0b0344250700f42881940c42034081c16070402401d003841c5c0034803281c3c905515102820030303036141d0010f41882e00d0102c040b0400240003412042ca5080c4213203200d84580c58800500d41c520380f01c0f101400f203110300100585031004c00320710700c41d0740d681e4110b01d4140c40003508843c201d9424501c545805503540d4102500c614050484042032400000600b28100c50000b0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 537757428 1250 537756178 537756209
    0x110c0307060c0219081617090103060b033105160e070314130201180f0612020a0c02150403060204090501290906090301020f04080f0d020109050a020112020912031e04 73
    0x2500c0242d41d0243c0d074441916061086d040000c511160602d90041020f040c105903102d00361000102160355a0b04141c0f03000c5401d00c1171211300702041d445800c00c0217042c540b010000014081c160b2030300c0c4002500038001e01c5002101650342d5607620030003040b8ae08035000411551501c1c0020b07001d03180d0b00444005070320114030003c0c0d1403004c804e120b02c03c001e00605003000100311540303131102c150400750000300091402c82810400360764444002c000380c100c0007000714140291a540104040301294020307204201c0200d404100840480c01c4078000c1d03500000443d0743e10742d54011385000d03000034407a0040841e500002414105081c200e00c20860301407008103803800700d03400200082a04a100c94a426660034008184880040350040c0040c00d4244010300d805041c010710079140a035070014040441e4180100d510000d000010305211303069090a10403800c0241901c040024042d4113044e85d8041c0d0814002c0311118808001880a0104500c0d00810801040554005440b0b01d10400307104402e19030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 537758678 1250 537757428 537757433
    0x2701080406020f19051c020c0601060806120a050d0806060721090e0408120603070e01030b060409020315040201080a1103040f0809030607091e0b180103110c0307060c0219 75
    0x340180203000707400180f241000205000084003013844405000801c1c80003880503220014aa106d1000c0440541c0a40c42d1141701c0101540760a8103109075014852110b001c150280d40d0f088050700241400340803140c41d80b04501b4504d40d146c4020f0502008544240c001c10b20b03500305070040b10200c980092200308440092040c200041c481e0310400c4080091026010919141d0402e40034001c07805004556100c3e406600c00c582a01760103059207110350302c5174000300003007504c0c0100d80781101e8012100400c1c41c0e039042d0114010700301064000b54140207103058080342d54081d0300c0443c061030003a6204c44160b40c5d101d411404442401c402051001c205000060000d80b55415000d080d9100f0a005420710b03043c803001c64075125040d151240070441d03001061080c0c5080c51045251081a00c2c1e411000a10f0444141118890000a200e02d081d6440c91902103074003d400c040000f50031010050355803c0103069040c2c0786d40048508558150401c00c910900e1072000a412002002642c0f40054001d1702d903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 537759928 1250 537758678 537758681
    0x50c18011b0b0f010f0f1401031b02060702100204120f050a12121410050904060605102d02151005030321060d03140f041206022701080406 61
    0x1482400d0410503070038140d181c00144152060314151140300099a2400c207505602d001c103005801c02d10408681344800c01c00100724003c45802c550079208040003000d5580012005041036803c0900d41e4440c2c990300100340c6900190b4a4400c0c0f4242e400c0d01e42c40e40f01401c440041c1d06c1144030f03042c0380c00c600d08000000708144c40c0c402041c85108004903540418981c1e41c00d04a044065000e801040401e400101c00082c079000300750b0701c000104004009480c1c034140e070041c100010301569005801040001c0c0401107207900160103008000c003011242d99149000501e042c2801c0945074805502d24484107a10705075461180c8015495005001e00b5100b103400280104801031034400c40f40640e100c0095282c4092000700304100c0d522903411040826100324000000010f00001c1c00b468040000902107980402d1429445c0d080c554a20340d03928908510802600071a00101d5000700d013a04014204000343d402005040d0510205103069a40d88908003a802d00f4104d0b2280810502400140010700070f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 537761178 1250 537759928 537759967
    0x1518080f090f09070903030f0801210f0f150f050c0a0509030709093f18030c1421060f041e0b0a150f031121061504050c 53
    0x142c0000288524140010312104058550318082010030302c06005240c0c0c0186020301403005420304001039403602c803a004203580c40c860340e69508000c10711840c04214410f0a23103e5100d800200c4488001c440741000114900801c1001026915003162100d041c0d075a0301456118500340800141014150403040c0c2c2d03d0791100030709692500941310041083c041c544039043c0554018407c0300c203e0011003041400e0107100d089a450800b62080c644290600041c19036107802041e40341c003402c09071088e16001c1980e4480c0c0c0004148150107800880d148262440c000e140d60300c00c8480c0311a0091390340e5040c800ea000c080d45c00c2c103d60425800980c41203406400b85420500c5194203031072440301c03402407404090606008850468040003032003e24021400b513558170300b244016100c00c19240000000341d07814180b0005103c5a10580c40e0b590541d00c08011860601c41d42800c0252206825a4030742c4401c0102d6090504450002551501d4107040c490030740716000a2500929100b0303560b81030143c8408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 537762428 1250 537761178 537761197
    0x4020402071506030b070903020918031c02030a0f0203010b030117031902150a150512010e0706090305160b030a0e011e0b0a0806070804030809010204121518080f 71
    0x1020095030000800a41040e151180d900c2c00015059066280c4120380e5a0701904240401c130200805101603912510907682011a601e0700c0100d42a1701801907045000303055010400880f02004400012801e40055108056184c410058090030740c9a4200300d000a00800d03618a0082c0700600000d00d000c07a0043c61074640408480c1000c05144841c0d450281400c1902d00613004031a410300701c500384505040d00440c0a02c001c2c44005c050349207810320b0043e1807040c3d034800e040d030586546c4200c50a500501e80d0207480e0301034410362902e480d006081d81d500c2d4071003203c2d103218074001406a81041901e40c002d440101100394a540c80f400c2c4440c0c0a041e2056111415558802942c80202c100d08070900c0300800f161008101c0c1446141007010103210cc0c2e00921081c0c0100c020001040c1c2d100c28983d0340640d00d42881c40c1540c40c0d401402d4024040c981286c1c3c00b21600407480c43c14014440341980007205415014400a10f10145052a003206041c004280035000d002001010450901901d101c15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 537763678 1250 537762428 537762431
    0x24060e090c0c0a0804050f03060408030a1806090b010503070605030708010605070305092e0c120f02191a0a02090a05042708190c082205030d0807081617040204 70
    0x4200d080541c1490883c00e402c5812030300c001000c200500f450306250280e22004c501424640c40d254942003154840140724150039076032210706a0700b07440342591a00c0b041b0307004081005802600e103080b0700016000e00415119118452002500611903011240700b012103655190499180440039100354019900490a0190034080c01c10f45840344950030b10801800a9640701000464132305c800c0b15017501d0124010014852240c4010900b005c100c110340c44d0107490969404800050304a04000003140203283e0314101c4501e12040c010710700051401c003d0741c642e01c65516226000100e00302d01c01c1e00242e541224420074104402e2030700303034004040b00080403400c030350395003110052034410000160122032070103010038084c000d0740c0b0524494400052a0802e104c3d00e0700c943d11400200e024041c030405054096000340c46680c080600c5000c000c0c40084d040f140c13036641c10300c40501602000c84110340018041c0c030000707074003005801004e2080c584984994a03d07941c4100a421200000dc000340e2700a0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 537764928 1250 537763678 537763687
    0x306180e1c2a0605100906080f150c0f03090109050705100c06051b0403030c050105060a0f14061b01050a0c020616031a121c030209090604050910020d24060e090c 71
    0x40c0c3d86000d031501c50004801c140a10f203040055190072035595401944241d882282c01502e0580000b5558151010800003481d481d502e0f80d11110300c92040051402c4040008018881c1ca030f02c054100d01c000b41c2c0315005840185031101c00703211860205c0c0030000006144c0000344800300351540c0c40300750040240d5080000100096030044181d604c00e61040300003d450a0949091150a104507500901d048500408a0345440102619080540244c42c110031802d203600045a40f40b400f01c0b80c066940c603041083c0742010003551402854200c0c0d03400c0481e401c1c54031101c009032010420901c1880c03d4010744a04412400045000b0820344422035080c1006242c0c80d0302554510100000e03068001c0010007090780c5a0b0824080d541000351080d0515005100c0c95606a45001d0881c1c0d00030b031305450000301c41e520030b19074502e007011004000e0241c40c400074110300a034116410100099140400707010742a01000d020f100761440030b101340400614089014211803030070340d00707103078200c008400d145040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 537766178 1250 537764928 537764933
    0x305070314090f15012402010f150311010c050d05070501150b1c09120c11090a0b0f090c040501180b030106170106031e0c0306180e1c2a 60
    0x124107042c0c401000700d500204000351418030400052200ca20803942c594229458110070b100300020000351000c1c5264200041580c8074402d500012074507000b180300303120000d0110f5a00c840c1e2501408151060303c0180300c4440507501569601c03441c0396000c0e004240000c040c00301181c50340c20000c3c04440c65522600000ea51000c03001d500c0b405415503c1c0c207103a803458805141e51140704148040c4080c9820400710710f0110302444d201e001e43c6078080c207202c141500240b2307280554005003460380741d02201c0c000078080b024600750b00c001886c07507083d1501960b40003018100424094101c0740002c0050b420802031080d9481020100d1904002c41107054096032a42c0c0040940c0c3c0090300300400017031168524510303500398501501e006103442d003410031420f44a0032201038448070408840420917143d14603040e020348281c0c0100f00801c0e0070b40b40324194440c04a4034401034988c410490f5001d200c2e4442e08078166a0041031140d2440075a280c0d071480300000f40c0d803d04194100100c0d2001d528400009201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537767428 1250 537766178 537766211
    0x170a060207080c07150804060c051903060806070212030406020a2f01060b120a0b010e030d0e040507050c1b01030f0203090105090f06070203040b0306210706230a03050703 75
    0x104500c90400940c86584090700c1d00d00c1c01150b60301c802c5c0d810101c81d8240361003a4200c84800d0f08141c11183c0420300c001b0301007003910148145000c07108443c180c040c1c1074511035031680c4060241c0e82040c0568480303032168601203a03160700d030640e4441c44050030004140028582d5004049140c9107041200c1c3d0303a00300c5489407501d03840300ca100e1140054102580102d140081c805c2c1c0c400380008009040c18480304074281801890000e12904410f991211452013582c080c2a406240840080481e68103141c10030780240010344102389140220b0400001c140e449014805032005181000c0080c6004800302d141c1844455280203081e0605a82e0410580d002c1e0140c001144981e07540c40020a180c142022207900c0c01c040c81da04c0d0ba00d04c1d0003007000d210800313501108070340031140304c01c1d5440d840b92900c0000602c036004d4a22001001c40e62101c0d103c41d500000328104044510a8590b600007829040c00c045400340c0722200b04020701d204200480609000e94820740d042130b08c6190005800301088120007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 537768678 1250 537767428 537767437
    0x40e010c050f090a05090f040606091e1a0a06210605060703050a03021315081320011101050a1e020f03010b0a0e100809010f06030c05090910150515090307170a0602 72
    0x2811f0b030003060422060000c5400364000601400c4000c2045802152444805d135540c401404095a19030401d01400c281c10340001c91b02c10030091103100007035900c100c090308510807408030145040c0002000840c400c5c4604c40e4400300e0b50064000f6107880b17080d81c0d0031500b0380e012074240400e1641c01d20041e0500f0641104d410058425880030b00310611400708007403e01900100000b1802c8514070060340000d45100d10300101070320b00ca42500788504e043c40165035081c05071407807110340c0d8640001c0018840350f580160010070b04841c80c420198901618400591081610f4580c000d08200300400000d441400145001004c03452300c050f0580860001600154407200c510000540c150140028030320203114800011101c01010820240765544202400e01c05200f0280314540407000610b1a500520003282c100d1401c4c1e904110711203220069206540140c06110300030310000c00070081e2414148100c5501c068010001c141080c58904030413248400c40d200390849000c0d110211000410320700280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 537769784 1106 537768678 537768691
    0x106061106071241090d05250f0b010f0b04081e030705030c0d02070b0f120709150201051504090b0c03060402070b15040e010c050f090a0509 62
    0x40510201816a50451038201c02c03202e14518030590342d0b48030381212442c4e0050740d129010110381e034500c90810307200824000c2040c0f00754400c52101d15481131461a615211080d02541d03510000da440c050100ca450400e180140b040c540c480050002902e1443c0085041c2490b1001c80c960700c91641100004040f001d03c01e400c10207806000315000140c000701204d0b03480c00549861903680102240d0300c0010300641101182d0015090300311607140100035171460030510f004000b04110580030f0480c40a2022304000022140800b41c490f508140d80361300009450324202d01020103246240c07005501c03903072a2841e84070000e4001d54a50303401c0f5941b4051203403603a45140104000788501000545880413490030000d1542d868035a044030920265010302c440b0000d00d01d00740c26264441e40110225034144208011218410083c1c04140c8000b40480d2100b0342c1c0f070020400d544400c1d40c06 = true := by decide +kernel

theorem cover : BRFrame.Cov 537589928 537769784 := by
  have h0 := BRFrame.cov_init 537589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 537589928 ≤ n) (h2 : n < 537769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
