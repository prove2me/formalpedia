-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:28:02.098996+00:00
-- url     : https://prove2.me/submissions/91da550d-207b-4f7f-b6ed-087c7eecab2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 730755395 ≤ n < 730935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 730756645 1250 730755395 730755407
    0x20d030c030b0d1e080301080a060b22020a170108010e0c0a06080f07170709140111060118060b040f030501140108031206120d020106050307061e050d0f020a0e01090506130303 77
    0x904c0500409550300e0b902c0000c1240740a98000c2401202034074030380590f8207001058401042c41c2d0f0340305104030a040301c808140c21000810404050704010b0303d40c403110381c0654044002541481010045200000700e02c881500080040110401550005404a010700071a0716480c0217030008201305000050b4a8035090b201d0a1b400315441c601040301c0d20000c0e0035019041c00540f52040015a1807400340180c100f44034031610b10550a28200c40010844080645c40d944180294982c044143c001e0030941c9881c0c1d00702c0ca002d4117401032280d0f0348c0c0d6a2210b00c089901400d1100316a203508045600800d4050310510038100c5003004040c514017808a40f5481002c140148a80d501540307903030030214024010404820f407240389800005030035042c00c04152410400d9440341003000300d6940c207124012049820168010b201d400c10300d4a506880d411100503200000407184c01603c04100c155032a80c1c03084514080f0b107000e0300c60171000c540300c030b05011141c415481c1c1501600f00421040000901c240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 730757895 1250 730756645 730756673
    0x423030d091b031b06030204063f2405030a0b09010e0d0c0606091b03020a0c06060801020c0f0f0325061b0305100803090f0a05040c09081009170d09050607020d030c030b0d 75
    0x180030ae01001134081041d901301c103054019142c0c0c0310340e00d50100010000c0380b01d003802103812181c00601500d286c080000c0d44c45c01e05c084003c02c4a103900e404603e03401401d40045400c0721031001030720001a40f4101c0100b043c032502380180d408e603003401400108644140320300e040b02c200008940207948001c0c4000d0700694810044841001002080f520100d8194810000504101c100150352500b00c5045545440301005202c0e0882d0404506140c00b00f0000003150110b00300103500c01c81d01d00644021703440d180e24980707010784001d0502e0144082070504618000e03118106460402440d12038004100098010f4021305a40d903000700503250982c941400c100c0d0f2616402070614545a8070342020a040d80c0e11030a030400417a000d0b60082c00b9180b401c1c0440b034203a85c0100b5007001040442d4580d5006c0340c2001007148820040061518000c1c142c68100310100c541003411100c86041c1a0f000a6444034448414000a0714156000017480e00c00c1c0140c08071104002d0004080d9105070710f030220011140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 730759145 1250 730757895 730757957
    0x1914060d1505010609050a050f0604090c0912030309030305070c150209040902060f030417121b0c15060a06021219021e060423030d091b031b0603020406 67
    0x5040315101e00d18031402824042d082c030369a000a03440c5440e0a100081005401030b900c502c10062551000e2344a0b9000e41d000c41f140484045421b100c9224203407100c00c1190841e01c00800d01210b46000e064241d000f080f4918801d41e000c00403036a82400c102c400386030f1030400504002c1403800710844482140c001e0300e0440402480050f078003c07980c1c0058010351180341400040b41010041205100181c140403030054003e140c10f40c81c1c000e2160b00d003450458000c20203011000c09500205201602d0400d81e0600f07607140c4101c602d08079103032902003000402240e0041c4509001100450914400310f8400070030801c07100c01d103081c00c02c2000c4160503030613207aa40f0b20131842101017000300003c88048503d00303242c0110107800c5130705060a001c81804a005612a4045415400302c080c51400000722204001c000c1d50000344054203281c906044d030600203088481001c0c030706010040c41215240c5020080d20a14400d41d044d40e20081079003230780914481c490206004100030304000301e0704010383d0088283c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 730760395 1250 730759145 730759163
    0x621070311070b0a0f020405030a060c02011107110a0603020a0518060d061518050604030f14030d06050306060a080a080a210923030f0903070302181914060d 69
    0x2074503810105900100b105031180e541030018401c560700c451080102ca2020904198541410400440d40c0c410601000601c030540e03550000d03008520139400304040300c003180d80b025960b05442c1081e1507a000080e640780c3c410b4500450001b000742c001d20885030b03052600d031101428000004001d81c50000e521aa6a80024040028503501d0010340b08001c0900f2881c05d00e16150404100010f0800060319600d00b00c0c001e03140300030b1100b0f40d82c120548048942c0b105071034203902101c0c90082d185083c8403401100512000c10000842c0034030350001f01c02d68034190201c400c80c1c0c0d02d00e005c01040e500580b085884541040320078001107a100c1e802409405100c0c01c04481815480703c41403002e40722600380403e01c0d40da07a0b2492007000700c07922236520044100800c0b0004801c0441e46240c491144080307004940100007480c241649061180c580103640091030b00180f0312940814401c0c000e41150446070340441c079203441d045407450340700300d2910f400712034160055542d604c1d00303005001c045218148d0300b03050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 730761645 1250 730760395 730760411
    0xa1707031505160203070512090d121e03051b07021903051f050f0705031518010504050123011b050a0302100e07060e040903030b030601121106210703 66
    0x80c041d00e5605421810580000300d81c6045212050920802c988041c1150001c104c8007000c81c1c800544104203030056a05e590742c444402c40000c04c500c591000003003c0200700d980b40d0b452030341c2181402030395000310250080c18010311401107040b100122a00181440b41e01072030005841520094041e1340c1c80900f44459000c07041c0d0124006080641c4125129031103081d8155006240a21301c0004100c5500d040c006400c1040000020301001440001080320210025150905405203038451580240500345000410100010780b03501c24000c1c036000d142030100000300003840306501201c0441d42c10040c0410f020b081e00446014003040d5840c00d0701e060000b207182c003058084c4521403a0511135001052000351181054055424200300441e090700010800c0203140d4103c03803010340e1400704a070005042c124034581500100602c0c10890f41606c980c2c000850388500e41000703030340c03c6802803c100101014907001c0000c18480c0d00c0c8000001e0046207c0d801c0c1c2e400e801101c00d03410541c4c0b800c010501ca4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 730762895 1250 730761645 730761653
    0x3040611040905070215070c0f0201090b0403140d0903020604060804030905040507020102070614130f0602070b091608190b19020a170f040302060622060902180f0a170703 75
    0x508140c1000008994840034440020b804106c0e0765090510b001d6050041d1406030700c003906480b000040a030a11003680802c0086a10401301d2201600312461101c0c0c50725102d0501900b0345403183d607000c4880c801e0600b040d16190182d40d10008607030b8000e1841d8a0a401d20204031138104019108405100c2c1440b800300311030303880c0e000e01d03071003000c00d81e00068903144603003002015900d0842c21100340410340011310800c8200300214000060300b01d81d0080900b1f1862400000130300c554031010f425a03d90006200c0030600225510384136100c0c600c2c0f40c48800c0e880382207290b00c1c0c100907108900340040c00d00d407203000103600c03c44650f44030680101040f00c14028005c0340c001c0e40c1c4840240d00019030800e2007003800b0003400180b0303608017075100580600751800366800f95940d41301811503441078082c81340c1e25600e400c0640c00c24201207502401480301a03a10a440e1002c2d400040c003200817045405008001070500c486140c1c0b05140040c01c40d40c0c5903242070020325003038002541c6640c9034007074a54080085 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 730764145 1250 730762895 730762897
    0xc06091513330e0907050f070c0f03030f0201022104110a140118030b07050c10060e0412030e06010611070b220506030c1801090509070c0c0801020a0c0803040611 71
    0xc52400184002d841103070031020340c60190a4900002402101910b4510645a600c00680c0c012044d0070b05565840c0b180c88100894020710343c0c0108070580260000c50030004003e807100403a88240c4840c40350146504040c0d091f80218101c6034814414828800c65910701351450580083c05404c0f0381202109c0e100c042604c00d03600750040c041d50100805c1c034800b10350b0302c400c00001d6205a0301003010440d085a850204001014044404101000c80d014080d51012300c0896201d0007001000c01c001d6666600d440d1030564200c801390f80c0c465410903100b17483c0b03001303000f0843d4001903100038150070381c03d029095403850107148000c0e0032031284500109005003020f00a00c003501681449280c0a1200b08901e03450304a1900114041d07882030003030116036017040f425a240c0b00641100c07069171408280c0101c0b2980000d9224550007040d280a11204070f8002020781d140c90300a54031174201c20340750510b8900382e05c00d0305d4100d4000b400c00000d140216000030301031034000344500b0000c00c108205a510b01c00c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 730765395 1250 730764145 730764179
    0x8070c1203060501080603010e03090607023606010908151801060e01081603030c0b0c0f030a0e060a050603070303050705070b04060207080106060c0b0c03060a08030c0f0c06091513 79
    0x2082d59080140003540e04180e211340d002d10124000d0002d4210240566100d005444443c0d010b800c0100c0c030f0004542c0c0d01540704141240d101040044200741e031039a280f07800440741c0003114000d10500032505a5101c0c1040005913118100200b41284480604811828004250700d0059040d90000320a4030000e016000c000c0030050018512541000c54182c02c01295601c034a100c030300f80d040e0402c000381d04105400c0045030803406202060780c482d01c100d0101e11404410a0724044000100541d00d0050b9000f4100b1907484000c40b495642d074820804200c070001e840306c42e81648114000c10009108400500c241c070310490598a40d580d0300c0201700c003250455000720700543c1020005002c4c403002480340400030115032600c0300301c1c200c042e00c509014000152954101c03107000130004050348c441201b05802030410900f140c5d600c001107400307262644070801d400c1030341340104100303ca090300e00b1000b5a0b900f8407008100c8030600340a843c4242207a481113003408024810301900088136401c81d010100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730766645 1250 730765395 730765397
    0x80403020f1e07050406150507060b030715081b0d090201050c1501031203020a050f0d0b031209030705030705030d0f170109150e07140c010204050d0813050d0506060108070c12 77
    0x4201d114140b00d041100942101d40514034010040140b40c4c0115402012003429050184d03464010b4200f0001400c0c0420070755400d0311812400085001c2e00000152041880d5591500d05071500c10701010026100e401c08880d041c01445040a11400c50f840040390b54030504080d07103001003c141650510b03003000e1803035000b004042c00403c10311403240050307031150a007071404500d42401504090001e0141c00c800031040100442c00410005155000c0c01036010020101c6e40c003403400e00682002c80d440110401c2c002e0007081c900040c0c900380010400152000103014101034942030200301d07041405000d030a001c02c442c0e01d1785840c2c010301c08060140079004004011402c031210101c03a1b054142180e00503e03d07401d00b04104202c05070301143c0d4007a00e82003190079a90b1044412102c0c0d000e805140c100c1036021072821070038000c1040c0d4400030102010f88220a00f03140b81d0f103408010006a5020f0054560341100001815645c480c9220640c460142d0911947e030003800c0d01d640d88800640c0e29050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 730767895 1250 730766645 730766683
    0x40e150405010b1206011401030e150117070807090e03070803010b07020f011e080910060b070c0803030c1902072d08060c1804020906070b0703200a080403020f 70
    0xc01800000c0c081c00c0c02c00302003550052030f50003810455903a2a80305209401101c1d030810400c1680380c2c480d401102107020744d0000c84e0f1221a0410714901c40402c00c0c0702d02c2115070354141003800014008941c07841100c014001521006142c6600c160150821b5411000725020800100c00016500400f860203040d040003d1600c0d40410720510803010070b022003403410300440a05000c50086c0e180043c120340da0041c80c2c101d40a40319021038500d410091244020814140180401c5540540003d8660107004181303a030802a556510107480344020b95540348141d00400190707180070420718410b0340101003441161115690f955960429509840c0c8182e40705227240354240314801406200c0024103a00c001400c2a4244142e104645100c0c03000c400d101c0340340400e0416900e0340c0342e5064505c241c402800490380da80c03c0d45410000348400312001c6012034175140e03120514254211400a0540350301c000e00c2c1c42d000c03541c1c2040e074683c1402001142188505070300200c1d80311051111000d550030740c500722 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 730769145 1250 730767895 730767901
    0x1416020a03030c110a030b04140a62071a0103060506031b010f03090803010f06080115050405040504050102090d0605060a1a07030e0a0e0c0a14070b070e040e15 70
    0x102e82c0d405013502219214034003030385090000c00e61030328515411a90082d03410341c240b0b006091240c01c24000450190129181d80d408a08980360a9540c1420200602282445101c0b074030840741074003c1504501c14192184180d03c0740719041410010116101c141841c1c20094a0340e550309a03a40a1000381c0054400c0100400420145000b1107800c002d0440140c4181d40c502d1081040c00e403001110075040141e801c1061102c0c501030380c4100c01054002c0070703045c1d80350784034610030341c001556205407000505504000a01094004c10b01994803441d96501031402c0c2c038040401019000152007034486550821803880c0a540d403200d43d10301e00b8400d8a0114151500c0010001504003652101c100c1948111280f0343e0a40684100c401243e49070a02402c0080c03600301040e480b9006820001c00300e203041c0240403200444201070840100550b4448030340411409200710782e8062442c00800d1607641d000844c10142c000d151814030610054400140c0307840d00e0507810315003030042600f460014900018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 730770395 1250 730769145 730769153
    0xe0109171b010309021e040e0a120e01080108070303140912070e07020a0c030605040302011b080609070e221b18060e0310020f0d02040602010b010809010c1416020a03030c 75
    0x14601c1800909042103030701d0483d004200e0030030002d1000040840c050220134a103503515400a445820043c089a0304100325107021400302035070002d090003003a00542c41110561107520b4060586081c0000340600c5490340da01600d003400702036950300026506128001e8203488035007a11a010350000010001d1510340500e40d090074a0240c2410115002440081c0c04103014051282c11258401800141c41d40c940c101240102200d180701d104210304070240044603903221554500504c400c840223440350310358400c03e40b015080d5482c0a034100554a01200c0503808503076a000b080303c50010085039004d148034508404c0d40010252030040303800c070220b1f00d100701c2c1c0b1200d0b1440901050708280740d024691100081e55104c03850b026810352500040d038242049140f809885012500321425500c2c1c5842c0d000c0640a40152440140060010b80005d0b00418050103143c00000407615102417a54403140c85042592101004070900482c0d070b0361010040e240c0f005554004c6000b030f9244d100c80b10582c60 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 730771645 1250 730770395 730770433
    0x204091a16020f0a1e051e150712230a020d06050307030309120503270108060d031b02010c0b04060506192106150806090c0102031305010e010917 64
    0x740ca100b1548606007001a1400c00950810f2890700020850145520041c00c40c05103907001000420710b006200c0d10169807000c0400f50880c1c0c595034416a41110000408041c0030641114031a00040700c0358803c00710003c00b030303010924080d11061081000002c400591802803420394000c4c9245078005159a040d20b62441044064801117000c3c0590700d146840007002c0708600d01603008071404c0e244441003005810412540d41d40b11180c03e4101c0c0c2d40c4c010784860340c44549070030034601017070841c030000b9403c0c54202021081e240c0d15031a145c105908251800541e6038005800700c0c1800008113491020031101c0c49000d01c110b104070404501c0349040401d101901c0f1940c0c03000c88482d0383c10041801440e100c801040c100401d030007210349200d0744078207000d00900344c010325554100000200200c0c0280003c6030807440388100404450300c02c107030f080c0126520301c00d46581440c2c00c880d101c003e11066208140590b0110414907290659580303414810f0000d80c03850300081413640c0400e20507500031101c89 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 730772895 1250 730771645 730771681
    0x1090809030f01050c04030311030c0106060c030e1c0809010e13020a140a09140f120c030106141503070c12091e260111070507050406050f03030f03040204091a 70
    0x20b030003031055003000e0350b02d0700c0d05002e540402003e020040d048040810000c0064411030300701a0b00034807109683c5c00001d405006401010780018005116504007410290007050b185010040744c110303160340a0302d6800581d0484039199041050007100803c095540c00380303000e15000e11003401070746c03000d0186002c1d20442580c408034141060034440d480c6100d410805507021500300d0f584c24050040c402c40000d20441d81c1d94003c5a100744503460030032402c0c600080c02480d4110035002009116203400801c1400c2884100c2694095031016130300c13400000c0c0c0c2c1c014507004000e50604c40c00b07a000c29520900079102c00f070104400a01c0795030003000129140c4990704032a0302082c0200074482c1c14000d050b01804914131104202020800b0503075440c80c3c0950000f0a0640042c0143e0f840f0040342c507026407a81680d20605100300e042001c04102d03840c0541441401d0b100040056240c5030306107000304015000107105a920682c1c40782078001180300800c818001c0010b6400c00ca00d540740510520898503805 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 730774145 1250 730772895 730772923
    0x3030a031409060705030a090f02060307021614030c0f030a02042307081015141908010b0c1f060801020d0f0e010504030e01051c0c030b0a0b1908180109080903 70
    0x100084c020020380050460760005400300000c0380c003210500302010f0035000102c0084d0800c4c0c000040061042d40490141201c413943d0032880c070115520407170030b001101e0b110030595054020140300761441c03400154070240f02c003002d025034903e50070f40e4000030100e481c1d10000104150048002c00140c024560109900030ba035410003424600381442c104070071407101c0c084d40541180e02c0b003004100c0c600404c0728800340d84002025a9031940036040c160780940480030600c0104200400108a40e5112003e41c8c40300c2c0c0010004008030171a000780034945480c0ca102c003020055480d00c0100d034a40d003e00003000034070700300480418451130b82d45600003240c214160481c032903490a403e0000103a0302107003030450368009203040358454201f0400600b5180c00c03c00517000c0300385402980d0085a41607000031041d4002242c1d10380c0c4903965900400000d10410710f4080460846004041c14140299020780e004660418190340303540d500400300b82142c580c0c04c41034500000c0401d20341450702d0200002d8143c5464 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 730775395 1250 730774145 730774153
    0x80d0c210503181504140f211308010c0201020a1d09010312050f0304050109140604030909020a03090f0507090501080a02030c060a0c0f0f0201081e04030e040b03030a031409 76
    0xc031000081c01c601000d40030b03804020f0320f40014190706004100b03490f840010b41180d000e080c00c1514085540004151501c01180605194510000e81c08070b80b012143c410030180b042d501c90030314045c11b115400031800d83c1c1401904c032000304514030300b40720300c401c0411150001a500d20010b03002030012181600b112080401c05819050b10341c542400081c11640d014210b0458005050001d840d14050002c0001d0352150200030417061080540046a0301c900980c01c24000f4180a80541c0e01c4000444020700410610344081003283e40c294010175104499107070015400c402661f0b40e034558100003005480035400a01d052007107200600c0f52a005044000081c080701d40c1e00e074042621100d1041d43e0900c241400b15010001d070b03008650354200c00354000e45041914055161004141254000980c00034001c84006541c12101032024100c80c2180c0307140703c50565072503608460421500043e40e0300300b52182c02d00d05454074104007900c020308254402007040d0242c034960130300076807000301110110b40c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 730776645 1250 730775395 730775453
    0x4061d01140d120c0203032b060824040206040902040303020c010905060a0f08190e071406070b01030b0405070e0106120b0402090607143c070e060607030207080d0c 72
    0x1c4900d610030400c83e82c2004000c045030380c00000d0450152031817100804601c1c03c16003500f0580311010b045d021184030390420030b56440300f81e510f69459507044c01181c62240f00c21250b4560103540c00307603a4050700c0149910703d460344031460041030740c00076072045001d640261051303400741d03030004031a42c0a000280d0707480d4280a1015402024020345014040c01d0050320070200300b0400803580c400c01e4101001d0300038415900c00304070207990340680b03100740465100d000c4003000f0546042c40c110381b1030f1604000707030b19000d03400c64858111041001e04200e8480c40b8400d000661186c4030005240204103130389a480114201e0120301003034485c4411140d210700d01c104030980c996582c40094500ca25084105103000e842c0b424401480c061800c101c0403004d60710003c8110b912100c0511080036080c0180b00b142c512a151b00126507591100c0c0980b038810340c00ba100148290a00f980039248241c068811a00c04540d43c4e58101d0829403100010700024500c0420381d002d0110303000c004950103a118080d00c202c03107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 730777895 1250 730776645 730776653
    0x15030304090f020f0c1f05090601260d09060f0c05070603020702010c05010204091e0b0114161a060306010b0f0405010c0f0605070801090f02090d1104061d01140d 71
    0x48a00d00403060415074030349a902c14080709030f06445908000001d996550b02403010095034a0100244580b007148050136144840d00316070150500031045c000081071182d0a140021140050b412458070720506401c442d0052140c04011103075170708915442c0c0c0556582002e0008145440050380c103010712040700c0d00ba034001400090b00300304035400f030704c0d0043e16891180300403140311081c40006030541d80040b0700407414002d540d00600c0300164400f51000b1486180c01900c0c01c0d82c0c408a481070110302c41c546070700c4c6070f0784602e0001d04020900398064110340318940e6030103524014210300821080f9228041000508081002c0c40c0504440480281840c1031a102c0305454855406014100303c0130351710074010040e50340fa4011605900c0704042c40b02e444c011500400301c8a00340325148540d401c1c070a1411401c0c0c450700c22078030344d1040030f45400c003091070300c1e1281000802d40300515500240e44081c0042d0308070b05901511030600e447c00384900d955140c04060300c01810441d81640c4944041d074218800a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 730779145 1250 730777895 730777897
    0x40f020f0d02011b030e0a0803030604050a0b030c01032d02041a0301030f11030a06050109050a0606030204060e0607150504030f030c03110a080403020c03120c101820030a1109150303 80
    0x101c0d042c030b10307104c003810300d140481704440c4200c003042e0403041200001c2405030020000d1071041c03000f62800c01c4039564500d42c003000c5c1e440200e000342c2c15402196520362035510035007118041d2455401810064407425180d8109040340d0302c10b5251607540407500b44100c3e20503410020412041d492464115410368903036038070010b440380300203003403c480805001c02c0c4d860a20440d440e0642280c1c0421031503070b40310940f00140800301c5040c041c0614110000c01d441d8001d2090714140d504542d6600b840c481c1013001e004007a400280309441c04204c0020356950746640c1d0040e18840d91280d580c02401703100713400025064442c0742da00a4107041c01c10a1005400e4200004d44414000d24644160251220b08060b400d00307034084155038050080b1140d141c40c0c0700c04c00300207003e0110400112216982c0401102048549413600e00d0902c20a42030b40c20003191070851544c1115207060a000340c40206500043c0c9480135045003240c036888101104074492604401d01a80400c40700d000d03882c440807a200090b00c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 730780395 1250 730779145 730779167
    0x180a08070b071106040905010323060a0216080c010207151b0e12011515020105090705040b061314090601110d03180b0112110a080a0b060d0b040f020f0d0201 69
    0x39030300814500140101401001403c0c0c00c0038240b0350b900d9031550301c110701820090005652070168060002c00c0d480304100221101c484020180050383c80e41112140654044104801c07000012485000400c405038010001b40d4a02c1d000103a80700100d01e04101c6010200f00889080c0345403c2c1c0d108140004411240024007107480c003400da155400380001c20413800c09490790340c15807070b06401c648820075016540c0241c13440c1c003444088401b031518040782650011101d4810300d0300000001c10050038160808044820002c103907a0600400d240000b0241a2070b901c102c074002d00e82c07220f11945040004000f604000d0030310f010840c2d40d001282e103550b80c5828518503802c0568810300350301502c0345d0038903841c030300c0340c0c40f80b0201d403196955041b2605118003880c0c19160f078040e050600c50f0503e03004008004644102c4081e20141d4495150b800300850000c0a454100f943c2130195000500100000c0d4130071407256507030001c25100e070300500001d16548400a13000319401c0c0b07011000350313030000c00b44c4207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 730781645 1250 730780395 730780409
    0x34030b03030a020d030f0204080a0c05011202180d08040e0a051006030e0a0f260d060e010e04150f090302030d0f02030c1b150f01080c030a08030103060b12030d02180a0807 75
    0x2c0307a10503106006c00070300c120751040c46540120346842080102c0b041042003180c000341d0704c1b01c298a500c40b40c230104a05c900e0400d0800401064062142400c5c5034640084050040c0e100c0d9051a07542c10083c030050504981006017580e58a04200400030261140030240506140030480201c0806001c1d40d51144600082d14244954807218100b100403000382601444040020100c5200b10320700c202e19803c800401c810340b03820400c0c0452666910508a81207d4032480211065180da440d15a990034240010000050300d6240c84c0103401414000d00001911941c000c50740c0e4500d0001c4a0308031a8900c044d810003500400c1401070003415441542c0d01c1090081c031442008402d41c800d5031070601590500894046d082040060381c103a098911412a42081c007950000c40b180820552683c805941c01811000c05200620200300c0300c0c0c5c02600004009403003003110f101c0714419146950002807603640281d070000b510502c0b4000e0410244035400701902d82e00c0289041600c9141c0b10300c0725000f003007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 730782895 1250 730781645 730781651
    0xb0609040c17330d05030c030909090d020d0807090801151e05012a0210200a0314071b0801051503060408040b0f0412050106030204060e090606010834030b03030a020d03 74
    0x1151a44c81c68036184107160300c441200ea03214003402e1115100d0304140b025901c04d4071000002481c0740d0020641d00140c0c441503010b058002080c65055440c01d601614101c1040400d11010500201c240305804050306c1014565405516100321101d03d2400d24000191000c4078207010886030b6042443c2400710441411804003481c2407090340224400324540195003c0c5081180000150b00101980c00b031062a44082103002032090107207540d6000c1c070300000c1c001001d00186103580b188182c09040310903c6008c01a903640c00044c1400b45101c12a0031074a0240d640d1400e0000030304c850a80c44207492800c1c3c02a14052509864104060265104e004019880014100c40b20030170303201250090180d0b0005580d8000f01414840c1c001d0460f0701003240a1403a0500100380155044a000c0c400c030b00781c600510407036480d0b07401141c480c0409060125550103000301d01d80c07036001d01103403400b4540400740a40a5000741c0103004054a240c0c4180c0d60003604100407044546901107015904541282804 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 730784145 1250 730782895 730782991
    0x1020c0729030f070906050a020a03050f0c0a0b0604061203120e21120a090222020d0c0507111909021318051e01080c01030b0609040c17 60
    0x35980790046000051800400104004008026150060180c02c02d6501d40701455200c103400d44e100d200b0518240701690146900400280c402c1005061114500b06020305001082141ca45090982101203034403a410b039080008608091185100410040b042102d4254003900d000c0d0850007040c41c081003454031041d520710915410440d5808008106c000b141c02c0001080d6107404e00e801000020403013941e1030300801c0b011001801401c003520380090000810740522003d81800c0b0801e43d046070300c130781e4080c8540804074000c1d204600180c240780c0c561640e10b01003803030400c60b011030040d03d151080d919030640800001d411241d01040d646031440060340c41056540c2400c020416900c18400414031480e081c03005081500450300400f5281d02419101600500d182c55148090080c11001d0780120715003010f961103604011000c0314054070b40c038505070000e00401c1c1a00d000c1e5411340041816420f08100c1d910700f20360101d500c11141240c051030401e0812030111004c0202d9a1400580d1000b001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 730785395 1250 730784145 730784189
    0x30f050c0901080a0e0607050304030f0e060f0d0902060d02040e0130050115061106060d12120b04021206090c13060806190306060f050f030a032a0f060e01020c07 71
    0x5d032105201000c0300c81601d880c5200419540c01107908400250004115051050040314040300b10540102054189061800580c14a821050040100e0340e1150030341d0700580c5480004002c00800d007840540d4a82c1400d01030041c8a02c1079000c0f00780c04a0ba5141e60410139440344002c1640003803042044440f200c1e03400c00c903024100251005402d140d00070400141982c02c01c901044041e59642644c1c4155202d03030401407881c0c07605101078a03c10034081395403550b5114100c5640e01c44280030000603031944410210b0201e822018a03e0200c030781d44c4040c0490381c42e0500005600640a04a182c50000040010501004144114028041410041441c4e40d441002641c14412010300007620344d80d507801c0101c040e0401380f050304884c0a40100100fa03a050402080000903800303001003820810729070702198544420400714244218107415260b5a60513008002d248034001c4211000124890a00004481c1900312020042e0320400204509407004580c0d40d0031641c1001c2541080714001c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 730786645 1250 730785395 730785401
    0x8070f08180405070320030a0f050a090203070f0f050402070606090c0206040209060f012304080f0c0310020301030f030804140d180e190f09020a1203030f050c0901080a 74
    0x14000c144110110300d900d001c515255051a00c01e400301c5050000c2d80300c80307109400f00c840b030344000801c0021502c07500076515410401581c101c1c03d00f050000c0d4820840041001700c1c0d00c180d40ca0b214842e201d0410300154581041518040d00c8211200e08400b89400c000001850a5101d9a40500e40104283c1c1c00c0c00315079405040100405c8100340540412482c0c02921400f040300d08030b04c181d03018404500309092001d00c91a000c4010b03115940d12403910f010502042e06c00524141281404000100e8504000d01c080f04418403000010003503023481d03c0c04c06041121206401000c01d10610042000c100c070311120b07000240d05410411410781f04c40c2072081800f040808032540307900c10b0f0f000313842c1900e41c008516100d10164800400c800354807105107034201c120a40300480b034451300402021032004180c0c031507030700ac107010703817000420398003640c042000500d8940c003520f011071014024a045c0741e01800f55000e5502d91030410001890084402d1286028102115042205420000346000d07120342c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 730787895 1250 730786645 730786673
    0x110402040b07030e091503030d0f0b06070b010f0b07020a1401121b0809060915090f060a020c0c03150112060e031303120318120c120509120a02030304030807 69
    0x5803a6601d206500700a841c60031100101c2c5d018410351000551082000b80c0c4141c2440070041c05035207850031010200f4003a21801e40d01a60107540c0d80c01c1d40340b241e40c0d88401003ea052241c22501841e615200c60016400d1050740720341401c0008001c0d000041e80d4001140003a40d45052045110311540c200403100c008050010482d401c0c90403454005104041c100350301c0500640d543d2105036900c40c10444c2d11444150340d60889640306003607200036003009610b40c0d0380c01610141111003075100054134626000043e40d0b49031555600003148400c0000078010f0b895039440640c000c2c004500440d0301000b2015052141e002d0701007141060200b00091500309200b401010000c0f240c5548180d50719045105152000303c80d510b0134690703003200b018068010342c4482014611301e842c18200781d40f03480c603000380c0d403009a604002050f91840005000140c0c5000303a4041c5d540c85685a16129007881000c2e0310b8040d16a1055003c058603800580c2c0c000b08860a0300da006039200c0d194a441d281c9042004007007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 730789145 1250 730787895 730787909
    0x3022214010602010f060f0b0412050a05010504030810050609150309070320040b0a030c05040209010c0b2401050705060612010603020904030c0204110906070b1005150904061d010311040204 83
    0x300000103540f81d0541200000c5144040c007001b10702e03603520001305c19640c0b074490440481780c01c0c0420003040c0741a1258510050182040c2c40020f4030980c1d4250865130102c1c1d044012501e001d042c49030120070888003101910041c0c503c24a003c80d07485c00601541c0e43c081c100f000d0400c002000496a68080c803c40e40150f42c0101d540703031150000c6c804101d500c040c040b5518062450140e0b0101c16103080c06880c0116600325051007603403030500c81800069807000104505104040720380c0000900d09480c1c480c400c200003040110010341110f030350300c541c0000a0141d41000001e101c40d0340884e5001c1100c50f0131503004c440302d80b44980400c0181c1c0c003501c03503a480654490350002c208024190040d000030800e074400c503003c00c410100f43c15481d50310b02800c070078203412030f0301407003210b00048845410751b0700f115001c1c4000003030035a603000250799a400d078001480503400c040350f0300301c06040501505020b4040c0802c19080c2480380440c943d01e5100c1440050494005e42038181141d803035603070488000e0009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 730790395 1250 730789145 730789181
    0x15080a03050d0b0f0a0e0a090c090207030e03160e1f240309120807170705071b030203060609041b06050c0d0c080318010608060f060108070207030222 66
    0x40c103000d881908041c80d6000080d0030031110119526149180d002070b40e8004181c46885801c140e40c80004046c0180b401c901d02e641c3d0511500895100060100140040c0e0000f5a80d494039150003049071078000007082c0241c2c0700d04d9010a081040351000415150a403114000701da0f18080c0c80800c000801400e444c07800c6400c0030200e8500032540b00d000503c01400381180b854295107100700d08454841c00090080051941c000c000c8500c02c0003c0d41d048881460400d10001c404c502508241c54180d074048080360300000d44508000b00d1038541c20501e1803403402e403c00189150046611040004c010a108103c8040001c1c1080507200c100d6006051914808901c1ea44035032003e882c6900c0304584500c944200706030006000e2041c500d5054803a4401c4004e03080d40c4801341050003034850218a0380f029520f603d8085074219003005914400ca2103100b40b940241042400940400c0014188070f0442d00407500500250300e0342241c054481d600300c5859484405040020360050605031085408040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 730791645 1250 730790395 730790413
    0x152306190203040e0f0f041e020a0609050a05120a170d060f0513020a091701020f071b080303070806010f0e0d05060406150e0c0f090d080304050d0c0b0a1508 69
    0x140c000050400d0350250007000599031904882115200c070f04070b608090512046c0001000141070101407203040c490040040f80d0044250b0015030650f02540180002a006000421880c80c00a16160041205880360100c013020741c0314058840300c404202428211100000000d03113a0040c04031380c111700c0c4140c020011283c984100400c58052842076a2203202c10750a0269441141d100300e84006140352200c0b0640380c41e1807030000c410b44200c44041c02030b55017032000c0c40440f4a40c0d002022a28401c0191041c81c1e1000c111280100045401811040c0d0017070042150650700082c500e9000302007401c00b0b99503601c3d20002100e92038113040107203030800c0201c500c2d40308000f030004203540601e104070414050040100c41c0c04600d0101ca101e40040d282201c80414080e880210040000c2c5940d582003918025845010030340d415810f4030100d500d61400010002030010a1080002071045860564441d000725200ca88a0000c06440d21111903515094032a0014020354000020041c2c4025074030364407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 730792895 1250 730791645 730791647
    0x312070903140c1305060105070b1f0e1f08030301120602070c03050312071d010c020312040f0f0902030c0a0e040b04110705061003020907140c06160315230619 70
    0x4070f00c1c00d070b6500600411009881c0302c0103034040c20b44100c0040c0d407024284406a140d050f844d0030003800f03454101801c900c17070340c050020410002015090403220035619080c54071220400b00002e024145048001c1c5c2800c0c0811540801140d04507608000141480036007070070400300a00c6034000003060040c0748007000040060100142ca1a1091a0140031065130350a1081d0350100c11030041c401b040d100000d109102c0d601036040081e62900113000c441e19039030041d19400c520360094000c880b00340d0305014104012040c0f03c4a0001400d0713004029030440c10078080c0140785008034000b0703005101004000c101c01c0e441c0c6a00c440b41c5404010014080c1c541600b0751030803164080b420a58042c010f11000555400e0000210380890b9130280407005550b50b440030845800c40100b581007074024040040840381c0c1810171010b405030443e021006158104c140015044455050190b00c4a2003002e42c2003044403c502d0b03140c1858400c8014070030000b01c1c0d00000400a2141d40c0c100080101d09800542d021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 730794145 1250 730792895 730792903
    0x30b030316020f0409111e040507110d030c080a050901150b090f1c14070305060408130608130213020403062a080f0705131203021f0e031207090314 65
    0x1d4000d03142a041d00808005010a0320b0342c06402034588800722032900760a0405207840c03002c0b0075442c0319152100c4040400581564010303151500020070406a080358100e052025003181d210070704007007084644662024180002c000d000d6102140e440d03001a140302020b4000385030680e001c1e040341440c141c441d1880c0000790402483c1c54010840703c14031010034140b280000c02e013100415102155000940d81d00c03501072001c0c13055154607001300a000000280708104141c0035038810100c0603240c1040b00e00b072004c40800744d4403a004218404007808044000d035260700b4a22601682c40e0b400ca000602840707c0070384155840140780f04d143c4200c4540d5448100407007294541c4080640c0d240652001003116080d05c281d5414042040280200d000607001d40c00a0031588142c200900d47c5075520554004900428041500580c002110030135061045007015480c00b040c145e001c0040c0d040c010542c0d90b490154103221134101328004085680103000d684101d0066501c09090004c1608000c4400e0f00c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 730795395 1250 730794145 730794187
    0x30210090f060903080304200901080f06100522060b181302070201051213020904060506010207060906050a03020c03040801020310030302070807060e0f0d120f02150103080415030b0303 81
    0x16003400c81e00d011600d94070880b040802c8a070801041800c40c2c9441d00c411450162141750409a1440c034641000d850301e903908402c0c02000c0540103040f0900c4642c81c034904040c0c006001c03101c1c05c4040c41007440385a03a40e40c000c456654181c40b00d28001111008030400500c42c1d504200c902ea1408110407848401d212813020800c0c00239910802803424032001c0c402a801244802804110180000205040b0049501c0d921400641050340d01050907004118130040564003520304a444200301314483d601001648003d100a14046c0307981450200010030034003400c0c1082d0109038001415210000042096601401c0200c0085640341411121042003e8941c4030880c054080e040340015481c202007032810880345035840304041205648100500b000001262991000544841381d001ca0361800010540032503c0e1209018048100d00c068a4040c2c4062030b0309036030281070014800030760b40d401510116a080a2180142d0500900940103848004e21a542512001c101500704280c03000000030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 730796645 1250 730795395 730795409
    0x4030b07200c1903050c060304150c03090b0906010b03060d02011101150f0f0e0a09062003010f0e1506071a13030305090a110f030c130c080105010203030f010306050601050403021009 80
    0x10030441030310f82c1c00c0403491001070000e0708080030000103810500e000315030051060035089040605d60601c28219802d0104070340010b0741e500040403c10012010098001c0c590400411296142c440208502d1100400d82c034090301880c030040307046901400c0701c1030544141d50300900040c1d071124410240720303200c0e04c15018109410900000e02806144540c002c1c1c541105a8802d95901c1000001c0607124603503049504903958125080c0e0701c8400d1000e040102d851000b0b1039920351400384070141c3d0b429190040400a200700c000d0021803141d001e0350100c000c40c2900d046881c3c451505103801170384060300c04401d0750b01e201c030108515901402071820000703200303880030859a105c82864607550904c600008150300001810010545007a035220340711044000c00711102005c200300400c0d0a1880b6205440e15140c0380e0040796609900b1001e07a6024103800e100850035494280354106d80307141d0611006d010940e60301d0205205900c14030854000c3c3d034020341031540700350101100500100551261f24 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 730797895 1250 730796645 730796659
    0x218061c05060a030f0201140705030a030c11150a180c0602010e010c0905030604060e0735150f070c170a08070f090614090d0b0901050703090804030b07200c 69
    0x384072890070407183d80a5075000342d106145411554015109080d41d80d001541e10201440a90b001503030800c01090203000340e40c0d000c1250340302d11401820a412040c030140c0550010034190341c0c00c1c40c0c0ca04505a0005286a01043e0801103002030202844000e0000d4030007120400701040f620f4054103c3c900350f2180e42e00030490984c1204044070100414010603506401410104000c03c9650308400039002d0041e05441034650340b041c419920440c46d1358207070820b0000907619260100d510040344101c0b807410000d00b002d41041480401e850f50010081c0d95480c02580101c5c158030700c00e05000032400d038003409010410040488002598011503450000102c8103c0094411842154080304480d610340324041414204942941e042429403001c100c001028000e48985594010035644c0321805607600810900380305503224251000144202e0a01d800c0c01030090000341c40c20129811a034200000300407a80362060300311003032840034940e900740b1700c070710310b869500040086008540c042c41104c2103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 730799145 1250 730797895 730797901
    0x507090e060f01120903110f0c01170c1e07080a12051632030f090d1809020c0327030709112a060403020304062703060218061c05 57
    0x54182c040c01c40301ea0003d130803055154807080041d001020700ca4468140088a104061800c62400c6011009100a9401400721580030b503084102e01d02c0c207925a55040005140822503030381c0520401402c0c00c2c0d0450180030380045488601d0696203159809400c6907901c40d03903100b00400d50351010303d850a5103454000410b2140500b4099003030380314030317a881e1030500801c4440200f0030b0f45c407800341d10403103401d1300408601ca0301003400007184143c50054422050b801c0c0b80b110f013441c2c484c00c040200300b8408052243c0400286410402040b10480744000d0307030710300f6045401c500314050f4112800d00103c96001c6032003081c142e03180495000000b42e040b0b943c0d0070380d03caa40b8015244c602c4030040910704104071400110044030171048010305d400c0c0700000b400f415441c18615010003201c0c00c0d0010b81010509200641d803010f00c4415038078100250300346500c0100310300410001d580c03200408695001480c442640103080103002100c4c00100010f88905511005031241d0600c0b44580425900d40000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 730800395 1250 730799145 730799149
    0x303150105180405190608100c0f02030909150d120206160c0b07030912020601030204140702060f070e03070f0815190c0c2906010801060f03090f060507090e06 70
    0x64800100c2c0c80390349401e0600c2c03400d061100925004e0481044203140e010390308070049450040c880200981d400401c003204100c0010402c8510189a41c0d081081084549121541c0001601c0c011001103c020003603444451052400c0c400e81c000d0302d9084603244d8140014031081c00e11000925505400780c41c05a1b8a02c20341000c1c0c0e0001401450200750303030011900118408003c171075841503043c180010009034a444200314484010301c08001030313000400600440c1450f00512135508001c8040c0401c80c141454065296000208190a036110352400541da0502c154400409605e014003a100c04a03115441c84c0764801e40c40c0981d80c038610070b5070110741140904108181c81000e100c2d1110706003600508410303018140e607100031000c1001e68901300000c0f8201044d0185951702e2082d41c0c0300d804180c0003501e070329104020001418003010000401500d40c004a0340404425145000120120b091034500d2421207030b02005415217280408000800f50080251000d880f4540614030b080e94a0f101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 730801645 1250 730800395 730800397
    0xf120614120718020d02160f060f05010b0706021e0d0903020c0909030a0c08090a09020c060a0e0303011a1e090a17030403060b120d020d18030c03081e0c0303150105 72
    0x2c07441260785072840480c100c000d519800b0302120710105c64003500c1d000524000001100d90002e00740d401310750010980d002c00000d4420201c40903194841030100d5851320035000e0107130203040703405089690002220680752002010305200341100301c0032182c850300d600d404076005100b41002140507200741c12400c0294980001494450034001d0002c0d4a40b00c2d07080030460302501d070404c04669070b40c0b05210b40241990b41c1c210250107450740c0d4a0058903075a000b075038185405006040462a1440c200d00001c140350f0120849045d600c202d203500403003d01c3d00502207036074803450f1034070781e80344256814045802d80ea1600604206400311aa412002d071504030351207052035480d222034a2035004005c01c20019401da000307258028001858000198420b034002400c1851400801300180c110130240520160022804121401001c42000307940f820741c1c0da069110394103400003404000000c21384550742680d141139196074403280c0e0744040e242c0c031150064558982050f50f040c0001c1c054002c410031036504c100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 730802895 1250 730801645 730801649
    0x6021314030726010204060519050a0e0f010903050f010204030201092c0a1d010f0501060504050a0905060d020303040e09190b1308040b0f0702040506041b0f1206141207 74
    0x2000350090501d4240841480c2c80c900d0548984240c50010f602626242807004c2c00040071503444042c0c1c0e4440c82441c42e0307005880324a8050500200380410540b45900c071000c1e0080c0c0500361820100640c1050040c1d500040c00d078030080451003412410140000d041d0090320489100fa298010b003182c540240d00826000c102c41402c214140d0506801680c10304c03002a030304481070100005108144484c5280c0c2c1c83c9540140610703a80d1100200b00040703c440c030803540180201c0c9001800c19080070002000000c2900c6545a423035110f0000c83d03c195514249034520941c01421250355a40c0c0d03024030a4040b104440d001f074103005429112840c43d0700184c0b00f4000d03070381c40112880f460791307019480407544880c0711085e108600103200114403607603640010b152100c06c0301c007520b4507403000b0310406c000d45000402c00c41c0510705201d04d94200040c0042c18400f00582410801e119000d0154100d950702c10080c0340707a080900740403001034006940800000090340c00e0360001c0c0c8141c0f240740320613034901d154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 730804145 1250 730802895 730802899
    0x50403020f040b030a0f020a0509040b090c10050418060e0f010f0602340b0a120f0216120509060a0c050f0c0307060c03090312050310080c01080612010e01060306021314 74
    0x20308400c0006c45c140a4512013600c01804d181850740c440010a220303100454003200e910000c0030038001044800c00c155209041d04403001603d035191110001d106010f28424180c0c0b5114401201403081910342084014004880148078585402d600101c201902881070543e2003103100d401094080c80804c8040c50040e8000940d6031003042c00040803c0d600c1c04400c000500003440078081803000002c4000c0c5144035003540d44c409003561943c000400c40384000c2084a81910400c1032400141c1d5004440c80d0068005500c84102c54141d40103035210700c41c1d03000c1e40b6403210001486450640e0002c40d850f60b21400740e8129548000c8400c4810394400e000c034a06540340d80401010004903201e814440d059910a15128529613601e80c0d407415880188406600400d5000c800c00060b034494a007406c00a02e400801002c0d805020000a0702a00c0080d002c180500d000d9000b20710340c07031000d400a0f8042c0c81e4240003040b1030355a82c1400c3c8029000303805e8911400f24440b80000340700c1020012a0042000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 730805395 1250 730804145 730804153
    0x41101122702060c0d2a050a032f10060509040f140a0c030b0f090303100504150e070f2c060904090f0f06050717191b050403020f040b03 60
    0x1801021040c0c00074502012607020108010005040c61300b48142241a00d0300d403240c00000e40ca122030048606e0781c3c01e0782d00880b801c0500c81400440c200081c0c0c0c1d201c80750117050200c088001c4049180030124001080011040e8040e1007010a02c1c0001d00300d003c4901c001002c01c0000d460394100103802d407060742e000d0700c101c03031501e001c00114003810300703044a40541000b21802d1181c50b9903010080b0f0483e0b401516003001d0741080044224000e03221560082141000d13510314542800d034144504440d000d601e00490742c40c46410014800e900b03034007000d0705221305400d00c01e14095034002e100b80e041d160014000341e00d4040d00c881790a00b1400d000c05a20804007518001218070040c030416805c00d00c1e0307241d40292a0940c40000c52408584002614041c0c01040a00c0110741041011788102802075030822000101481d10300325a0140d05412250750301c1e81c80014214030414070040c1502089010701e0020f19400e44400f250000014003c41c1d2081da0890f81c103108110400c4101c030382a402560301904 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 730806645 1250 730805395 730805441
    0x3010b0714070504090602030412050c1e0304030228060f0c0204200f0c0f0309090f25030c11151b070507061706030a080d0f021204110112 61
    0x30400c4201c208030300c11000c80b00180e55a00c0003a0684038441019661540c0c00814881448102c100c0c4c0c28142c0c08600700f81d0f15110203103a11907620344084844201d4106803c100000d0b482060046500440d00180030100004145040400c89504d80400b010001d002d5040098014011546400d10a140d903c890340c90780165000d200107440310341c240540c1d000184000f070080b04680405000c20f011080071040e150080444040d14040720f0780141b46640c1d0080c0300765841c40c0c1c3c40032000c4d544661140a040303401d0319980da4000d403100d00b03409030080c02c180b0712002a540ca80d265000080d00300b0355643e01290390782c0524040341c4980814500301d40c644403000014100d58100001141d440d0390024100749402c1103a180e0a0a200541d00701c4400900114003a840342849884d5241d0070841c214060180510079039120400f43c895124840b1455442d0245441d9190541e410b40b5410013882c0d100c0380300d1f85440c5c5000781000707401c0707100140801d21501c0044d10584041c49000e42c1e80c0099039030746401c0c503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 730807895 1250 730806645 730806653
    0x60304060906021b1b03060a020d0e0a050c01080a050c04050409020d061a130912050702130c08010614130e13020901030b0609180c04021305060d0510080a02090c130e2a03010b07 78
    0x1500c0074014584030354480f81000b4080c0070170001c150304240654050700c0c0133b003052000100017160250160f00b040c1c1c1002c1c24840c2156580c811a4100c03541110002076022042c4041100800408000791110340303070145000a0b54500006004540c500302d4004030750705100d00120044070085c3c1070107030050344500d002e040b015000303100408465000070700c440f11001c1c01c0100b04041ea80440900c0c0c0002c0c049000401c807203501300c1200803101103038100d0300d410403071000911004c0030581c4c03140704580d40b81d00c1c0c007252800d501c041142c0d03402e40e0003400c421680c0d030b100e080c600480c107426280305010320b511034001a0384100e000703000601300c01d80c50064100000380104100203900b00528901103005081c00000b00da96412008010002e80810007107540d02d00100001c3d80c0314810780c080300c400c3e001104814010b075110411207034030482d07401030701e51030f8042450491801034298001400001c051002c3c00860300c0501c0c80116589a0124208800d9100b08400e6008d804280b042913041542400100002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 730809145 1250 730807895 730807897
    0xf210806100e0d03230a02060106030e0307020d110a0b0309060702061006050d1506021f0506100309060603060903050315030712030309051018021f0e060304060906021b1b03060a02 79
    0xe90700074601020596503000304501403801005c1c0179001041c00242e40701e003164040c403c0c10b0040650f828100481410034001e2030f101d104141c0001c3c4144a22044c0354100702d800300014207000006032840282507151100303860b07554000e0380d800e0080d1003000c0004034114030001c0d04911602d450b2070114010351801e40b0980d6240c000040300c107403603501c3e00c0f0410100d426450404004040300d40c0140b1000d03c6844071000c00210505800401c030342000d04102e61519654000d060004562800207100d00ca40c4c1885001840303141c0004041a0401c0303001401e1540c804003841c000d030801c0040b29000250700007059a2002144525154501e9440010003c20f0081e40114003903405801500e10784460004510f0856805c5015654110300101c1e100c406c0d0300f4001c0441076014a014901c180c0c1c11004140a45008504d0107410711811000000a04003c80341d00603120090f40000295102e031020748442c001c0310403c440601c250b1103207445c414000c440c110750007240b90102030080c21054440203003220103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 730810395 1250 730809145 730809169
    0x1f090f0b0d02030c12030d2904050708070e03010b0603010f05210a03031109121c02010213050411070602120a050a021206100905030303040614090304210f210806100e 73
    0x810b020034890100400a18000d407003510000d460440450b41c0b02c030180700250301e0481c03540c1d400f403450001007106054201e001ca80d04403137582000c0040d949070b60700003030140020000303207a0807a001000010719802282181d0094560860b881c4003040380054081421280c0030302c0c0d140c1d03035a12860f4000302103030284c0e00184010040080440c60310401e07202207040c00c0c0d074400010f001940904910036040e40400400090040284000c0d8504082200100c1428500340646803040d030380c138415a0107100340b03d0103c070980e69102d1000d54860102c05506e422407030003215820b031070b10b04020006644139014400c032441030402d4030384a072464036240c052154000721103070018148a1503003008a4565030800196120701e10512011aa0898289c243c00c072003040617000c42803950090005210801c00d64100c1080c14a030040d400c50345910b203080c504800c640400380600001342d002084031f06110300314141020041152101d2885032207607400d2100c00f860b20418440094403d801c02500752400e000d032144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 730811645 1250 730810395 730810429
    0x70e1012053606150307051c1719030908120c040b04080c1e0303040b070602090919050702030a2a021f02010c09030201080f1f090f0b0d02030c 63
    0x1920ba0044040c039400d00300b01d00c1055035268810300c1c241c107044000c02540c3c0d4801d04200302003c080d088003002c40d40d074200600509102da01e0580703489500c590105070301040c40d9002083e030017005400c6940344605034000e4003442811a8420900c00c0d00034002e0007150050ba0344000241d00d0700b00c000c85440c4446030098503134003c00d001080b000401200c03040151010f05054070140008800040400000b41d4141c4211010f85100c5403074840b5590300441914110354080125554600030381c5041030087c410032005035880401d01080c012020010200e8800400d04000100100d4989000c140e80e82e014201c055000241c074000342c040e1220070003036400d00d00105007241c540040c15a030700040c25130001100c0000d02400c8101c200a06560901410558803103500b040400c079030a5400017828000014050014202c03d840400c8185111345140c00405006c8842101d40949429084020708030009424a2440c1040181c400e585442008a008160700900500b201110017042c80b9000442d000065 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 730812895 1250 730811645 730811671
    0x50a08010e0a061503140105030105060d020910030204051015140409020d231e07020d030c110a05030c0f01020f0702010309021507050705010801060305100e1914070e101205 76
    0x42c901d49406416010604c1c540300401c1c898002c2c100e01e41078102c142d0245109a051400f80106074490340c0c0201040f170740548003440280d5490581414400d000ea000a421900d0301c0e0400c0f1401c00030410140c1501c418045501c00b00c2c502c50411160a00701c0d00d240da0740c034601080200b1030b010045c1d00603e400c0c00903080109104040c001035006110f00304507000e100040b80d100700086101d10310300c119601304105003032900d182000c0000964510100208005050b66540c0c441e84290154885044c034105181c204c4191482c0d52801c85d8994103c601b48401078800d0b00460f080c0c012041c029a4000c0c040030002508000c4280c004501800c1d14020913032f0130154112035018902d02d00002082407a009030300801070b0510b40000100a440140e0000f41010726000c00e101c058941d082c0d05038110348204803200b4098a82e00e0202802c43c081c03503002070489140c1071004024041405019104010b261103000e54041c5503410b00036440c80041160700065416480040b8920b403551085421191240d01c00c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 730814145 1250 730812895 730812899
    0x220e0a0c021b13110301121118010e19092001020708060a051e0901021201050f2d060a1101050c04080718020405060f09030606120a030e2b03020d050a08010e0a06 71
    0x44c0c0e0194005e0700f24048103e0008143c1080c45120245025804800e40d005400e0203192802100d41e182d045c040c58142d0101840401c40b400c14200159800c500c0b03103242000500403614190556881c2d01d849810020721190310704c02c40c0e600129900e01201d8aaa002c0c041940d5006060001000300034050200d21000f5500d14041d03050010381c0e03038030401c030348400140c5d03a0310301040207421810141d00040c0f240300b0700300300f510b03060701c0340210312000d102040c0060844450014280c664111001c1e5065040380d408280300c024294410b41100c480740d02e20000300402e4842140002c03c2d8490b0f801000040c0d44099410080150046441c0c038849141000c01800c05071240d0005000c0d62001d40410485c2c2c60200305040346140071b00000b03400440485954026500700614035442d440c3e808000f0301485040c52030001161903c034016412400c420808088680105402e1805082e01c458140c0c0140320f03001c5000c213900d004204848021100d9101c650b81a8641703080105100c40040039205500d07107801d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 730815395 1250 730814145 730814171
    0x1527030a0b0c070302060a0b0a0b130308030a0b040509030a020a232b18060c11040e0115060e06030a0b010216090203090f070515220e0a0c021b13 64
    0x707500e000b80107000049654650600300203140c890060805401540703880da2062556950800400440341503a1207191160b41c0b80c601c00070315001584c000341000f58000108130713a242d480e03800044440c02c211010407160b00c49500307450380c0780144400d010140e4000241c0a021500422002a01d662204c01645011141280b00d03424140c0340302005420300f013032501d5a2419011110086030100144c41c0506242c7c0e4070f42d010030b07101601c4ac1320307403400e1200d0082200e00b0f11911080403861142c0251060000e0111250020300130048802d50880540c80e812020580c031f4403c001e850900c1c0d00c014a41400d60b02c40024110050280103005411b521400d010510b8910940c40000002c00392954016200e18000d62700a080404034111a00ba58100c08828459036640030f5003402e00c0740b031110825458808260150341d4014805c2c8012500301d402100000707078101c201e41c01a10455102c00244100b40246100b680d40d441e001d070014040721485020ba58903030500c80108900620901c03408074002c400059 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 730816645 1250 730815395 730815413
    0x15180717030a1b20090a2a020309060c0a03110a0c0b21040c05040b27100b0d0603050d0503240303160c05030f150c030406150e061527030a 61
    0x7254420740c40c221a108510308480c0c1c00354401c103180014011450380c11142947d240074074184800e01c05001100003003807482082613414441010700215540c00e9140d180c1d95a40b00c0c2414102c0004615001a0080480104d803d603501c0c0d9020408100f014200a01f28015800ca9102c030b8010003200e54000c8500082141c020380268050b1070041d029600b810b00380000d560301e400b8082c1c0205013000d0701100003055182c040d00c0002c01500c0001ca16255511641005e9425600c0700300c7e56040454001c903040150b83c0030780c049900c02c034102c8511558018090350a40001c0b104004c0301c801040715807461180c0700c842d6688000009041c3ca103807050900d42081940d82d1140c3c252011402178105004a0804001c2c0c1156141010020841c8030002c5c2807543c01c0ba000101b00900000004c00480c04020359078008146280d0003100e5000f03081c0e1a4016000d100300104c40151055400da03040c11854090503049410b181c007040c1c0c060700d040100d01c03c018202440d000130650148a003582c10740116140031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 730817895 1250 730816645 730816673
    0xf140f090403170a18061d0f0313081b121e0706120b0d12120f0f0b040b01120903090f0603051e0108061815180717030a1b 54
    0xa218035040000316080240c103814001c10442000e494174400d500c40440192040e0155540100046444040e039004842c021482c01e02d05840c5102d000a000324500000c0094500541c00060040c002a900d0600d02d45d2501c08000107002102d4055903c82e213802c10001506009488208445103100d10425512211101c04207229641d00003031000d102d6154014040b024240604070240510940c040002e03481901e0141e000304980c5109180700180c41c05204008483c402500341001841e030350901c544058081d2640031041306151074a00000c074681071040c541003540603900c4032010314031400ea240080600741800d8081c444003241c0011103002d070080c0b9a014010540c0d0125440c20420348048030303000c50100030310309030340b411006000002d0001190b65002d2001c0c030b0158001800b802a080c1005802c0450300d821b03e8240041004281c05000c6c50290850344400f200c180581d07039110104035142e01d02a00c0e0f403507041001803020340d6218030750100c3c95000b0764003d101088019a10702c4155a015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 730819145 1250 730817895 730817897
    0xe12060c0a03111614150c22090c03091406090d05030a0609091506120b04020112020d020c0601140a08060a09080405031506090a09080a1d0411030f0703060f140f090403 74
    0x1882c07034001c1c0c0d030b1000d000481c00991094a000c01c0307410018040d003800d0003002c0c0c60700e01001c8c600348800035103040b07002080c0003004114000c00408a540c03400034050101540c081e901c1e0700440807424425280014014400c8080c600504110880640102d56507440a442840000e0702c404000c192a40c1d03601c1b40045443c890094070240801640d000d109a61590380f1442086015a8052003c101420360165001d60f0919111b990b8181e00e004540082c02030101c104c0d1130610104442181d07410010305941030303c0404900c403510201c0b40b070402240460078000d0070b1413500f021002c102d4514a83e001b1041c041d2242019604050311a03000c240340c030000c1005a40000000c00902c0b050f41001c805246c0c200ca0404414003039002c0c2600c400c03200d07208a000c00c9041000c44803a080301c40740c1c216000480c904000380184100203030300d08881c43e01c0d0000c1c0c0e0580c003070103401804554150300a1049130101c8060101d10b00c0214500f01d0b0404d03c00e44a02ea10319040200c07900600c4e41d03562100c0405100b2482 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 730820395 1250 730819145 730819163
    0x120201080703061706180622030c0803160e12030706180b040c0f05010c0308070503100f12020f04150506030c041a0301090b0d031d04110a0e12060c0a031116 69
    0x29200d10b03100f81c1002d8500300d285800c44024070105018448d034009440441c4218480980440e00e401c4441003015000a016008044144507005208075071280c2e02000e50340c0d805190720003c400b009080100300680446990080240c1d0f40019030030380103418041066072004000c500a0788500800d0a400c4508035003401205800303014011303240410301d024100a18081d41440350542d0301030469000506201c00340440880018140d1040384000000342070f0803c0704c1c0310041d965100740c06842102e24000c0b0300c16412004890400e040070300c603092a510b100034243d10500c1c030b4036080c40003940c0050454840740008002c003040c80a400460714203109003825010740e880d85011500c0080314a1031005601c41c40103400100046a84040700c600034030440c148000a40d286840003900034030684048054001c808652a01c0d107540103040a0754188080d40c1480c944408140072603100c090807a2100d0710b082041c04183c01c060f210390301603c004840c11202030714102c1026020300340c0c400d011100b2070302c03a20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 730821645 1250 730820395 730820401
    0x6010906080601050403140f0703030206071b08030402150d0e0c01092405030901060911040f0807240c0f1515060c11030c0907030f15120201080703061706 68
    0x64050540802000207262036102414004002045842a44405808030120481c0728801c25024032040c8000c401c80b074200d96101c2c0d03481c0b601940b511001c403100808601036505194005522804074100c80c1e40c0401e556143d83d840da42040024010341101c9030b1100c105000b6404150001e100300380a40c0000401000c0203c08900014115001d039003002c03103600503091a0041000030011003081d0b115403070400a40fa595065081030041503154880d0304001c0c186448460a5102d243c0184252020311a2000200d501d07441040d54a0300302d8441c1740d031000c800c0c05440c5072810b00c0030825600b180f418035204800d5840c9455403407120300820815100304d004410030000c80d803001c3c80b60340307404158a14020b16a600d0b000001e00001c0410101904220a4840b201000d94042c4554603807440018141c5c4014280b070b0200400601d554a0743c1800380f40f901490000b4010b508480b4812aa40c00365800e080381c840703500450311030002030b2072141819110710022901c500c185400c8290020b40e0002809245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 730822895 1250 730821645 730821647
    0x1712040e091b0906010e120102040902120a020f03130201230a030507030b100e060409290a0b031f080105090f150402030a140c03011a0907030b010503060f1f0302030601 74
    0x82c01c98002000035102e00c02c0d03030300507480d1840303580d43c411400d08041400e0b000d100c3c081a9030160141154159510006020410b440c581c1d010704041100d85a0543c0103603141c4c25564101e2003954001e0509800c14000940d1080c50000c580440c10710614000000424294184190010100c03808010800206420740140e5040c0b050a0b0b010f40145030074010f5001d00004500c5040d03003030422004220010b405d50b565501c515003203900800050304208541c88007212802407285520340c441c2040d2000066100051516010540c1922103501d1200c2c515141c1e2074010302240d1100840d03103040a840034002503100e03000c0c0b28a80c8500d04210180a1a83c03a00c0b80081c20848000d40c50800c0250bd00300780005a140004d50285250744161100031201d4140440c5160078100f40c40b131603040d804c05064a1140002e0060300005505c1510100811788545100790305444642510500140041c8000b858a14081000e80381440c0080c3c00f01100d0314181048400c03901c0340c03800007400710b44c001041c08815 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 730824145 1250 730822895 730822903
    0xf0c070308310f060327141005010f0512100606091706010e01030b06011e0f0f020c0102100c05070c0308030105030c0a03050a110a0b12010609080307020102071712040e09 75
    0x4402c0300646040141e090465030b9030a01480d0007400b040543d02c11511b206444201601030149550904d00f00b04e422840c6400c554880701000e64000f42d02840408080760b001130b000e010b050303840e0240306820a03410803042c444c010101182c4804180710340180d400d0003401c07d1140304050042c6580380d01a040c1486115000f48010829400e11030344079100400c0650000540c0354150380d44244034016517103400004940c000d400e110010440001c0740400c0046130381080c1048940100c17900e40b0751015542e0642640c032003107010303000c50158108410f11080d00d4810341c00020b04000d1800c02c0b60410820342c9580c1c4a43c6501d80040710041400030040c000c5160811011815074070403190a40c01509560701d090725980f07100300040c81000108035044180d92520f82c00800340c042100c48985502c2c2d4201011141e0b43c5c20301c24080424201c020100d980d80000c412241f0380e07501a00184015440c01c0d401c10000b5040281c00219400740305c0c403a50b07460b00d07984000e0000b401280300254440c1043c000d03203410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 730825395 1250 730824145 730824217
    0x4170307020c040b0a03051b0d140c130501050d0b0402011e080a14090a0f060908031f080c030d050d0b030a1401050901050105090a0e010b0324010b040303050f0c070308 74
    0x5c1040380c800108000b903c0002c080d0f209a80500d50390b6100b24452001c21803100c0440401401200d0421060200f2076000134090001e200403940301c903101400303900803401c030740c1c0c01c4c001c09410910b119100b501142c0c0006007250054810301d07040002c000000c50040200080e140c0940000701d02d80140100504240202d4107011440d401003100d50800e945420b0b502c4841110042c403140c0700030858801d104450b0b02407124681c00c256110b54134580941510541e4441600c05810b581d810b070000701310b0b041d00082d0622410310140007001100403441085c2c440303410010040c80700382e89600a11150f0344003800380d120707850303ca81000c040d080c0c0c201e0011402d4070802440303210a60300d0170300108125a1103030360554204031503080000d00350b030110a0160140c40c00f81750207501486507045419008541c000c00d440400751449030300345140d807a0110703000b172072003603201c0500010b1050005109000810006010480c004411101032541d41c1e0b40c2d54032903810180b4235000c10400c4102100900042c0360403010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 730826645 1250 730825395 730825399
    0x1a04062304120b091612080c12030118090305040b0f09040c020607020f06070503240405150f0103090b061c12090303030513020a060305071403010b0a1e08040b04170307020c040b 78
    0x9640000e481c031701c600c0344c070740c400c040390780f5511480c4000b4000510103c0d03038401c0d55001a80d15203000d119222409900c00e110341c0101500e602403024085e01280f003070500c85589a07403024a030034640300c0318003044d8102403951344201404005058a0340da4603c40c0c080c0b20001030700900f01e180391960000c1c0c24100c2003c090400c0d90011020028000d50003422603911821400300c0c1c4400c00d050b10f841038503010f103441c0540e40252a0000707100396241114081510640201c036014519490b0000460940700b01a1b001441415910045002c3c0d02c0d18030160500c1031a581c1780c1e01d09810082d201d00c00c0d10f00000d906074000c16030240d014418580e150160991000c60096000c0701003200f5800b00314481710510a880070160781d85c012030f80661180c05260313007074804400b07030a899586034800028203512040c05030020130b1155030f00020460203850300c0500c021094a504071f8580c0e4503202d43c0340c2624024011540304c200c50f9201282c92500320007846c01080b040d4002c0403400c48020500c4219108105554 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 730827895 1250 730826645 730826653
    0x2090708011401050a12020a1206050406051e04020f0a0806100c1211101a030f01050705030c070507050603090a1a0903180301020f0417071a04062304120b09 69
    0x212280d004240e00380381c0b541d004e180c03856071480683e00450b100c0c03882e0200300340500e0000402c02075460707114030b044580b680742c14010001183d840381008115183c5106158210b075080b800301d1a00710880c9010103030100701620151400089034541d0798107901881d807942c0818204000e00002d402c01e203c030402400c401d030070081e20f1140c582d04c131014a680c2c0e010290041005402c1048801c000034080f88104e0200c2c81824005440e1541c41c0c00d042c40f2940c0c1c0310a000744103985c070615840405014a07030103540780303440c0c2c285980c8441074070b0710280c3e111400681c1c1030b2040c408001001c0d2504401140f081c4807441c0506501000c0d85400016541818401e0780c0d000c41030f000f4002010804021260042000440007641c002c020000c02e0180c003034090442c407401c10226000481740100390113000b040700d039101503ea035a0384554820061362403800481031a414140000c7c41014020031003040c100c4224085540740c0c0c00311204860b101d0b0b0040d0444041a800c1249040c100aa066191600322061801030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 730829145 1250 730827895 730827899
    0x150c06011229060f13060f031a0c1b030f070803010503060f0405120a020a0f1208130f060f0f05090d090b090f0103050403050409020f130839040203130209070801 71
    0x510b08040020749070a104d040e40c0008461680e0f00c80c14144054254040140240d40d95161350068a04040c031082d070302e6265041e0040200c100300d81716548582090042c1d5420030040d000508441109280e20000038070040140c0e049001d06a40540800d43c440c8120968a40c1810f0078503040c007d003e4040044080c000041c80001040451900842c10172024100d442e4810f2040032443c05900b40c00190a1407040610003041c0300b104000002c100d01c140d04d48058684408552103070101c81040d0142030f6138013003d01500024400e40000c1310074414031700c020a41241c20412603041300e02c2a5440b501c958040d850780d0700c07502d4101c0707100402485c03250400f0341442e9403840865424007540c0109810149d0712070000b020540a0720a6070701801078503400719210030b54030408810545c0401441d4200c103c0301d00740081c4c40c1c900090f86422f5940c0d21500b40706038552030f046070020042558100003141c01c0d01c1030034245030f4460b44041c5100b85641d02c0c2d2143c4114190041c0521054050300d81c0b01001051401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 730830395 1250 730829145 730829213
    0x6040e01020720190306050703050f01180203041401020d060501110304030201170406020c030d090501150617251205070c05070b0c120703020a111e150c060112 70
    0x80c0e245510f22504142d816003d1550001d036041203003040704411003100c120040240203c60740000d2151100c1d8604201688864038141c801c0e80003441654181e02d041003a4440e05031207900074540003807050340700905002942005c2400d9070080c0091100d20703541c400d810403045d0b074010405581c054100300950f150600f9500000e115a50407001b003880c1200b420045001c0000c0d0758111442c2d40801070540742c03a100d0101260f0040c28101405071059801c12005c021081e5940620904468694885421901c0b640080c0d045a0900030408041b1444402c02c050601114200700110900943d0b170305401054142c000a00f282c4020b81610100a829582c030700004000013100b509680c6680940c41e101d4015a6186c3d00c1d10380d41c107141400c0c1070390200304441010380024084000d248680020300000c07400e103062080d501c505203100740b01046088040b5299013080950310060704280c02c200c524100c0d2240c0c1003450641c081c0d2001c29000d001000d01c4050002d000110034a160303004252040710290303d54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 730831645 1250 730830395 730830413
    0xa092f0a0902091e1201092f010f0e0406031203020a170606070f290403021902030c1210020703020c0a0914011a07020a080c040f020309060114030703050601090506040e010207 77
    0x200c804c290751503646842d865940c00c820059584e10800c000d2007500d003a49481c000c2e4040c4501101044407080f1084402c2444000101280400681d20010b103114605400c442c02d204d80031829030807540d5500007002240d9040302c1c41c4250903142d200540d80e230031000301c01484c543d0301000f202c10121400d0248560740e03a400c0225845c541d04a079115803107004034101301e03801001c20f145901a0f41800c04d98900315040f10301a951003240240c096421440030080060000c1010440082d4140c1002041045515090456034600c2c2c0d24402100d04513080d1405040487c0c0c030001c0140c01507845840031503208e1030015004400390018100c00e2001c0214981c1c40800002e042c0150204020084246400030b01d0701026250010380052900030310380d80c0c07101c07141d481e4503020540600650410503a030303142012900849029403404401040d20ba0720b0b201c0801940131410741070b954907001d803002c0000800c10030000b0380d001c0d120f00c6000003502e00300301d006c0008a6010328030080c0507034010300c142e80128000c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 730832895 1250 730831645 730831669
    0x6010f110c01110f0d0e090702061b0f041e030b2a0307120213060f0c050304120f02062217100f06090903030b130905060a092f0a090209 60
    0x2003420b0000030180f1070720900745652580300e1460740c41468580942c455220385e555070300713400c25241809a5200c41400301d850b0041100d9056414100d0140e62098000003401440612502c9043d5401d040d22054600c05441d032410440e5640002d101e410300c1817012000a0f150801d00c00c1c1030402945d40b410321084841980c040c2c100d500041d0100009440501a070040404140c010804560360314034103118202c500128020140052000740d0f04800380c500450b0041900303a0001e0080d4101450845003600101082c0c4080380c5244107000118010b07200c88014200340c1004004015192410055880018509501800c1c0302c0c1c07203040c180c074402080402d0900d6841c411510205a000c0800c501d007001d0100343d88209e5003e450b10140b1024503a01d940000c1c01180d044807410041c1d5905000c10f13007903500e410005069900814003041d5200e110b94803041c4281c4c8a6140800004002207411120300204614030f0780d1903122110400d020300c1c0a52190001e01029801141000000340100f10000005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 730834145 1250 730832895 730832897
    0x506070219060203151c0c09020f2209020408070801050c280c080c030a12090b011e030f060606080901060e011e09062606040b0601051812030306010f110c01 69
    0x1c085840c52140da040281145c0000d0800c0f1408400c08050040e04407211809031842d40c1c0041002c5200352050003117500e4070300d10715043e07410100104a5000b8034010043c03018140d10a03807600240d40606400940014000d03400541034051500e0f94144c29100d0042c00704104080c200540401a03202803030150b035400c400883c80444110a05055480f1480c1c3c1c0b00c090500307100401e010350118400002800d08040c05e0b900c114000380e86240b14400d41e07048800003442c0c0040240140b0900012801059040c01e1800c0503c011303a03038a07240c83e455a2601c05086e22120f4940f207081c052250440307840780d04003560310000c201061509805422084042c040d2901c80c0e030303d030115086401c1d0748403800b002a00c07a01108006c1c281d651100c03580c4000321102c4210009007410910b00d0324440114810340710700d400c0b94030300303040765111001120290f00074240c06125010300500c42e02907445000c41440c817074240d43c0c0159602d062500024010001c5165040100495440c0c5401400340104a500b211007007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 730835395 1250 730834145 730834147
    0x15040c0902070602073503010b0d050c1608040609140f0609120f0d020d080705190522030605090f1b1212301f08100905060702190602 59
    0x168600f10010744241c0d038001e0031504912008466400501340e0302041070944282842c0040c2c00943e440100740024030890300661003d0082c0ea03144081c1e40c120b0759000d449070346114641418200004505860207100340c880080128040c4200d9400400c0040034051022800b000c8490050000d040101111902401200081006a10b5880b440c5480b8200c024040030307501445c200c00c1d0315555030040c08881c2c3e0014850f8040382c6642c6400788400328001d007241c2e96003030300e0948a0302114189140b007104c02020414104010038070040220f5940d04883c144c0b200d201c0b442450750400c3c00503500c001e018851150801c942200d540c00000896451402c103041c4000300d0075039000c000038007502041d0300b01c1d034541c0070716040320300307c0010b20b00140f0b8101e100040020003640580d00801d4003440c2503800704d03d1810580f0100d0180680034501400c1081c0c8441e40e842c2e0b442d11042468200201d2180003c40c2ca5111711201080003414400903a00807010f100070011001208500b220000d14004090400d0394 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 730836645 1250 730835395 730835407
    0x702010e040b0d06050609060d02060d151a0c1b01020a030813020604060804060c091a07050109050d1817070e040c0b1602040e061513060503120c15040c0902 69
    0x7202e4001604001c0003c04001c21500a8108803000e45011902c0c0d51151003400d00185980c03a110498990640d0050002800d12410314000b4000b0300366401c2c1c0101c8030042c014001400c01540d0302e01000c2c1100054240d0f19511882502407402003941c02024950030088504105a6170010784400c0a540520740540030b916a00264000e080c01d041010303400080024010070900d4201c2c0103c1d010714401d00b0100410429584210342c40c501ca03014640b20340c0b540030f03d0900070600d0b000141803190700800c0005610032256540741e10b001121446140030407601d6511042204114460100501a05280641c0c06120154060b2104614050b01030010107040224040c0103545041c04050040b11140640d10034007003c40c160b800c2e040d601d040340308070f0826028440864000c690031b40600342c0d69041c0c05e41000d4130703000c000000b1150a40000710070755580f000119550104118205901060503203035407170f03141c092400e007000301107108841250000380c144000034036981011004c80710b6100c001070300c8030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 730837895 1250 730836645 730836649
    0x607120b0d0f0c09050c160501020c1507120207080a0809070b0d050402040e0a02030c1003090c0e0708161e0e060a030501090f060b090d14160e06090402060702010e 72
    0x1010180c803500540041480c0c82040303a80d00341000306a00074020001110340d200c1e0040c041d140c0c02c0b28407100321039060001c013045c08820210b6000d0303144500009403c0840385800645000312800240c1c0807001d1100900c800e850b0080501c0751034880180b419071401d400740d154040c01f40305075240c00080202100003d40300090a21250014052000e08981e0f14201240030001815054030268071540c0340c600000040f03500001d00210503039025026054045440081040b840c3c070fa052502c00f45500c42d54400000b81e91340150101038080100300c143e0a042030000148104c60040407440c0c0002e050686668064000c0a104a038911000782c03000e440141510485156a0020710f85400c41c0011944080381d58054104606032180001c1c01c00181e40144100c8003a03e50504c1b5511910700104581a018208450b5840e2540c0c061059031450001c21a60181780034001d1009400094010005200320010015405d4001c44100c8018100c2c0c1480c1d00050005d114050b0001d0502031703e03c1d0443e4240e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 730839145 1250 730837895 730837901
    0xc030b0402060f0703052a3403080c0606060702180a0204090509011d0d05070f02030f0f0d020607020d0f0804060f05070203090a090204030c030b0705090405040c0303110f060712 78
    0x880d03640d080f0580c07144101c2c50090141d03003107081c0700035000103907030400c0d69035000e03404401c2154041140101044510101702c2c6000c018148121400b4854905080c4140c20245d5511002140f040561598602c034000015003091001340c12184100d00030000d103405a85c0b080881400511072100180180d12180c03403070002071145500403401107051400304105a08198011545140095441601004158211900d86003440c4064000c544140b040f0004034200303070240e000d00b0744060700700d680102d01309032050301e804103640028019a100c1c521040e0141d80c1880074940081d061700003000002c07140900540715085001b442d40800c280c4030000380520a80341c000e00400f02c2c06000400182c205010001e4417a445070722070078081c07000e641d800580c00c007035071080718201d1b90444281c3c20303a54210b42d40c40303a000402030144410014248411541e0340d070f844c8607441c0240d21824801c6403061a529016200d10001c01c3c0040c3d03203802210821541c00404102036510044e10302e0030024100764100a4001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 730840395 1250 730839145 730839157
    0x1b010e04020c060f180d1d01080708010b0c0a020d05030a09090b090c0901200309190f03020d0312020301140a05100c02060c0a150203010603060803040317130909110a05010302070c030b040206 84
    0x1984100980b140301603801441a0740247c05e181c03855101024a4401500d10100503161900010322400040001040e54000b804146952200b0364905603800c1e0000740b01d020300e084c0203a50607040090704204440e085005000140990b03070013485281d440f80c0014580e040e0090880586030300009901500b60702c51886951603208503540c121500c149000760960300d030890610f4901a03c0106203030401c4980791101003080b130b0502d4002181550661f800d20580e0004c18104605001c0002e07100d2602405600195010b09059807080c00da1050750020000e01a909078049401060320040b1010a560b01010b500102501921260b0703032410203024092a20000b0140501203140410748000c683c149600103504030394856800b4064103855203850368403032040b44001404003401d00c030340b0480e0550341d80240810701200001c041c882c41d03840f140300302614200c10044030079100c0b0388160382083c50810b601030042c0000380317000c40c1008103550761003218585502010f0702e0340c41c1c103400080c219600d54080f00c2c0c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 730841645 1250 730840395 730840441
    0x9040507020706030b2b0503120906040606060e0303070f050f120d05060a05061c020409091a07021911060d0905070320010c03030203060f031b010e04020c060f 70
    0x2226103000d08000307465040354001e510000c2d0601c10441d0451411180451080b99189211002141c0c80c03880450b8600c149071084415000c00e1040401020702400308a115503540c0016040614082c078000003100c0c0b49800540034404201406c10b0551400803e40d02e455a0000b4019641419800c0143c170388001c09400031524464107000c4a807499408025084140e044003042c030176501c5080801000c1d0b80540a03080c0c0000e0300740520030342036843c4402c150140c441d1800061038640c4408110301039440c0c810044d100c1070990080403204040c060742c042e51001007440602075160100d480d80f44c0001c4030030001780c00e240c80c0e401c6041a542d00c000480d81e095408000401c203801962500d5a2100c1c0d1600c400e846000c0c4450b03840781070700c01489000b908050141c0d0307003454540d481c0e0f400781d00a4101a105980154203002011096181088202d061400e00b074150b40804800e40e0004146404013025980100d0040c850418411000200f50740c2040d0341e1002c1c0b128aa40c2c1c90f1300c0e2151400d0400c0302038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 730842895 1250 730841645 730841651
    0xe01080325061d010218100c0f0606030b04030804050f0d08010911120f01030c120809120a0203070b18060f090d0203100204120c05030f07060809070305010f0c03150b1e0904 76
    0x8a10148151700030b000e42d06540c5000e000600c051300412040c001410106c10200b64030311241000188080070340401980b00364070010f015612074813601070041c07040b2800c8010400f0340c030601c402e020040000c00c42202c008001440740300000d0000814000d010301c106602f01e80c60b0802d01003010070900685454007043c1d4881c0d1850b1811211400c1c0c1c0d0ba4007840180c42c00b885031341c4003081002800025040c01030304049040c2c0381c9201a01401890505518031030500e0148031400d10050b902130240c00001c2c02c10110f409d4594904101c0d07003d24405555003548502d20070490041e99400720816201c1c8400c003210200103000107400400d007040c0d60b07081030a4042e8400540451032000d8800303650105805003540e030308480d458800b855a294603021502945521025040010710f02c240e084603030284000c01590406541c9a4480f420360710304000050415445003004890186d241c4500c21081554900000419240852a041501c05e40700803190f0f2000031500d685420404400b150030454002c3c10070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 730844145 1250 730842895 730842941
    0x30a09150c1e17180105150118050901090e1509070e06010e090412050f0d0b0f0307060f1416060504050105070e15090d060203010f0e0108032506 64
    0x100c006103628588940400e001d40031405840015100110ba9466181c0f69405000380302c00c05220628802000c298040075040c8030040d54100a0040790300401001d15406032404a54002414000000c507940c0205008410100001c3c3c1c0d8103519281143c0c1c9002000500200842010342400c440903240b4102d81524014072805020005410701112160114040d061722240011154441c0d03c000c03a03a80b0082d980b0100d00410b03e40c21184606807102d0400c98a00017032103003d10b0b0755400601601c003203540c2e90100b15034542031900d01c4260743c40d030440151880c50305100000d8401148000319000b0040d2454002803010310307007001c0b14900109036076201181c1c10071349040000b504c3e0845086810394204804201d038503000720303000402c4860060060003220400e140e02c0c1000d0708580c20031076220301108000d50200351284011400707081403c1881c8280c1e400c1c01d1035280113a4040e88203ca0350340c0108440c80c100c20303031004201d600090042401d4030441041c10b085008d00304100070300c00456810904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 730845395 1250 730844145 730844183
    0x1509150309010e12030106120e0d0507050c1503040b07020c0d0c06030b011e050f1e0301030519030915050d05190e03040f050d020117040302010903031407090308030a09 74
    0x366104001000007408800701c800d000d00d07200c06142194800141d0107100500c0746501482c0700300c040e403d82201c005442038101c00180d18024147c0600b20104000040e0320b000d000301030000590446064681440014100c6070107045844020b00150050f270704000412221407081c001e05000010007030600c40125150700304401100041c0c880e100100386002240c200075400350b03010001406059040c1c84c840100c45600707a980e81d100c041d0180901004201c40c070220224940c0a402403002c020350300e40c40390304504d042d62804840180140701040e4074400440083d92140181042c2c07802d140c0c0d5501c034030170601016034031800f49111510b40941003100300205075195022118028180980c01d010f5000d181000326284d116500440c20200d00c215414091414140d030704a03d0a171041c507020b503040e4009014070103400c4d400e0380c040700141d460751120300a259150240743c1c02c034100f409c5900c046080000300941a80c0b814840249020030210005035141181d038010008203421103640714003c0c4038805 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 730846645 1250 730845395 730845397
    0xa1d070504051008011b170f0106050309070e090f0c0604142205070305040203010c05120a0e0a02061305030706030b061204080c03280305010b0307030b40020a020309150915 76
    0x142000681f09950074400103191100030781c0500030080382011107908000003110b1a0380001e00c124400e00c600c0070005822803072103806e94030603209800070f08034a5035003030300e0142007603201344000784188400c0c0002c4c060440c010314000298a400c548480003032403081840d150041425515045c42440c081c00c0101694254000c1840f40c1d200714020004200000c009595500801646152100f5414001190088150f200100d143c403d08115000718207290700041c2c8136403020b24003000703206107500c04120606040219a01134501c40c02c017845481041008198180208101e02d034402d540c490100f801c0c4100c200894400658035010b51341d4818404200e181038030a0074550f03580200390b1096900845110384a941d0503a07502d1a1450b2454a03013601c02c602811084016036448112a803501c4000528040c21060030040b189144090401111004d00c44e2643d40d10240d4115004000b2640d4281d070100495251041c11902030203801c03100d450101307850091044041d0010744c030b0f03099200c80b446400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 730847895 1250 730846645 730846691
    0x140a030b090f0a0b0603011211121204030b1317130302150a11030702181018060e16020319050c0a050102040302030f0a03020606010509061c02030a1d07050405100801 73
    0x2143c140146200e89052049520003440303072100142c1481d40010000c0c1c03010000c880d510700010300e4100201d014007030030f500741030004807c03004200b00083c04104201046496580c0044c0400c0d9100111300c09459074900300c40088055102200c0c0065103000c4411a480250081d54010b041094640500c071180d02c00c551108041d100829605d5121300e40c8904004119030200c0d502a01400c0611130705d640e401c84c1d140025204071142102c0700c07030101e202840e0960403441490f002601151003442c0ca0100303144910040c080109081540006000e00c940000c1120504400090449001d41d2110401c880034000c11380c0a003003c0c0284807d0304140041500544103480c001c4042d01e2148401da051130b0360359909490010301603000301001a6966000e88094420580c0207400c592401d28074803503582c02c1500303600350050895804024071008203094803c201c0d071080d41c1e49010320484200070341c0359500c04207403144920031341e101d000082c0e0000074586030000500b01a4000e0204d05d40e554008104030582c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 730849145 1250 730847895 730847911
    0x141c021609051509070909020a0804021507050a080c0c060d14010b04082d1501140409050606040c020304080a15050f041a310606060e01140a030b090f 66
    0x680001c034921200d0321034140500740744842e0201d002d00c1e40e814440d51000c010594800c1c4541441c00040c4110b0314002000081c1840c8e40311021403a00d40704100d601500d080703c90821240c14850500082d0001401c0814030342c020000d661285c1841461901c0e0030345020b4000c2e040540400ca01d50107403015042141d40003e901c04c41c2107241c0e20340340c40d04035a00a5210f0900340d42c2c480c070308064a02482e040c144c0ca02d90308041d4034083c9099a250414a40b011036512603200070300c041c00411a40190100384201130f442100c0030300052342d140d11070903a81d01010309002c1c4900c0da20365021078100d00030070072540102110400c1c0d40c440c401c581810010304e1030000000d000c40341030000003001e0751003c0501303600c504c0d032104004005502400288a0200004202a046405002c0004203014000d840e4280702c10411095106480c0c26192070026294254058405e12803000190303001c50707800140307801c000c82c0f5905086032901c01c0d9540440c060062032150680101140d01840040039032440240d12404030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 730850395 1250 730849145 730849183
    0x10b19090612051902030106050a0308030709060302090109050910080f150a021c0b1201060807090b0301050106230d02032e05100c05010b130b101704141c02 69
    0x1440966101448900d900100f841c0c0081c14141402e42c1c40b0420490b0300c42c00540001000340c0c41c4d01c0411300c840340ca9001600c0c055004020402c21960006002c0b01600c4180780075420028141e0028100300d903d4040c003482148540c1c0010001042c0e089000010200241100d0050304020011600c40c2482c035003402041e041400000c10108c0b880c0200c9011803880403c004041e213000712040014a0004e001c9940920001403500007602d00340030707403c040c10b105009032041502e1b00030745030211648080e0716801383e410a00104500e540000074044901707200351005134200b04004801c4a2445503a06150210b440882444000b0a4181c0c0059500384250a41d1040c0e05030b204100b4030742e50091084130340c400b0555001484040c45684101d102911510010030b24500100015814010600714510850340d41d101c445120f10b8030025040301001d580c20000c1c912840b641d41207071000c10040c005072500540b510b140b4080c1004011440842e028510040e0303041801210094035111420a0a001402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 730851645 1250 730850395 730850399
    0x30807050307080411060915040f0f0f03080304170403030e09090f0d050a0917280521040e040b04020a092901030912090312030b0603070e03010b190906 67
    0x1024904803402442d558984041c20b070350310759605031041c0c0c8a420312508040c0c1881a04e038180c59100c030001000708400e81c1962074505011140d04611020741c080074401d000403400702711b1010602d81f00800c1d89d0700400d4050750381c0d80d541415250401c6202070100801d0001400100303055201c80d904242880840d0422151784515108558841031f540c2d281d8125080b10030400300d094096070007403d00d4801414440b01c80380e030b00e0000c211181081909603420340c01408145100620544100c000704d540c07007a0042c03c610040e112141e407944e40101030b1070102184240e600352190310780e055900524003070705616290301e07061030800640c0200f5241240140c88482c0b01007031310045030180d007038040d4020500c0107000da004120405041e00c0c000405061681d9404104041064800c0410401c50306071034540c5c03441d1441c602940c04c0090349813078004041c98807603618026a240400c80c1d400c0001d6252990407000010002801401c0307002a0940c020754181418803200102410501140d00c400e100b08607450f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 730852895 1250 730851645 730851647
    0x130e0118050732010e19080f010606030e0a060c0509040e0d080c091e120708030a0905010228020a05130b030724080a060806040f0b100b1b010e0316030807 68
    0x2808010340e21025074483c0018482c00e51062541c0034151000808880318180707402d2401034641d80c6604981180c1d0408040781c8164070003405810b00801c80d92908102c840c4003444101d48822594500801c880d032520000c002451003441541c1c01100d004004102c000d200402150b40d8000c003c01a0010810f050001800318030780d00d05031205810058a0700c0d0241041c103180311100182411100e41c04041c06a05000125081100001802021005603550a1b012401a00c0031b141c540c445811540031070b214035501d2641d2001140e283c0e4248100c04131942c060b00c001030030706120390010740d0001204042c5000d656016003281d074070600280c081d0781c50310351142d0400c007104583c1803c2852011084511150241c130644105070311400d02c104c000b4410ba2500002400e00c9002d540581d840e1047c140120148440443c465405c0780c1e481c60b4001846241000e118a14025003180790300c800201801403225680070f403c6440980460360136a6030740d9142102407500b000803000180c1c0010707213100000d400c2d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 730854145 1250 730852895 730852949
    0x807060309050d140f0d020706060801060503060a150b1b010f060501090e04020604032a060c030f020102090310180b01091a09090c060d0b090906070815130e01180507 73
    0x300b2040c01107140202c44030503503099500c80d1b2a140c1e5120350810100c4085541031050001400203a800810000d00c1c00e810075103401005422241e040340303052011800c3c80d01d02d082d80d00449031780074015620b4249090310382e007801e10191134421055003042519a0946041d501c03074015100d09886012079030b0344421041900d003800302c0d40203410240c10801840400e42502059400410400d000c070781004a0040056480241d81c0c07084010502e540280c00c105900000e01504070b40b0329100031030501c00c40c0000030741d40313802c2c420101d58043c2d82c5201d41145c681401040c0740000b50400d0f04c0505a5a503161480024409090f80030042c1d001d81004807620324200c0d0f841801004484010013490030001d007041019881144a140060307903a242c040002c0d101c40a0262145800b01c02a01c002d24060300b015003855002000c41c000c010381101d01c0462070341d0b0413090040e1031000c1280004c800d85e006034101d0040400440110180e40348602040c2048000a911807c0d0380490805001c0b000380c1c60340205034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 730855395 1250 730854145 730854167
    0x60307080d090302060d0b0a060e0439180e1503030910032403030e030d02160308030c090a0f080f15060d0203120f070201030501080a0203030f0c070807060309050d 72
    0x209142e004002518004001d03040c1100c19200001e5500c0907000041c1407146c0543c06000410f066801004484c1b5262082120f17070360303054101031040031002440082100d8503001c4034128a0359003039180c108610500382c0c050640a1641442c0f80d95490710120081c5860856402210116075158a08503090200a4414401020304000321040c42d600302507001d0485219155985400f8103620b21130750f0340c2c50030b240004600035143d054a140710482450b04100741c4048107020f40d80904803044031b800018a1000c11030390030600c11600c9032116500200148504041190b010705201804102040994680c0f0112a800811035000380303072010742c5548a006a088030060080306000090541c205400126040c61005040d42c59881421100319010b81214161004004000c0b810780b0031540c0511845000d400d010300103200d120a1980080d980344902d0804581842020800c03580000b002c2242c54040e09004040d00c00307050b10f40800178010441e00c0410b6809205024410700194054549920 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 730856645 1250 730855395 730855397
    0xe030f0a02191a0c030f030112061d06011205070f060203042c0402101101090602030a0b0402030c0723061e0703050601021b0a030b0907030317090a060b0a0305010212060307080d 78
    0x250086044424607640c0c100403994506030001b0464160030210010042d806020b0700c3c02c0d40c0064903d981041400c039004041c0348100c2d101400700c00c0146c020b0000701e250449408051085020b44180340080c00c0003000e504c078001500d60840042000c0e07402101030000c3c0c40100403442c060203200103262075120003000d880f0155605220201d00541424940b662500c4120f04000d01220000000c19003101c443c10000c0c0c03100bd40c04000d000032049107000d000c50b6807100701c40075811418003401c00280c2c2d2180b07140007400c08040c500300100c1c4588286242c0003200243c42541d425140405261354101080c0d58006404050b00002601990207445484c3c010403040e8002c080d40501c49940e09404100c0e000300d540d00011201d0000006517040c1000c6108034145400f90010a00e5032501030141c81004071141202c1182c00704100000c00700143c10f10b10107402820125004d584d5501003039030b40307503541c001034215400000c0d5403000700703c01e2058602420090b0111144296100146600c4901c14a820343c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 730857895 1250 730856645 730856669
    0x10052701031e0b09070302100e0a260f0313060906020303070c030203040b040611011a061206040b100e030715141e040e16170c0a0e030f0a0219 63
    0x400810080341241040030200650741e041c640007900c1d942c3c0c00c00e800b1154011280d0010ba401d004505025000300710542e01810040c984041c010002410103c0798022101c00c003020380c04010661103518040e2560b44c903000195400311b021140d2441c0c40c0d6004009030344c80101d288100140c00c40c894103500e002c44d1003e501071401c44e2035000084841d91032409080c0c04612050202003000d502c603d009000070303c1d140e06c5444c0d103940300082e034074250340700356140bc6a28003010248036080c5d1501d0007200d4050071401c0281006580b208006001800000480e41e0490060807900310202e4000c4948000c24008500f11110300da13072040c444c0e19184001040c8400100300d81040c8004510000c040c003410f100c481d41d6800f281004c00c007080c50a421550040c1004d164110500c03031661162041c05081303c50a180007400b02e030700382e0711092851102030031001c4002e0740090450000c5109003c01c80c03090100a0030b0f5401c41955000b01ca540c0e1103001000d070311a803005d200030b0768211241607155040300d20760b440ca0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 730859145 1250 730857895 730857899
    0xb21060d080a0c020d051e0f030412020111071a04081c020d050d0e03070602040f0915060e0f1203030a181a091f021206030a03090302130f0510052701 66
    0x11210380101c20f400305d0300070452082017000030300f003070140380f40348440c1c0d20320309440e030040b0180c01e03182102200c5c0c1e00c074030381e00100b1041c0500015404000c15103038080c02d0500515000c448414a000f03586e510440c802043d48141c14007405071039008004903221081195050901c01107440340d502505000007015178803214000c44403d0207140a06829103205400080c82049005070b5415903101c403604407000c0d580041c09110034980c0f00007100c0070f031031104020040c031506d600d064a81083c00740070341000e009562802804582c0c52006807200102c010307140000c18110320707010b5681c1e508140d45400720301b41014006c0d11248031600e00103184640143c030030541481442e10a00c02030b030010300f03001c00a000350300344041c41c440180c48658410f000b100c0c0c0180d448030002e17503100350a00098881c0381309030001002440469803140da0401941c1e01200c0640f00380817440342c810700030408400d104d04a1800c11081110038120f1740c11000c101d400070f03500d1a401e60514021010b15100c4001540d542103188401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 730860395 1250 730859145 730859147
    0x1602010c0905090c040305060c0a0201050115050307030f0f0e0d12020a0507021314070504090b090c1206121902150c0723130e0d0f090e0405070b21060d080a 69
    0x5104d070020580b101c01d528080d12504c800c0d0814000301d4190058100008101000f241d0920903140141010010761038152481d80004040d84005460401055142c0d03141400e0103500c0e6210002502016104009449400500d10f44a0444100f00c030049490703506503803503000c118001c0b545c030340c200b40d40c54500e00105c5508110a510386510311200c03042c0d0390407031000300c2507100042900801058951a444504d8002c0e8801540d228100860040015005010f801d0501905a070784c5440384070250441c960f1110042005904d001000e40b41383d1203000b504070401e1348081e4180301030074000d4650804000303900c644da540c0d62181a901981943c407025003040050343d409400010b020b0310003040100c18520b040040d40c030111280121414556a61903402210002c105100344003031141482c150740c601002c00070700f09018501c517942010341c0080003d0708001c003e10401000c3c060300304060b5224202140c00790064000f8081c102d003960010340c0441e0051801042240015034000c44a038540a85484 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 730861645 1250 730860395 730860409
    0x30c020d11010f021201090f09170a140316080117030f0a03020909010e060f040509190f020604090e0f0102070503030424050c03061809120f19081602010c0905 70
    0x90000001d550320700c1c05440d10b80f083d0000340501005c00c0c600301150350400e001001220b803140040340d0b40c10728151504000448004140c0b015218402420b51074400312042030780c94054840c1c9903070090500004008081c0400d01099001b980701d40e41e00c1d250f40c0e03203480240480300318580300716410380e02c284460005031229200803c49a21645805410b00660201140500c8400c0e000300014442d104204001402c1000703028100a40c125002d02c46818400503080c3c4500014900325181c00c603c10302081400500c001d40d641c415801b80c655036a0355a51302c04e801c01032200301c005140c0d5000b02242d03145124014000c0d00c200306d0700031001e90724641b6142c0d11400740ca0319001d000001441d2509040300405054890103224203070f60b078000c5a592429000700545151001e41d81c680c00c1c1c820360284060130a0008405691503c216089075075014111600c50060088070000480c000320a038403003008aa21081e864054044e042115080300d82070748040c0c1c20380709548044000540024020005450b2a00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 730862895 1250 730861645 730861667
    0x150803030a1508030c07170a0314160213060e070c0c18061706010602010b0d15020706150311010e06270f0402070c0f050d0305070318051c12030c020d 66
    0x101010001962641c50328110b07081039251510346c0d0002c010070444500303040c002c2605040000c2c00703818036001c03940d80984140c000d5035401d007001c040410301c004501c1d4880c02e24140030344c005011002895048a0000281080340540303030204510b440400e081c540204424403c169210701402401420803450b407450508900c48501503030f8950400040f601c014a51030702440006102400031503040c43c3e406070a44002c8203590b400b40001c001403401151441d44038410200341c01c0c00c05a59072403181090301c0070b0150f0005000300c04c0041d4100204000b01034280c035224540a0320345454240aa230b00308803e034010045a4004460035441441c42060130507140015104028a0210088400ca01103801c0780c00c00507040b20303141c107000c0b4103114008030441400010001101c4034840c0c040d659500820a000740c0d41d005061121624195110001c1450800b015100280c00c1070495141001d02802a180201c3c0944d20854801140d10a40b0300c64007a100c200082600200801c24034041c0841d2135440752 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 730864145 1250 730862895 730862921
    0x8040b060109050901030b07090501051c150b1b06160e01081e010b090406050a030c05131b121b1b0204090b0c03071403042607060915150803030a 64
    0x340b4040349503501c0c0c05240d80070794010300c00c018192a00410240c003070714240d00305a040c80428080000b01c1d40c07001089900d20b04001e03801140c6030340740189020566001c0d4002c603030fa40c04003080703500c1d210400c00e0003003e684540c101260469100c03030300d44404605104888000251210000c00c10030350040034007541180703082d80b60410b014010321101e0380c492000c0e081550781502c0080e41b081145410300554000e01022641e01c3c0076580f42d0758078062038145910405000b02028030390b181d401c4c2d00d1580704414047c1034882000c5800342044005210440d41c08259884c1450000081c00e041c046000d0b03505000b101e501c81c4038045800c003001c03ca0540080300200da1207a20b0751500d40006168150701801118020451a00c90811842c041c100c0c0400e410703031140d80742052081001050b115170134600b0424031085c00c4d400c80b202e94018a12184030380708000c0d1019040504035410440c0540982860200c0c02004110340c00c140b80c03600d9440c2000f4030803000254402d1005c58000c201a0b0321024841e412 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 730865395 1250 730864145 730864157
    0x21020418091e030302031503120d0b150c01050601080114030606060915160317040503040527040c090b060f180102010b100915090803030403120e01140a0e060708040b0601 75
    0x30100d0201240b05400c079003200040d4001c01803141542d20b116030401070780d07021006800e1070311406c49090000e0240c1810044a07a0301c81c48140d0322502c40c25078030991a00703500380c179964030150f8006071030107440c050380d5081c00964004000519054090018080520010007a0007141c55500401c00346820030b101040e40141c40f810001d00022800006080c0d00e1040d803c0b404140e41c01e8140508609d000d440350300c007008103d0041200040d07002c800c403410f645040714601901d440b10840040302548841103540d05522820602c01405406d85c5041e08079442e6030003d009000b5484244080350154008070b80340c01c10240407003c01082142e214038180e07481031000280c00340c00e0800040c0141e07020021040401c1c8811428040c0464469128440803083e0038204106864200020390701c5c40300810240812214400b849031100381030300401040d01c2104000c2c002003040029050600301305481440303c0301d24240103416180c0012a255104000c40c0e1a07803040c81d519503d43c5080f46d40024072403410800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 730866645 1250 730865395 730865423
    0xa1b03150b04290903030712020a080403140105010501030b010e0d08090324060d11100207090c0f110604030e0904061404030512060906060301120809102102041809 72
    0x11000d0180000340700039031002c42d8003001510000102262101200f04004003000140b5983c0c07000400c0b07825542e400816041d030141030203070886c14601264402080300d00b000a002003801003920405070052960f03802040740d640d0b101c1c015021181d1001c11203011400d46641a241b45c50031a4501f03151500480e07000c1e25240e0088002404c2c200e144090b410490f94400d612422010050380b0103a2100051b14004405401c0f0b4a9221b240c84e0201d403210310548144d030b00301000501c2408031034014520124180104040c44c140600840340c005070313503000103d80103640005100001a694055a01a200e1103e01d41c1a2030070700001c01c000034400e07030f035454032081414045050480c001d8440c80c0a0307500c4a8407244825840c1c0c100c03407009003009104028000a0090580d9114104c03411500e001030881c5801c2a01e182c480c0550203035010312688404810000900c00f60029001c2d0161107440d150f02d003200d88440541c0d4200d02440c001c042d8010603a0412150071038140d404280c51600404d003101c0f44e10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 730867895 1250 730866645 730866659
    0x106320d180f03090b0c1b120f0705100c2d080a0815030c030d0f0c05120405040e0f0601090207030c02091e01120b0406090c080a03020f060a1b0315 65
    0x90300c0800b2103070010000c16400c1410b5002511501a12403160400e281404d04540141e07200300340710078102c400307401948500301641c0d0040d02d61319008070b12003662030707401410351541d44566251140350302415203203030a01c1d159071244210340c180c0da0344940848050140c040518020a14141400c0c0e001c070a000104000700ea000300c0070b01086400b594801943e8130305035603c0e00043d500c003001240030390b010180b40d01e040e640c00300780c44015852a01c0c0010032000d60400884600151860113042801b40b0140d00c0c845042010046c01a20f0b803c0d1014000340c2024078456a49441c2100300342c01e150011001403040400980013440154060b00d08020040d01540006188010507181c01096000300603040404804000401d8018005406c0b48074800340360340c4505410010040005000342e544002110402070701c0200080034240c0c80080ba5150b51092401070350b41d615500313101e001e9101d0400056148100c500070a02e0003d4074000c0f00c1c0c01c14104600c1075015080380110112661b08248000c1014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 730869145 1250 730867895 730867931
    0x30a022407050f0705191404110d1a120706080f0a1506050910090f0303080a0f050403020d020606031606031a060a0903060b10050f030403020a060f02030106320d 71
    0x1d180f00900666031800d8100706490100350307142188903201c10401c001403035000401044240081c1c40c040b03030400d188070301c011251050140d070805051410380b110081001c0301c200141c0040c42501c0c448416524251a203903107640d03a02c200c8002884030710014190900b80340c1900d0f0803403056040440c04004c0f03c220700b190840d11390030420000c1c0c1e02207032192091500f0310010704c0034000340c2011100715040c500c5020003543e96000290502031a8004130301c2c0206254804070320b41c8004401080103003014540251200c0741c3c0b40150006120300004200a0728000c20080e041350b2404020803802d42ca012010750290032241c4820002c0812101c07021010345032074000340044825541c3e4440018118940081240c040034030480c0a07030061604015280d4008085440810030503403002e44a50321031800b00c0c03405020900040c0400d090070030240d851041a005103050311607903101c071015600c01222140040b9401e40200140110302150005d8150320b000c003e1072000000d0b000420742c1e040c0a1250004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 730870395 1250 730869145 730869163
    0x204020d0c020c040603050c01030902010210062d050d0b0a0e1605030f0309090a02070c1203170115020a030f030e0f06040b0105010809070302060a2106080c030a02240705 75
    0x1000d40c891104410075035042c4001c41100500b29002c01905003141c60b09560790f00d108081906141e40c9640c06004d681c001c0003102038510404e9000e0281580369840601da4102c540800201080c03008a01c00c00d414504840105441010f020612242b4864a50307581103503000c0c08400c81c080e501c20310342602000c01e01c51075038040340e2000400f0f6803600e4041494600f4140f2210b101180e0401d01048199a03540480c0b150400705002c0b0140c1c4078803041c10074020300d00d0554054804050100c418108040e0407103c141503c02100742403510680c3da0b1210603002102c00e40a80006800c08808480021300810201a041205190004c2d5581d1502e64880c684441e00358510030641c8400204820000f40c95489405440b080c03070007240d542007083e03506039130381c405000080c030641001c515890440d04c81c113030310000e071807030050005405034404440200030901e500079009207004076649841103041c006466156194080c000002220300f04000780110741041280c0380301c07101c0c100182c8020070010490090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 730871645 1250 730870395 730870417
    0x90206220e07090501090509060307151d040207111915110712020306130516030f02010206150607080f0d05041505090a12050a2f01050a05010b03070f0507020402 71
    0x10650742464850080724000614503420400d800d1010b01c040c0e44c2c0000c0e421300b140c400703441a45840e1511800030307003004d8041d007000c04240580c424141d41540e000030401e440c112021140b85942900c44180402c0c2d1203907587c080d1107049040c10341c802d00c1c1040384d1640074542402449206458940b0b90900c1160804902c440005000f030b5000a40e00741c09002d400000e1980500d189c0106103580c3c00f090303c0d08401022041c0750f10f0201c03400c0c41800300901a40c4141c44101a80c010255203900d0050502c0c440d600301a4018451100010100300300044800d24401004200303d08140310355680c400c2503440395910b141191810b210510684416000e0180540d1040a01c030b448901c102581400310f460040804080380d001c0076200000c80e200c02d401e2504000241707000740d0b8a1aa1000558641e40031442e41010031403034402ca8080000d81d45104503410b100c00000b0b02903034507102900420b8620a010300d001d05031003000802e8408d802001d9041441a160130510300301000c2d90001400c070b82013000090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 730872895 1250 730871645 730871707
    0xf040e030406030608070e060118030f0b0117012c03120f04020310050c07020112090b010602010c030c0507110613170d09060f0e0f1513090501050604060c0303090206 73
    0x200140d030f098010b0b40050403800e401001600c0c903080b043c3c110745002605290606c219480740e400c240403c2140c1901841c1c01110001d04042d003032030880f180c520300b4852410180c1112042d03249400060045c1100101003091810613900f440d060b000400c4040c2e1040e003024032080040090207101091842d12480104450602c20314040c0107043c2000c0342542c00345800c5140c00c003003000300c002403419a0302664081c13801c0e449400c070714110700b401001c0d2100e005e0300c44810b50000140a50f8150054640710041b03a40c2440141040d403c02e48060240c1c203001030140c1e42c2c034020803090b410414081c118402c40209207440c4103036955a204480b4408000d00d9526400407080d80c29029008184400180f00e580b0b40310381003c00300702009110240380325400388540307100503001e01c2940d0780d56221003d810700348bc003107170340c80c1d51044a29444828a1050300034081c2003100002d008d240c40b1069900f00c80080c0c503a0707510b885407550b04a000f40584001240d002e03a0510001240e001e06000a058880c030120f010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 730874145 1250 730872895 730872899
    0x606270a0e0a1505010206070c06090f060504060e071706010512010b0603090106080c27090123040606080a0b0c0307020712030302070303052206050a02120906180a200f040e0304 78
    0x142c500f040058000358190350040044c40304185d803000c40302d00d00c6500050700198000540ca81500c050075200c1d0040e00080c142410310051016540c081500c010000c0100c031074050303588082900c101d8443c002643c0542041004009605080c4455184011000000103c041d8400001802900282e8071300c6c41580d52104284038202d07003000102d514550403900041d158402e051a000301c2407410b48a114450022008180c096200f5080b004442c156060101c40c01c0010340c48000c0ea80b20101c0e016075241d230400703400044c441c0001c00d00c1198540c0200d83c84981d40d48480d400100c2e0361020307020744118411800006081d590004000c10310601c6660007580da981c41d42402000e99201822140024480c040403a1008100100c5000220f42c0000c000c10981d646540c030100038007845034490901480c04003003041300c1d000400c0c138602c941c1040226100d45c2c03001d411060f69407d04113500601e030ba400d958051100095005024025080043c4a0451011132001090646840d51401c40c200d41c400301e81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 730875395 1250 730874145 730874171
    0x2120705120730030c050109021017010e01120b071e050703230412030e0a030c1502030708270307171902090f060105040e1009050606270a0e0a 63
    0x2c06000f0540351000400e0741203142c624410034803212001010710180303204030310402801790031580c4e58640080c141080d00282c040d001e00200c0c83d0380c041d080c2241c20240007047c4000c0005195050346c0e000031124541c1c0f0182c0e56440390034a000340104052002d1a42c40d060010b803204090444d4031000e40d10f003a140c0185180192001c1d1071007083c00c00364404c4c10711001101c154402030340c04548040c2c014002c6d40d103880c1015103041320440066034026a020a02109100c500c030804002c0b600b1b401e540a40d101000c210072601c82c003c4200c002c10814042200351003c21540e00729210291140d41c00201084045d0002482d22441c1d03480485400719101ca0242c4401041c0080201c030608803c540e00c060782240d00145aa19000b00b034202a070f0000d8001c18180c0e4441c00c1950040d00342c0381c0c07001c121400e001c81e503210f404250b0f01c0350495103400d010000e00030342000c0d8140c0340ac486035554181e101d050782ca1030243e9800c0d0301100460b0007011280f03000442020868007240100ba000302d00051004590716 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 730876645 1250 730875395 730875419
    0x106031a0913060f1e0b01020f070303170c0903160f060c03051b070f0801050412050906030f280509060703061a030a1503050607110105060607021207051207 69
    0x40c00521819807041001000c0031402e140c0140319601030000a0000b1050007000c1c002c00034100b2001c8408940c01000c090741e61036034410312100800340c089520b40c405900403180d9403002c60200400281d0900c050b1003208602d41d000396003140140782018207019250303000ca880c1c000c01600c01055680002010402d00c0030f0b07400440e000d41018075016010070800d446c05071242c070030402500d0b42011303800800d6203001c4003407044a02030444031303c620070703681d40d0344010385e01a080c16130f0183d802131100700692245600902c2200e41d0b0b41b4028060314250f5854456201d00e01c5070040826240e080540503104503c16003000d03050780200c05100c0000d55042c4100c1643ca40030005000c90300303040c5810028060340302c0010000d800c0a498401c0d85544e84d8035103880101614104000d08801a00b089012081103c0411500d10940090392120740302c0008101c1c1d10300f40d403400d481079074000c2000c11101002d418080d00c1007600302c0034001101c444a40d40d0002c5020040c2c000b07100f0076550030051040c020b09034615 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 730877895 1250 730876645 730876691
    0x70b040b090d020307080d0b0a060903031e2c1302070606123815040c17070309031103030106080108190b070f17070906030b0901030f020603061206010603 68
    0x64000c00b030007210907030041d50740e10802801400700302c0046200c104e085950b8200c0d903070740c11001d0100c503000d6070f507203001900e010241c0c001140440c01e0020303800000c040d140b584042140e080e64400303110140c4011502945000c44040550614415030800c4aa8894490801c08814500c000507036070326050074280d048401c02d8004c14404207011805034045407034444e10a9807405041c3e002c40300344500b0b03000011402c030409156030302c141341002003080325030075011504451001694280510100c1c6182124581035400414980d4204c4601203540540b00390b101d05105072007801c01d800d0144200400b5440c6070400da0092380010504001481b035440103010401c0000741c1c2e20000f06021060366590407405074000e10800c10021502d096409061140c80350890980011a4030301150800e503c0081c48203103035003ea00302081c01c6c0141904142001c0e100076040700e4000202c03200804690342000210340c0301034109a4006151315000419050134800b250081055407170000758a128508126100101d80c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 730879145 1250 730877895 730877911
    0x3051c090b0a0b0109031b050f0913031d0411030a062115140a0506030d09081504031103030c0405130204080d080901060812031f0b0f070804030206070b040b 69
    0x4000e1210000d02440c0100b5000345900c07038080b03000105400102c0d140811948054907550300d00a5204c0c1805500e00108103030381d016554510185802400d22a00d400c0a4984401800441d40284003007849903000300030a0f084929a040018001400101035914250f480d0080304000010b1000a118a225000040c0280c0c050102c00b00d080c140c2c02802104891b401038901000c01112602c0d9400c25072002c04c160310300c0c1c0324039441400e000d40440010a81113030114040d104480c1000200b030b00500c404011241940000c05502e290780103c000c03844409403048040c80b95006408d9004d04090010314440c0802070503d9032120b1503d0b0030010f84010fa4011300c000c440c070403c0180b0041030003245d511503070700315410105200d4940343e5070903004140325804031095010f0f00030505007450106004501805508820045583c00d41800218201c031b20321603040c1c9000204401960885184040c0c8861402070351000e04207541c0c1d4003c1400e540c44003c0841e0500408030800c020840803032a5540c0213080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 730880395 1250 730879145 730879151
    0x140f0607020703030e01170a02031e06032e0507121a01050403030503040c0503030d060e0612070e070203040306060605040618050310093002100b030c04020c01140403051c 75
    0x440340001e91100e025020180c200481070b410480181d024006202038141007060390a21b9181c031140c0000290400d80b0b010b0201169141c2440240c0c1041ca50107028540040c0940a01c01c1960118848212100b8002020b06d140c802000807103080b41c8100c80c4958600c1d11000d24501e4a00100d10486040414484680d420440315150a03680001581c0a6941c0b5003070281c0d5940b00c5007070160428150381c0c01958103100000d6040c08180c3c6603001541110740741c1300c0c0f20520b80c444004000381084140c080c1039070b40c0c0c045002040743c413001c01c0d00a904200c02c0d0054914041d1251550b00550310305400c4075001c81e2001404111155200542c1d0801801d40b0080d0f0182c1e90410300029140c07049616880b9449444d03411410501804c100c10400c020111040341101490100320280352140c00500c0314090300940050314410000c2e8000c5880c0240002c020704003003100314080000079088411440f08940d0717240804401c2450700340e882400703180a0344515445125400c00c201e55451803006107500941 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 730881645 1250 730880395 730880401
    0xb18191e0303022d1b040b150306240d060e09010203160806010905030610090605120307030309063207050f0729040c050405010b0c2a0a03140f06 64
    0x940403404241030410945510000300100e9618015013007542d1425103140205254143c8034510500740c130341c10321400d840038003a591410003004299a010660042c88140400000307801d031621a03801070003060061000b030000c842104001d442c5030040003a5502159443ca014050321041d8041c44e0740c0261190003e62561030242401d40da90070080742d03900e080c041c2c0701010803020b078080d14001c1e02400d800742c01c40b4800d103000b02d414402966607200c0e40d4010740c6004008a15800e24407030f9004a03411f2440210300d0005107550440060003c440203440c107640d1182c2280f80c0b403040ca00400d415484403e003100011a51404580469401070b10709001d0010400004071859010001da444803034200c140e01c1810381614255030040545030030141d100d85100300410007044900004d001c203894040e2820807003aa00e030840ba4410344120403603040030ba44040c0701c2041400390340d91451083c25490207a14602d0210700c01207000c00e0700b2501304890b20210b0940c032481c480010030420b44100c240c14000c0c90071341 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 730882895 1250 730881645 730881647
    0xc030f0a0b130c021c17060d0f1101030f0e0c030d0306050d0201120906063b0c0c010b03241303090506030a1104091a0108010e010b18191e0303 63
    0x51a16105052607903c0d400c2003081e0030700a00605801000700d0401d1401002d2103103004010380c01c4184140c06100c5400049545402e0540200296079401003011860300148d80b50b404043c02d8005c0c1031810152101d6400280c0d60080c0101b000c401c0c0d510340105000c9500b0ba007014100514811928101850110100044e50780c8030881c00c01a9028200454581c440224000c040e10340e13540064002402e240c03000071546803191002d140b1b80d4003038003000170308414103400002180b1003e407a03d000c4a1520041640707824454020f1880080c41c200001d030002c080d1010900340b04250002210242c07044024070100b000480ca40c3d44d200e003107000c1403000d1103420303540944004450700409020341c41c040005094451f0745d42c4040301003041c054080d43c03140e80e102042405000d80300c40512100500c0109a1140e50180340c15a06840b0403000440d681da003004054841c1740c00c000aa407070b06071461001d072101925222071311012481c689800d02d004500300a1510251801d00ca84a25440c80d128410030220b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 730884145 1250 730882895 730882909
    0x9081b06250f05070503070b041b1503050a0e0d09090b190b07020d14032808150609060d0506030c0102030403121b051c080601030209150c0304030b0c030f0a0b 70
    0x280c1c0150a0405002d1048581103d19004000c801401d500c00040d682041c42030328a81c052240d88070b005044c0c00f4441e0701c02542100407881c4100803022444640c0042c0c818003a030813440c2c1c02042120001140c80c540840b940c0b400010140d400301181118206001c1003042e8082c41003501011348100100400c0080c81c001a5040c2d8800e41404600100e440d00031551602c200205d00c98110300910500d070f0b0440804da0b200d0707206414072100200040b40da600280c0701c036103044034000344680b250001a52105c08201443c0c6500e000c207617000c141082000e44658645000d44258105424001818540700f01418500b0544c5114941958802d05c81003000a0700050403200307604aa00d000c500300000c0c030b0030150300360150f41c00042560044c2c01c209a144a034000180d0400038159990280341d8a510006504074030607648a41c1d0010b0101000e01404504000140426000003048a240590700d0b201c98400250035203458240d02000418010100005282103420255515040101d071111000040c21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 730885395 1250 730884145 730884211
    0x9051c021f090e0f15011b020d022101060311091b0c0c130507030b0910031b120302031e0412020f010c021905040e03031003080d09081b06 61
    0x310104403640c00380d0700781c82990800d0040c041e5024401850400c56040d1a039400101e076100d08024400345030301c1056114a000b510700c80d055000c0280c0180494003030242864101e24141e8100d0321110040303200d01004640c00c100e003210340d0b0000811504501d024501c40590030b0182c0e100e540030000f40800c3d6881d40540c840c0c40c502c0c0a4071150b4800e035a0602500b420a1800026413006684010509035241c603000b01e4821821a60100481e00c2c0460800003454401c1c2e4440c08120031000081c000190300481510100c00d18095486469550342c0c0301d010300001d188411401608007048507114640c1e00c894503259000c008070340505050404540f035540302d0b51001c000e4419807000548291590007600e51440440d0007403e1100001c1803842c46520440c0c140c45110701541c50041c1c002040100132081d0780c02091048000f01d2841d246484203800c07078200b130b00500d01c2c0c160349e1030001c3c001840300001840c079400d038031482008010341c01c464507041800c000d180c1c1c2405071405d0110681c0711000c04c80300c16 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 730886645 1250 730885395 730885429
    0x90515070f0c17030103080405040e072405070605040503091905010806040c23090a060306030f02061b0703120f03020c0a24060b0903010b1903021c06090309051c02 72
    0x9000d841c0b50800b10600d0241d51082c43c0d05110000012060000c102c00402c10b4078002d0300d0600c62030b010b602d9990750300e4415110307a503207000492581c09904020b514030b042010001c0d05c0e00d94203010498480100310749050790121010782c80060086658184147c0300754a00380b1480302c50324050328110003c0c107041c070014500d52085a640c201141820b010301400d1444042510031110214010422034419600101140d480b5903c0390400082240c468014401942d6110b01d10b542d07540695801c1c40100c1e080b44403204c034400c107001c40c3c1c01c40d52903041004000550061101510700308141030090b29511128110000b05801041400400e11001500c00c100313582c003040441500d0294441c00f01c80a481511044c11f843c20040b00240c850312240141c80000400c5000b04040300e40d440800030213461300d403110392002c00840000c001501d00b400740740554035034400c40492000c1a595510301201e024020450108a07151010322081c01c20400070001f940c00c80410502006454000520320704e40401105c3c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 730887895 1250 730886645 730886657
    0xc07091b020d2f07180207150e07080a1203050714220801020a050c070807030b1803212a0d02091504080345180a090515070f 55
    0xc054110f10302401e00580b079018040f4014048880410340b0b0f91418800c1d0410340c181c2040400308a55184200d55200c0c6c4e0241d00002e10b40c501c3d99409014209080b8008c805014461000507809001c2c45200456072007501c1d4105001040000903003207440c003508120401c84921404040c10105008460954502c8000025800c45e03100c0d8006114400360441c2c41554000319001d103599030868085d0800d8202c180540d52400d03160800d01c0d641c1c0385144006403140040002198005e1485080110200807071b4040c4ca02e0b1050011106200c0c250000c00d10f444000c0030310400c1a6055956615050001100407aa000015a460400f05030107400780414903142d000910420b02c1d655210000c02c121000c0190721740b80c0c0e0391001710075101c1e040102d0101050381c13071012008903400012070503200708400c80e000c0e00f004081040f0089040d0300300c0c0712068005800d1014401080070182d5114030842c050000070500140518065003081d00f4090010a503d64400c21f010a5980040004004506900d098 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 730889145 1250 730887895 730887917
    0x5030a0807090e13150f0c09031a060609120a1707021003051b0a0c021207150306050303072406090501170c0a0504110f0d05010f0617040312020f0c07091b020d 70
    0x5100200301882806c059980303819016408036410000c1301084a0080c41c90711000d11100d440c01d4019881103420341da0284040090250b941340080c01034820f218420215a079191560b9101e0020071305114180d0951000400c0c01c00442c030700003c400c6d128980b540350601c2642000b1003040d407005241150090620404108000a2841760202c0030546030000d080c04148140b9452091302c4420702d00541c0c28111a0006080d2620300038001c48013242c0c3c024004503e001c086407600183c002649a4140f0044403d086d6180418514043d40018040c02d90001074554540481881580d4950002d000706400481540d00580d850f4650303d02242d80c143d0300840d4416070f0302c8840340b080c801c85850902c911000b05e04542a00d88a03440103043e50900b200d5402503503208d200681d00d04c00713a034007080c1a89003080c00280c0004c0c0728000b01010501e0501000d410031000244244064000041526817a03012400c1042084224010117a0201d10702c1c519a01d008000390000f902c8420300c0d188241071244800d4a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 730890395 1250 730889145 730889183
    0x1803030311130e0a1805070e0a0219021b030d080402090c16030e0f010806060a0e04020f0406020c040501050d0506010303030b01020a06050106080709080607210905030a0807090e13 79
    0x100c031100701008050880b010b80f2003076000218001980c682c00c001c2d241a860340c40104101c82c10900054221000b00200c500e8218640140407000304500c0003d9024450b02800b2003010910409a99054003d0201e104041042020000c0b41c5001c0902c030303038400f5a80c41d4025401000960304690150354020f01d69640d500700720f40c28854418820b005c2415508100103050348101d4030394412008840702501003202c1001124861820307035209038007502c10460204000d0091074500711030503001d4000742c00c22400242d016400d412550010001d40c110783c09110140c5801d20904d80034003022560014048501e440703a0b80d848605010080601d5940e007150318071a03008008103155294051414040c96071148401000c60b2001d4a861020620391003020600c510003288840c8a00d0700c6a5a001030f60300314240c04221810a80f1082550590701c03001400800c2c0d0074001010070360203a40352a01141001c0200403c800c5440d800310301c00c3c58402c0140001841055880c06003581c01c00c1401d0391401d84045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 730891645 1250 730890395 730890397
    0x6050c01020f160c0e010605120402030f0f16080313030212030f03010902040303030c0e1e0a050901030303020901090b040e04081b010c1d040b0d031404170309101803030311 76
    0xc040034500c0c101040c000003551010650780b01042c49141180b813003540e10700038000180000e0082e20040740b003e10101541c0c141c841034440c0c0c414001002c031901d0400d0643c200c0d00b0011101d021044907040407070030300540403012403114020030260000b9032400301011b0b0f002113000c2c0c0c1400020f00c10400725040191040381002515a07004960146076a25603440c51540300035440f40c401100442d003890b0f00d1040d018081d020018520314050180d2040b5400004664080e0010000860b0301000982000c5015240c1d83d007039901075072003a200169565085000540100c20340e602c00d400c2d02104000505c00703081546107031600254040085a151045858681c07980c10546419609a42c0fa08140c4a07001e640f0141c4a20007040c402e00c28a190004181800b0607100c0030224240c000c18035065001c0040d1040568207610741e20281d14505140d01c0b12081810380c29a841d00342c1c410b40c00407580c48244c1c0340100707052040d0316103424180d206c0f8450807402d03070a242c91480050241641e41c8100e0841601d110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 730892895 1250 730891645 730891657
    0x6120907090501090b0a080607090e19090605011706160f1b1505100515030a180605100b070312090501020d020d05011e0e040b0402270a150f06050c0102 67
    0x20206002640e11303000360b04001c01c501c80c6881d02c40d2500c90400a525040459058015215035880f0b59500e41081960203842c80c01501080030000400e01509900861344203502066118a0000c1015450480070850861100030395407004c1c4c0080043c8070b00d02003407178681c85207000c9504102d61007101c404010b0b1583d841c15490110b4846140169100b00720041c1c1c202c0a005a2400c010000c0307448035032400c001d01c1c4807070049a4100d081d0100c425414100e80c0f0140d40c2c4414032280c04100065200c0c1b501d440801149411a0140c1c0c6401c14083c1c2d98600c0107010000d07004884d03480e03040443d140c60080001101c184113400701c1c0d03581c05a48051000c203404540e00e50707001401c150340d9460040e44c40300041c482480f954204003c07001d82c28004840e01c0350f0100807202209191340035a1107503220311030064405041242d00a030101d40154802e8003c2c80c04a249004082c040c150f00e00e403c0c54078205540c2c0f180c4c03606051102c0d504c8248450b281034100f040031f03955145041034880c8040d0200e2030082c4180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 730894145 1250 730892895 730892909
    0x409110306160f0807210203071205010b0403030305060307050d140f030a05030a090c0f0f08070b07050309090a091203140601020604030801260708010917161e020a08030d060f0506120907 82
    0xc0d03000303560042c0150008c0d801074400c0d40c0d903002000c3c06c10a4440c12582d00780503850400070200810000b0902c660000c41c2c0040c0d000701583e41c500e5882c80001c0c1800c84920003151401c00055004400e142c0503c000c0e035000e0030071009140f9090480e00020114032004010000c216510040482405070380d02c142c1c005080760b89205081a0b0311080c90441520461041c00068407803c00c0203d031f12000c280590707820f594044011400c018000f01045014a0b0003051480c52a82d600310000205407410503c0b001582d0b5500c000030602041c1903100d05445004252906660080c01030000003a44031030344c0c0e411100c0350100000c5504040b5207800c0e94600300780d503030003152041403c0800d400e50194400b04109200302d80804000840078480303040c5004e01c6007054166990350003a003012805081c0a8400100030390482034803410b0315030000c1d2032100c40303402118090744003080e4080361845512404001d49109024800824078180014420384034440c0c500c1d03980e03481c0b080843c2c3d0f194410003208028285c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 730895395 1250 730894145 730894187
    0x20d0c0b040519140c06041203080712020a09090b010806150c03091e030c15090103021b030a0c03080a02070f021314040f0302060114131a0409110306160f0807 70
    0x1404c180384c9441c4400e4102a9074001c40d64030b01520300c0c0803021201120400c03014580040708a4805403804c0e5030041c401e400b8444030503d0742410855520082503018042d4948c5e804440c1803507982c108075a101500036050000100500116503904001c91050780c0c21610032565034817800300000d045004000006400c6604045007052503080149140c442c050260116130b040d201860400808032010301c21400c000700d0030402e1000350352003034008140b041c0c01858405401419140d1851a60b40860305402c000703800300240030200b40c0c0c03200e142500111406420350030b080c5c403600c40e0308154092510007807065010b03c8903011031602d2a00500b070036200304d020307101c10b130316240c2405403901d400300c8000c8005005410000c61701c52202d01d8800100b85018240c800e08510007410304006180d40d01307444090b155041c00003449076849000741d8615510469095616050300014145402d6010303003550480c5051030b80081606a01c40390700a80347d5403900d84111140c840c400e0540e0480e441d0b004814070b82e00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 730896645 1250 730895395 730895443
    0xb010518241b0d140403030809071d1609060905040504020f0303040f090b010504420f17090c06030a0e0a210c120c06020d180b0106020d0c0b0405 64
    0x850079901000041c049001d07203e048903128411038207403c802009100000b0180401e00c082485000b840340c0c4020348008580c1c10a0f00c41e4056040c20030441c03000094820500c0401c4601c4506080060760b0040508048824a0400c04050540781c500c0c02140d0043c2d9aa0000400399581e02c6400081e40710094107036541c0e40e4031403120554140c054080c4905940c2010b00490f8194440c008450031500f030131041007002071000c000700002c410305031a035034140c520034142c0e201a6107032500c1e01e100340041c0d91110007082080e8007010704441c640b041800500f0070401d08001c1c01207404128110075800407a10b082d03980da64a01c03440c0090038104189142032081b580b640b0304200c00d212000080b0000c0110081140c80c588000b200c80503880c00b40241000204c10a00307100a0042c40c00c082d03011b1007003402504000341d05201008452002c0309403444000c032113000c081802909541c240c0580443c2c8050500001c042c1009041508050740c01024007142c01c00140a00609001018100950030f42400c5c0200b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 730897895 1250 730896645 730896667
    0xe044d210f070e01030b0f04050a150e25060e030a050f01020d0f020703140c030702090c04260703020f060d05070905030d1115040204060f090608010b01051824 70
    0x700480445005500c15000c0c08100c0d4611500c22038100c0303501407035a03462076840d04218604101c1c050320072180c0e48074a013925070000c0c10702c203400e41d03050076254000541d038040c588540786814007490040e400e0b014040551100c120070803141da0150344050a01404140b40040032a00c1e01210b04005000e030302901410510000c0103400510314050905000d1041d0f06250200004030320420800401088406403000d07101c10901024008040c803020076242010005e0300854109a0100d03480318000c100014203001e030302c4228024483e541c80c2e0300100c2c840411007051150b561046030001034800c0c0c00c1c8a80103c00380c0c3e0340034100c80310100c030807405010500303201001810300c5005008440c420b001da20300d480702c0c0a01ca050623200c071140900007441c2080c200000c82c01c148030060302c2039030400d0319a1404210401005001d10060407442c2000403146e00c2c3c0b0500d1800c45862940d601c0c100b20b0100620f1200c902d10404074456004120f8402076030321601d0b559503d003910b6a00b4250564080869540619 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 730899145 1250 730897895 730897903
    0x9020a090501030c1b0809030a030c15050123062701030b0f01050d2a021e010c091e180b01030e010209061608040e044d21 54
    0x10104948800c20255103078001034007950039645000001994440702081130010182c03000180c80d0044113414500702080e000309041c07035100a000d41c041205030f4001000c1202030700400c2d800500c2100d04000b9941046400c9241c0008081540b4103a640300a44408e155680403c1b40c080260b0400c410340d07a02c00f00031444082c040303030001c0140843e1600d400b8a21508020400d8405150305a40c0d10b407403c007010418000034800d1050303544100307071043c0b142c0340710303d04a24000303402801a800070045e44d0100d00701c0c45000142e100c0c0c41801a4103003500d0b28a2242c1004565094418000751030207001c005540c0441c0d40d11040c0c0c05a0262910510030b0030404100341e118910301842a80d041c000704407590b08447c03d1b8810341c10b102d038020b801001401100b580c40010210480c0c41050001e15140c0e1310008a0000d9200381d43c2aa5160704807180c02c80c1d100e40400c400300c41001050241c00308040003030b0003011541d0f850b090001d08904040c401e81c140d5580e02d00c1c10030a1840800b13440e03581031040a0a2599 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 730900395 1250 730899145 730899157
    0x402040f031a0906160917150c0a0e010503040501181103011508070b0a0c08030c300c300405060f041104020a0504090e06060a050103090507030221070902 68
    0x2100140d04800025060390100403481044843c00900c015110364a01104a42c00305400710200011000f0104020100c440c0d9000c00900110040c003c003101d01c1c00d9590f1102014010001c0c0c1d8000b040381c0844640c00400d0188101c5003401d0054690750395090140c0900850000041c81282c0620440208920207104004c0b800b400d1b0000c0106c010350000c0701100581500131543c181c2d1060804100c7c0d60300c1c45004104410661078000b0b0748021070b0355294443e030000d40b00c520000c00d0104240d0444410030001c40710410000003024841b13060401170000b03035070014054401125001440030b194008010b6010380300d44c051848540c5040d4090403c06014009441c110b94500900c0040f138414440000524025a00008a281070b041c448003000001d44c0030052940c1807080c18480003610703100d80d100715400c1071510000b4003c1c4d071601800b040012082c40c2c00030b605062800c140e0740302003000021410103895041d070f480204400060741d5800c100c4409240044c081c89001c0010950203941c0c0c000e425 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 730901645 1250 730900395 730900403
    0xf15030901060603180b130302160806061c02221e0504060f060e181e0a02120d0e09040819090812071a0a0f020d090b01090b0d0201050a05090402040f03 67
    0xb04400e002403805d0728060144d400a0580c0705070342c0c003044107070040c482030015041c42801240c0e40781050b141100700705030443e401940e054000b581046140d06210340c0e004510f01d0007842040180312698009103076448110310300c3d2800d148441050740c0815007070384500c0e4000144a50751241d80000041140503140844048441c507081045280383d1030440e0003a035054502001540100c0e5955448882c000c9000b81d0324000300384244043d00d02c101e00006483c01e215051000948100c036036a0042c002c1540c040c0720341800035400b140c0000890365000d0410300100100700e6000c2c1140e115820008100d00400c60055040301800280c0c0401355040719031081204c8003a001e9070071341c3e510011444034074003900301c003d041803442081a481c0146102400c41d44000206000240703520000c1b12001241c0104030a0701c00c040d5500300010074014403d4515006200e0a4801c1c46404800c00c0800c03115083d000300203050000c00326000704800c0c024402d681d44035034003401c110b4886607205029040340364607200c295 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 730902895 1250 730901645 730901651
    0x3030e010e07030206071a07110d0e01020c010e010507120302120a050609041203142403010615030b030307140a03030c05030402012a061406010806060a020c0f15030901060603 77
    0x50400040c064400c0080c6007102901e5100e10f9a02800030681c01b00000300c070031590044400d1580000c80080a003e94007a5481c003e503a083c0402c0e141c86e09021034451418007100624413201d1b80c1c6e002443c07a03121002031034400c44030105040180e03107501640d00005c01005940c40d01422042c2e06601400325043c240c000c2c0c20182e1581d490941c11904280c5025801280040008002c00d80080740003002c03240c030f0301e130000300701158829000c8004400d80344a00005085000b4920a04404010415400e400c40081003c1f0381703440089413006a02c010210207040e2a0b100341c940c2c960b03040c0299600d2503001060b481c89008501c81071a00c6c1d142052088000c13914200751501e44900c14000da034480c0d40d040e15424141e5211508220001c43c83e0076607503030782401c07414081000855038020141180000412268241454000584400f00007004640100000c0c085050345580c00038000400c010241d6881b4842080d1401040c908c03e001e8901d4044d040d4004107019584074154442c0f002c941d1269020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 730904145 1250 730902895 730902911
    0x608010e0a050d1403010e041703190c1d0d061404050d1d010813020a12150b0d0201080408090a090905100c050c2a030601030f030e03030304081602120f0a0303 70
    0x1034524100d0024026454101171005100310141074490a030818000c11181c400c80341d0401c1880000d50049800c040543c091800c850b45c81d960500030200c21000728107000c14411100040080300300940d1220754840d0403184038060600c58141d0001d0310403400c00740e510449190a0800681d01c40100e040000080c041d81d034022409401c200001c50b100e407050f91504495202e804009032890b0131000241d92085119400284004601c1910142c0d10310804110000300d08419440341260303103215405024161900013100140c1c0c0c00060650b1159106200a880700c08010126481120700d030810f112603458040c0c40000d22a00003040404810404020b20600c1c02980301100c031402203c200500561014000006041203100c07801c0c1c0602d141021100300c6070450300044c1c50050700ba403083d5212080c0929400900d07900120003802c103072094000310300c1e50500e5030310f9400303910035820110240c0c2078290344041199110581c6c08030030480d2004507042f0280201c07034680c545900c0c0c8021000300e85090301d2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 730905395 1250 730904145 730904147
    0x100e0903030c0702010c03020f102c0a0308070c021801230609060702220603030813031e11011406040e0f07060e060d090c090f090b0711010608010e0a050d 68
    0xc80b031080308059610740c2003156660041d5020203100c44118150300817503c1c000c603005000c1203001eaa240780910b0200314140c0f81c64000b124004840c0305002c802400025201c070b801c1e00018000d52041e41858000341c16030f01c50404680140700008029800800c40c41c0340ca1010200344800c034140d9080c0101c0609140c4d10320820150152010091504002c06100b0b4058900e0480050040c0034006000e1000c100010400d089440d07103e131400b94411540c50a042c0289a03202c079030664032001380d0010300e07819400307034401400362000c007481d03060080315441c154005c0c24410f050f01d2080c1100b22000780000c02c82c0004081c0300f0901101c806001300d280041c4400e9075030001034001e025640c414050943c1604186e0107c0d40017518040c05604201c040101c100321400501c05c200c0072500032802011083d09001062095481d0480c482d0341460400518401280c5420a1950014a68182002d0714110549800d000d09060341c010001540391030000c83c014503002c12a605c01d9882241503035404c100d8044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 730906645 1250 730905395 730905397
    0x3f0206190506010f032705010f0510030f06020f09210c060f1e0702131e09210210180209060111150402041503150b15120a02070209100e0903 62
    0x18840c0d0004d0384d5102680c44080c00307a070001c0c8803500090360140c00c50304409044010112021021102c030ba5454940070038850700b611560303800c500b203190f8a001981c91600c8900840c0c1e0b03501000341c24550b0000b8510104002d80040b5003094a000d08100c03408100d10324100104000d1007441091070244031841402031422400700e030a40071103c075115003040f10100444d0301c1204c00015818040700200309642c003607980d4071202500c15482c0880850002001c644800840b184203102c1c40185003030090a00020303ca80040300e0a10b100d0409a03294000400001c0307241020070015180c090b4030f80340c090300080d05c0188140c0c141a0099501240648600300110360342019a940b28206400c0460340390354860380001095001800140041420714003a003d42d801c03d1490b500440c1c035104020000ca4403104a402a0121301104030782d181000090146410a0351048007942503e00f9180f030700140302d40c51958141c4108a8001d484c598072494502c9464850410324014032440c201d2010000f0101c03a4000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 730907895 1250 730906645 730906651
    0xe04020a060e1e12030f0a0f0c02010e04020304020d0605130c170601050d050a0215121302090705090103060305060c1209010605150a2607090b073f02061905 69
    0x74282d100c100040c0a0103042e0300541c21509980104e00c0c040700400640204082d0007036072003500d0381668030620300f000070b007151169614802c00d21203050000000350382c000c2221011401c0544003da61f80d915440082c6c150f200d141070080c440345c90601484000d21142090f400c0841c41508a044184c1e1281d034200c103c0b44041c4006903660384000014062070501c00707220481c141c851001c0b1a410741040c0c2c009a41070454800368090001c01003858a1102c0b00407403015040100d01c1c0800310109450b8010a81c0014014006010720a00241c160050391107648030340019604001a56958140302d5a400e60580c070405400661060300b01c0840c07041700d410702c1780c102101c00051855502c001c1c1c8401c504015000b9000440134404145528400e40e0044910341e80441c0c110380800b103503071a081501030412803541d0421040a1010301c078a80001e000b948542c4110004604d103500c0944581e04240002c03580e0010812100b108403d942c03042c40d030000750490154041e20314000c4c1051005403204100d0ba070403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 730909145 1250 730907895 730907899
    0x6110a020a03170708120406050f09121e040b0304020411270d12031401091a060f04030c03030c0201030b0402030906150f030d05031e0c0406120609060e04020a060e 72
    0x401080010080020154043c074a40205402c2c00e103241c0b581e68450b0007a90b0700c0b00c1e503900058108800c0052501c29190b119541070746005943c03c0102500303584911100582c62441070009000c00000602c60782e50309250761000505070780d562112101411500181c034101e0040303003400d2071001250140c3c41507403540c1849000101c4240000301c0204140003841084941003c6821602e40100c0d51004200d1100141a1400f1a030480e40098130280190168860042a40f80070f01c0851914507112181c0d118000480c1c1c11a00c0341c2056410300c0040c41607500041182010940002c1095000580021814004d0320300300405d031017050070f01003a88002c84400111f504200001180f140c105111700b401c0e084081c0140310349450040102c0d2510140c074890b2400314002000704003500c120b58038010711250f54810104024101980030b100103000e1030080c0401d101900035a030103072101c6540548000c183c00c3c00c0074007107140d0701c44542e64040b00030740e402c1c0e0013036408420106445000310a85181681c0c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 730910395 1250 730909145 730909159
    0x15080f1002130e090c0901140f09040503040e1e070507080d0f0e06090f0f0102090306010303140c0d1e031e0e190318080d02030d020a05090d03030606110a02 69
    0x5890820009500c030000d88188800c0c1c1280108010f014030100b140302c1c0120030b00400b510380d8030004011440d007050b40b007070031240440c01c1c205040b51140012018415019600c0011944403850950b040d4040c2c1e42141c0210140c80c81040749c000c40384601100500c1e44070380d4008064594503030488051041d503001130040b09080100c28501491507001103a020041c6100080f8801c0c800412400c10b0001c0e115403d0561040700707181d41040c028040710044621501c0214038004241001c40d4807510148409014040703141d5003822420844401c0760306a0b1240c1c0213071060f03c03203140000fa219010003140c0350070f141884181080aa40070b0301c00c21141c99442c1c1c10b600005100380000502501c170341103000c1301d940a4200c100c2c001e4200c0c10f48001c081ca02c643c94504810155103c8039142030750607800400640d00102c17046c000c40e600842101c41c80b25005802680d01c600c10841500d4620424607090703000001c1d054100240350f40b582c0700006540e040d43d100c103070003001440140d0351020703411006980111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 730911645 1250 730910395 730910413
    0x201020a0614043806030109060606270f0510020a0503070317010e040323300615070b041406040b060102011b02120c391002060f060406150315080f 65
    0x1d50b04c0205911060040c000310b003603812980d41401f036401c5540090003140c650043c21501100070900b0700e00c00f42d454000c00c150340303103081103401c00082d640c0700303490180401503098200184240141004203802030211380da600781a1500030120a40700100142146041c0004641815149001e41c000c42e003580e0352031140303040c0d50320360503e010ba40303040c03007058641c10080c0200b00e05101495400c280c4000c418160f490310010800b01c0c1f5008001c180340d1040b6401500c056007011500140c81d8013a80050b802d10680d615460150180c4210079145c403018490740382004108051180c00d103105407001e0f4020b01c4600e1000c18503409114040707804c400587c226030000280035256030090055500044201e030400615800b003080c492406020403001250852039400c00a1142070300c2008402c0180c0c1c4524000c41141e00081d218207015107003062480c2d80c0d002080f103503580d581040c0c0c041c040c406d20110081c1441c0601070000c00183c005807041080a500c00203002d100480c4410b014180b450142c80140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 730912895 1250 730911645 730911743
    0xb010f08040b1f0609050f06160308100509010b210105010f230a081501081b0306030c040e0a0c050d0b071107080307080a0e1009050d0201020a061404 66
    0xc4000c00019103c0f0310b001e9400c0c100240e080c2c5010061440f6181c41d9045401c0c4410320480c0c00030508610b004481c200a440f6001c0907006000400c16058904500280c6507502c070200c0000c21584025840003240b4004100754410ba00217000d41030300705000401040404010714074201d0248a4507000c20055101c07011a05c2c0110059000d0000174103a400000c3c0d0000002e00b860f40004411400051843c2e08102c2405003070301b403014600e003090030004040e04c1c2c448145080d00341d40020002c051800030012075800d032030030011403003c020300410600c4010000f41000c0c0c3d0319041c80405607100d0406500010386400c0051a1010842d0004058808c030f503184074081d00c018420070702c055054401c0c2107001810603010300240008606c40c5c0711040c3d94003150400180021040e4003c00d105d02220302c01c0410480d0400301e8002182d00603150031012008030700060342450880e1101900541c102120031440382144011503105922a040101542c01402481076040d00c02d040350788144141200040015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 730914145 1250 730912895 730912913
    0xb0406081903050c0613021c08041710050106050a09050402070b060108090a0b1003060507110c280e0a050106020601060e1912050a170f0f030705040f1403010b010f0804 74
    0x80e0b00a00340546048404413a05181c194101c41216402d510001000300b1881c1503052112219084030510b101aa01d680b01d01c9030501c2948241003180c88034050a004d541c0091103401c0f04500c20f89420042d40d0303514a40942564000340301311340002d06220000c00d1514040c8240c40c3d5940e0812400102c0d96035030401500c44604c05009007100b84031f94502480040c003160810b503c00c01d603242400c050681f6503c1c014050700e00103007901060040c00e0b42242404580040d089200c10001c4802003000034aa2a40c40704000e452180803175400d488040205203001800c01c1d080c001c0d4201c4008016581c3c0c5c5040c202d849038028000d03c000504402c00c0d00007203141641c2036840f50100b011008041c1e07a40c41e90798184a903444e8404881030740018034a0b01c103200d4003002d00e01030310f015284107520740300f6602c1d072221031841500f1903031203031000200205030880d1040b01600c1c0500000d81409003481c0e258114075003e040c113003000034482e40c03d118072806154820648000f040083d9160b01d0702c0c1d61507640d280d03141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 730915395 1250 730914145 730914193
    0x30b011509030f0303060e1509041b0b0d0518010608030a0e2e1206050109050607080c030304080c0705040b0d02131e0b04060b04032f0d080c010b040608 67
    0x401c0200000400415543c12a9120f8140320b600d000810740d1a01002c0c0b03540080050a0507810340032008103100c80d85441542c40d92295014410000210700b000d280c10004205410448038008003007155a1800540e60180d40141402950564484810160103003a80d082d030241c80f002e0340050187c0446a40200c4145107600401861101042042000c20a8140045403030308130045240600c06019504410404120016040c003400312a08240000e0611111b03480344034000d810004500d018001c492081e01c0d00d0483d40d07010f9070764900f084e003800107140e00040c0e00140140201d607070000d9103152901c103225003150090901c041104043c2c003088100b1601184841095840750b01e50520031b4071040e00311600e00f4550307100242480e008003c1c0012507946400070042c0c944100000e20204102c007441542d0044c000c81001605203583c840740c03035000c40280c101078000300d4201c410010403507203401130245081c9440c001c1204668520130001a9002071240035821380050038241d00d8022002e0400300c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 730916645 1250 730915395 730915397
    0x81605010605220e06010f170a05060915090607021b01030b0a0e1e06030a0f050f1207030e010f0909020c012d06050d15180503120718030b0115 63
    0xa003507a80b0b5021416000003001411840711081e10380f4160000d142c81100c07201850140209081d40c14001250645081340c0200760070603c140040e030380041d03400c0051240c10b03503010040d40e00a08080134038075516a441c036401e010b994244030000d4900600041c01a20a198650051a42103d405804040c80c126102c0b6030b0304064403208180d825480e1050000c00410004000c0d071100e150030042890060070003071841d803160005c0000c0c00180d5400140028249800a040c00858565403a01c0c5140c4182602c4842990003020011140f503034482c4007034900305002c3d80f40c06c0c6e4814141c000442361201201d00300700c082807160700140300e07001c0a580035207104003207000001031401884c000354240d410745d43c41142c03101940e44201c402c40041c5010b50340041c10300b90b4080344500c10343e0740c5140c0f080c150700d0561800c00343d4035003003d055105c07618200c0e03026503040020b4075500c400728003007100864030440345040410364200210000e6000180d030141101c0c2c01c0080c40340240d090820b031348500844050301030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 730917895 1250 730916645 730916651
    0x2030f0f0403090e100902310b0d110417030a0e0405093007110f010302311814060108090703110a08010204060c15140a090f1b05010809010908160501 66
    0x12030121b40342e100800c4502c80301d00076800e120401445200481e04005440668104503c40400010505a041d01e02c0c4c60314024022a2555850042d00f099018a80c050709500c24041503003000c000d4080010720160340c050351441910720844050200f84e803c00d0340ca000c1c2a40c020350009403510a040f040c00c202501016151880134080c0074103600c3c9401500040e5440d0301108200c690b2850201044d2500308400e003801d6042042441c1080106a0031400c80c2d141c14481c240a1329140041a9515024164950502030050003603845180140b500511400000700c811010841c81d6029080280c45200700500410303042341156610039440d0030844c201c540116500001145a03102170003e04013918890b902c8076511007850500525010304480c04855403481c1000f481c80480c01c5560043e4815100240401e5041c024600300c0840a150800648641d40c43c0c42e2340e801d5000108806822900b090b80d42c2a0310740c4038444058201d68001d00010103400b02080a4030a00d4403181c0c03a444410302442c000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 730919145 1250 730917895 730917899
    0x706090821072f0913080304380f0106091505160303050414071809020a0b03010816060507030e0609130e060108100e1c110f01060906090b100305061903050102030f0f0403090e10 78
    0x300c0013014915505e51027880d0381d500c001c0ea800280c21a09540012250a25056545800b8005d002c183ca075000707100302441c4580c20089140e02070000c80e26401d10000c00c2e030300d90002500700200200000d440840d040800d001900c101d000000031641c0c1a5a50000b990a0032014000e1081c000d16140400f2604203020f031070005080078048001e14024014680a0455001a059445007024282d00541e0038070005015080210340e0003900030b054114241c950580d00e000c0100090740c0388242c1c140d042c04441c10840880b21488022a07100c0c100d540e00d4040701d0003110b40425480541e000c08200c2029a03001120a07a400207100d824060601e1950504140440d05070740f0b40c504000c136950a2000703c0e911780008101408040c0b0a040017007168820800c076003146d020000e107612001000b203000b01911030300420401e03a1007611b03101c010000c40c03203800007455036440c041b4040d410454a000301810b141001818441c0900c031402d10071a40360340d81c10381386418000c52103000040500001c083c0f200c00781c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 730920395 1250 730919145 730919183
    0x3150e04060c0305100f060f092d0501170406090f0209070906020c1c1101030e0a030c05010b01050f04060c0302100207140706090821072f0913080304 66
    0x4100d0095000781400300360701c41c65510140582d80042c043d20910009030302c0800c1106041181c42040e02d03928034203c0c03125190841304441c0d1030301c035420481a0b620008020060400d4140c8010008100e44031076107201c40d558001550000c60055148101054460008001513000e90103189442d200c0c4603155901c41c1640c000c1940e0754001c884520209403c03d6080c422140c040020004480088070742d000481446030040111a6400000610502c3d01403410f4119030702940000e201c00c03030004112410801d45050007010740240b001c00b604c0e25407a0602d01c0c05294031603c204d0b070002a903110070b103103442e00e072007411076985900c0302003135045018011142c011841140000e0041e207004000e80c5d40e0030820829560f0900507554000424484e1207a400c01855002140d02c400b14818600240415030244001594601c10702c1c1c03005005040703d00c58103c00c0c1b03500c201034079030021b242210340d000081e4034420b201c0710030000ea441e00c284c4012241602d000805000086501c00e00ca1030042c84120302d800c01c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 730921645 1250 730920395 730920419
    0x7061503060501170f060402061218240a06050607080a0c0b0a051e060a05151e040e100803160f0b0a02030a0c0c0f030516150204180218010315 63
    0x10b50410300f44640844581002042800e081e205e41d0000380c13050f41456800990988140c0c0320001190700e20200150308901c8054401d105c0ea103404060320105138200816242d020f240c0580e40c6042c68804012031031104d80c40c414403094a6015099600e00041e680300d4030503640040c0103010401261860800019151400e00d81c0204c11205000c100c40c00c0c40d003088e030f100030f090142d4504019141810403107565207180c02141115005c0e07a10166050071031031200390a100b9402095030480d4004e0038888000c4120b4010400c8501600981e449505c445000700050300c054402d00c140d0780c4c400d0003101da41c15511240380c44414462200280540780540c0c1d9080d030520304035003640940e60f01101300f0041a106004149840c50140340c01c0410100035924600299115a0080d042041c003160383c45101c040b0a9031000304070b03001f101101122216440703200c0690300c14020440c000340443c498030f104002138000e49080341c600d40c2e401001924000011402800b00c580103600c0752116100008600c1e2982c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 730922895 1250 730921645 730921649
    0x9050919060f05090a0c03060b04020c0f03070201020708060408030103031803020d0b0403080a021e0c01090c0f060207060c05030a0807021c27050a030605090c0a0608040210050a0507061503060501 86
    0x103010418202c0401040200c1d41e00600e142a00d80150480d0800034002c0644071003903030b522000014000f040400414020700034108440d41d01e00c581090381241031000805444d00034801d0f1f08403901c05440380d000e15101c0754203560003803084074203000500010740156410100c6000c01e091981150380d403900001d40d40360103003001751303240e403900310510041c580c0c40105c05910032484c0205502d0b2400343c02d071010398440d00d11011840000041148200c8030000e40000e11000d070040507100480d6200c82422000e08890310078400544034034040015a18043d101c00785010f07406c030000d142440801c46064590348001018103007140200e802c100141c0c0000c5402444540c5c044d55120000170a0b9607c074500614120f61901c2d0044618004024554a03d0480d0056941c0400c010445c0c0e10b95010b49843c110080c4a040d50001c060400800e5850344a02604e22403070080710801f01c07081c03002c0c038142d500748035900d007040000b44104901404520650040c030a0703100070402c2019013640d44e4807003408441081e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 730924145 1250 730922895 730922903
    0xf070303140703020d0b0a050604030204092324130209100312021b040621060e331b09030f0d03020a0f020f0705090402060d0f0b04150305060109050919 67
    0x420f241e04003d40c1403107410501c1b81c041d1440510141082c0000f81d150207a480000c2c492901c512400302006a0340d60300c160303019105400f00c0242d01b0b00203840307501c9040c031140700714447d2100010300c080c50035061041806441501991815030156800784480400001c007030102079030f4000d0001000842c40c44824004d828590b025200c40500d20749440d107000301c0d911001c0d11070740c1400c0090043c1404070044070100c03180200d03011101001c524208014080f441c681c44040c0c0500165426911206002c1302d030b4001030342c0c0729140c55810009140440b10000d45608800704100b080600d00c0100080013416a030342c0090445880d076801300c3c0c1c903e140c01c0c608d101510000f9004034041c080e441c1c0010001d030b600f04c0c260000d48440803030a40c4d40c0366100d42c1c40c03103070502c503031054030218056445003401c40e0784810701e04030280030038440c9680480191070111100c0f4007451800400f02c0c0c8106210f040201900d41c1300c000307044580d00c1c04c0a40313006004040e155031400c2c0a81d43d0010b840a584850620a05200f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 730925395 1250 730924145 730924147
    0x6040c1709060a0b0a051f02190501020405040c11061812030a1a01170f1005120d09080304030b0c030928020315160f020f100f0e0102040302060f07030314070302 71
    0x103c29888242c41d1641c922a00496007000c0500955459000303440d00c60200c007030b191101c6a81010120f240c481a101d00b00e5414150003000014450103400620a0f11001c0c2c2c0e00740304240880303401700c50b46226401c0e000010340091004c583c4114003d01c170304803036250310b40440e00c03401c5400060224070b61056a0385003100f9a5980030503240c00c401480500300c1007003402d0a10081c046000f0821104a0051202000c600c1d180002941d80841524074030281c032010340300900c0f202d0441071943e9070750000b0440802107001c4003000200401d00101301c0d0f0a8903800200748c0344548a05030354071240d400207090310300c2078016030a03283da4841c244210040e43d0901c0f400203964482440c010b141c10002d20038aa4020201100c0400c8940b0007d04c210303000a911501c1c05040c6400884400ca08040301c2c154180114055103600072040c2d140b07904050a58020103904010001042c0303010790807031045100003504140240210031054000c0000350010070300a04010410400c85c0b4002682800c00300e510001090b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 730926645 1250 730925395 730925401
    0x9120313080a0b010e190501060e032b0c0f02030a050d0e040c1d0109091802010e060405010e0105130506040b0315370909140f070e06040c170906 64
    0x940c1003221401881030700081c00e82c0d03850544990321020814010a80d54000410116011034030b0b400d0700d00180400c1e00c100f0070465031075000c020030503481c600406103e80b14440c070220522400031404c549100e000d681180c50b10007001000d6038541c2d00442c05685000c0d2000c41034000d62414020f8817116845800909010301014801900444a0615250280d440d220350008415008076200705082c5d010070700000c5240074040125003505061708400311507030800d1441e01c542044e440780700c80030034800d072035400740c1139a0201404018001e0f03104150001d10245002003ca500490003001e5404881030440c4059480e43c01103010703640300e80d100c0c1700b0f6480700008010989900c4c4541e140500021600320800036014054804528440c00a4100c0f00d8502150b06441c407201c410144010041000103019034445801e010822440610000002d80141503003062001808105031042d07c156403070010307040e1501743c248401441e50218110921421081300340007a004652258441d148640c02030009103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 730927895 1250 730926645 730926667
    0x70f0912110112110306040e010905011514010507050309040509030717030406050903070506040b0a0608160801060b04062102041e0305100e030712090e070c05061b0a0e06091203 78
    0xf40c030042c0400c515458494801240042c0c0f07003ca0b50400c034110707404112000450401c60041c600110010080d620306103016041c2809900150b08460314480c0d01c03947c1010017001500c15104240000b002074108000c0c0620500c0e166000a800103448030841c0d040460550300c8103828039696200c114080030120400c01008114001e00783d1004004005e103080c101c0070340e81e40341d80c0c900150000b4440001500081c2e000c040950040300240500411122010300081078881d081342e25010301443c41d400c04d50007142d2100303007000f210210b4111b03903540030550021104a010f580c041580c000500b68003088001481145a080c0b0b1600d0303d078107810100414036500e4900e240041c01210744a4a900300811000c140780301005031204179800c0041c0442115042104a038540c0054000803412150081800301030381c1e0010030302e1405071184044038002d440f6078240c00b001c207800c0a10200400410408054424030540038501084e070050607581c102070b1400d0008040c006592710750749580d800030075504801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 730929145 1250 730927895 730927907
    0xc070b01080313090612170c010f020c010515101202071a0910050c040b0d150303080405010e0a081c0b04181a060609102d02010e06010e070f09121101 66
    0xc0900d130404100c1c4520b401c8141c0a4400ca0070005000450000a07101d64464502c0807241d8000041d00200314250b038a09111001f900840c100d011190710703010025040640300c42d206040d008009065003100401060100c804542e02d240c182e40d40c0740c0a22130f07100040c00c0c00b218102e000d400b404110300036103011801715203040c030b5a03010741c03808500302014401303951030401c115001d4609200845956140941361702000d41420b000b01480d03d03540c141c0000c1410340c00911203006c0e511604c001d00200d002c054150f030780d0389894040940040300401c03034208105010740c0054010030701c80d00e0210f600301c01c4000007001c440d08903082d80c0d031081f4440350b2841003140c00c0946290034503590902e80300301e0411308003184030b50140d07188e4540201d1800310011000703402142066916001108880408594540d00822444005100d0000742d0300f00407004141d02030100e001416515601c0345c191042e51051000c0720400394061009040c060740301c4000c204e10094540d100d05160240c0781e8000d080981c20001800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 730930395 1250 730929145 730929149
    0x20a0e030f1f1a06040306090b130209010b030601030905010c180e011a07031413030c05010305040b040821240d03051606140a050a0605040c12050c070b01080313 71
    0x307900907803240c500c024614042c03942101c5030380c04009049440307005148007041103280312036400f503004103001007000031a40040804910601c0d003440703a41c4440e180581c030030a1100c030003036200304640014040101480c1c05503611000515010801d0342558035142d0841d8800d9120500080384403400d28000035a14070402e00800000202082c070350b141000c8120b0b070040e00a4841c0b010b840001c2d1324000d05104201c14914545041c9005a0714a41000da0102d500c1052000301d40100d03044c48000b85d190300a114092080d50001000c1401c0d503160b90b00e0503260b501a00481201400071071199100d02114500c06105011100c03004600d2840b96601b0190f40040100c0d00d84111b000350302c0200000d5008007a01d120015080141c0d5503101c0c1490700c0405006e0300003c005101505c00200030a209482e00300380d001d0341c0c0c9030310300b040301c1ca8544051100b640c10440ca00740102d48036480e1028100f1700d9500196102c1e401c0383d180b43c2041c059680c2c02007200d82c00c2c1e200c00d442d584007083c803004000c1061382c0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 730931645 1250 730930395 730930423
    0x702060a1a03060402100309140601050a0609180f061703030f06090402030a0f11060a0c0309050307300221120307140d1d0109051509062404020a0e03 66
    0x700c8194002070f0351408000c2000380a072070341d1409604524069004800c949611844003400748444039541c5a03110024440d20780700d000e00c0705000030400e0254030103100380d1b100c01c2c0c1059010903680000402a00050b0f103800c8185540d2000000c903c41a0101003035204850405555281481402d01c83c220700e002e402203128030026001d110060740c001a00c555141d5006400d221503800d60305010311021009080e00ea08001d00203069603c15511519100030305220791074a44460b51220f091580e240e0207805000d01e0034985c0a0fa0421078030001002143c06034508000000c10003583d804190828812007940800d958503106195003030005001004400300911409803c51038a11001415640318940c03070b0404000c0000c410000503845d030410308c3e005646442e003c14000a1903145402403d2821050b102409418000321506610800f028014101d901c000c090548401132025804e04903041c1c0e60800200500445240c2d813030354005405000e02a4840c008070020b10800c2c5402e000c502c0c88268 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 730932895 1250 730931645 730931681
    0x30f0a05150c040b03151504060810050d120201060f030c0501170106080711030c012d1b05090d1b080d0305040f03051c090605070e06070b1605070c031101091d010608070c0206030702060a 82
    0x400310380c4400c11601e4103b41c21281000d2070340003080d400e900401882c2c0005411008142d008070901032a1160b9034215803083ea5803112201050021244525080c011000056109008030700407520420101414a0180003543d190580c210101402c44a031240302c19030030320803109189105080201490714090f01e000e000c0c0101c030604408400c401d0300d51002d80007484004902e04d81c0f01c0c1c66045550000036844541841e0b20000705414a0ba00c02203442100d17500d01c0384409041c401840f82c01590f028607400540c1e4040740e03101d03680a03500d81e00010b4413201602c80c80c5200c903406403403d0084689050240d0400107017030030441c1c00142600241a0058000e910030050000000c0361103810700d50100f21400040c0ca070301107240c030441c3c0611508902405052901b03001100340045098a1045810240c98841040d45e484080c240251902e031140c03510b446990b0010000350780609460350380305025184c8014520100e0303000500710340090380c410005074011005c00409046a1080c6902d1800c10382c200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 730934145 1250 730932895 730932899
    0xc030c0d02010b0d05070504020715090b040203070618090e03090a0902090117040320032a01060f030b010306050702032512090f05041a030f0a05150c040b03151504060810 75
    0x150751b01c0080c8900b40c0901e070700140000500c00344a1211004c50451001441150784030f0500c090304442c2a01d09910a0090756030010340319000d414040d03c400c0e81070955001d032601e000c00704170040004c85040b031902c0c002041100c1c242d54510a600002d81700f021401030301c40c1d40d06000100300c089400064038807807903054148004241c1080d415109961040c1e20194030111048003142580625030290540203200c81049040d0000811403042000c1442c00803c13605903907125028035080c4a100282c02e6800480050000c20016000240e1012090044a02e010044644040e442c1c0c0c0da2220300070180f2211030400c040041d0340342c17030032000e00c800d151010301d4074242448101c0700f22a1b841214030440c0e4a03103040c0d04078032034007600f200f03500f80c000d041d40c2401440b9a0115200d0100780070845040c0034041e0b4500b280515810568002d0a007859101d081604003079402a60340d03c0a8900c0c04c00c40380583d0018500e685000034200500d81907503095854500d00320000e04030030409807946040c01051481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 730935251 1106 730934145 730934153
    0x21002131203140a17060402041a03092506030e070605041e0b030f0106120504030e0d240c030b040207020907050306152802031e0309030c030c0d02010b0d 68
    0x8402d00d5503506d00410040f072183c1d00541c040301018201da45c146203480da010f9544013002000301c440303901c0c5401c01125803c0c10100050600000d03100f0a005c0144d15016403a02c0000350b0700105041c500740a0040c0081c004e5001c1e030312050005103a102c40b0b01e01c010444200418010080555a050030244845046001d002e035001080507103440d0300380c0281902c6030f18840c0d601540c61520003901e00c0100036858814240564039940c0440100800480705078420145c0f004224001a0b41c6009000c00f409860014001d50303c210320600c01007000d0b84400600171b610444501d41503559907201400501c80050030240d02c903221320b010403a203d07980c008403080440c03840f404810350b0600c0d42140080b42d4910170b035108403a24064003140f61a07004901006903410100c41c00c1500d050803580480c091444d0010b40400043d948214400c5100507020300c00c007800540c0c191900c0084042c42e4803 = true := by decide +kernel

theorem cover : BRFrame.Cov 730755395 730935251 := by
  have h0 := BRFrame.cov_init 730755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 730755395 ≤ n) (h2 : n < 730935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
