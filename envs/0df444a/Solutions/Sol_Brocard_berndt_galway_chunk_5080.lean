-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:40:42.377564+00:00
-- url     : https://prove2.me/submissions/bf4d2ac6-8944-4516-a7e2-22b8fe88db73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 913489208 ≤ n < 913669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 913490458 1250 913489208 913489211
    0x31b060206040311030409020f07151a1215090d0206010e04020d020f0102100513020306090123090a020618030c1207060c0f08181002160b0c100e070906080a02090703 73
    0x1001103400c020403c91b00a84141d16055444000381c2d1441e58550b007100c04101d400407158082c4250b1352100e031080da52400b01810740547e404c4111014130120034164106140d80c1d00030f00b0b8030485c040d0040ca0849014800050080545880101000341880010f800031400405200140000f40c1c1d28105641c040580440c1c1e041e0b10048188010307460040041500384690b410042046001a00c13000c034011404d0081d41501c00c19929046810300700c0c0e8500c2c0304a111b89a0302503400243c011301c2d011545d0700101d0700c01240d0402080703800244181c0c00001262100041c040e20ba12010300b014000d074044c905060740e440c0600728602441d2a1580c1c41360140c1010090002da8080034001e021300f80301045504203030015900c1420744200ca04d0300c40c43d4503000d40038001507070b013000f0b03c540b001449904a01c1115042c640803802d0489801040d440007843c80741900c902080e40d0641c210b1880b40143c1c169011000f42071186c0351174000015038105a01a01903504615031200150310707949000780d0b02900301c2c6070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 913491708 1250 913490458 913490477
    0x806100305060607120e030d020304140126060102031b07091a01171b0c0627031204021810050a1221090b0c0601210807060e0106050415031b0602060403 67
    0x80350140a08203a4640c9403080100b840348c80e907000700051058a010482a80740064154019282a03e10480004007003010301d040900b600e2a1245481d000403051040c0c0746440072070402c6d52000300003c40d11385a15003144004000107026481a02020417207015002481e081100c00a00110380c092525111200441c0010307200350000100f9049540750398085540364804600e031996101400c850784000101d551030b6810300750181d10241c0007485c0498004500d4400c3c00200d540503404040c0c030882e0400795155400b01e0050000c00101d1040c03c54241c00403142e840c01c000c00030b003810380c2d41c801c600c071801c03440800000c5031944000541c8007a62550080f007982c0c03080b40c03c594003603003588400c12020300800c1c040c00560300414510304848001c0e600b9100c41001c030320841103154001c1070040c440841003003000000b820316000741980701c080b0b200000715940d881010500791110224010400080d0301e40600800105120049614400550561a06040480c069912080a840901403140605 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 913492958 1250 913491708 913491743
    0x13110f0310021209070302030d03090203210d0501090b0a0e0612010e100b0109150c0311061e0a02070c060507050102040b0a050a021b0a27020a0806100305060607 71
    0x69011010510290865400e00084000e0100070f4000002020032021001c020459a210000342c200c01d607a00200500039038107400703205900a25404c08126054003c1501205083e500446000340c06041d800b1080d50791030b2000000022100140c01c82030304a0b103429178045141e11002403050076101013070f02958854948400050001180245c0040c00b503013000303060003403548040381c501d6226128180034003e0107101001502c40340c4260045111241c140780840300e009105411a8a006001e402d11070105403010001e14240b403411240004d014030213500034101040c064010070f602c0344009500f142006081da0b0743c1c0e4a1402141b01c0c007010040d012600e84d00344074080d411603005044030024540d4070360707030007401401740d800014600016010740160b41048045401d410382400c0d0005014040c42c504104240d10100e82007109000c10340c6408402c0c1c0b800a0080c4003c0c5509801a11400365030300c0c00351f0400610301b141d2182c0e98201402d050034404030351035003000d45910302c0e404807400c040010501d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 913494208 1250 913492958 913492969
    0x110f07050c04050a0b09010b030601230705121e090607020405071e030510050108040b18070f0b070605060a06020307060c05121501031b080109020703090e040b010806060103051311 79
    0x640030941c820701d040c0c2413140406041e80900032468050319010441d03a61404008858001102c240703000c1201c3c2c460501400d002c0a405600405d138440e0a00d0030507a013515810b1900c0c8141c80c0361910140c0004400000038a0340e402c8918880e0804040d518100940005c16040c0c0030700d040c000e0040e0b898601207044140180d40046600001480d8400068102200140035110566a04030070f60b00c1540007043c55449441454429034000000c00c9281e11745443c50f814032580180a14020f0082680c08100201e00d500220000e00c000e0300f4a03a15039072075081040480e48042e24071031054448103c2004040e80100c1903502d0070f50040c00c000340c0c18001c0319090303c180c441d0100301507600e0b40840801500340e64a808038000c03004203a0341001100507141d9a00201000d595130380c000304e00000010018620150003d09900d03100b880c2c91602665140c0d01c0d00c4101c2816101190a5038001d401070049407403c02259a100c042480c09002d2403c107900780140507441100094403c0c0b03da44002210394440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 913495458 1250 913494208 913494223
    0x10501090e071806170604020f0f1e060d1e0f091a07090314031b010b03070308090a080607081902030f010e060a05061603020705030c09160207050a0303090501020d0201110f0705 78
    0x1001200c17041c1c0c601000d040f500c849085604a10442c183c800489580c20710080c003407504800070700b03e03036136000482110401c0402000021980400200f100321403c0204c0d0160018000e8080a40c0c000c1c01c1c54044080255030107040203004082c5004203c50100b0019004580e011024004040c0d9549960030b0846507010340fa000605040040b55048460100000041129400400c030503007070548a40540340c03d840d03411080c240e150348440c0c3c09001003845080281204000209966151580e4000542c00e2000483d00f034404542c1e10420415a580005d18000d40303c0310141d070441c510300d09900e0607034103080e040c064a80025001e40014103951544401c803005410002c0c4084c5c0ca480708110108840e105201c2c0c128014010303003d0000341401c000802d11031b60345004240713040a50701d0800a61811345600307000400c6114045000805407100ea1440300074500036035522035082c1c2464000392601d0f501480e003270b04681c5070812501201c4030359425640b130141c000c3c072800e036036500509196181595 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 913496708 1250 913495458 913495469
    0xc03140708030414043821060405060f1b090d0c08010c0e19050105030c0d06030f0c0b0a0807030b030a0c0902040312080405030d0f091211010501090e071806 69
    0xc0018013042c44a007100001d2400e03582207409200c8080200403414055003540000a110454105420282c8006804e001100540640007e1f94400c007180300d201c10840300c01030840140c10036400c2c4402c0c041e061001c0d90784403610001d41d900c141040d02d102c00000c11071741d4170b00540e035102040040440c0e8840c643c1031010781e04003152402103078075900355500070310151003140085a1004191031803030820b03090840b84d5540c1e02e00e128404a15140054070b0640c001000c2e110380420402041135401014805c82000d0342c01890110340e074000da4902480d48400c1c940001040c08420b100c0d182949a00601c001c1e889485490080703101c0b20481d01003072a000300d00a000380405c5a040002c9104140ca6001c0c2080741c0c0150b840400c4c01e200103000382e81c400400d94024000750010052807501e100160080109441d8040c0c0003e039901d02501d5140d586125004034800103003640b081e40303035900303000d0041d0350141030854010440801100c9941e55140b07113a12440e903820003206a100d0074141e00b80d01520003460f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 913497958 1250 913496708 913496713
    0x80a0519090507180b0f040506212104081c020102040f0b0c07050108010302012a06050705070b0a062d0b07050a140d0522170a03110a0c03140708 64
    0x401d20b4095101d0405029011001002c005001c0a81d107842c007501041e484050200d45209a40c1002d200190000078000d940180001e2a07107810242d080b44030b0160136441d0000b8100450011704d2005400015005100d01c0c803030180402c0c000000d0203d220714045038602c078101103c181d501000d9004e40121b078401c0f10318194150000504840000040140c000e03036505131a1000d44690041d9169502804080d000480c20000706540c4407490711640c0519400301402d8a052415950b20015a0340854a00300010400f14414081000080b1041d8000300032a00c2030145d2030410440102429074411980290031042c401402101c1c0440324501c0501540c00c407290303550000f070604943c0c0c0c11340124102c42041111007109000a40404c86030000e406035541c043c9071040c1c3c0c0c12040d0100d020b6010781981044614400254a903e105d03c080e40818141c004d0070360300c0c03101d04000c0d042c00d415080c6424103811501c0b02000284580310b01c003003078a520101405012100100311850944650460011071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 913499208 1250 913497958 913497971
    0xd0b03150a0c1103180108070207030503030c2109100b19081c1107180e06070809011a09060105071403160c0501020d021b040f15060f0c03080a0519 65
    0x140e042d049800c210030360b5269014080a0001c0a0703a40c4c0c8280300c035440c1440c0c604040380c1c0075988910125500401c4034811280c03130984a0700c0b81800c40d44240c2d01c8080ba010300160751070b6080e82004540c81c0018860a24901d549401d000b041d4680321400c440c804120b0f500e51000d0341c1503070741291f8082142c0c000003002c1c0c2560785440c100c0340d88001c0d03221481d40840c54960b03030000152081d400c1e0207100f031060002d04090751a02c0f0710b0082c8030726015410315100b91a08030790321011404001561160085a40c0d1507840d051a003030b8182141d00c0c1c2d4058180301c0301028490000e40e242c1d130300b4a40c1c010200386481552403285080600410084400c014198080007039800e66400340e201b0313042d0425000701d000221980e40c550040e65955221140100035030020803450035400d0b1628030f6404d01072005040070034640e620189040c11102c82041c040032107404d0f480244141c6901519001d00280d49052003440401903840141080b007004040d100c40a032114001007410b0240c5043c00c3c4040c01381281400351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 913500458 1250 913499208 913499221
    0x108070f271214010e0313050105030403050c101a0109050a030f020612071106011202030a0605041e0302070f15170c04030210050705060603060c0706150f060906030b090c0d0b0315 79
    0x1581c0b00740780f0702e9195609102c2c2e03071030750311802104840510a520329040c904500e0000190b800b0380005100b038090000078040300f89020b07810701908a400328440e030001030a0352280c020710802c080c044d6030b0358100240e1310740600064480c060401c0917a60458400c071f225020074130019805208100d43c04c4038181454003404650742d0806d043c0031440d6000d80030740b08581c2c0c0f00e0504484045513504060f5143d48111741c40360100b01c5030b03400182c1142c0141480624284545940e07118060304030710490040e48241000c000c075545041c500e0003e0280800c00003004043c1074070003841284115225030004044801141020516004880041d5809080005d5080c0c03600800352043e0882c3c0400d60b46801076100154440c45d010551a11641034401c545040100e0307501c901d8001c20700b00c00100ca480034114008a010741003180e908004190540d60003280d03034141807006061b00c8280e16054001e159000c1030111481c4d540c02a41c4c1d98200204000070b028007600c00203494421a0034000444900b81e0003032021 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 913501708 1250 913500458 913500473
    0x30a02091f0914130509010603170909093c07030c210203250b28030903020a0209060418080c01111c15180b0108070f2712 54
    0x410229466028002d55280d80b1a940c071103864207066407003641e8450780c180b0084203500035500650900e000003405c544a0b51040f440b524521161031070510003058080c014034040400f035030301c40c5850f0b0190019250500351040205000c550080d40190715205c07040c0e81902c1105081c0400300386030308560301c003652070824281405190080e280f020281407500075071000484503031021982e000d4000c14050421407058004110b2003000c56071140c60400000400f860480c01802041c00e0340320445580020030380c00501030b0110306c08503030b0601d400c2101c0d080c042900821080401d0b5010b903000c01803035a40c0400036000302542c4c84042c4604000500c408144405a00500100324406008002d6508507409408030340c0902c0c001c0800390240701140c8455185590050380f041d80c01071440230125601c68284038485402c00e0090240c0640c1e6810070b0100b5a8070580c00d03178210071542050403d902d8680d4000388086010703000301020051000740702c1c00030002c14081d94018903000c241010000c0c0345261454 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 913502958 1250 913501708 913501759
    0xc0a05151602010209030a1115030a0f0e0f03030a0c0912031106070c21020a080309030705071a07060507110313050405071b11031005010e090d0302030c040506030a0209 74
    0x980300d41003200700540140f0032503a0205000b0010200101996614004e44426820b0303a40c0206640020704104c0182c4400b03913001d41c0390800040341c2c0000d07002c0300e4403c40300c044074020216448600010784400c7c003c8200c0c0e421400218000c01da4500c244070035650ba0000c0d5200707000084110b031070f41d0140342d80b000f907412800f90840f040d145036446400c000c9030900c1c6100405001d005080e407848076052520b21682540803203d00607a000c01c40c65482e0500380d50030840307400d400342c1c000184941c10001c0601c074090190010302034070134051460300f004074420301900304000d00c52559080071038201806805040792180324201103e503544803820351407070400110b100c0ca5010300d041c0780211701c18a01a50311000240090781000420301025100c041140b24041c0500b505070007a10f41c03042c0710034014020b09029003003c0740307001703018200b03000002c1c42d0440303004040c0205403040c410700007480504030072034044482c00c4406c941c0f0ba45904803003400071f208143c881a40a10002d0402d101881150220f4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 913504208 1250 913502958 913502971
    0xc080f06010905071220030106091401050a080f060102010b1903060605030303090c06131e0608090c0f0f0f060c0c0901080d0e2e0905031204030b010b0c0a0515 70
    0x200d420740daa500b08001500d030165094404183c0407400500415116445103202e0709810755041c130300355181c4221740a203030300030307003101001820042080c8100c1114402c1161750034400c1c0f9200385801c50740c40b0002c00c042d2003d450005541004004540a030f8800d400c12001c8000003070402c0300104020018000601e45884120344107401c042c0700085601e000b0064034401da2812000c7c1c40e0841054082000b80d9111a010b01035000240e8000f081c040c00403080c0384640011140003581182c144840609840c07402468184560b014514013000c40d1105409003800117420b0710519030120400c0001144c00324210442504210041800180000c0001d280c1440f00310a07983c05c9000d0344c03500269500d032940501e04001083d086400e00c0700d01d003426040d123000d1924103144107541c07008a004036003882103268403038070008003c00d0040c0428603081c8a00340100101c0030245180c980b03990307980404c010052059642c42c05001c9594010340ea005d0125121a42c0d00c8001d94208030021280064602d0080d100c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 913505458 1250 913504208 913504213
    0xb04140d0e040e0c03070b130e09010603030e040213151202070b04140d0f0f05160c03121b0204020d0213230103020703021b040f0e0c0f03060606190c0c080f 69
    0x25001e0f60710210380341c036040001902603c035240c10891f5601050b80540080700c824500e0b120300041600c0b041c4a100d015400280000c5030181c55414002e10400342240198400d500c10090610111104e016443c12500c0c44042034005614a441c1030740c01140c24640001c00340e00001300b060421102854141c801e034840c0d48100403503071640011547d141405520030000c500040681003086008050b62120400a842c2951826903402e54101e8130740070741001110105101c0609004200c0c8004d5003102200c514035120900508a0001c5e01c03004280440c041d0040b0360016100c05254195011260510180207202ca00700e980c03840c0094002300c4846420252960b5030302c4078101588a4000c54045540590040c02c0115188000300c0a1810302c08103540c1c810780d25040c844414445005210b00040c161028084040c440d1051082c0350010031020303440b0341c10090030880f55665000a961505044518040c5107056a440640d03201040d80c03000f40c0107101c0c1d601c000411100015101e000703504840700303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 913506708 1250 913505458 913505471
    0x1218040c03020a1d030a0f0614070203090d2004110304060606140909070c2102070512060103080d110f0c1905070b0901050d15060f0504030209040b04140d0e04 70
    0xd044040303024460410300001c040010020121a03c1e080840308100300909854118100d03660343d052881170b881003165010707101e040480803400e162500b164030900d01d0000e07602d0700e400c1800242841242610041c100e094504010a00420f540c60107011004054400c02400b2000820000381c0c0e001120101c480c0c6003041d0004c90310328480d1105d2507c0e00c80172080315080c03606040070070a8010004280c2d908003c1d09182c2c000c0464400402000e0103a5400d2030030820303c80614000b030400216400c041d0040c07804a0349a40d514030000f0f032483c1103e402414280c1c0321a0b80508040c0600010300c1114550a408141d0143c03915042c001403079000303608401c950040c80b9030102c2e41110440071302c0c06452600461402c000e0700750b2203c001e02c90483c0515140e4038080c80a01005c1c06c0f04c00c00b004110f448600f0020503c070b05500200029410201d80c10041e080a18540c005880d083c8002c000400a4203004003241c1003040301e14402e003400c000402959a0310422010092440b407004101c10f00c175074240706 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 913507958 1250 913506708 913506731
    0x903060109091518051605010e0303030c07060e07080a0302010606090519060f050c01140405191e080904091208010b1206060c2103100b0313020111121804 68
    0x1142e50310741c0d0780c84070b2a2600080c0c100e06403c01002001000d458803400c2000c0d82000450501109010100b6000060240d0742003200051080310201d117054040e5104006010000b9400340680308082e50100c0041503840b048100282081a5984030856612541c80540b0802d90103420a80544040ea980c05500968503010451001303007007048142001429802800389c80d21681910f88031240c3c60610340d10700700c0c4c0e14030814211500303121010071581c1d1120a02c002c001080c00907540c5003803d00b03c2c105258146481c0c1410100e5544070303031004041100c0c140d008100c0c181064070381445000b40100243c039010b040580900855542a0f40002e20740c200103c0c641003040700341c0329103070a044a40c559980c1c3d10010700070b1a501c40002c6103030503c2941c0d410200d4810913501400002083c00381e10f078030703400c0903075140519000c19000148080014402c10902240c807480713007084142c09107440520a000c449145041400014040c110f100c40003a0110045c0181c8201c1100d642090b00c0400c607100104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 913509208 1250 913507958 913507961
    0x15020406021908071401200904050114180613050a020c07080708030406081003050304030c090c020c01082806080318060406051e0c010f09120c110114120c0903060109 73
    0x400c002410f81009120b0707040802d0482c00152a403090000c00007943c002842e484920442010a04950010000464005c1800c06000d07881c01032442c00301103040d030803030200019642c84082c0381c4003540300321500c001b480c03a59407002500500107042e00d027000385040880c000c101075840701c4280c1c0003900c50300a0000f02110000303140c00c12100c7c842c4c042d506141c00c14000301c50354403000e800a2158203880744044003040007031006000440c420950001d00c149408900c2041c1d0f00941c8c201340c195040003a4184603640c1101c4056031240d070030401089114001545400004401107414039594034160004caa6410000300800f19824026002040c0d400030700204900e41c0b040740900070000302c0c18007481e19800c0008000d040400d5002511605000c0690219800c403040c940300c0680c42601c4041d0343c0280300e294003031201a90090b2800c041d20f4040e54484400c040b10300691541004200e00e40c000d45019a0001d54072011200403440ea41420701203143c07201c0d074112000a51107802030301d00004001255 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 913510458 1250 913509208 913509253
    0x3030f1415030d120c0306050a06080403090608091e0a12260108030a051e120406050604020c0c33040e07082406070f03080a150302010c1e1502040602 66
    0x1c6590380e490b04d556414102c4003600b95400900705242c2c4504c6d000c01c45582c1c0390f030360070007800c1c843d0341e28a410700d010708005000785455804031081c03001d00c4050204030040800c20b191103c494051040c019203c0c0e026031032070240090400350050000b5149511280d90005c0a06441200000c0659848007814034480306140c0a02c1025040d9004028100c03000c0d000d00d02a00130302d038540c850b448040c000d4410b800c4c1a07030700032140b9002c0d40001600300030130014140301d800d401c540180c50441c205070401d08000d0b43d8401c6c50005a1048012840b41c2001d07080f4401c400307070201c2101c181c0c60310504c048a1054216000b5008201e030780b908100c00550b40174403030101c0030300c81c0742041c0c0c0800e81c40592100050200d82408905900584101b0013003000c20321030b41c520340400c2e110765504480d070700c1c00c40f4041040740c0310511800c0111100301800c00150f07078009036130005640c0180c1a03840504010815a0b001141d03242c008020070002000004c2e4298203034040c200311281c070b4099030707840b41c045420300f03005040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 913511708 1250 913510458 913510483
    0x313060c211b02010b180c07080f041a040506270303040f090506040513080d0225030f030e0d0e0a03050a080318160b130b0310061107030201170403030f141503 70
    0x2134a00f001b000e100044002c8542107410b03504560310307000141e141d03030280d54002c0d0202400c1c1e1030005410400300c01d40070f602541035946030300428181418800011072034400e02c6040f030220398070101c000414451550500b08040002804c0300da480303a56038a000700d503030820b03c1000340f043d02d082c000607513500307003401654800e28039040d9000f01040180d0315012260000d4403400c65841e400e006070620243c0c1000441041c031b841e6101030842c0181860020500c40070001107504260901d0888182c008001980c00e0703140c20103042c0003410750010804501c0040c000e900151440c410f4031001010f010901c0000d6008601c4446101080315910700d8856031400700f480e10903005082c001082100b401100045c00d0340512001204142c039540705100c42c9240c00c1038030030a041503411001040100d80050403038000034148000350400074a9a00041c021400c1c40941c00d0003590741030000307400c26119038460300320500205000c100c0080c2c06e0243d62140c601c221004101c0440194135441140340005200c0002103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 913512958 1250 913511708 913511719
    0x906030105010503070c02191502011103010513150e041506081903030f1b02071d1f030c03200f0d030e0307180207030e01050313060c211b02010b 64
    0x920700701c01111640c0c8000e2100081090070b800300300043e0f45242c42c0f01c2281c04800d01c2c54102e94204090401004400740911055a03d00161540f1551400b0152411a1404c95144c24031410410092002c1c240d0464034900a000c02d41020602461400c90340e406640100c440c036000c1250300402c44101c507101d02652031182c1c01005c1144000c1016904070280d54400d00d004110441c011388030320705680c0d1000700307102c0d86030307907581c003411115810002c1d48024030044096034050492030140d021300580190440c0aa03008007514008003000b420700010080d640214810a02603407420400701c50020400e401c0b10700d11a40000350141c1c40c2458806185035001040801c1d81d0700c003990161040e003409400540c041c0071b01c200008005040400c5117402d03001400b8003507074803081483c0c01019110302000c000c5c1800b0341070040c01003141c1440503019411b540480300145200403100300781d1301c0280700c0400e1b08001e41440c515406210a03608800e201100c826071110300048240020f07401e0307d0355540141e8100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 913514208 1250 913512958 913512961
    0x90b1002150414010c121a090402060a0203070c171903021005090c040608010b0f010f12020f0904020d0e060606041d0c040812040f05100f0e010306080d120f02090603 73
    0x9007909030303680051051403200c100c1d0407005496425030703100301da01d240031408440420a06481030f010380c6088224450800e2011400e901c0081e8408101400c00390141d807010848150b164020022601999001148000701c540e07550b0b2022580c20440102016900400d20204041b1011070f5190a11a40c96006040d00350204009100103150090030b101061040152107003d644580c41034070b0280c4481d10000c102d038038040d014010720b0613000c54994101300e05600c07900003443d80980c5410f814901540051fa40b000383d070031709050300e0040140240e4418800541d004401c50749a01504002c00400c050300c01d25503605080181c50f000c0c0c1c1c40b80c021900f03410b10514280303034090314107a5801407800c1c2a09080c1500c1e090000c0c03170500c001ca150740d621000082d0501a0010b4007040d032009100858201e452001140d1004180007140401803052281100c01c842c0075070700039044031010b0112a41124034054010800420685000048030181840d2004518080e81d20b4001c84800784009440d46245 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 913515458 1250 913514208 913514233
    0x311031605120109080a03090b0114060901080406091e0212010e06070c030201200903061005060706050919050715050306060708030907030f061d06040201120507020708030c0601090b1002 82
    0x801030b1540010b0555030382d802440000c19040c0074000e8106c039580e00151595240c98003d03190a0180c102c50061500003040c44115982c03003040342e070401710a20b0200456291072074503038007400840030020540106100b9030301451912084175520903000310790b0365200e10700d0100340074222104107000319140c4e003203400010381981c013034600c44118070320a100015042040c200301015905544004149940c2e000030b0079074881c0b4040000582108040389000545860140020801d200300d1400400041c1c840c400a40e070243c040c0180c2e14903d5000741c00c490070110303a141c069291423190248452500360103920b48080340c8104292841102e002c0e00d5503107000c2e860349560427903810007030420401e84079252020000926842c601060f4a10403180400d45010000e88805940d106021a0403694400800c00c00940e900c0310341c160359030000540001303160302e500004a081c000d040c0c0140403903110010710400e03a402c0000e8064100d4020300c1c0c0400c0b50b200f00400304064040c0708181c560060380300c121130703090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 913516708 1250 913515458 913515469
    0x6070e010504090f0e120a02030a0e0612090d180617040c05030304230402030402010e0d0c260c0303040501021c1b0f0303050c160303020c0307021206010311031605 72
    0x18044050601c14109543c40511070141d0368481d181d4044103072a503405030319040d0304100c4000036598940c8081d050281d1940000c0d13490003072004403c20400303a000520811b8803200204c610b258a40360640c0f0181c03900e0b49426681c2c0704810304c1500000e50512010828402224111f801d840079230b0740b00c0000d0b04440c46c01e142c81003000341c401e540c0710304004000182d40e80c0402c018001032202c01c01030701d41e854010780c0100600d224221013a004034010020000141c1e803150b242c40685a046500c2c6400a49074103020341400d060f0b4000050380c05140740c04160102400503000c003071802643c00c554110005509260b200d000d18404d01d4050b07408002d440d003804884000d0009a1441403400d0506c5002d0440d50329240d0030b100c0416102c11800d41c6080e02416810701650b036000d800301501c139103411541c98580f400d1700b050703846c060201580440d0b0316540c0b410600c2101d100e0754009041068103000090025100c0b2000e110071200c41425074010380c1035040c0070400d194816108005165520303d490305024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 913517958 1250 913516708 913516727
    0x41a0610050c030d06030b040b0108070501090302061b0d11120909060d050a020d0803070f1e110c0a0b041809030c020411120f010f21030e0a0801020a020606090f04050607 75
    0x40c180d00061020451403502417040c0c038001c5000d1084032400b801c080c00c02111010040e00440d0058105800038801030b60040c5070407080f6581660010f6a51111002c01c0c22076035205240200300e4042c0e40311500c10746030301a103280c20b18254042a116484101000c2860511610081c01d4014441000145440c580b01060346415030260080e030ba000d1441c1d5000525800c428030044450f02c102009022280b07910042c120705501d414141101344046102c0e401c00592000e2860309c0030052003101a007641e00d0184154600303450058400200280c444500e9500394020f405808000128108078003024000c41c055000e20a8140d16180d51040c000d40902014058080401c0c442e042c1c100600718000b08a190658401e2504034055a003a50400200240070175681d813108032600f5005041680d10384000b000c079a00280c0c5400d1450006268a0120303003802d901c0e078081183c030b501c00714038800d003203802281d03240c421501291100b1043e910114100380c0500140c07000341441e806940020758003030283c038840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 913519208 1250 913517958 913517977
    0x20906090c0d05190605040e0c12030c160905160e0f0d1e03030b0a0b040b0a020a020a0303020d030605060301150806150c010b100302120a150e040308041a061005 71
    0x80b032400c44600030034019107205071602c6190034940c1d00f0001c0a40f81c00d10a640141c1421141030200012592070a680e803405c0e0844c481c4101200c05d4a03a01c40c040400c1124850340208042c0e40d2499105a114002c40c100d92050403202410000001c07904000604140800e8070f03282c6860b040110a801800514146c282c2c01682103000a0501e07000300d90300f001083d0210303540d03011a08460441e441c0080c25602a070000d0303400742c16406814480b41402c0401d4405841121102940700c1028000413441c0c00348105000e50071010500020050660100e0103e9a01249860500c01d8555440500c035583c032003445024851780701710300000b80e42445034007625040b42005148551074100b0104641c40e60740b20030b01c10324107a907558030750074070b5400d02c04482048100103003030441c00c00391520340c6107210900c0288001d00e941c2d074410720701000e040e1040022018181880000880340740c54940907080e528280e5003501e00300004401d00c4014140200b100d44101e80180c030080c0052004c81c0705440c1c0d9003054003003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 913520458 1250 913519208 913519231
    0x6030b0406091103092a040509011b021b010801030305090121050a02040501020f010203060306010e040f050a0303270309090f09140105180106030b0712150e090c090402090609 77
    0x981d03890b540642c460800d0341e441d00c2541c900300000751900d0b240150400349a503080e010307501a80700300c2c620102c141d110002da4003c5200c3e90b4860b6400e0041090b1902c0f442501c881d0000d414a965000882a2011540007904602a2039000042d02c00030403d10000f000a1402c010003e03c40d48511060030b0b811444401c840d8581c90096050310503585c046842e02440e582c08070b0304000139a41000030480c080d82c1c1e803000310b1842c1001008030741c4a80b0705002d4032040301c2181d4085010005172460405900c2d03003060566040e50100d160040107031510907202c1180f40c1d9a5100c0203210340400d0084d2a180754503840d1011814908170b80d2402400c002980385902030303901c8505001050078105004501010350000040c00e2400e18840204a5600503012059a246c40c1003400015880405c640e089589414590056004a040300014003014000920121100d200004841c0080dd079070900540d07161007074800c89d00c00c1c0d80601000440489001e58000c4400002c1040d909000c450907070000c180080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 913521708 1250 913520458 913520471
    0xb130308070f5a030f02010605041a0f1c0804030212160911070c090c03050f0f04020609060f070c0512010218040b010c0c080606041a130510120c05040e030c030406030b04 75
    0x16004940f203840c00a074041001243c2c48010b041d07080c070812000d0601158208a411138000b040f075014120040900e01a10000341e00505030b90301c122078401041e140c0e4407100c100e1041441c1c200180c4c3c0103440100d000e2610ba441c100c0303100a002c101031203568542d1348640034841c60b1030b40c8200034001c94221003c40c4a02001001c000c030380c054030410050584100045000b000201005088a1004054580001c0800c0034411860481d01c3c16940098048840c2c2d03444954841c0000c040d486100000600b04070005081801c104102c0501e404459080f940448000d404542c6242070748142109074040301c106190b0070405141c542d10010340b01c041850050100580365070b03541c1e20f00c441608961803550101040000c24549800f034680a8448001c4074240c903e00c01001c52407030300d0902e0030301d12180e44540005000c2c20800003110000d0029601d80d1040780b20500300041d090346140503040c001c03402c00351440401071000040300c0d020084000118601440d0680840c01402c252683c280d0184c1c40301d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 913522958 1250 913521708 913521863
    0x3040803071d10080103050607080c0f030a020d090629061e0904020c06090606010215042003010c050a2006011203121b02150601090b130308070f 64
    0x2120602c0281c803d4450103001c0d419810052310701350008018101300300300c031004c0220002d00902500c500100b1941c2c030303d48030f49401b1302501c080d0040450179822146040580014884a0341094800b0156240041595100c10080710f001080c40034060b40c01280401461401d0000340a451301502648120142042030800005060f80d206400000c0503038440402d108072000180452a04202c00340014410108074508131000c0742c20051000c2d0032100803020603200e02c0910003900c0c606407001002080850440c000151484e040305c103061000a2080c100e48103994000c5d122151031085580c0140b55981c60311079240b18162482100310200128010380b500d02c40d10301e0003a03810440c4044807143c008c0c2c80ad14402403618031180046100307c0c0b0801d0500c510742e40c0102c3c581090700c400035103d1b41d665960045503001012943c4c40101850000589002413000e03544920f054a4840c5c420305c05944107074440b8901414249410002c11120388030800811141703500d049052000f9900b04542265400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 913524208 1250 913522958 913522969
    0x2151513020a021c0c020102060a020306060705070b1314030307110111010207050106180c080106080a110310170703110105030a0b0907020606011e050f0901030204050d0f02041103040803071d 84
    0x30429800541e00a031040708a201921118128014091405c1024901c8540000359683e6019003083d00c1e140e4000045292078a80c0001c840c4d40580080448814a90750b05040500740c0c4281c44400c02e1800d5004e0206119500d18400600ca0b5002801141044142c0c1c1700d07280b07100510940141444042c561400d030500c828000703051040d0140b40005010391600d880d1200108511404070741481c80c10400302200340d000300036241510424034103200585c0e504113119000f000ea82d003c2c1004c01002104100035081c03036004500a683c20055803100e450030b0030390859550381c0c007808000c214000d00720090200d948290051a880304202e24003040c24900c007404030b1325840342a100a1300580018042110b00d580103070281c546400c861101e515620b21241e8000c009000d200250200c2100001d1040c1c0c45038440c1d0156000b4100081010041041c18a405010150961400c070f01490911841110054180b0140e034440c0741c01c0340200345550f4036400c08a600655280c0300c001480d13421f04414040e0380f00d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 913525458 1250 913524208 913524217
    0x31002031023030d0f0c030806060c0109060b030f1c140d0204030b07080916120609061d070801050f0708090a06110a030b1005160302071802190215151302 68
    0x8160365031520303801406040c10244848400c400b80441c0d02c622111403075011050100c06c54042c43d04040589581c0e001070014420900800755540c200086030b001d02089074055407c0700411001c442003482c91141c40307074a9100210340c504241d181e8103852248503005039240c04844d044103405900e0203168082e04012600250001e42e82440c0b041d08102810303401407403890f00005280300400d07107001090a81c070041c41030350081594508100c445c2d0001c0111581000005d0340c5d02050901024400550380d226110210410806610840100040e0401c1c180324603402001040c1e0040e419903242d100a0702c580c8009841c20001d032180320800c1c404a082c40c814460310501d04070006986141069004082c0c6010792480d52080802091500c0c05a420100310340a808095116010445060130180c1c2803040640c8901c0740d41c56224035142184009500034134585000100c0c841105180f040c007240e5070100070070050140e030700c0d000101e184c00d600b0520390031051400911843e2140041d170310700b07020f0b80c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 913526708 1250 913525458 913525499
    0x607030e040b0916050a03020d061e06050a050f0711090a0501050a0b030112030c020d0605091c030b0a17070323070b1e090409050d200c0310020310 65
    0x200c440303086105140c0350240e12440d0320111098485414600000b200c600059030406003800000900702c5c105c80d0003501030f0394041802950070003080750384824400b65820781d900c501c60000c00c6030002086803401070041d074807003080f9503491a04000da00d003145503160b80510b005407079040c2005100d43c5655542094507100d00c061050104640d498101840842000b541044e8400101440103000444140382007502540e0540340181c00804140041035180440c0b650241c81700d80ae00c01040412000040d40124001c40a10034010701005c00c4c0046040301c18002069a014000d074008000041648494246229101040d90101680da9035003080d00c100070310880e1454000305403c440d80d07001c01e00905000f070920f03044d401d180801c0e45100d8150002c03000800201c0c42d40c04205908030342c5642c0d000c8000b0540c800111510b10300d2000010b829940c5855420081c21112140c01030007400c00f054142c41440c0242c018030105140005000107900010040f580c88411460002002e0103144002100c0c440e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 913527958 1250 913526708 913526717
    0x9030209180a05010b0102010c03020c0c0405060f1f0e01090e040210021e010915200c150109020306041506050702040e0c0619030615170703110a0e03060f1e0a060302060703 76
    0x2003170006420b503a6000e000350103051061000030000d1101080c420223103001100c0000705e03540d07000009202c68003010034503900481000224040c0c01640035a02003031010795214041884003d4004540022041c0142d020700c0c000790001c600103091290340d0703244141d03a81c01a1078450f00388080c1d112600d6482031100c840d41e91a44007100520082d4174003e298404511020f2090300a401d0358900c00c583c1c0e400500054900000746c1c900b411000b403240078046003481810701c2c1c081d40e540c2c00c0d00c0d01a400c151000752143c0d26000340c06800c11034a181d203a0840781251501d9041400913001c000c0180707100c048840840c003c407002a44140c1d46c1c00000c2c21403510414583e400c0400c6500000c04031000c54001c3d083c0306c2405003800c0d10309500140c0d02003240850100b09001565145002c070040e22007075500585589000c92007407661500721030200004603003507044400d1513444141440d904501035500742000050a084419030010b600c0c4429404109603102145882d030301e0b408604558880301c01980002e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 913529208 1250 913527958 913527971
    0x61e03260307020109030905150406180b0a0903030806031b0d030e030a030f080702011e020904140f01170a15020a020f0f2107020a05011209020a150807020d09030209180a0501 77
    0x150843d200c1c41c0942800e40c3c801ca88043c0c9c150100d07406115501030541805900805800ea07246000412000381c481c0d8407a0300e03156900304902401000007400200c011907800c4000a9007801d00284801d10240c2010403605079008110034494604d204c108150104400d11901909a4070204402d458092080d0344801c005400300d18000d0408102614841c05c44e414501c207070711103186114102e81c00452a000042c1d83d020404001b80003007411115413841c0348000402c1102462804503c0c3c2d04a420303200811240c1c481b444240754a5400c040f800819801b40c00c2d090301ca04183c3e50380600600001d80c0121f4689141c1002000c2c504241c0202400965100d074184002c01c01d00100d08010351504d4100c1503007800c86650000d021503005004aa04105940c020b01c0074540d201d8102d0f101d441d4002e4400a419511010128403c1d002d204c003010102d81d0100106400328800100031001180c0c958441c015541140d080124402014101e09a81c2481c102d1004803003406000b0901058400c1d00001241e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 913530458 1250 913529208 913529213
    0x50a020f3c0102150f0705040e0a0e0c03014d070c050103061422090f060501050319080702030304051816080709180204090c050d061e03260307020109 66
    0x2501d03010810340d045400c513003018074100c0b011184050700041130601c040065504d0201c03c580b1802141c0c03044040700d0030b1006000210740903501c40f00d1081c0101e001d448008400b80180f40c2650701040e0501d03000584031031000d00300c400390646424164908034048142c07036001c0c1142100b440c0841058201644001110342c01c00040054080042100b0708092001e140360245402014804219050050460100d00d03586880f142035215072601d1100e208101c1c9e4050740c14014405081510700b2203d03945411300102e568a800602591000c0200c3c0c0341c550070951503501d0301060b81290504a030075100904c80860103a40715814035150003451015008180b038540300c01c20a82050801502c1440120ba06001600c1d078443c50707003426519204000c51021000340c003110f00034401d90348001134a504e400c2034035860980c00b800804180203248014001140c480741440c0140d04050080105100040800c000040717603c644030543c01d01c03100311060110624514050281e2088880346d0050b50340f82100c904 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 913531708 1250 913530458 913530559
    0x307053109021020070b03010b2101080c150405031e0106090507050d0c0f050315031501030b01060207060201050709030209041a09012310030b19090605070f0507050a020f 75
    0x144c860050081031110319240160040c1d200601450b61080c1000500789000c0259000c03e82500c441c0e00218089580d503048400d8403080c80f113441c0d6104680d04078054955107920416a800e44000070083c2c039064200314a8907078480040120452035540301d140000701d4214038400c0510074246ca0311056039070310070703c603003842200e80c000c49007401c3c081812000700e411355104041d02d60100000340320343c620840050000385801001c1c0714060f104079501001200b0040d421030f000b0b048031641c0e0200c5114503214801130b400c1e58030480e5140002030313a5150400c058070f440c00d240f5400c030f80507541d2245060301d001c16002c48940112840d02c1d140c2c2d121003080d030840109004a032405041091508490300700b4580102c915081c1d0321000c1e04020a29011810141c1d80c1058800004020030040210502c9490708001800040719400e01151000c01000c0b941401001103680c0d440d0712030701030030400b0038031341c20042e0520a94a00316040124403012103006990701c500044d9940d90b511003400c40f4000888200f2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 913532958 1250 913531708 913531757
    0xc141501060e01020102030f0604020d110309030d0606110a0609060b120c09090d1b080903330c0a1202251e02090f090c04091103070531090210 63
    0x3e04582c0304004011081c501c0410313094122000302c40260b48c9181d03050001000d000e0440050b1212003001040c4011400008020700040700f010000303200031f542c1e60341e0680d2800d400005010054204c0f40300c08002034015070000d806613100310303000035141c2241d00210b042c40f4102c1c3c00020095014010012281c07500c003840c180c5c0130b04002d0040c4400016202300900c0314507824000796407104920042c030204207094050b070300c110102400700e03240c01c580030144204007403103000d43c0b555001d02181e8413010700340c1048000344103500301c40c041454890b021008448900b40b2110003146035600f03000d12150304024000484108080d102017004a62140c01c200d020101c242c00010070650022443d00d0068a4000c0c0e800d40c0503038844964109a07507090f80c400c0c20250900303c00c1e07034020718107260340c4200000040420340340c010980488064680f138009006444101c00718003100c019541c24040a0348400c141c03040c040c4040c000020402c0c0c00581d0100d0030446110011102042c251004038010580c01d44805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 913534208 1250 913532958 913532987
    0x20d12020307090303050d0e06040f1509111c170d0b0402030601091203030b190602060f0402011b030c0804030803010e4b07030617010207120c14150106 67
    0xc614504100304007400f80d8250b84402000c0c4000425500803044c0f01d58054003881c11f860702a15120319103894546000284c44c4c0c3c08450301010b403606c0290011a42c4a01a44594800c08a441403500c0e03108211200710850302041650740101e0412001410400c00c000d0300e490340c2400103483e01c44044c113140c15100b40900d031341d014078030510400c0060380c3d006c00e100045881601c0d405c1140007160030103c2c00380940c144016002240304441905540b4404003010460782c042d403da031540e4a807941b041020356030650703020740023a0700c2065007075000b500000907907559440b900b440314200c00c4d1340d0355015071500207901c290382600010004000c4500500d039400e0340440307480b51107940c07038400b420030300d400c010303c0d0300b0085030740c00f03400c1035000740968040481d9407008500030300d0211850402001805032181d401215050101142c81082d50740c8140292141c0aa01400381d07100c600186100300c401c41c10f400e1701541c41e40c0159074010110602484003202103a0391502a2005c0c0d814200d01401248110002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 913535458 1250 913534208 913534211
    0x50f01140c0d11040f120308060d0b0f100302040509010b01030b091605091513080c0d080d0c0302070b1005030c0109060f080709091e06150917150403020d12 69
    0x1c204541d0401e60032188001003041c0000b99640c4601190641e9009940240015607003404000c0307910034032094064145440fa503190f068543e502c0003444240000c0c400e000f015900d25201081200c0c84c012160382c1d1081060242c54038150752500024261a4161880906c0340d40d94522031075903503454002c3c0710090301c01b50358a00003814078041070400406800421010001c1c04100d40c0c1c0e20395200014611203144c0a64050b0301e0360210031701801310b1601d5106000062245008006060a04071003100200ba0481c0c40c3c181808000b28441d4041c05c03020702024100b65080283c0d200203000002e2150082e40c6130f0b025000a0f038282418140382c03048004880d8148004403234200000c5030b10140c282101e8050b0b00e000200b60302c0b402d00030b80300d0700c000d904101c02d0309081034a0441c000078813400b105c0c02000c00541c03e000956460360444000040d492407800091398601092202c5103114054920394111681244e100c40303401005894003140a5404030010b802115074040710341e43c80102c140711210800350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 913536708 1250 913535458 913535461
    0x21090604020d0b0406110f2a07050904020414010b0a0e040506060409090c080616081501020a02210102040b0c06070306080c37030314030601020d200a050f0114 70
    0xb141c4082001c1c00a0115150720001420045036400c50710602c000c42003841c1e240e040c045524445ca0300301041311030582042207005600c4214000019400e00ca042020382012420074052100c41c4000410580e04143c8071015450b103200394040b0a03008100510003140c4409091000620417454440c03d14410b606050074020140c0d500e10440301114031246000490348220300c1d21b000080c205a02000c07950194204001c600480f0b410341980035034080c0d513a00076a69814001c1c2540c0381c0d2000801c0d0050740301c0002c1500601704082d0381040401200a14490b4080344a98142607a009801c20340c103120020500310200c0904004081d08202c55043c18000c0c103080411240d030300ca07002282d061040c54000049032410102c1e003032440c00002c181041d859510410200700034180782c248011000901c000340c00300c0e41c030580b0b0f0090740d000f010160b001e000551046c080442d002e01c40500c04141d01d1070014407080d540310742000482d046511500c040d003440480f805201c0e0840381c009034030181e072030200da0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 913537958 1250 913536708 913536713
    0x100215010501030e0f2410140603180d0e0102012f0c100204140f01031a0618190609050d0c061412100612092303090a03150f1b031d0321090604 63
    0x40042300b81400554501c2d80702d9a94ac4e01c208090001110701c203200b4014801d4000703038035600c040d01443e44da1082e0001d00c41c1900404d0984100b0ba8400c40c4070504400300048402411078200090220400c0c600c21210040450200c600c00c9030700c1a0f00114110344001d40045d4141042c0949114401c800d0a040100c480e8800503c1d64610b00c0c210901e2050b1030005880413929002901d00c0500d060152004a802643c1d0304048000c0b0007501a0304003065801c1000644e0707140c038000b0010381c5540700152003030580c51700341c0a48102a00c1c1a003800410014000c6042000c844542c003841002030b02d01c8071b00d5852404a006d04140c902c102100081c0707050207001008a640501d0401d1345440b00400da42103600c61480d01401c5004401100f9803114808200009001002c51070b600e84024180c400c100c05003807142c5450445031051071411800c444003030010b41d654042e921842c40030030300241180b4065240280315003964450303404c00300c0d2070060f2105140071006038000e1076448000c0300010840fa06054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 913539208 1250 913537958 913537979
    0xe060f060d06050604110f0301030501180812060a090f0b100f020c15160f1b030c060e1503010b130503030708071401090b15100215010501030e0f2410 66
    0x15100501803648890104e83c040c3c0303450303100c0d0048800f000c0410352922410a07102100383c2c0f084c80b080e01e00d90700f0301c1d48039202c0e85858803020309203c0d4402003451815a54001b00c1182c0d000040c00c030740d40000e0701840010802803074094200c1100c0c4065000031004114010004ca15801800320410800400c580c2c4082540014080444020484e907070024070001c80c1a06119219540d2010310750312541e4030720010441c008142000c906e108138103140d02d011001d4907170320b2030030302da44406403118501d07500800125000d03071211f004640d00030f06420100e280c00c4005060305d60003a17014044000c0006510003a078690b140c41440a400c04802842c03904600b522007510601507008003400c184250344041400000941c882c818065120050703052a1404410390300c42c401c0c442800900444125122200541c400f00b04840e02c1030300220b40c65401e034200001100103041c03092210086102d41407460f038641ca410003a2400b55051241c202e000081c010000b0407004402401d03083c10001444003d10101640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 913540458 1250 913539208 913539229
    0x301030b131502090d020a060513091e0b0d06090302061602011a0909030c010e01090201030f1506081806091e1504030f050f282102070303061502010e060f06 69
    0x1849805071315984060002005d901010134000c0d84555a140d00080c0a0b0b0010040d00c0e0802041900d041c2480c0c0d1189842c09443c0c2d0361090308001e04013400c600410082e16071000e10282c5c006048c0e0b1200714100d588040c202da400c20400d6000da0b020801f080011190707001401c001c202244024000320031071429401902c0c182001c11803089420200180c03c1110800036144051442c600078458001480c2c0d200d8028a1003030400e078002030030107500403100c0246000703d00c46c0460300741110356a5807401d40c00b1218030394040c0584402d00000d060b9400082d00c2003240900400e010300180503d00901804007240e0040f54103050350039001004045048a4110701499006416003080e00020700080011100791240380600b4486c44001b050594003003504051080d0002076040015100000f1280705444040c5102120f0381d034012a00103030091900c0640141c15191310a00f8003048603502c0b810402e50a031b801c0c01135000142e649610342100e00c007080040c290003509a0424500d1402e0010110f20344011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 913541708 1250 913540458 913540493
    0x5130f0c140f06070f050c03030703030203011404270602210f0f0702120304230d1107080c0f0a0503030403030203030406060504050c09010c1a010b1b061302100c020607080301030b13 80
    0x42000e17260003484024400480c1c007070300040680e5603414692502400942080c02804882d4514452904c00c6003040c0c440c1141b510600403015411180b19225181d200071261000c0f180550280415140c01e031403060b01c080481e13201101c0e0f0700d99203043c041c0010821001000039426040762014005d10036004103001149440d0210907030b5803903649041100b41c010300d40707440201d032244503142a00414404251807192400b640e03076003803081401d00384556032a1114050302405410410081c01c1c1480c3c110b0604045801c0a490120320507034a000203030840d00180d00560250300000104070810203248901006070a00311030401183c01c3c010743c40f48241c01603000c41410302c1407052040781480042000c00c0380b2600304050a411568442217181c040340c05c02c070080c9024030b0450580300040c8001140c000e02c129001d42d038460502e00355400b0800048541c21180051024061840000d43c0399503000b00000ea000780c83d007940c1c1e54910314080d545c1010003805400c140b80803441e400c0002d003840307210041c0500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 913542958 1250 913541708 913541723
    0x90e0c150702011133070824040b04090f1b0308040311120717070806090c010c08070606030303050417090918070b070501050a05060a06021005130f0c140f0607 70
    0xe000380034514110404503010300e954801d02241418003074000440ca0300e0f0b508217485884685440c2c6040c0d41070300c0140c602214990315481c030910756010120780704041000050020918054104c0854221811170205644803e600c02501c002e000140511024100140c21070556080c0b95071650b00d050b0045000050007080f0b521842c1d0f0760781d500d20b85120302400c0b581c000d850f2001d83d41d1a9941110089032a581d241e4050031100083d20900807511521600396135015140080707000c1d00465028080450840c5e5400e030610003000890b0b08c41c8940006184252000500c43c10103040c030102c081031441d810b4080b030b24108240801750310742d03100c441d410040d407949901c0201c552152031814540190022015100080748660070300c90150030250155070103400030011502c0d094244004404903004040c05a17005980745440a45c013a44a50350121416141611601d0303aa03442204000000b08240c42e00b9000c0d00d010320000c006603802280c4400110343c1c0300c442140e600003151040c080d0140150a51 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 913544208 1250 913542958 913542977
    0x507080a120204080609060708070e09011e0b311520120306120106080a14191101020106080c0a03110d0218011409040201080415090606090e0c15070201 67
    0x9041e0742c05942c040c1c0640b20503101d4518140e4903465490104640b00800600c1003c0840d00b85800380b1020140510040c0400740f45030b00740624100b48661031014503800038004040010701f800c0c1b80019000d075051144060f410030748030002020700c0300b0f1142c81000c100709214008001c0e143c441d0402d103010701000d08000504005000d0391444120b1144084da0032409104003007951016480003d41c45813100f11035003050202d140040908a40141c00307400341540c00760307054401180b2400850010342e070340c020444064040e070b50401c590159001000701c1d840c2500000100031982c080c081c88d00600f200800805603000781500180c503e5455200180c401506030f1381001c9151105040e0054180d00600703103280c012803000559003210b0003440746605d81288407180740084c0c607001180380c1c0240d405a5070b40303509840b9a150780e04c040381d0b0350110000080c1d5070943c80b000120103001e4803005100038000050700148904640c1d04010100e26882c0c421084003d030355000c6480103095420403602841c0c000001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 913545458 1250 913544208 913544237
    0x70608160807080a1407050a0909090b011707050a0609030b0a0e060a09020a080d08100602030a020606060d0b03060c0c1009080403060b01050706050a0902010905011805041e1d0705010507080a 84
    0x400e0405c9844030750007412410842c40c17a800000500c020343d001c0d52101c4001c2d40d199221000c40f540400020a8200f144d40108460480c580d45142000d1400003511441503a800000e180c0181550061020903100c0c41c0402c180a900e43e88203501411201040c4540070403600c4458035000300a00040e00e0744e40d240c5e03050040d03403912500000a840f6103c00c40f140c00043d00d801038070440088450852204402c034001c82c1241c030110644032200d01c0c0740c00408154a400b0100301141e040f4041040055554400044c1e180c0d408000d002d005d403009030103196451880d4210141003a0000c0c0305001c0c2e071410805103e000500010460382103a0b000000019902e1003000121500e200312200a05107604240500c180c076000c980c02543d825200b41c990790403055440c00159280310f502051084104c090f42000c000714103180d0007504000c81030008143d0030096950118080b102d0035894040d412500e2032907040005400c0001c00301415090900601300182a6a0076003603208903503d420070000d046448090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 913546708 1250 913545458 913545461
    0x200102130329190b01111b04021c0c020613030801030b2802040501030f05070e040f06050409050109020f0108010b22030c0303050703080a0b150c03090a08070608160807080a 76
    0x241c0329022103454040c1006150f5031a22509444680036452078981154990b6000341075010000d08035801500720004c1000c0c00c240003240d00d8180c203402c16020408002c40340e51800600d5404045543d0000f0f240706803060007840c1c41c10051001d51903e05418981c0042034015000e0ba04682e48400520080d80d41c00030b2170350380d040840d90401d10700c0e03000d0314481000b0546034029005032802a6410410b9120152034141a01c40c256140c1c40031813044a1401d80909050300696a03503d80d004021680030345d80d0010800321600524141da113655a003820342e00710f140c00c41c01d110050748246426803075035040542c1481d243c0320342c0004240810a01850703150501b00b0384840001150070400d100c01c96a902c0c1405400c075442841c00301c001501c5200000d049046900c282030100901901000b842d000041d103d88455111501d40f0b00b462009000507205a501c0b00c08980203044654085c100003454000054805000506071101749201c901c0f5251000f6484100150b0200d543d00d00016242c654440060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 913547958 1250 913546708 913546763
    0x70617040c0305010c21050105010e010c1a13020a0e071e0c0209010e220c06140d0e0d0f0c11041107020d061e0e0303150613062001021303 61
    0x41c4a9405d10b0b4000c0340040e0048100300600c01911040d4851300f9140ba003030f500f254424000c3c2804120304900300d0401d94802c480000d0f595104403c0d1075218150360ba14042c80340c0040398004441c00b2a280700c1006c50070441c502800400e03c0090305262401c1481010b0081c203a00301c03420113234024072010301e011244542c0c040d1101d40d4000d49400d0b00c03941c4950000e15402e80483d508040701d030b10090340c60450320446181c07021054101844400300c0f1700b050401c603900400c680c000b450300e91007409076140c0306049200350001c6500410003000068401314003e0154004544060103002e9618180c0f004a42c18903c40c0380c40c03000c1150002810f910700e0500c110f090041c030391701a4100003841c05078002c110300c5a204488910b80c0061100e800c1e80c4072000d40056420300174501d4501e0300305102082426080c0403040e8a02c1200504181c1003100811358218000c40603489200019100b02ea100c8441d034102e10b00504d2101d00ea0b000358039088040740d512a981406101c010082402051901c5550251020b0035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 913549208 1250 913547958 913547963
    0x70512070b10080c0d02150d050a1a150426030c010509060c09031218030307051f14070c03020c0a090b09011e15030207080703051b070617040c03 64
    0x65103418103800c00c900c0c007220450340c207042680000008209100001042002500014401d0312404000d500f03020705e494500a00708940c0f50203000305680300348030f80580e40c07103218080b80028402002d031000c5010809030030781160044000005030b24420180a0842c0c2c02d5034004028502030589040b905020f4103030b03030783c42501035000c081110b4612900640005004200110464410b9250034110310031314481c0b0f814155140d44111a04110358601c5400340c406180010b00000c40712551001090a680c03000d082140c02d90445003c070281501c54102c1d207011346201180410000c1e001d082c104040304400392090b802d10080302900000c140c8204038215070302070040c02e94a41a41e4038011000904405840c0c7c0f882a4550b00001c229007007a810362070907502c19110ba20704000d03d094000f61096048411003800c00d6020481c0b40c5c081a0510003c000d01d0b8800d075607895441144a07085900c0302003400d01c070b06954000c48401c000203030b404401c3d44c25070300240c100d01c0502c3e203c070720f880103085246a000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 913550458 1250 913549208 913549243
    0x3152c0c0306070528020a1509140c010c060b04150b0c07060e010509043303030201050c090a03030c03140f1c09150f0902100e180103050613020d061401050103140606040b0705 77
    0x200c9001119940203d43e40c01c0c810b14100302b5405001003030230f0b114000c1100007030004101f00d4401010038070b00c3c5c000c0c4a03e507001410024510b050010b44442031845900001d58603100062406801345040050f0320040c540ca281103030001e516680020994810454800c4c40345442d0030281c9014a21003240d58001300d00d50441800c0344100d4030704d10340000d60074403066016501e40f600041c800700591003110307a0359100600f43c1300036134250742e41a01c28150000b0103404000d46904180d02643c60a001450036162041640751076070320550b42c0c090342e00c21a20502c006107041c41440000608a0a06003601d0591490302040d0756440c45001d0000381010384001e548841600f03c01d8540d0740d001349894149072419a00999180b10b40d0070ba0003075030002840000c00c03035400100080d42464116400c01511840107000004c00901a1100d200f1b581d0800b481c2e225403646040104000e6070188100500c40420040300300c62458600d0004216004622400034108400030b1268104482030103000f1407813a11102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 913551708 1250 913550458 913550483
    0x60a12150525090b09040c0504080a0b04060c0e030d030c020307241d0d0c060b130e1c1d0103200403020a05040603152c0c0306070528020a 61
    0x82520b00741d0254101c03400b0a41c44400c2c140011842900810b065649102840c0d19240c2181d00340402001005c12140400c2414000880c0414042c07101d810464081c0c40d4941083c00d15050010880b0340401320f420501110250005180d01d000c00c3c065118039050500092280c2110000c0c0e003540b094031802400d128441c00c0900e031007a100c100b00040b500800c681003090f00344038000c4a03003505844140c01480d43c0241e41810070381c1d03c201900c8030480d10441e00841d03e003941002041c3c0043d0700103100744000d900e40d0090405a00104030107a2007505030b03030003070340c26200c0c603c03000d44060a0070b000403860f030760003c0b01410264082d4000b5103403000b400344104030300c0901c19803808168020b80422442030841940000d41d070306e01405030005680e04842400d81845980d03441c7c04c002d1407005d045411004a40c01c2002001c0b01518256080c106980080d00075144000304160030709030014003c0c01481018002d52141d4103401042000408068814194405400d2816403820b03040c8035000b41604450b41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 913552958 1250 913551708 913551721
    0x80606120604020d030e12031206041e02090f04060308030603120a05040e1e09030a18030309090b0103060503070803090f0604060804170f0a0504150905101b050f0a020a0905060a121505 81
    0x3000304141c2c0b094240c81040ad0b2075480803c01900c880703045039540101d1007109450f04a400d40c1c01040030b40d100a0841032507000c0c0c0701c04201a50711690080e15243c1c0040100403560038140071800511403100d00315441d009901101428500580c090b13000c001c82d500e00024600c0d10880b01030b0400305517070b06a0b5030491801904c125a6640400780020005882425441d5100311140342c0d030b418ce99042e06c1d42c210740ca052070041002014031000050415407211382c0001c4c4e80d10184290f1001e414880d01860303035407071031101340300800c0080790302e03903009807010401000350a40c0107210b075030802c0d40140c00002320076000a030114076000300c50300c202c22044001654500140c11500400c1191030301a000d080018032294281c2d0481014418690030a0a0001d681c410b00d1141c4000d1060320b890f046502c03194050b540352980350005072000410180d00c030001300010f62500944407c000e0409080c180014a80348000c221f010b551f03031042100c4103243c00b04070000c201d00f804400480d1076420768100480d00e04070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 913554208 1250 913552958 913552963
    0x91707080405180705181c060507020c010c020d03110a0804242d21020a18120b0a09061407031a01090b070228080606120604020d030e12 60
    0x144196403007080511074940320881c0442143c0d12035000381d114181020b03e4250300030015604a41c8155012501c1420b00e2801d0040b40c00004055004000004091801b14000381c40c01e0141302d015170502c49240e0960006a4a55403409211076140c5010618010740c035034110702e400b45070b070b5008041400100e030114500441c090104240c8508010201d0003442c0c2000543c1c9204020300500444102c83c0200102070b8617065445040311034030310300003083c141c0590100d4901e03610540b0905540d81c00154011803250b003c0b1030924802820220310f410540303003e5440c900c0315207600d0000c2601c00c141c000100c1d5540c1a5002d42d0080350030480511220410210981c0380d10400ca6020740424a4403c0101212001034000c008591042e103e8014113820104405030315088040c049902c0001d00c5903a03440e030041051101403031500c0b0420004002d00345415681005c0c00207119502801c428205220391200018007290496010341d1001c00003840c604003102c2c59401514107580002c43c0c00001542c01500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 913555458 1250 913554208 913554217
    0xf0d03180e04030206070314040f210806040606090509160c02100e01120513030503060d0525080a0201050d0e100612050c1507171c020409150e0a09170708 68
    0x70340c20755174140e503004415402c031802072000f0220034200c41c001400013600e5900c18104603009207a030960440c6000e9001e1094095401c0ca00c1c001420304040c0320f40d900703160145c040548070760b040080920341000302151013404000c00060740b4071001490600402d0040100344d00c0c1030703005440c050115102d140003401051048500da4002601d4164040001c0010b114050080409100000640740141c400310f40b0340e000074120541c030080404909001400c208a101300000494240340d0842d00c0394506820b81003010741c04100641c000d0520341c80181c0e4000b044948240400d03200040b00e03000d603140d01c1c1c905000c0c415090880c9180100100e00040360004240c40c0500c61011124003800000511140004003e4802125401802110700007121401410b42550700380026078203111f64603030003880100c0c1e900c1101650a40c006402e01102c00c0030f0251407180625000b507004400d20700402c1c1140300b100101140c80003544c2d0603200c002c001d00300031404200d4810707001580d1070b1840e40c2480e1155600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 913556708 1250 913555458 913555463
    0x5090a060f1808100c0e040e0a020108101d13060c03052d06010311160309031406091e010f09060f0510080622050f010507030e0a020f0d03180e04 64
    0x30344510700104030104440160660303c03000301030b14215080c02c0800001d00592100d0405110041e00c0a904c0c944480c030810b141412540001c02220109000141c50300134090450405240002c1051108200f060300c02c481d185041501c9138034694491300c007007411250295004100b44d090250726002d40d54182c00c05030203040c0d002ca54032445c20b0540038451070b130201060408100d103031440020350342c0e41c000d03030040c810f5242200040d0b18000c900c1c6110030f180c201c502d40840110303c00c4c00c8180103108519a01c00030340d4030740c00020043c0f8102070402c00d41d0340a21725040164070844a03203243d000507082d0081c14200316025400d01941425207400170140c2000600304600a240c10300003020503d60055002c00ca40741c21000d840561140146175044140010032030302c0c55000045814005842046501d00080c8401c1c0005064209000010143d804404450740346603c124070000140c0c0d1405c002c1984403104807400304411080b45003d903904034005807244c50f018018400050912404205079111b2031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 913557958 1250 913556708 913556717
    0xf0c021003140c16060213080703240204051f051c050610020102070c1206061809030801080d140309070e04050304170601030f06091401020c010f0e061b0a05090a060f 73
    0x750781c0483d6a0480c09280020440e1600c07040f03580e0301180d190b50007000c0480c49400b020342c2507500d134200d00340340c62120391080b01c50160429950b18034405400307840b100603105a00c03d40c82c0034a090001442740380840840000c15095850306191a400390b8100d8041800c0c601d4060f807425519200100101030407503e03d070040322800c114580003403040c030803616515402070b0350a21072030501020500860001008451240d583c1c40c010911004400614114a00e255000310381d00c20540f90040c00c44606900c088840c3d40043e204907016500a104a034441d0490400640c49a64000c069407505400703a0001115080e2a81030006005004c001030066a803890402600c00b034440030040e070f40700424480900301008000f00540004d0080e0010001e035401454403006080410000c0390890340042c08180040e9581d501022400109000e0020b200c802c0f0405040700b40740c1283c48043c0d00340c048901da151030740b000400c4682c85004038160703505000080c000036003207501c0340c501410740650a441000400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 913559208 1250 913557958 913557961
    0x9011d06070818010908120601030e0105040507052b2603010f05061b01050f1501030608060411010903080c070e06030307020f010e0a03060e06040c081501060f0c02100314 75
    0x18400050650107411565110152a40d0700c000c1800240c070701d0b03003510720795540703d031303490700200c2c0d0740300041d007942010742060045a00f0300700005011140254840c02259040c1410440447c00100f03480c4101c540030303100c8003c84110840f10109003019032414400340039402013414244007120041e80c201c00c581c0002402c8003040c00d803103035040f40024840d4462018100c5000c1c0700604160000e400e011a03420b1860700e101a051213083d0956a080782c400b5aa416080c040060000d070f161385840d07080800707090800c040e03820045e0b01a02c561000700f0103003c1441c1c034142880385910031550180107540080700d407030301d0381c0c000d5030020b40b5030380d9a02c501b88603031a45001140252402108503468190300a0004002001502c01900c40e9090400d11980c840441c5100001080c11402600f00344c244842c0a48031a00d006d141c1041e010069402c0b03640c541e404070382900c00311150740b041035042d00d0030b0f4103052084028600f07088a5108010748000d4018454031005001140c06401c400e0ba1100050169a1203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 913560458 1250 913559208 913559261
    0x6010906082a0d02061b160b3405060106030209010f030b010e040f02220302240304060506152a0f030a050c0106050616110901050a05060a03140901 65
    0x40345025a5059102d00c841c0c4180c0e500c0e842d02ca03460040d00d62001d482103091015100c0540180740d800c10288003943c0158001e25000203101c01c2140181400c0e40c401da003040108402c41000100350b11180c55160b1100a001e81d445000b02c060080450f032103400c5516544e1a03c20060103500035800160102d10842805240c0c180280156800c07800f0680d5030241640c07414003080040c10078811915082d03682005800c1541440d0400c50800809803100321188501d94810300411551411058440000c50078440095030b41c0b0700103c9070000d0300b20348003107007646413000040c0440b1145032106401400028000c4448220303004400c1d0152020720200144240160000d0303216030402442c1c0c003c0f50000c0203100c5009010301c0c00351140311403c000000b112519200829010791003050031440c00100c96541d0350801101c0c200040c1d01d018150b9441c10750b5450030380402c0c441412405100e20600c00481c60b85e8880f880b070f912210008000350410324180c2000400700f80240144494124501d0804030040306 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 913561708 1250 913560458 913560493
    0xc180a0b030c46200f12030105030d12020f160b070e100c0311060a050f0114030c010525061b02030f041203051306020d0305070c020906210601090608 66
    0x40d841698100c0d8645200322901c0c5030628585a000c6106214134014400d5051040281c41106039107a03400505200c022254005d14042040244183c200020801484a5100450601280a42c1c0d05010b00310b1640201c1e000003038007a05180201c800400304407402d4118003880c0e40203000303020f2228108192542c035411151201d0303400b00103170412140c0b800c05800500c59119060b00300c2c001e20344144044a9400298100f1a054460782c0c0c400c1d440c0d4042c020300c01170040341c145c014034100b04039014030307000d03038002c00d40f80e044000800f818031801040c4200700d441c1c840044240c2030709174985c04020b00e4491a191000b8100002c10b0000c096800380d141020900000844858004058501d410310b441c2c0b4019042c00100c044080b0304000c42400411811782c409a000c80142542c3e80240268046c42c44005046a4004019000f04410591140050703100e9030842a04408103540c0180300c0721040740e400110208000b04100a445080d00000b00c0c01010703409a07003507541003401d40300140b8044540b40e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 913562958 1250 913561708 913561777
    0x303071b05040c0503070c201201020d15080705060a2f190803010308250605070201110405012102040510021f060b0d1a04020d051e0c180a0b030c 64
    0x6000c510f503400094003141010700815101c910440c1c14080d040c500201140306c40050507100f213892b0f900451603032800d4001e40146080120070442c400b041c3c924002a480d175a007040c0c8505401200006072040b4142d03c00c8180c91481d0b041d0030762015044501e00506050440e000c1c42003483c50180d411504481164090b40000c00c0e074002c4076050450742141ca0f03048080c0e000d111450000303031079810017810601280d0745140045000b4140041c4914007250041d094030300700c4e01a001201c4040100f4030603a038222151166100303000211a2802c5e00c40981d02e4001d100e1508090307800540c00c030340228141c3c0d0000c1d0447c00c820148030b000f031884600c07110035000c2d2102400749114400d4280007190800026034451180c410090005188800245001c14100d034001c1882d2a02c00da16042007082c10f901030407102c42902103a0b0b1100b40d0358503114620445a000c0c00840c0c401c0c0341442000100e050362080c1000001e0012065899502c0c1800744600c0591ba0041424484c0285030404a19410700c151000b078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 913564208 1250 913562958 913562971
    0x41a090108010605190e121e07050a030b04060f0902130c030615021c020309130203150f06160f0c0b040e070201090206040e070320030601020c0913110303071b05040c0503 75
    0x1440d110002d480203607003c1d190207413080d0b044090100000c000520400c92040d1004801054001228001f08c00700d090034525001280104500d103401c1002801088880f5401500500005002445502554040e017064030700694000803640d19403e0b648069480b8123015081c0d61010000a5540c4402418100000c18a040940c0280e11150392000441c0f107180007a070704500c1a60b01c1c15501e00001510700c21042229a55940d002c020480f407400750050170742a01800312007402100c04107d0015140d803083c8017200011a007005120f5082004150032070360007a40c010701e1840300c076842d1401c2d8401c5820610425019961960114140714018030500d030f40d03290040c111502c2c0c142028003102c04144060328650030503644031a15203003030424801038250681400c0360ac40c5d41b414607130002071415491a003c0d81c8145903040900c0941c604140c2e41100d46544940d030081c0d03582141c00002c1c114024860080c1c004403060854000c51111040c10405079401103c08204000c001a4116001d0104a802 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 913565458 1250 913564208 913564237
    0x801081207050f0d0323060a42140403200f0301020703090305070504020906160602120f07091d0a0506060903030d0b0915060d050c041a090108010605 66
    0x8800c4514005044031405101100c2000c0d200103129450801d055075400d00081c0d5940c0c07841080440340c011260f204c0742c0185c40e03944a00702500081c0c038500f02c2c0d108601c175040c0ca01c100c0013541000c3c040c51038a07284100303086000c00b0054543c00202e0f400301d1111200018100c4850909604404040c0d40699401050110001b14039007403401204641111180e40001e0070520124295001d000820741030388241d0342d9402031413851820901c1d01c2145e4210600c03840c018040500a03881c5c81041d140002c03404048140b42102c542001030091064450591925200c0420400c0d410800402140124184d6668070403039591040500d07000201004610740880041e0003049442402d608001d030000001812203180106080c0060302d190302203406003100a803580a24405845c29001440e804400a603c0310490040600014040e115030104480215a41c00210300717480c4414042d2000f4200032a880c01c0382601e104d220782e55a0700030089440c0016109000400c03128810302c199007411540544 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 913566708 1250 913565458 913565473
    0x2090306010e04150c090e01090f15050607060906060b0705030406080c130e060316061110180b0709030f03091e030201080112050f060c030601091706040803090109021e0a06080108 79
    0x3d4000142055617051000c000c101040800c003103e102d87d1180c02071032500000949071419102d9941079519080300503089482540c020481515094100c0307a1003079101d800024980003c0c6000b41c0185640c0d045019004d0002c20380c80108180000140203030f8030b481c1c5503003640c0d40d1032003080011031143d2f42c80905854a103c40401410103610342050f0401c40083c2a82c03044145006804160002d69010400140381c422044075100c0c0240005c1042c01c04c51502840346103904601d26142003014a0b0041070200c982000035211803240300c01c03001035a845038000850706014100188000c43c0b0740150188014079040000513040402a59812030380d040e110741485a00e4040508090005640c0c00d0301c4c20b002d120b20b4050418014000b8921032201020016200e0405000042070495a508080d5490030b12014060032a040002c0840c0d0103a0f11550080c0d503603a60a040f00c0c050110001f009401610503003e1144180051005032850a02950a030010742e65503442140c5030142031084505a801c03005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 913567958 1250 913566708 913566743
    0x1802280212070c142419080402030d0e1302040306050f0604180209090a0c0e15030609060a090f1a1801060308030613091a0402090703020a05191103040902090306010e04 74
    0x1040c1d81e810060043c0700390061074802403502e0944281d0f1a25179206040010540e040100742e00d01d42d508500c0d40d181c146002e1410382d0110340d0f6040340203c0d01c014001c0031411045030f90381d40c0b404403c81c0f026840043d174a0310307640d203060000f0f01816158a40341d45078941c0001c80d00e080c50f1050076100261516a400b11083c42e400348280128050501e81803402082400004907a092515000034060401d0407000c501c0d040b000c43c0c80c1030040003412072103500080d0500a082d40005003154104000030000034140c10f03645071501c2c02281ea0300008180c950407011100881d103411011301d110b44a421a0402000035904280c0e08aa0140c00010030014040c0040760341030904400000701d500c180400090016010307200c0207511202114455000b180013400c11045051641009030040d460381030a40c1000c0c0d0f4141c1c003501c940244120514802140b10750804524803503441c600d003a2040301c040d203a40701c0e1202d840c90040d601030301640c0e00070310a040002500402d000340c5644500d400c0404600c0109a4a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 913569208 1250 913567958 913567979
    0xa03050408010513050d0c1e050601030b010510050703180e0f1816140622170c090705091810030318060f05070c0f06031e151802280212070c 62
    0x48a050307030642c1c00055030300356441508c0380c0040024000d42c003c101940c9180741c0699a980b0581180e070040c0e80110203251415040b005840d95a40e02d07081840c91904007038001240480250300c00380c040302c0403805209000c0e80e0303900e20a000f0303c010701c04131481e1082c031500c0a41d034032035000300f0b5030503e050307c041040400881e41040d003002c000101903c0c50700d0702e6000d507801144901440c0c41504031450400308910698280b542d00d8074900000608640c150303290014041d460020124400d0000004404903160b1300e4013a03201001aa440b050481400d040202480c2042c0a01048000c40c000b45c80411000541074000004c6403a1a514181c26132061a0121055006010700b00c900403001e03140414401842d02529004d0065a0344c00204008c3c2d0f4801508410280003024000783d24181c08d00e41e042180642d100e0580340c4080c09052068440740c1014021312445000200481590180c0900304543c28080084010309500b0ac4100c0c0c0ca02010b212540d2244100040903030440c0310301000040c024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 913570458 1250 913569208 913569227
    0x3030c020a0201022805030d060816030b0a0b010c0c062303010f0504020c2e0f0c08012601090b16050c06060f0619081b120a1503050a03050408010513050d 68
    0x45c050114a0030499032980c0c03450300031030007410032152111800e000c44001001401d0244042c080004107161035038685209540014111000e442e40b201c40340e440c241d0081c00030462480e8460540e07000c0e56030b9841c1c010140700c400d03a079042d40030702c0041d64841c02410100507079050351341300015503070924a4102000000d500060340d44100d401500c0042000380c0b80091203110280c1d101c10300d42c072200c030404a401c08840045001c943e66502d41604030020030b611141007130554000e8010030395980f102100000e8502c810340c806c4011582080c2e2040200000010034a0280540300070003140c069030b012090701d080c09410443d0700ea0f9405080025668070304075040e8046554042c000902d801d40e001c00741489855400e19013808151440e06101c0994a4507003a001107403811503040e410008140140a101e8102620000d1050b03210400340803a800304d043d1610055610034101c5850100f00c1c68050843d40061143e6400c035440c042c0010400d5141401c24003039260b1290142c04503200424003582d80082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 913571708 1250 913570458 913570513
    0x605031b040911031006050a09092402190c1205030f070c03050f0a0810081f0e070923060901030c05091f0f030b0603010b0105120c070f0f03030c020a020102 69
    0xf82e9862000040c0c40138170040e03000000c0c40300d0104244c0d040c04240300f0400455808402c100345000c0f07070f0002003100ba000b185a210510900403103141000c0c2d40c00b030040e004511030b841340d10000c41d001d0315601e604040030040711803103a00c43d0603001841d01c00c140d034680001c0700c10324101180c82000941d0303540b00d03014844100e842814151706000c5500303429240d6400c140c6a00c000304204406001da2200d40c60f11150003021844014204036646901415010156854205410741c4801041c3c0e80414144400000b4000d0350b0003c01c280446118500c807004260a5200346001141012420790305000c00001d041c2ca41003108030240074580030520086c41001000c40c075407040c5c68a442c80d204403a14281600410402c9407902c409411810300806080c00600081c1c401d0703141524114081c1d03000310660700c64810000035205180d581600c1e82c0006c0c481d00c0f10041003050030071014820003034480600004103001c1d94080008014001069a0750742905402901507440380c0c921000120004429190200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 913572958 1250 913571708 913571723
    0xf0311150c010204030c050f1e15250201111504080f0d060b1b0c0901060e061204150c0201051b0a1704050304030308070f12090f08070f060605031b0409 67
    0x400d1007960b08a81158104441c034101c0c205003040545000d40c2a40d5506104a440d0714800c5195892009120b41e54034090f03002e04840c00c06040810010000d546240058102c1c036000300b41e410030400c0d24544602c80c200e002c80d0300351000c44444480015207282489008207500699290307501c0e4511180c000480d0740c03440040030819940c402d02c090140900074205640d0640d02d481140c544248008841c1c40c0240310b907400644441c48540d5a0003d00f811200541003040c190348803c0042051449400b101c0d889520002c0c0900c4100030820111440d60402c0450070841c0c0310342140304a00365401900d85010b8401583c0c0c408030307060f02860090940e1102421710b090906c0b8443c5c4c032940c07100e2341110199445d03040030a0400c24160070201d0158007041134a40a01b10b44620317030b030103408003524404010340035959891540401c40003420070306806170890241a01c40d5468940030301e04007000130b0210340302c1d8140070001406041c00211070b85868140c3c5d1103201c1c42e4014105100007064521002d6400c00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 913574208 1250 913572958 913572967
    0x605042f010f050c0c060307021c02071e08060406110c0106030510050f01050d2a03080d06090203370c1106010506031306050612030a0210060f031115 66
    0xc0d01401466069801012803894030344011400034010507240021841840402c100e070124520001c00c021030412403c81c0c0150300ca481d46441249440b04992000c0600c2000c0031003a0340c1286c00045020131038134000886582d5018000c2c00000e03e020318170940ca0380740c1c000c00100700040c00c50340280ca0400d1216480ba410207800003101400c0d10705503401940d1f1034004426010700444607014065101d07451410b245403a524002c08140380003030000e0058000d01800300752012030383d50104030750394041c0482c07855682203499042c018010b0b40030441f050229482c0c03001c0051300103890300a8910801d4201040c00c1580000f0400c1c0c07440b14403c940d144140528000080d40b203c5aa110300c0e030800c0c4943c1d44568403007001f0840e03603141400c10f8028a1080074103208000700040200b00b4100a2540110302241d80c0e202c803400b00302d082000129006a500011600c50b181513800240b00d0a01070240c0f1060003442d90710707080a141703004507010103006a003901180d02d00a0a00c0800d03452981c035011815403a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 913575458 1250 913574208 913574243
    0x30903140d09140a1110050403050d0816020f0c10120c03050907080a050a0201050903190501021309020906040303050f042c06120a02040c0905120d11030f07060504 72
    0x561000e407040285698952400c03080c460051074440c0350030740f200d00800c002c240035207031350301d1552100300c80500c6103011a449224a901c510b094070010b680c0942110940603c0d143c0140c6440f1044510100380c1001040901c8a580300060110100492002170602011860140300700038810075130b6903084c0207038004140c000c0102c42c800c54000d0380c103668001609040084141c2d00700310301588410340b26884000302030b0103e9800324800480e01d44c242003240d84c0300040c00109040c40c0072801d10005080c00c0340840024814103400410881354074404448440c0c0c0c9030b00350003040b4050320319019000a010700043c40000d000340c0c01400e100c40540c41d42d9003401c2d65240018000800d4402050001040000c49518030800c070031000d030080710885c0e8800d41800c1c8002026038400c41c990b0081d20450320b8011144101d80a03503844c0002c0e04c0c1c0a41500502c0c801404066510729025500c1800114001c60021000b0004810f03500c0020609108925095580d200d03980508400b42c4295000d40c03549488505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 913576708 1250 913575458 913575497
    0x6010c0b0703060e0f010f1a091c020303160501060501141e1605030a090b03240105040b0f04240507060e010b040903030e1e0717030f130314011506030903 68
    0x417582050140325030560428046224540701c0f644140003410f1000780e1134400481103010386809542c02d481d02c02001e645c03c1d0b012090001c0c40301010390113000000c3c1e94038105014180703208001d4000c9009105c2d05a03034000444007404480d51500960034240110200d9844010b445e4001380004200350b401d25000d031f40040c0d03c0c0c81c4c21082c11180d580c0300080c9000100e8012a51000416220020b40e05501d0a020024000050b00c0c130886056000140b002a440e80143d059401414000e480b1903215141c1001c82c0302540d00030300a104202c54100d59980d40407502020101e0260550341c2d031541070003456a900005044028103003134403035480d841c00100fa522244103520002d0301941d408940e2041443c1c03540e007003402d01041140032048001020b070440c800050b080c01100c16441050b200c10442160382d60540c0688404100407190008068200c2e46039499101e0a8034003440c16003034100c60041e03480303080381c1c2170a070a0400c0c0003912200b04034180c025030001d1344650090610900c20300781501d0094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 913577958 1250 913576708 913576711
    0x4150602070626090304090f1109010324060512100b12090a1a070f020d02190309090f050f070f0c031b02041b03241e0b04060203030a050604020306010c0b0703060e 72
    0x1003030b80e0300106d000c000094060050843c6071400403402c003d900c00c07039003001001d4843c100c101c43c18951104035a102080c0314101c14560900c0842c000403a0300d407240b070003d01d264400105201c1d21030364100804c2c407240340300d03d140d4102d0f81122003880c5001c190310030512101e00c0062a090301401549403840218000490407807070300760040c0b9007042c0c0c4d14000d0300203410107c1044000003150320003c0700e0f40b070f140d800290146580c150712510005460701c0f031400315800c0b55603401c50f004030783c188032584244983c0758109074000d61385180a51410355501c20300b01d40010010394000d0000d01140070000110380650460203905840c1c0d8040c2e84000c00c40c0e000326041c0e03985902d0b18402140c03003d091920031030749807068a03d48803a003241c0c5c0c06034a1000e0440c0403140014000c524949285021944d481750385070389807074021f20407803a21586482c3d4901c0f0107501c80c1c100b1102044180d0070040050345501d0325108481c0b0400c4141c65a9140486584070622403050052407081031542d112004100c2d881c40c1000503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 913579208 1250 913577958 913577971
    0x40807080c04060801201305061c050f040f0f08040e0f090c010c03050f0309010e0f06010306050f01080613021908340605070c0906080a0204150602070626 68
    0x14070740307205624203010440d03032590300041c42c60741b6240074026843e890300e82032000b103401216001e441703030841c22040b40b030752010798000c0d82e01c1580000c00b21a200141c4034162151850103008019540e42c942c4c5030b00c122401180c00800062002000d0070015010513000f11020b4018103840341031075111809025200810784442e00000306500400c409194104990880f020080c606401d03229030a41d03002d0402d0140d40004d80d044600030002a41b170f000254041803201c15800111444002603062440d20b07002d007800140c62240c180360016140e88102d642c614100c030750b410014a240c3e511010410f4401d00c03070310303412a40701340240100381c04600082402d0026000d0100507010b0b02c8151800d045410340030035240c20721070010300040402c018140b07451104a40480c100039940e22058900815034481d503402802700e071880e040d00400c20802c0085e80c500c05510940e000c00c036620b010f00c544010421644122401688080014080d0340d104107020882000e007013542005851070100012510801182c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 913580458 1250 913579208 913579213
    0x1211070807020a080c011b1115031b04030206040612091416090c020c15070501021c0b0103060e06100c02060a0f0f0912022e0818010216060e0304080708 67
    0x44107610300b420340e14004000c4d580092550710b240b40000390207002c0c01c00c0d03444a0103554641200074452038402035603c0f100020300d9081c80240d03451048580f07800039549582000700c40115501310007035003c1100d09883e0001c1c80c3c5400c152424101300c90110710049494004ca0b184c500d40c4c4000b40001800080921030900501401e06407a0242c401d040241e82c0701ca07205506001e0403e41190700442c55050012050791501d0700101c12000f5440c5603c140359004000d0740c40001d0340d0f01d90104404c03001cac0848011400512036001e00100450941d8461300445030f04d80d8008000c9141c1d4940500496100301850030314890036440f540020702035410400130740e00840c1d40d030344400305c1d401c3d8440e19101d16080c050a0a203031250a00d1000b01007034000e030300e00030b000f14411235000d08081003041440c440e000b200700300e00340c4140401000601d030b0138043c2ca04100000250304034030840320040c000d555866800c00404202c180d04c035282c41000e0032030600c1c0c0da01540000c0101246994061121001500f6903400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 913581708 1250 913580458 913580467
    0x10240b19030f1109040c080f06060702120a030e01140307090611120417070f0305030a05030613020d060f091a0d0809030d092306030f04060b0d0506011a04050303030712110708 77
    0xe105c107580200941c481000798400030000030500340046c0b01c3c2c10040545105403984460b1001c00c01e101841c03003c846243c400c1021035010150f0060a0050100302a40e81f00288a102c07450006140402d6801c00041201140d061041d0b82c1300751810004049220100c80040008690070701a80c3c0c410b4020929060000307070900110602000302c0b03401080d1420b00c4a4a9074550f4031516201d01070110a1020010b0000c04101160740703c07858a0400601d00c4000c6584031881070042c07005082600c182c080c48441500005124120340c810301513035880603070504007590ba0420400110600b20700d0100d42145060001040c5038504000c200780c001010313100c4040c3c0905024052040c1403d0705400b4607800400000c4810740d0311058207a83d0001009030b10f1101036115032601c24090040c0140007a004600c0044410510800045540c1201c80d1440d03a201c203420b5040d00c11245214030301510b03403d0350040005c2150b051181c103205020217404000010700050344284c0649179030120000359800b04d004136 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 913582958 1250 913581708 913581727
    0x50d030e0312071506061b03081302220b060903340e070816090608040309030501020a091403030403111021050105010f1e0e1210240b19030f11 63
    0x204005c082c00f01c41c00c001400b00718580703a15294913a82c0c0701c000c0421014102250900108020a0b091b50398000c1c40303003e6488940c0c480700c0003a101e07440340b0791583c3e0420259203202e0800703004039545650050064580020011800c007540200502513110011031414031112500c0e490117840e003c0d12140c40c1081c10307402d10340070060826001400c01071101e0250150342069941281e854012258a0b007041d452070b40d100e04041e01c802845a0010300107500000f00d20b1025a440003000003950b6540c0410044c0c5180c40d0280b590368091800010320361003696102204a00d0041d0910701c4c0400c0d18601001511600060b02c18502d613001007241c6010b0b15500188000d41e00400d040100c1803882c80c000d90351000e0080b810480503400300841061006507095480591108000401003103202c1003110039985c92562042d0080201d0801c1c45103181120040304c0052600701c60100840b004206c2c4607060460140390f070801200d1095283d4107140c0d0f10029524000f5071802100401101045040e80b42d45915 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 913584208 1250 913582958 913582961
    0x6031707020a0e0711071a0a1101180305031e040f02061605010c090302010e030a0b0703050a020708040b030703180503460f031e0207021810030c0f050d030e03120715 73
    0x9401c90711618007040c1c00b101c1040700036030a4400100c8c3d246051000d1003011403005005164954500400d02c13540e003410014142c0000085002d0310740c4000c0c22085040601844840b442c040e98024070304c500500d04030b400752510304040e180c1d03a03801c1005031109481c80d03903606007120540b00c161004221158410000d540c0c201201c01000d400035005040d8041c03142c0e4441c2d51149004000805040c2e40e000458280c0b17181d50f066508a950186020f81d869855542041003138204580034000203041c0008503c3d0325003c007000d09422a8480d00950800002c45022850b00000d042030940c01384905020b103406051602e100c00c034a01181c10140a00241d440e0700401d029060002d2609144c1810341c1100b0130850084540340c1c14059842c0141c94035280c2c80000e1080d90b142c0001ea04164140341030003812002c040c2175908407403040106012150741c495101c91145414803d86600071800c03280340000c6070160b07006a001440040c00d860381c066001d991880700c1c1d003048600392030095010189440e08100b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 913585458 1250 913584208 913584223
    0x151308010b15090d03111f021201050604060203190e33031b07020303040f0609140f0f061c021911070b03040312021e07020f0406031707020a0e0711 65
    0x100d0319289891803a03c040f0704c2202140304020100515004074090040062102c00d4040348180d120040040c0014101d901079007082039001c1c880d00c0003000000d1130f4649101240c04442c900c0c1c0103035003410395521110040c038040700b080078240120100c802905a40e081a164900a03200b403c101800f124490382000e095241c0a056040721810014805030f410250400300388a1061220b296868040f880403900f54010b95220a08842400002003080e81e000104c40c1d05980c0074200b101314110300b15040203805074104080076004900f00080c0382590900c480180141301d00390034044554994400010100c0e400200d600c80580c030080c044030281c590028820803845001c0c0020700c54103003050032407842e91001410090030300402c04008204242c0c6070701a2352901001405082c90200e51901c0b11100b0340c0402c0c8100e109150300c9106036514a81403060909aa401200c002e20b41200134058203c2e960290000b0b82e8003001c0d4034170005001500c01403503442361001383e540c0b40013407007450f4206241000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 913586708 1250 913585458 913585489
    0xb0403052a0f120d081f030819030e060405101a03120918040506071119080904090213060f051e0607061d060f09070f05151308010b 58
    0x12620540c0ca0341c0001000d5860007075045505800c01026000092900d46000940071824015041401155a045031086214285400e002550f88040000d5400c0101030fa020040c14120b09007c03480603110700340301d4006e0050942c10300041201d400d40350285001000c0b10116141c0d400070700c05160740d0810740240940c440c01c0e010910036081d0a903000948030010120800c90100c0b02054014056641e8007224880703005000005196040c00e05007107488180c125007400100e8690700f00c50001d5600020b071103014001d081080c840c9981196188041035109101666101c2d40710008000503a413074108079001403644000011722285400305911020240b6030106115180c1002200e402d11144081c0c2d00c45410b0403601d1b15910a201e00d00300e8000c10700001c1c0540403c40425005010303940010302e81d0f0207420b02d10341d40f0700d503599414841c65842c40a4050310800200c220010070441c140752050f01da421011410150801616003814001c0420560090510740e444070760352125410702802c00c0d2007440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 913587958 1250 913586708 913586743
    0x1b032a040e040f080403020a081c09080a12020f030a0309170f0f130b0a0302131a0a080921180409030c110414190b18240a0b040305 58
    0x249040321401518000602c06020003a4421081080000400417035002e90303401452002c0c0581c4811465030b4030455880c030440102400f60780038109074014500d100032500c95000611a841701d5035a0342e01010b00c5a400c07101588107050074a070300d408050001d4041e40105a800160062207401c02e00f815504100d00900c014500300b110600d9064080101d4040c208120303141c03540d5040403c0a4904034500e540507071002032001c180011b11544c10740003040ca490550702070700a07650f21045500311041e00921940031046003000400c1e0700601400078164031000103410340d0301c202c00d42030000070360281c1c1d8480342298000029155900789800c0ca225058018142d40070000c888107640c0107020607500140141c0b030342c1000f0b030240c00f1940e80c98004544105410f214800b2504042414038100580260140301550500e1080c2525084c5850074050103512000103034184c0d2105003c2004564401e0301c0c0302c040f40b0500c000c0c9071040d154486800024051454075030390311441e6003481c0d8100140c4421110404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 913589208 1250 913587958 913587967
    0x60c0f011a150c15070e130c0806090606041419030b07020f010e0a110f1503061e1003090c120803010e090a1106090105211e07080f1b032a 61
    0x100380003d881c080701d1004e4a00d562641d00c942c041500c2d1140c40c00540c0c1d900150841c02041d5403403a64008441c3c00000c0d8030342e8240c640300d1a0030043c0d05982200c0c1280c02640a0000f002500d00c9001007028441c8050030801c0941000c1e501d89501d044203820684401c5180c41c1400b81c825810032180c0110070041d0020843e5101300700d001500d4203540c2102425403110181d01c004c85a50b000c950500d1560000c0040b810310964035454103182d04111403040c031800707100407410f02d10001d92000c00344d01035008002c1c038621030060b042030b0002c12401e0070542d05c941e4241400304803444000b0800380c20303070f0007114010b0300e941c5030000300d1440c00d200a00c0d041407a0003c03801340d0002480300d240100004411110301340c03980f28900048603d4001c407000e003038134903890782c400c041111f5003186481c0c0034190b0b02580007455180c02c5801011440141c0328400058540400144041c018070001500441501c41510303281c440188640071940054a0040f0324850007a6070400441a01c4890a859402c0d00d0f0481c0c01c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 913590458 1250 913589208 913589227
    0x90b060f010801061e11061305010c020a0201121805060403020102072612041103011514090c0301090203090304120b10060e210a0807030809010b0d020d02060c0f011a15 74
    0x44581d089145960800d17040b2142203c05d00a0580c8207801d40800c0c1194428030304080c0c824149032034000240d400703500c0c2840e407010b4503101045041c1016010b07161000e003c4907809a0900a145502400d43c403002141c244400081c000d00c0024080ca020761300241e00c2e8045800c01d40c0c00407603c4001c003e500c8105004d50104084600c00b9219420100700d07248046a96a00f81441c0d070000f80c11419030b055180c51501b40700d00d4116020001a5100216404501c9021500340b001000041d030b012040e008080c0010042200550000c5d54040c2e4807500b0780741407035035600714180202e8071000221442603080f420840b070390355801654401059246048401d445a20340030920440c40d000c1914081c1640c09169000034000300700f641441d580c004d0406940b00241c0c10020400e074800d440700c010b44c1d42083d801e001d040c070b4502003c04002e60020004c0d42c070b40c140c45d8200500c40e44012003201d207074000d100d881e0400b02e40038420000361081c0e140e1a44215003028081001ca02c0d01f0344100c8030a204107000d130014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 913591708 1250 913590458 913590467
    0x20720040b0a0e040317010803041a0c030306190308030f09010509012a140406110d0306030213020a120501090f0c080411280602100c021c0807030b04090b060f01080106 74
    0x4035424080782903030a85545c20100c80d40c0080c0c02004480056080c0001046000003009208807050303152a400e9003103022055110390311410086190660080c0085000c81c40e119100c1144103880c0080300342605d513203644003032240d04201d422600c101c2e040d2003000700300c01080c01758a0b4059200c0000700614041c020303140b200c8004010340ba14840c204c03c62402c401900a1400c000c9184100c0d16080c0c460342c3e20780340101150120100d903502401640701980b072050103400303524240c13640140703603031901000c8400c050000c1d04a420701000700b044e00585071801e034003140b142501070900403a021800511404032001a0361020700c421007049110300401001c24404040c40c0d071010307400c40c1d500c80e06031000141c007000700d4003202e4001048284103e0010b4040c1e0001085030240c9800c19062003034082c006801c0c0c2c1c560b606214022881d00f01011100364030b900c100e0078039a203e40c103400c00080c031200c0741010404482c0415011070b0707141c0c461700c1400782d40c0ca0016440d080f03440003442d055100b90b050440042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 913592958 1250 913591708 913591729
    0x17060723090a090903020c010c1a07171905010b040302130c090810140c07080d2a080a200a0e060d020c01050708090111041e09020720040b 61
    0x6904103040100405805414800c03105071800c01848030311030503111100440105802d00085000d440340c64404034655000da602c40a10700d4010039140c11920b19200400c4031054000e00c52010081130708910f9040c2030300a20740600845c4240c50745100c01900342a040304031801078005084020741840b003003005a42e00260891142e03148040810120145c107425217130701e4010f4000d110540201d0003508000f89895100307003103401401d000310a454036401035017801c0348203d01000e000d4a10400c050794941840c2e070030400c00340815000381d08900d128400c64010030200b5116100c00034007012b0030702000c4c19080c020140c0051700c034140c0d072252401400c000c00c00c911441e010301052184403011100c140d50303184103a4072141d01a0310107554034008060340e01c0c0202000c0f15194080b40c000d00100302c10f28030511900010b191a0075583d4a00380c104422800711815a60b524084082e40100200b48a8082d00203440344030712501d01049107849414058020031000c00520380540d180c0612a00b00c0d0f82c07440d1008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 913594208 1250 913592958 913592987
    0x70e01050d08090f03070b0d06050618011d101d10050715090b0c03180c0901140303040b0c010e070b0a020613021f0e0102010c02030702090f070c0c0609170607 70
    0x10743c2d500c100002107031a0100505480e60300d07020340080014105241001008210300d008020008a5100c80030003c1d1030003201c01e4060b00c40a8035001c0d210b02e5020f4010803000c0b14003100c4c00300b102c0002c1400100380b16050100c840008488007441404407c80f4425501401012104808051ba035510014150b00502e44054000e07940c5080c4060101c10035813010084a400500961041c86e10410350001584240d44502c010042e40c10980d00040010a451010341c100800c102150307481d2450082002d9030812071140c5c0750004010000d91002690010000f007000c0c2400400e014103016140c60a000e40c50b44020038800c0208141c01c841c90f0301207503241c0d10064010300188090414000b045038a080148a000d6031000c1801942c1041d402140f03402048409a00900c130800c10010100c1c1c580c0141d2100a4010000030040781c0e4849148160541c81005440d0500d0888001c0c1c9840b60f41001c5a030001000c170700d00c65824442c0401e1803007240804440f8000805c40c60800220041042c2d9906415 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 913595458 1250 913594208 913594223
    0x3011a190b07030c03080109090f060b010e0909070e061c06050a0f15080106091a0f0103140708042619090b0711120105070807080a0f1409070e01050d 66
    0x8102004099441903005845101410754941c0340e18a0090880981c1c12019000715030103030000500c90a542c050710800035400a94000c6114040d42c0b61005010352800141c18860408114000390310b40b600000d22030b40c2d6003001810720301d182504007814000042d1400b03010340c036062407001c0e9400c2100c0b4480d03400d40d808140003c050399a51200d4000342805502d4070b20241c00c20600441e0080580000002c1e10041c3c4000c0011a990701498000c55a401020242000020180750803178580100c00c0681080c041c1001b207407031640b4802280f80c003801151042c000c01d004400340018000e040c0c8030f11000303a0010001844c04201c6440105090040480340022401865010303032000c0d20883c08131004081d01e40381c0945460045c580142030400e2a113141e4003c00b025003101c07400001c14054180500e00940320103200b915081d1045801450043c0100c3c040c64a40d0301200040002c0c0c41044007444815910000741c0c140f54480605040d032560004183c0c0c070021006000b40d039203001d00c1031700c0c1ca64031020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 913596708 1250 913595458 913595479
    0x1413060c1b06050f090613031b0b040f030807020d09050d020301020409140a0507020c01120e0c0a08100b030102070f020105130503030f030103050c01030501140f030708070f05100314041e0209150a0503011a 90
    0x9d42900d200d41c146001450100b00c141480b08111018804000c498402c5c1c07640042e55450f88422070f91011011984400500340041c100607906100101d086031a00107000503182548840403801540d515180310740c40c8010040401a98241512415820040b00c1c4050466911044002841a403080c0349600c603540d664801140140020013440d1007400c80a4801038080790366951242d15200e00343d1515049604050486d601450b06108451025901003030031021510300c0d8004550075004180c0e85400807865a50205165a0400203040300102001106940b0f40c11460090300704802d28801394181410400103020400c0d0b0f15050551000040d55100c2c00c004c680400645081c003550700484a0380120407011440020500d000e9040c0e682c240c807010a40481c1010490841e0031000c94031f20103014990100300010300c0856400041843c0e24410b17855032005400080314043e00b5141c507100525401f1802c1560708051419034001c220032802000780e4100c005242d1214255810050f214950200c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 913597958 1250 913596708 913596737
    0x1203140609090a020d03020c0301151503020c0f0708030406030606051303141f0507270501030b18070c031103090a0905061c03050c011413060c1b06050f09061303 71
    0x3ca4603009070b400504030b0807090001d017800703500c038403141c01c44a0003942007103520f07034000c02c40320040760440303c072060500b48515043c03034224000d4016103561121801041c21503d0712090404c5120060042c0318061035850b407501c00c015049980d80c0d0300940c188a401d20001080d140f4503078004c0100c0360003026420f03810300d50381003a6040880341d12508049000d0080c0c1c00c05152040c1c1d000920410440e100c1001c0489a08800e03410045680002e008000100000740030951098018001081014044100e80d0881003060200010115194000125031040c41c00605500200c81b90781c40c411500a5858100650007141045440e801486c16040e02c43c00401d0440d140e15201d10008001e8a01c60907020b1294a4004c110747d108820804a44d0b003004c04020b00c203181d200c012401010201d0640d0081c1842c0c3d640c0f80041c0c0450b80d0207006200541d0884600e07104500b4550181e00d00c903020010b424680705181c4005188081c0200e10345a0089042007801030315400383c003003c0c9402d807c1c003054510b08174 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 913599208 1250 913597958 913597963
    0x60f070923030115080f01050a0e03030a0c050d060603142202060f120403020f100b0a03150e0318180106020309060d061503020315030a031407110409050a120314060909 74
    0x10507881302041c11074030000030f43c40c2021452000d466194802802691038800600d4141c42c440c62038100241c00c00c101103070480c1a03a0b442407200c0310f400e05201781051901e50f08a011241140c5c03266000c2602c800014100f80300e4000c549520000042000d103440010002000d04903a407100000d0140c400041d0711018407c20308151074505150110286840c9001d03e4002e407261000030750308806214034004502c1e90340d501d00a039591038001030002c815051039600e5904110f0032907072903118029a01c19241da0f034030b141030008110702c00203080c6a1070280800000d0050380c4e1480707010004811007150045c01019404411a41152400c0b00c0981d240d0440c41d032010024180c503440314031080f80b884103003454250107070061442004e103441070ba80410b50308030038591200d12201e4005c1c0010000040d90b02c4a00501000d042c80f03c0c0151600304000890001250482d03400342d0090303405912000307403076040042a0242d490b4511413480e00b8031000784464107680070080d020344614443c0390751304001759880104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 913600458 1250 913599208 913599221
    0x2a05121f020c0106050604081f0e030a050a031b030507090503070f0b0a050408010906090209090303070206010b1c0608030c070812072301090f02100f0c32060f0709230301 75
    0x1400346d5501d40d954012103075180b030981c00f00d082060113100e120440c1e040c0761250241190001010b1443c0452542c0c08981503407094040300d042c0340d41c404444101c1d049441800709040540c0d00c2c000343c0c90401f01c0e806042001e07564807103031081c0d010481c1403151000c004400022228070900d910380341c003160841641c1c24041d07500088219071a081016044c009590005c0084074000c1e1100203103034030f588002075101e03c0304643e80c40141c0c2c01003004006403815403000300602c0c0142140030120b001d6442c0700e5020f8442c0ca502c02e17403141d4408a030b41c00c4508014031560340240750341e00007000074000601001d4154090707130700701400c00e10004011011149800e200101310b0189540200600e403950301d412040c001003404140e008605460741c04903060702940c85c512003400703a515048030500480d51644011110740003000e4615050b006960304442541d2000d45030040c0c840082c01103454490b4140201c0c403030042901080000d200d00070444403a180d28001000c650b4411100c03d01040070b804031740903003603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 913601708 1250 913600458 913600469
    0xb0a0c0f030512240a03020f100917060906062d0604030b0a090611030603030f090f03010507020a0501151512060803030709230a122a05121f020c0106 66
    0x4400c420440c001510328506a481403181c00d1131403c46002c0c0083c094120100d02009401c01040002c184a81c903004e6009200c0810324074060358041e03191140080e4962500b40202003541c80081400640d101c1446103d174000e1055440a112a44903201400c0d4040c0031028034542c00703005096506035460b0b6600300c402650300011180ca80b810f0509500008004151056030014035000d480011981da5208488c081c29004009501742444c03030450b01c0a99005004a40e808803404054202c2038600b03000309441200380390003800700908a8107040e801e44144655040301109211802d10880d40340c11a0500842c1d07051921030081082e0348400002441503401600b1a0f1102008000e650755020b62400140c40c10045440540050300c0c10280d03808007081c641c2a40f02081d15018441c02c01000c59458480b0300400001100f284000d42d003140650482c0c4c810b0140a120090511070f0b4200118004244400d1340001d202482c0d10035490302c1c82411034084000050f130009004808400250001e8020f0300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 913602958 1250 913601708 913601737
    0xd140f0c03190c0801080f01060609140d0b040501060515090105040603180c170f0606102d0c0606060509030a060b0d1b091508030901080601140313020a0b0a0c0f0305 73
    0x200e0441c3c001d0902c40c03091107040300034881c00002406825040c040c0c4000c0391131079140d4400301070034030312200c00e1001c804008079002240c0200703640104004c0d40310a8040c902400c00001c001d800c0030180f0041110b6000442002041000004444d90b4003070100e4040f1a502e280014100d108145a046a00e0202c800940100142a40414119507130055004210441c0089074a80806003124585038402203a00d0b40d40004074101100956024088020000d2281c151440d0300800da00400d018802455400000050180c1024000c10001d44900700180c409030900358240002c000000e40d403104403010003020706403510100b10060712010034004586a00000c1001307a90100000040c1c220a244251904503007440c008404030103036584410240c807541005546070000000065400981c09031809040081a000344210f4141c0c01d405140034030501c241c14081282d041c0100910360145420410b2500810404620f040350040c080394030503079021106003001c00319401d0a81d50ba029550306001410f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 913604208 1250 913602958 913602971
    0xa020712030f0c030c09140103090b01140f01081504091110051305090103020d0b04110a14010f0f090302090a1b0f031a210c040606050d140f0c0319 65
    0x360301900881041c00ca0700308200502290488114140d80d00c040822020a0b444030f010f10445100d514103020410041c10046800b0030140d9805c1c110180c2607000c1c0d906883c508140d07000d207181c00380f122441d141003441c1501d12400d028008554041070013a1551065070b445040d841008100501251403010003410325500142c5004003500b90741c0440100d0300c0340c0ca000140810f9a20388078000d54141c0341c002d8640100f11565a543c804002c02c0a0000d5408240003c000510390356100e1911020b00080c0142d100700c2003c200000d000d10b18940c0404050190b0380c07410402c0300d82d000c070503401240c1e01181d480f000c40e190000030a0040800154184110140c441c003541a560081018001c689080ea42080040c18603881d80d0504400824280d501001c0c0712042e0035150580e01c0c2d84080350404205451200200f040043d044440d00d41c01140861030214080c00101300324420001100100308100340300f4502050020824007004081c0e00f0240c0020000c00c0490f2941c0d21040c214805000040116 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 913605458 1250 913604208 913604243
    0x2010f0219110d0c0b0408090d030905120601050102030d15030204090f020319030518120f0d30020a1202210a0905100b030309060d05010602071d0604050a0207 70
    0x11030440d81038100226030b4801450050701030016000c1e070780c03031034a07600c00700a6107156584611005002d0429070f0f08500c01d201060055a403000e02d0303a03840d80302c2e4039011486444d0106000000c03800743c030341c00040e800500041000741d0300802122030445001c0000500e400822440810740c08180d080690442c0c50455130360104542e505031052210b000b01c0c2202c03005500180d505800780c0072108010006007050041a40d084ea0741003004500d940014204200c0c07111307503031075145400c21003000c041c8154008000240042c1d000044d2201c1c1c1a84192108003514800004412810010780d43e0080240c0c005800f60410307218120414201001e41d030195664140a00c042c0380c2d0800c01c0800c6881510030202040c46003050344501d83c0c1c00355228001d4415501c00001031002000740320062358250008109070a010394500009199800a41c0130008440d410400000c0c584103550304442d00503015480b08401d203144840c4065802202145d011441e0741d1081c40e01c1020b4051040300a002601d03101c07107240c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 913606708 1250 913605458 913605487
    0x302040306150317031e1009050f0609090c0105030c070c170322060c1103010204091103040c052d012a02030d080613020f07050d02060f011514090102010f02 69
    0x11079002e941e40c6043e104e0740190340c4049200c01e072001c4081510242511a0141c1c40c00c151907405a139914040303031b056a441c01a082030b20012503a1544a40e0f050040021074a01110415040381d51000181855000074002802500c40601040145031010410004100c000c00300c0c080070705003140050803514480e6448a550380c1189010070000e044501c04805100b078100070341001c440c034a40c0c1e96007064400e0307150811141c1c05c041c0000c0d0155001c1002244115030350080d074030400b16222035a540c078a03150a000580322501d4006602c100c08030039650400a2030803950b0f80d5003030110700e200034551010800589580b500d03082c0844281d0489940303050803e038210072031010b20340203405650761412040b00c1120000000c540981d0b022403802c16416052505a010700161221040b45c9882c3c030942d40c03151482d202c184410390005134490004c0000c5a09401d08803801800b0345000030003400f00000c00500070340d48440d000444000e011895440aa00c01d4001007418403645204540c1c42200880405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 913607958 1250 913606708 913606751
    0x2030d050a090e0f06060d0603051b040f0203162007060c0b0f090d121e0c020d050304050c0108091006080601140307030b06010e190602100e0303070f0e010302040306 73
    0x41030751071000240c925042803c1600c5441c42d50210080f940d91002040030030307000010001e0200e40d46070804000150200115800482c0502e0f0300011030324041e0810041d594103048400c851401401400b8a4042c0144440020540d60800b030b40d2254580c0340b05c6000b422505088030803403040784000104c56420814500c0124000d11000185039a542e821462044003610702c014903078032000550418602c90355600701409036040d000320b00300000c1802c009540c03a01941d640c21082e95034081906060301000354507451501400c21030305500d06034888a40f80c0700c240400030306000b10400028010101846407112900002da003c2040b107442d00902c03581c4850902842011407050b80100459290004a910845e40d04c010001140c5d91401c00440700c5a00c6002550340180c1c0f6104c10320800f40031582c000001d403640fa40200010b140390a40d00064030b0098518080f250420001d000206034401607000f02c09580d4200320b5550300300b1400484c000e20035644041c2045141002d41910040b1010154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 913609208 1250 913607958 913607977
    0xc0302090406303816080414120c0d08010e0c04050d08040806090609011d030f0a0309020604030f0209180303060907020f0a0b0103020f0301020c0601120203071a070308090303100603150302030d05 86
    0x21040c90745c48118404642c0f128031010b102180340703038000030002100c1140310014908a482a50344554484c0b101c41c4042d00a80f03a800c500b90803c0c450881d0913a80854958014444c3c42c51840c103a00b819540c0403200d10890155600070f0700d40b045800c0c24090005c01b264000d141c0a01161124034101c10f903035849200640b4828135035424000114180384294280603030603071042010398540940580f810741a03a000440d0b11044c941c41d0780d00311000d40c0da034102a000840c043c01500410030414410070110800091042c502c5003440d06035500300240c00020b480d840b10041d160002c1d581c4501500340e24080301210100c56900c24641c6101c10424000d4105040700c2c400d0710112003002038030007003500782c0c040c22000c51030a0384800010404030302820400c0b20201c0c00134040e100e45171344654140c06a50b04040150180d04400a00c040030580e115001580c0034801001035800c504100c20b03200c4507814030744506020961a4030803850140d0f0480c1403000159801400c6a028480308a4050083d0700100b480d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 913610458 1250 913609208 913609313
    0x11030403111204060e040e0c1008070810240207030c0902040305010b030c2b0204050f0610110606130608030a0c12020c09130807060c030209040630 65
    0x1001042c40c0c0034020389066542d243c03100c000401101d4140802081140d4455403244280103e61006441d40242e580e100340b9542e403006c0c0107140c06c06001e090b00c04060065084540c180c0010040b07036103400000c0504030402d40d80e0443d950001c0030304918102c5613070001b424140400b40c00060101740c2c0d0740100200d91183c0002d21100f2202810103454890001005800c17101d8580740d0b00c40800c841d050840300901c800000341400c0c03a16000f00c3c0445004a6102c44441492001c1c462103141102c2c20b904200300e00e02e04485001504810a0340742c42016140500811201410181072440c5400c103078050101502125102c0c182e41074020042d9403c0c0a05a0b0303551090341c604000f141c8040b4001c550040c02400d00b9a103a02c0701810006240583c0005440903a4180300103000901c85018080b0884030541d805030321200218100000c0740e585500c8a02a20030410041c50f1a00c2d44a0480e0580b0103100b0300180c00000c2803c0c4290000f90b95041850481c11006000030300384100b0000750080c3c20480e41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 913611708 1250 913610458 913610473
    0xf130f1505030f1303050715020301060e0904051518030705010b01031401080a08180315070e04092609060d0c090506250201020f0714031605010906050c011103040311 73
    0x41603603984003da600d92800c000c81c0e00060907080d10403441c400c0c07152091600ca442e145041c0c540c002c4c02c281058858103159000001003203410350001c9600704490044840c1c0c4000d040950343c240c0d0390340a0100328203903001000002080e110241c80c1c40d1b8445003503402038a03901d43c2c55107801d41c001c22341c4c0d01c0b16030302182c90001c80304408680d000e0b0681c140c400041c0204035041c2030703880b282c90039002000c4000340c1c40d64614010200c5c0e101400303400684036822004020303034102140003522034030800c1e01b507e028a02d015403030404240c0d140200240220092a0419240b103d103462000318410307040340b10741021000415a024000507400403040500981d14105c1d4142c80b401085014800d481c0007070321920619891103082040348103072011280c814011240c8800100c0d41c958140f043e540c0c401004520140f00c20f050034282846001c2040c24038500901c199070a09001030800504c81c00342e2010000b01203106078900c007007540003441081c40c400c0c5150f120310b05441e0041240d521491851541e004030745 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 913612958 1250 913611708 913611749
    0x21f05041a01030c23040603081c020310062102040b0307080108010c0903110f040608010603140a050d050c030d061502011b081317040306140906060907050f130f 71
    0x30701c00d06a030303804030545500070325142541e04070ba4284161250981c02c809218030450b80d446c89510000c5114810301c9485981505070b403403003411260b4051085030300420401074100180c488240650f11141004072044a813403924105021040d41d20340315041c0b000601240c421905e0024500c0b58000b5902d88106a8a40098500340c5170310390056408a1507128045c000500040120351800c41c02402c890311020002c0d000a054480ca540106683d0350b60304000d1081c0614503648031030b1429070000500d144a1fa03562140c0d60344158480c10f0040050100745103842103000c2c0212035845403c003200b030200d0b546030a40c00b14150550f11405015602c0d00309042507000003111001280c0e40c0703a44422607a40d5070038101050071181d00c3c10480780040392549404408815a002d07202650145000080202c0e418003a1111a6805804620b4590008040180c20b0703403090380342c0b5031054242c542180c40e14080d40440300b407801415403c511306001d0300000700340d440c2404000d0f0112805404034844013000030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 913614208 1250 913612958 913613003
    0xf0907060f090b030a02091807032403020d050a0510050609070810140303040e0f0106030b091005060f0d0c1e0e03060115020f0a1a15011d01021f0504 66
    0x555101c0104498800403c000424040a16032040c5c207450054a0308820400241d604c1d0749034410701e2131000c2c550b020301c03440a501d441041566003400803411300c2000400030403510042c151000901c00c541d40110131042000a1055568050380302c8100c4140300c03001a00c05001c2c01d4110b030b0690245801c503001030005032003504224080e204d0022100c00f41400d15807688117000c1201081a007502c4100400252074103485071252160b8a05003401501d0750626000170299403200000c00d01c500411818071084c550481010070448808a420079600c40c8132118188850140c02d024404084c6461b40d0385070b8050f00b15030036040045040580c59540d52011105480030703440d580103241c0540c000b0300144092205883d01c081d010400780121554514141b8400d0f05d020550042103a04040087c9041071048004080345d8100f0340c0613050022580004000810110200c680081b4a43c4002c034001e06a90091000c102005158141100916800d50b081c402400007078a00f15500140f004800008a0a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 913615458 1250 913614208 913614227
    0x12100501031416110f030a1101061706131a0702060402010f0306140906040621031404060507031d0a06020a0506160917010e0d0c03030515012c090f090706 68
    0x20080040141443c1c41011282041c454140e00705a11596040291445080000d003e4051051380ca004075003411032100350a44465a0001c108040314a090301480c18021030416805071952403000d450400d14206041484841800c80005658203014030028030f07808034800b0b01c80c6000380c80711203965242c480304038100e4070a07119000e02000d20a0042d10203141c0829001e41040c401000803440301d0300c4d011100b903444240061040702170040310302c5508140c1c01c0840802e0400103074038401c0c1468903005024181d0301c14500010100500b19140300e01e20145490110b00c59040540004c4150b0b8843c5406551210310220580312884bc072000240300d004011949021131019660f120000c6103400104480134500050310000c0d5500c0300d42c5c45840c0503080164a45050039941c1301c840d0130000f803c01504403240944081900a08060b421400380d811100400c0c4040d4034840b0080c0f1001e000008940410340101030139400002d400a00101540a4400074002c500341d8003074440c2140c0d940030a454110b01c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 913616708 1250 913615458 913615471
    0x40f0906061b021518190f0e0411010309020d060f050105040e030c1507090306380a150504081e0c01170705071e0f0c05040204061d06121005010314 65
    0x56045007000d101c0d80300809000324000b0303174113801d91060010002a6005071050540b050300980e480c4100481c2014001110003001d0524803001a0f0406896013000f02d0601c080d46414162211685400c40d02e41c8551524515040042000f1040391403407103a018090a00c5224402d50601c800f081e0000c8001c42101c0300f42d18210020032484031501690100010000d090030700b4451150b00c0000030640b075005540e80d02d002c0300c0c4241e12a981c00c1c109483d20b09010141035541100318800500300c1d1300d035031070308005a80420485040c10509680210340900c92900207600d1801440300c1c940308500020040c104002c00d10082d9100003801100440340340b00c00d031180041e089000d1002c1550b02d409040200b00c03032030240d01b000a1020011441c090500400b0104442c0f003005900408240300321400c0180251000300c80a510f42460100b00400d650101c6c9546a08000c0300d030132015103a910402190b41c0a12800401c6049191042c1d4a1355125007620409000c2403c0485090800302c0385014984070340b0703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 913617958 1250 913616708 913616719
    0x40e030f190314040c08240723040f080c040216060e0c21010b01020d121e110c0f0309090c090a05150c0c0d02030d1103040f0906061b02 60
    0x80d45400d0584040d10140c1c0315018180c0e0344400d043c051011800e200d200707a00444d42402510326040302d0030701e09103004200388010341c880782e84c4e0480c07041b007009040d4100d5080e19000c0c19046903100c800c0c0100d11210f4403100c90304400070700011404034000758074080b90060b40640c1c0309500e028041c44240d102d0301c4040014202640d034540300185003640700006580c008400c41d01510003045c08141c4580800d01d400810314100d0184602c450000d0081200903c028030203007052444660018043d404a21283c4085503202d43c98444032032808031209895058070a81030003a00c180e4140051070741d0103005010207030701907907504100c00c000010031039041802c00790648800303540b5005048011303002105030591001841c2c2c000100c2d50780303809500c0720314014809035965400c01c1401480ca00443c040d40300d4000e0320402078100144c1d502184882c0d103000c95062608002c0c03804080241544a95005070601c0001c106c1e001c00d0745031082d4003d40994000d500c0300b200c12042519000c0340621607181c02540903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 913619208 1250 913617958 913617967
    0xd0503090d030201060f09020403060e010e0c04090f021005131d060114070510020408010f0e030708130b0309150c16060c26070e0111101d010207030806040e030f 71
    0x181810000c40758860302a10002912940b64082c00b00d070100a6403201c100c1540100e400e106100710f40c0705910300f04042000170820809200e0300305440e842501021485559565650001d101e101c0205440c1542e0060100c02002e40c81302c000303000b40d000707140020312031140e64030046082820304811282864000c490400b645d0381e0b0300011070f42d0a10000c00c6000c40c9600344031880010700c04100e08600104003240150b165401e1007562401c46420b003044c1c400250900ba03280748501004004c40e074407150490030469640c1161138082d0b2a042055001c448000d0000041010595000c22000c0040181560b0400c0f15280c0c0341d04034145008001c500140070480c1009140040c00c036610032580d0980a0501207000d40042d00100321140d41c8501469510902c4020403002e41d5000030700003640c0909003000004210b044910942d00c00c0070310b0400039016a51014600d10130030515030b008502010b0346c000c0d5927410881c03900900400f8241d44080c00350b030412003041082c0c0700c04410780780000fa080e404142007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 913620458 1250 913619208 913619227
    0x51602120d0f0f0501031b0b030c090402070209070e040b040b09070f02160303020106050a090c14070f14030a030b151c0207060204060206040c0603050402150d1416020c0d0503 77
    0x3650300c6200400141a81daa148400380003482c010202d101103090360004030b96245050141d80507038110041e007170039503a0b038109102c201c40d40070640c2d8110006a803041e844005400c0450000d200700320020b540601c20400300146c2950005d28100f01150580301484001015401d000c19140281c1036241c0c4170540100280c19644154401c2e0560740b034901c111030921100d1904d18082c0d030201d4006500603511000140010b09080b0281d0b0028444d0079810007602c0d00342c0f034008010103082521843e43d22800100710017800344007020810f00541205d59981710606d403000031541d0354009020030b40400d08140d44018640362400c8010110780010240c240f901c01c05019100d08171000729072075000982c2c2400f019003c10000d101030000b808040d002044030703003000d0502e200307800e05e0f550000302094140340810006844d510000c540c01c84c00d58042c41c0d202c00c44016004041e01185100d0440010790300e04019501004040780041b4800b5a0207031000d0108140c107020036007070900d41c0030f0300da5803040005201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 913621708 1250 913620458 913620493
    0x4180303020703020114071106010b03070c02120f0111301914011706010806130f050c13020405010e092205100f0515010c050c060310051201020409051602 68
    0x83c070910001075842c103030031405c5614810070791b2040c0005aa414000d0451a4204006805031082010484c190b2a0015008180055a0f40024091f201d840c403020f030b41400070481d410305081d0000c001e001c1681000c044640f140c2020030b44542c450400c000d0542c035201400c000003c1e03030070a0625030709103980e00c0781050800c00303450040703001e159503908100b689001c403c010039000e06210200c0b04803100001320480d03c0c00d101078004121542018040c840c0a407900c14284c804c2546c802c100b104214564240702c0c0c1010254804a6005403203850b00792031803007883d8001c0c001d6170001d884d860602c250040034000e002c1070440b82c80c2c036222000b4078081c00c0b00800854100c1000c0c4140225018a2070440606045d01e10000c10403415507216030900030440d10307013003412001440078a06601000203d0325a05d54407001076480e00e000301c10000c041822203c030722500c0b00140101800c1d589100c070b40c20310400d00075442413144c0d10656141c1b038046040101e540343d0380c100e082403035402041142c1c1d80c800541d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 913622958 1250 913621708 913621717
    0x12051203150901170d140723010504051c0504050604030204110702030d0c03031b020d110309210105010509040c0905150406080a050c010305010602030d020304020d020d0b150418030302 81
    0x30701520a10500c144540d49903400b080c0030702580d221388034685900e810110301d44003001c0c012005101440c031041213801c60340010f0303602054003c01303d5810200000c40e004203403213881c2003400e403e5003000c00300b0040c841c00290780c2c8a541001c480510356107240c8681184c240c0a00e00410358020383c204420005407616402510039119064501031030700125900091030102c1072102074000c141c8010b03120061541520425007180d02c40c541c0b040c910400502e0094035158001c0101050041075609161500740400603219080d001500d5840a0030380301c038004107150604a8411443e60030000049001c2c1402034000c1c2c05150700801c10000c06081030001e001030040189103041075005400c80c0707502951382e030007500b0081c240390000d00381c0e44d400c07418400d0600c020324041d14145820a401006010f41c00401c985c038081d01c0303d100507102d403641d20015160740303040316020f980142116115018801ea101d031480c000d8904007281c4a07450f20180c280015250340c025555900601c604603000407038081d40040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 913624208 1250 913622958 913622971
    0xc0a09060315050424050a03030c02090a090b0106050c19030f05072d0b070c0b06012715120b061213050d030203150901080c0607030c050303010e06010912051203 71
    0x75074041e00d48000c030701102e403070210040041840c420008117413050a01d1600141c1010f42d580488541140c401400e801e00c10880203000e01c1c4000e0000700030b511282d2080c11469448882442e0f1135a440f1802002508901000001400b43c02e031900c424111070100344142c40e60685036007414007485c04094a80f90012102503c1c2d140f41c25440200b403030b000d04400b01000d00d9032400c56090304002c0c20300402c0087c00070844801d010303804014501240d855080d882c0e00003401d20381904480707910b2000141c00c80f0809a05a0115081100811a59002079a40a4100c9075030344400700c1081d03000f0440e00b5654046103c90304460308000b1400c2c4880014023480c1e101031000940781603e07100382d030b03200d01d00892001c80b0000207074040203020042c1509800a0b402c01c008441c9003015504040b074141e1555203e6030348600c038180000c0d402d0205405200404ca0303040e002800c4e00d0322580d455118942420007201c41600094910101185055016090720242c580044c0200501110000e00b00b58603071026104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 913625458 1250 913624208 913624241
    0x2030c070608090a330f0e010507120c031415090f04030512270105040c1e09020c1914122b020408030d0204090509030f0d0b06070f14060c0a090603 65
    0x1126918105c10065a680720754035180001c0c002c3e0000d10f01821100d292610344140d074103242c2030144842d0b0100b100c20700031080b42030000d000305400c0415001050741000961403044002c04200c0010406110140c020b501924a800c40b80c4da180c0e4642035040d4100d4005011420621040a481101c0f03104c0503441044120302d851a200d80b80190004528192150011a91564100301c108128500060300505d9000348244130969007040d9405200e40358041c044000d42c1c04513100f03401034003c00000042c410309044001d0341840c941040c1c11503504e2035046c0310252080410702c1038000d21000440b0000150201d00c858240080d0b00c8890a0030071500400c8011902400003040102c014801801070000009005944600c2c0c100c4000941e1001010303030500d0340040c82210240440341049030600b46038600002014002c51000070700c00c0c001c00c0c1001e4280328010f180c2100b0000b9a07051a0700c58400c0b00220791096483c1400c0f407655100c4c10400400003a0f01420800c081030190b0482800344801915 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 913626708 1250 913625458 913625513
    0xb1e250318060504150b0109090f020f130602010e0604021c0c08031903051b040b0703120203010b1c05060f0f010333060507050a170705060702030c070608090a 70
    0x80c1d264080741201069485580d2a810702003000340711092020341100301281400041003550018040440510440582903110303116003201c480103504a0f03001d1400056502d8540c0481000070f01d00004901a881c09907103081c880c48070802c40042d06502c04c030303070041c08012020f40080c1c803d40c800241f0340044441f40104000819444014000b070079040320f800054000b00704d00c812006050303540240c5906d00e80b9404494030421200c0c4102180c0580e1121900b0941e2540d9900c0c00b00c580e82040010001d0042c0b012001090004280f8010012240c40860201c010400c0c80e81400c1150703000d0711034662000304034001030024200440444841181410001852050181d1034150701d06030303142250000c2d50642002d540b003900e034011a4007414240c941141055656922a80e4815014001500c0781c808554942d842503154401c680b00168050700740e841d24180317480069035a80219507001d810703000d1404007280b01c0d4401c0b19402e100f148648001d2601c91403903120880a19024650000c5c4100f1515 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 913627958 1250 913626708 913626731
    0x70201170405010b190302030601030308130813050114090f01031e0204031a131106070c18050402040b062701020102091203041509060507111c0b1e2503 67
    0x44a0784182d00403800031401001d02c904110482e000a8035445540c18880c209001503100041d01905680c0c1c141841d0015854150014030807c810800042050100086600c00c09005030400b9040714400e0701c840a400a203154100218090305039103e40020310056007101542c0f194011402000c04502108021800e041e81001640c0c0940c105440000a904c03403942d40b590003a105a0b40441e0180c00c40340c03044920303520031020b041c5940c0400d01c5110041349180034804507071903600091804e01c1021601000c0c0b4205000036290440e005d0307100310302e420031601c1c0e00c1c2400c004607110120310320490f102440c035405440300b05010031814181107650a000480e000c1e2500c3c03610808070882c000c010340e120f91404003005c2405100c1030a2404000c04503c00300300d15030f002000d852095900070701c81034140c0c07040070210340d4241015090f00d40c0b40e00d07080c40220501072030035000c230f004000d5100341520500024a0750400c410003a62011001d05041d400e40e5403d4640310301058800e0740610700442c00b2802403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 913629208 1250 913627958 913627997
    0xf13020d090b1501050706090305040506120f0105040b06070305131d180a02100c210e18010302030c090405151501030f0911011206080a050115210206070201 69
    0x100500301980c1d660103082404900c503103060703202003405480c440401c207020000f41940100c0034010142910352541c0d20400d4007440940d0080c000141c003417a04e80c501e0808142c607600040d03800181084854001040500f410f00480c46d0b202e40c084c0c40d0519048150703038229083e5001100e003803506101000e000c91842400311041e02c0082d520b461140060400b52000702580c010700590501980c4054044401030f250104079034041d08080c1007075000581c05042907070361002c1100000000103000c80c0d0b4001c209402c8000c00ca10310800f0354000301031000c41101400304020a010107035140e03003d8030140c4620f10f07000c00001c0e44644a0002c0d606c052040001e040b664940640f141c00c0c1c6044036191102d40c2d035070300d480781582000500c034050003610559121146110084241c890420803042c1d070030304102c111904950300402c078450403198101100e0030440d0007050f000009a045020180002401d0000401c0452500102c541305114040e0b440d0300308102640b1a00040b8144240410f5a03c0f501400303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 913630458 1250 913629208 913629217
    0x30302010c120603021e0f030d020105070e010908150403050c010501060804151e0e071a07061508031606091e140307050a0209060a080a0302030d06090501050f0f1302 73
    0x1980010820180040d400382c5800718100000b541e003450000200b0250fa540c3c0d0f8a00610600f40c0c40f000c0480010402103a0b103111f4440045801d0712801d0621f900c3c00303505500903881400a80c2e1103401e00b080c00c000450700c188040c03140e002d0030740c01807500244170701081444680082c03003410114a440900c1022030b0944009a001c0700200301c60717204010070f220341912880c8005400740810032804910200c20764030140401003503111941d841c401200900400c024000181001002d442c80500032128003101907409810308039a51400c0c11070141001c41e914507a0025101d00c440034504183d51a2049640f420541e0000d40d02d068403554000040f60404c007040c11000340010b0828001c3d01a818855500061440290000d80c010828107000c10f0020490204066045490300170701c0d110300000450359462a00004540c1c020001c04c4010190000010000c144a0350350a01c1030740d94034030481c4201c4400740302e95600100e001d071000c0c0d124508102c030031a09510040203002c80a1180c044481240c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 913631708 1250 913630458 913630463
    0x3020411090307180507141218010e0703120905090f091507030c110705030a03030b040f0e0a03080601030b01050f0a03110315150412150b0628080408180d0c03 70
    0x8010b004100e10005801000d0b84051142061203001c041140c7c140c0c41440303200100f0420003842e40c007041d03005109101c01108441800001d1168001b44a81d85403a16034a01c01103c44021350400e81140714005c1940f201200c1d03000f406054180d40b42c1c0c00b11001944002d000c840c41f4000d849204840c1407800383c03a20f0003100713143c0d030004000314040e1004d4051107210803843c0003980500800c04c5955000a0041641a8940340c0030a950700c0350000710340a003950243c5a074909040c02d0711030f40d810ba00020310400d843c3c002d6440220549414006404440e83c1d000c20900069040245c00758112030100244020001441e000409414441201034103400540e000442c00000d0003160381c0707501e043c1070342c120402c1d0502e8806107043e1414203821240103507010000d08000308810070561a4074198043c018403200540056590b03644152139a4070350840e1145065502010188614600d02c174000e42c620459002c80060310705280c1c058030b07400c3c403001010b0082d0310000510440001070b091000c0c0d10010752 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 913632958 1250 913631708 913631729
    0xc031b0c0602060624090406050a0326030601140702061209160801270213020403080d110703021b030115030f050106050613030b06040209040203090706021903080103020411090307 79
    0x5081150003810f004001d0403051044d08038103003040201c07003284d20040094100c1d51065079107080c3c0b000407030701031f08003a401031781e10450511001050101c507120080200d110448440c1080680c442d12910314002650890300007508944a100300e203c44000800300d860005041c0c41c1410001c0850051190040361000f00d9908170708010260084200c04074009003a201d0024414100d010103000405041b8007c1180322503407038015501591520b00040c00b030902d04a40c15980c4685030b01b084c0b04036500c030004143e5554548501954402d400c6004d44003019455405051326401d0340300b0011082e20105680c40d03145d566058440c5501d010070503e20000c502c1f449603280c030b50820307042c85800c48141c2e6100900070310301000310441101c00c807100700040d0f035030101040c0c4098450350007050090290340030a54200344000140180c441c0006501300403103100303600721043c40403100c00d2102800e0724904014085001c110041c00185032035009010443c0300300d05040c0c00e1810000000b450318642c2d80c842c0302d500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 913634208 1250 913632958 913632983
    0x4200a0906081617270a1115030a09140a060f0b10050d051f031103070f1224150e060a0e01060f0e13020c15160c031b 52
    0x1070303005503555500c03400e400443c031003401e415031000d810203040610280c0f02e000403000040e20b52499174400c01020f800540900100d100e031a0780749541c1d135001103068964401c070f0105100545080340c6d82d81041e180e6a20313100d003942c480580d51000341100c42c808a82e03200b96421501c082c88e000b0800700d4003c1e402285c01150346c42d404120b41e811950040720b01406000410001c0000d950484200e8106244100c4d00040039078410784050080715034600010740b885c1c1001d00c00070920603054082190f4200480a48a40701e0313031004950f01d960321510a0720303040c101040c103034808070309648031082d142440d0b00700342d08001c020320030b0410407514101c1d041119180061010f100142c481c4404607840103040d22017001d29818080d031a040013005220b0742e0200000401003e03100f40c80340500c1104014082d0071030801710640c558103c0617400203e0066041d01c5a6201d602040c00082100ca020f041c02c2d42080d490101a01c2e0201e801000550042d010f20052998890000544040c910441c0f0300401c80038400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 913635458 1250 913634208 913634219
    0xc03030310151e0e040506030d0819180305120f10060302090d021519030902012a0f0b1b0f070b100b04030b1e0907050f0307090f3804200a09 62
    0x841c0c0c0d01034a1903020741c0c8601989c05d02d00f40c006560030f1b0014030010805986084199500340500f0011000c05100803a901c03c540030150402e019000e006c040e0420f070701b400e6480400c40720424104403000b00762082c08140802285001340e0040c4060000508284c8040301c99802054441081081d109101180001d42e00c3c1c0c017002d00c0e640490a0059480c040c000c01100360002403428040c51003001540308075180410140513004000c40415a01102800311420181000e100c120300444048500c03080c4203403c46804507a040071222020080d14070141030558544503076407208001803901c500e403000c900021511140c5200a4001580305160344212454452000501c0b41082d5841024081c60036080c48005c2001080800030385000b9202d044c0f41f14482c400103840d00e81c6c145d0211a0080c5049440e04941701d081c1c105090741c07000c006920304490740460030001d0043c0600502d851020501d02002d405207460f8100307440048110141011003400a031080039243d210905801c045011307014100171 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 913636708 1250 913635458 913635461
    0xd20010e070b0301090b060a0509210d1808010603050303010e04050708120c1209090a05040816030804060b01171f09110a0e0a1a0904020d0501170c03030310151e0e04 73
    0x603486c4042d0b40b0203040801601004d400c60003080c0078076110781300b80d0b035038024014040118240120354010480308803e02680018203440b01589107071304204000c0c500815119030500bd48402c0340c1d03011004600d160b10308808a6240d1401620868841c0100744000888680400c0308030020424406070359a69030743c0059540c9000300d43c201d200c00c000310070700c5044215925806840d40c4400307500b401048070b55440c54003040e540705036082c40c0002000b0b04466400d059001c0c12062203207103c0d11040294043c43d200544e20303041c4032110800c00d144698001200c3e81c070082001100200b030001000d126503150384049080e9520700c1c0303070440d40d00f00100d45010b84550007100d40001a5055a182124504007898541c103402060b5840c0d840500004242c40d450301c1e01d41c1100c0d05e42c113181c8010095961940fa1113151840851603015891041e242d4000b135915021040302c1c000c1000c4900708482c24682a100030303e0305000d0aa03003042c0181c0c43d0485520072110000030102c00070039500d85240046031001c210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 913637958 1250 913636708 913636721
    0x50414010905062a0a050d141e0112020d1b0f03080703030c0309021f0c02130b031b0a0504050c09031209100c0f030309020d0f230d20010e070b030109 66
    0x2074424040c04101c810704c80c5102c100d400510302480c05580c0d55404c03420342400303029400c00001000118400700203400501c0c0701841e00c00709800d42c0804081e6078400300031203c4038034160043d50042950b8503903000a25004160b01d03409108041d03a0750310564425940881d4803841e0b00581d82880001400c00406500d0b22440303c3e14003890808202410a540109084035110030403240d84901c000140d800c02c5004176030b8842ca180e03000713082e000000742d0602c0b031101600c0c00c01c145034006c1c49511001c80d68181440d0f50310032000c00182c030000b4018900b008110140c4000742c0714500b4110704101e55074054406000d0b07000004401c080c01d82d0745402e41030a000e001041845030303000300058130082400203030208600700708083e098600030400500600009841e85003004c4002c1c242c404180e84101000414200900381d06040426100f40d4103001d200551500003c0d01d5840c000742e09a410302003103006601d0200c0a08201d03400019022071065a940d20b003038207a40241c03200e480040010820711502d4025603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 913639208 1250 913637958 913638001
    0xe121b03161e21050f040b070b16050d0f091b030b10060518030c1206090610031109191d060a020a050f0a0318230c1305041401090506 59
    0x79000300ba96519085a80050b000c080c0c0e12920f69140744111803403141040e20155000b00711155644c99444202d1003031039004060446415500c03000060f0f002200c83c455079041c0105840d914645280c8801150007040b0000112400645d18a003142c0400d4134000c095210040003040004c0b0f240c2107040401060800a2400050282b070000501c070140c6e102d41036070b41261099070f200a1181c801d100003800e02d5000c18109821920f0405841c005010010b00781d8022194881a01d51980320080800e07000c00680c04003402c071040343c51044880782855412030740e10000306c100685070b0b51400f13405002940c442e4440c2d202d019982c1ca00b8401403000c10307c410354001d05107400c2185010182940940300c1e00a544905000610201344003a00781d019800140b4100c440c80034481369142d061510310300480c0400c03445144094110790b4140d17030040014000c40f442800070821010580e40300c1011003d0a0004c0c400c442d811501c5950341003115090140381911031003039010b40340a203019902c02c0314070351400c0d074603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 913640458 1250 913639208 913639253
    0x902070204060f080a06020c2e0c02030a090530010207020f03010213061b060507050408060a0e250b040f0815070813031107090f0b040e121b0316 64
    0x400c800c48001441714155644610003503228216407044900300204401d01400031007100c00101c00c007543d1615141800069403104019101005904070f0352402200103aa0200da10720109001c145001032100031901c801c2c00b812110196402400906590341c08500c0c60755070740214209046180200300b202303980c141500214202140d0400c02c42c0c00c40b00c0c0b88202c0086c01528842d000200301c1c103610f5094039035000b603818082c6040c031a5004006600034840c4103098040c150115150010700d02a0006030b4a0354402040400007a80d412030030550322a07480c4445078154000042d412600c54041d100804010190820f014509615107042a5608501003a518500400c010b1140d809c980e42035003100c0481282c1c1c0302c4080b00e01d0282c03040f140500882042e4400c1900c00110f8140a03000401100d40c040d0003440300145480900c425124a03102d840c03401d03080311120402140d11907018044840d488c0784101021480c03104180e0441e40050030241300400e50f00908000d21081608a000784c2c000d85a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 913641708 1250 913640458 913640489
    0x60210050615030c0d1806061512020306040b0a0b0c190f121101020304110a05040c05033606060f0d0305090415051809060906070c08071b090207020406 67
    0x50314002c182000b0008010001c00450388a4411100351504100d000e10104510203000352030190580151000700d4946040c504045034080da442c502d0340400c611621084018000002140060b400082516400c550b466481c070f12541c0d9a41c55202c01070110f4140b45945442d100d10076805c100000b602c0d00d035200d00320a1407000040028040c0560180c03c0034000c4115150820200d640c01400c1408441035800442400148240095200d01d04c100440d44985400d03981c01c10b00068500c1c16880001042e000d2000641e100400003501c04491001001044004c040c1c0d1804e00d81c0803422034243d41594070150403c41a41007c021801685108a40c0361848001c43d90380107010b481011140d41c0900d4590000c03106041311010b01102130680100140d1000303626a90400c0d80c0c0900722011003c511038400807418642c40420014010b19066840d248810500e40707401d856a480303002c00b141c0d0103010040c0e036000610700e03101c0c0c00d015020a580c05a9604402d004000a8840c40e40001824601008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 913642958 1250 913641708 913641721
    0xa09020c0d11030a080402060909040834260406080907081f0c0e130b0102010513170708071509060b0102120306151306031b020d02060103061d011506021005 69
    0x16120701407558a06042280d1b0749101003681d0b030041d2407500d03400030686c8045c0700400074103d01034281c200b429141440390254002d14000442c80c0c148907003082804110030304002c9010250074001c3d4200b1981052003c1080d10141c1203123174040d501c20f0f4005483e40040c0013607e8010b20440c0010286600203190151180c0140400345c042e00845400301591400e1200307203540213015803801017800401003418007402881d86400303020341e6540c990043d442d000001d082d08850f465102c2410b42c2002800c00d4909081d4401c0340f607648609815104080184a04d000040000401d050104255680800c08407480c0c1b50030300030366181040c214190b40260104142025680e01a00c1d402942194980140c000d000d4000e80c09110707100c110b207031660541c000030480c80d070107800603c01d540c20f07125103c2040c01d1042e000c90b240c6000004010050308030400410200d08641c00c4908201030880080b01840c452202c1d1500312098000031550034001c41d03008111483c3c061001207611140c5a6050040740303444c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 913644208 1250 913642958 913642963
    0x602030910031d070320010504030c03030f0c1421070b06091023010e030307050307110f09100e09011401090e150709030507050f09240a09020c0d11 65
    0x951101010303a910a40b000500303000f0140300744866898161121240c80c1d04006001c80125030040c15481d5003a441103c03154443c10407502101c0d0041c8004500710708640d002c4940d420345060080c2040b60204051002c202d900440d19174a00d5580300912180c08124018544084506c03501003198205100710004280304680e1b2540c410011100c2410340d40d110100001c407440c2d1604040c00c3c0500c4050052008007042d00b80c1c0341a83c000343c940103212607a46c401c15984c0e104e00301c002000d41d0014022180045c480103020508418000d222049501000000c04e8000d881224031a5507000c032a07804000505208059540000090700280030307190704141414440c980611550002c6079070354112401c030030400d1055182e4405003081e840420b0902c0c0d44024000d80035400182d03601e009400c800601440d00940b60251141e025000b00440c1d07a40c00100030306012003425441415102d100d01c280290303224207900e070150422600060716610a413181030714288500d0030400c01e00091704507040062000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 913645458 1250 913644208 913644229
    0xa0614010c0209070908010e03090f0a08102f0304120e031207021203310f03081c020309030a1b0b1b0c0304060e040c0c020f10020111121006020309 65
    0x42e43d0012258581c120202c404181136848030003d5480c003030008040e2840400180341e064000c4445650300085007040041c000304910420107146d2003117a0040c3c264029411050603510761410440703031420840e44204d000042104030b80b070360090002c200820800010415181c414103850418841e90440002c20f80d030700300f001041c461301040400d00d0011541c9003030042c1c41403429441900e40703881d180c2d070024000c1030070700502c40d00c00e00d101c54001c5503007030703a4a15600480c1c062402042e46d00e0314540720000907074040c010201228100d2101e51441c001c41c1d00085006004030740085540d44803a02c1c0051041d005101125102c851a0100b02d021a07aa8890b89170044080d0450140c4c80705801c0a00006108c1d49060500134000401c00081d02074000ca2150341c0d1840503070b02030000c002c0e5282c00f2510326041c90720095000e0381a042c14070305030a01211282480c0424000003400320b885900301611a000442c05110041ca02010442e00080d68080d5800801545c0000c41c242a031401c000f4810011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 913646708 1250 913645458 913645463
    0x26151005010e040f02070f020a0b0c07061409043201030b0117030705060903030f0c090a060e0105070203100204090b120c04020918100602010c0c050307060e0102070b09060a0614010c 80
    0x948051040342d80d0340ca41c00039108100e070200c11135a8a101c0d1810500030600d0410980c4a01c00103040041c0d0551202c048804ca220084040c0c042c0c1810040300761041c410040c40317a1101c1c0024401134071152217074403d1940c048422042d10744d40e4140b035070107403c44a01050803241100341c40700c01080000c948585183c1903c0111581030b11400841500515600400d6800b900502c5007909012886c0400300055005011900d08148c0e6951a40700740101489000c070180c1d000208900c04002c82d40c0b0078041c94403040e02c14035005203001c04940010b417030729000b1500840d0560740060b00700312a03000d9108004a8201c00d0307c0c5101107500f0801100d03111464241c205003d56000108111117541d001680d40e0081c541c0d20000050707080124540110580500503100550300e0f050754404001e0083c40030302c002c290b11400651404945a86072005011504550041503400341b140c440004d0080711000d00c50b100c0100101081d2415194010075a02c0e1a48a150aa243e00c6da0094540e6800081c101c029038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 913647958 1250 913646708 913646717
    0x9152111040b1b0a0c1d07020c0d020636040b10120b0411030a0501051c03121b0f02070608221a18011d0619062615100501 54
    0x401019802c0088074400400d10300780e001d803901800805c2540c0d0b109000344d41c0542d84225030300c0d201001c0c2400c1d1980654400025a0200034824118501051f0003401e40e440500690704000c3c0703100012a680b041070040c601d60948040a030703c001c4210b035459191210017240e081c000b100011020421402202da02d980c200505089124091860f50700f18040038007019200b080741041e260075481450300127403400903c2d81e080c178000107014a0b01c014031810120940c0481c140700700b0700c0e903000e4030580b070420101c40c1950b403110226429052040110000c011030340c0c4400c0901c01c00e00c0b41c000d04000558202c241402000d105008040a02940903480180309413150441041a824449600d1014190b4131040d10208000c20101500d41c4010000c008050301c024003246002c0c0c1d560f1002c0d0b115060b90304103e548403000044003c01710582c03421540c9290701002642c1621502148060f070440e01000000c01c0191b111040822030811440c40c0c1c4d8545609500c440303040000a500d400d55403841650f0420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 913649208 1250 913647958 913647967
    0xc06080903040506040b07140c0303030a021b06010608040506090d02071203050904110c0c1c080a09030b0903040e160903410c03151609152111040b 65
    0x5140400455010b00402081c8a81740c41d070b0b402e0b0041d845d52013280100d41d400314078408102c00160005050140100c01806582075640d0510700e0b0000303401595910340c1d1626060800c100c0d841c03040c0111070207045290740d00c050394a424205589400310150001c40349a210000c0c00400d154040341d154151180c4942c000803180c030300d040c00c4506008640507280c1c028030b0300502054460b1001c000384816140d95054449034280d83d4108411041060202010090f442c84c900d80010720b44001800c81000605102809548139141c800852000710303100e0a89034030000d81070008117510030085a0251660014600701582c2d054010700b022201d01c4014002204e02c181c0c1881981e2964020603040806644614080822824440d54417180c01d0008401d000d140c0c422100c030300700420002111100c0300700408590b20b60b100328242d0760810740980402c102c1800000314610f0849a01695242c4540d9914080140c4080c41c0e50850224614840b1586281034643c030030680c80c4c1d03001d07241240d002d04031642d100d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 913650458 1250 913649208 913649221
    0x13060f05040506100c23030310051005070c03020d060603080708070c150c060c020f030c0109060c0206010501090b092209020301110901270f030b090706090e15010e0316080f0a0c0608 80
    0x11a141502019147d000100c1000034449410b211041202c1080340d40d03c2c00750009100136145071040304c01c05401c50480c14030a101600b8400c054a202c2d9104440003c5c040e540e075240e00076580c1010104a841001c0052000d0501178140003440162001c08401403018101404c0985540a14200106880c0d12a41070446940c000e12082401a002d401aa652001c18a400600900e0095400c59283e4544800c0381036083c070000300a0f05036030060b1107284a00d81040703032240c03070780c2c0040c0486540000011500021050b0150007595126003003003000c01d2440040c410076080d20304a41c4251000402801407800c6603034054000c82c2844005c1c0030511240c02100c94040d202040e80d0410501c0c1304ca490301c00010002c000d004103204100c001c003a00c2210391118400c9581241620807848030132000c40c0840d0151201c400e0510400805040c1614105c030f541c004281000400b5585003600f20034042c0c208201e9030240200c40d1aa600700003c2c19030000e046d9100208003900c1d00036003042101c8800094003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 913651708 1250 913650458 913650503
    0x9031d0301231e0c041d0c1605030d020a080f0603010509030a03150e0f040b070305011206020d091a070e010206090a06050903121609060201020c1b13060f05040506100c 74
    0x10083d03200740c03000c500d9240c100010701c45540284680c400b421401c0d40d0108000b0714140384a400f8141200c00e25107020800d0101c0c8116906070401950103000c00c00c8840242c0d0a9803005081080701a21490520700d8410b030030800b00e1000030b0a841c002e034100800c006100001004a034a40280380c100020040301c4508542000070150700f1a0a6400c200414001402d5580481c144214400d6450f40314954a0810441c1a643c00303200e03150800103140420400180a9000380020443c80c0b00001851078040e12407421015002d1030114801c070251007444541c561000b4042005002030005084500381007080e02d644080c81c2c84080e00d610307940d0317020501100050003216031000205100300c4042c10400b0400c007a1030840d09250001c1034480000240180c01030080e9142d2a0440018041d88540c10000030b601500f05100650310122a40b22644d41042510514024010103903858001031306005c2070004a54014058500c201a4240c2001156a0006242d11026481031103031887d203400882c4142c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 913652958 1250 913651708 913651741
    0x5030d09061d0306190b100203070224030a0b010318150f18060605031507021c0e13020310050f100c02010c0b070809070f0b12060f030109031d030123 66
    0xb0f516006400034000b025401e5000c800d9803100748001080f40005a10030803079581c00740401c0a007d60001c0c018000940750007011464181244040600c8080b429081c84d8002d500440300d9201560b5a00d60b58485564144100034491680d114400c6401c1c4507602c2c0c480c4c100001c940250f03a001d454401420800040d6045034a0010091419a2420486140c180042d0249000302d9001c0d210700400d980c40756950b070036464001e007015000b40c41040108041061000965408401030210424182d400c50b101d5140705000402e01100040e140d0406200c030412549290340814800e0241d000d030541c0c195200e5019181c010101d04044c00072694910040e10900c0c0340030405045c0c50002c40400c4015238100b00280c2c0700d0384003d02910000d84d202d4104040030b284601894240b0328060020800328407050390900d80186c0c0c0100301c032240700c16480001e825181d8030802200058a14903050800d03403101c0100c4110107404030f0081c40341800348014104542d110300d554000c013150100201b90b0981c202e40e00c14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 913654208 1250 913652958 913653017
    0x9030304030b1e151c060e030c0109050111031005010809210306030613030504091d01020304380c0d0f090822050906060c0322050a05030d0906 63
    0x80c0d5061a018004202e00f43e6598680410340b80030800054018581d10610507990300001d200b8009290000c00039404828000c1c004c40b00e540d5034250400040501f00041c202d03581100d0700103d40600240741280c01d4400070883c18410f28424028018103015181000d419510286400030303a0f81d48401916107403c2d51060f0980001038030405800c1c0d200b0741400110322601059045424075240c40200b04268a040c203000b40005809002c1402520840d0700f00000181d03004980240003040d0100060880c1e00a81d4100c401803100070390b031101300384050b0500d041c000060801e0074101302484030140c50884001d00b0108086000145070300928003550101f070034400841000c1103a1060b45c5009051744c3e01000305807400f1100000c00c8504032200074280c00a44070090107690381900c0700001d002458004090b01c02c85400240031001e425105440e0003422070210151014000d03142905000308015039401507030083d000715400ca40402d41103131110b0201c90552610003030541d00c4d41041910b03203118a910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 913655458 1250 913654208 913654223
    0x303040212160303050a110a0c09021303080c0a0302070b0c120307110d090e151c06090206130e0105060f0912070503010e01142203030c0201090f0311150108120903030403 75
    0xf100b410b40c420081c0a590901e5211280102c4403082c04070340d1140c1d2040700410380c11440c1d00c144403102d0300d42c01070070350120f1080c50102c00c40d80b03030303910003c1f140c120003031001c2a60b00080c1510141541046440c000b0074051514901d0070200c401c00d40d40381c114031151022624000008110098840c1b60315034910110352041e01d4900d010980010500c000c2481041c000307a100e10049501b042e4411680c200c0d1180040c502200c0e0b100046041d5071480c2c5c8200c0903a074a60303407500a100542c0302d21001b05036080f00c08450b2500c00741047d40d20ba82015060708000e01901d070502c502411103200400722840c05c0740803140600b40700041d5002915004650304440d405500f08581c2071001d0205400c6200c000c4501e00240c42513179254594804046010480c00c01d0a0059a40d14800320b4040d40c00001002d160f840041a041c00e65183c00c15103602d810390450025035903440d11000d0540071b00000640c07202d00114041d4551412507200d94580340300e00e0003240c02c03078000f80d05616076504000b20707001541c1c400c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 913656708 1250 913655458 913655503
    0x1b030e130504050606060310031e1b090509010c0804030e030a060e0706120e0d0f0c0f0f150506090c09010306090507030e0d0305061e03101b02070f080303040212 71
    0xc40010701001d64080b5501c0c032450010903203914054090341c3c424181c58180d5254145551910040107840d02d101c0c0301c0b0038000e1310139640414805280c030011006440206c017800c601e03055007142200c0740203054103296458444401c026507400304800390043d825240c450b0011045000003400d10100d4a4018041ca14040c00c19801c0d0130042680c01c01c0315400e488004070648071207044002e49101403805106500600e1800604501511f4074105124051410441a5040360b64010003009903c006841404280c01c030041000ba05202c401c80700b0b50300321401e0001d030615601140d008600505001070411f80810751039030300d034483e0740b0140050103c5030060040d410041000340040401e600361403410300405450b5400c4600034000c0c640641806405400304d000940444810b25010071f1030558140120400d00b11440c0141c003d109264090017440940110110400313450201305a00c081c560003e00d0740b003041646e401009581d80a83c05540702459941806074460a01c050020b400c0e00300c080110303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 913657958 1250 913656708 913656739
    0x117190c03051b09060f13090c05040306050114091b070f0b071e09050d0f02180709120c0e0403020f070b07020117091b130606051c020a1b030e 63
    0x80102d8050703148400b4801c441c4458038807500151040120035908a4010803080c051400c0d900000c000400c5020414041185c9501d40d120503038000c0100b03900080c2c8049000c0c41440b02d00d01c1064010450303c4035a00c024039080d40840c00160004000c02d01d040415084099451141e03001c503401c90360b02185039040044946014244542c0c26286600024001690107600c00b042d2801005a502c0da51274610f0319610700020055000d50020b81103c4030302844200800688807104c400c00304c00d4505401d04106e01d0301c00c000520f880b68990000041900903041400030071042503e040603103480007140711140c0e03920304080e8a44003200c010320109100b49078000030501d0310f10014007100e501c00d90300d00b6814400012030400074802502c41d1001500440d54100a9200111201da00311001a080744061044400d482c82190810340c011000b003800015401c80324046c50000c2c0e1841003681074214200001c003100105072154074031505040b200311000340024103000710841240424020f114140125404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 913659208 1250 913657958 913657961
    0xc060705030c0f0102070506010e04030905120c130b06070807020409020907081605182842080a1512020f010c110423010602030c0d09050117190c03 65
    0x1000c0e10185402142e0b195842d03d40306000700e80f01242c2210042229900342861a0300b041e0016004a0500c060305c000081c05485000707030318210f2001d00c07001e080c4040409050019110f24901160074003844c29803003c40f40c0e503560003601d603285d40010f075036602d17600f240c404140100070000d0081c0d07004c0740341d4040000c3ca560190710a407089114500d898440070091500361114044c102d0010995500641d0a441609100300300b142c00f4180220b0042c0c140b50000201c164040d0140c03ca07001b0304200c4024015101c0015065000d41d44115842d41c8103040c00e10072680d03110303102c24a100d080040220100700000807030b80003c801480c124401c101c2003a510f0208540c0150f000900328010f44c50910400f510350301030780202da03110350080441d000ca052000d04020040c900c580d9803d030714800c01c6415401c400603500b90b15000e403040d5002150780301c2c01c0c0382d0040d151900041d500020450b500310184241d1368080e0084008105c0c68005441079140c500c3c100791922261107200c0e2503280717042245007442d07505 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 913660458 1250 913659208 913659217
    0x9030a0b01030c0905130609050309040608210408030307080421031a0303070b0106030e19050d0908070b1c023105120303040b2e091401080d08090c06070503 69
    0x503003400320f00030350b55400c1d410a9400455103412504040e02508011078a281c02a5696900c10f001b9a0710300005400040c040f01c207030760020440c550080c01d005944501d01c0a180000342d07880400c040c106031405013450303a070303200080c8001c04101e5450042410840040c468040084090100e004800e0030454010000c0183e45000c40e01e40047c00018041c504011040382e4085402c0000002c40340e0808006070060032404644020300c1c8200c0707180c0b40708540500b4202c0300709c61003100646540f06ea01c2030000d00030007554101c00210f4000c20380070454018008100ca203080321010507801c0302e044004101c4002e02501507507400402505503c0c1d07189074225801600c0c408450880d18154039115000e110300e00e00f0300044d0103080e1b0b10404c0402d0100d042c00d2501c0d94880c005100140403144d82401d68054070b0b209510b40c0b0451400d4940c14400078644c0d0282005100c9003150101c2e1640c9064101580c0744c1001d203507a01844581004900b2100040c0040d1004003070103041d843e6603000518081c0c0e0759520 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 913661708 1250 913660458 913660463
    0x91c0c0806071e05070b1b0408010c090e0903120414010f020408010e0721030c140312040c09180f03020709021602010e06090d02210a030305040302060717070f0509030a0b0103 77
    0x343c3d00d4000840c02841610007850b00140e03d41120f070381c0e11006107483c103c05080125018400e020000e0f1022090040640065642d502c44203141e10b401564070a94070050066240364100748010740c1041a070481540e03000390051824a6610a1002154014039216180041303542c00040c011030440015004808124080c10450700c00c980d51303529015410749141e55640301d00580c51240303004030740301c2c546d1119402d010701810400003031485030700703032035940525500102482802d04020510800344650f00c01840030400500c14036008290b4020005d0355000000c00d451800e4240d4400d0500c20043d42000d0000480c0071543d0312100010600c10195040040380040e021070920025400c1c68406e035207000c180544201d0f0340100c5642003251645c02d00482c04640a180d12903a52124820080c6020680c0070391000a01c60902d818000c3c1041001010305007802450804540c68529422040754801e19900d0303e143e0505903020201c030b05209004d01c296240c4100080902801a214151b504992 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 913662958 1250 913661708 913661747
    0x150c09060310051f1409010513031b120c030f050c041a040e013e03100315050615030925090501170d03050601050706090f020a0605091c0c080607 64
    0x102c404102d1400e40d12101c4150000d10005400c17080b444c2260060038a10205041150800c000400030f038244040603807040d40c0c005030380c4c0d50182ea400d0340c6406400242181c2d00c10908064800c2d00c850f501c0d44040c0c80010905411403800c0414880e081c88000403101c80240144111014003d500c9038844c0c40e82a010701c1a0b1401740000100e9105101d4020008030840c1400c208270003501e6803400c0c0000100501c41001d2000717040d10301800362400203600c1112501503000303106096041000d1f4884208140ca8000742c0380c0400d1203940d584080000310901c0b40c1d01944d40e581d90381c800c55281401c00d8031107490108a0b045110071900d840c02403285007501d02950f001c21480eaa00c1c8807030390b100600302a40513450340001c241d140b4814805c0e044140d104030103042052500840380d40300320442c1c400700e009076a0301104c0c5110b601140303400c0805000410b02803604c02d007480300741c8000800010b05103072180029907a26000008000707017080c0c01c0000f0301700a001d8803030500d4070900c00b5040c0140700c40c0803407000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 913664208 1250 913662958 913662979
    0x30d050a051503071502150112030e0405060f2407140c030601060c08030c090a06030f05060105211b07081308163c0609090e150c0906031005 62
    0x4802c03030031181d0b0402c00010010031843d07142c21411020b24800100010442c052441c1002c1008034842c4a6030080a08034030b058442d43c0d541c02c005010050001101c1d2060b4140014082169165411a0810101100c4000ea81204141360844100b0317258030100c1801c0b804203a54051042c80b2001480c250307900e034192501c0c0180c550805485800900a10b80415034400803000881d90080c040d40d44062034080961074905042c00054102d50039612450000c2d4a89c0060001c41c00c540c0036035600141d0a0a1590800042c19140020790000c502424510a580c0d80050110000d4804040d01034808626407655100282031000f03903540f0156040c2c00c507000e001d00000356024002110b1604a0b1440484001c00d0b08043c42000000d14a50b87c0c0f0640d89070342c03d02c82d285031820b0108c1503108460030400505891400f000a006804540d02c409265403812100301e04901e00810501954855800821034565070b400c1d050409001c2d0f070f0311160f00004088100700c20154030000007000da54080320440d114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 913665458 1250 913664208 913664221
    0x105090d120c05030c0c0c041b1106190e151e01060206040b040f02010e10091409090712051f09030905060702010207060e0d08030a0f0c0216060806040e030d050a05 72
    0x982d01600310450004104100084010226038080c0107140c90820039206a40b000c2000a0140e480c46000384c0901d220002400c0c3e0000c1e0440d441c0401c50742d011005e000289446107101e1100c0f034034850354001842c0c58000802074010300307101160030741030b0f0781a4040403824940e40610b88407080e400510b407044071380350003c98034030300005da41c500c0b8513445031003210265956566004120391700d0800701e041c003440442650090362407450859400d003181d50f81b00000352803e00c0350440da98460103400c0c0290b0740001032207901000482c403081600c2500d00300000c05c403410300d8031b02d150200d4103040d00c41e039413000111400e61140503003248900c0c0380242d0780c503100e003a2280b0410500e0301c110403000b405a0300c59201000000e02521004c110b0b000005d2030082c200380682c854819030780c0203c82ca2041542d591000c0d9114003c2440707000400b401520007010301c00a200c0108010303142e0ad005200034040b042001540955580c0c00c80780d00c004000040d43d45031440c008411028100654500040070308280c0007070708 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 913666708 1250 913665458 913665461
    0x311010c0519060605030307030809010c11030702120c03030315030d0f0e0d030e060715180b0a0f0209040e0a051203060604051c020603090601081005070503270105090d12 75
    0x1180e9401201600070800b007490000418410749104440044e21140c00040564003030010b0720500d80a81c8500b41c16292448076070342165205c2000c0820f2013024440712000c410000242c440c0f20358156115101c84000c007403a40e240c14905101260705110010400c80845408409240640015402c40b40b900c250f98070141e900d648c008000c0000101c20300e0300b00c2c400307103050b00c101d2103124000e08041d401c071301318403010550726800050261154a0140031210749400c840c410064114440c2e0010740032900c15079142101640c0141c2038500f81620341c0801000504140d0498801006c002c00c01c112200c0c0e41c0d00c2c11525a100c100d07041d1024080c03422075003170148a110880384100304c01880310b807500781480c1c2081071907480c03920020f881c0c00001c00c1000c016201d01e40158016120300c00200a2585020300c0b55160900101004440508103002c5c890495005000d40c0c1d003201c81d0010444003090f890b0040c2454070040e9481003201e60a103400d10080c000b02180c0e1641101d416612602c11003110030340d810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 913667958 1250 913666708 913666727
    0x60a020405011e0905060a0c050705100c0b090f03070c18050106050406031a06160224070201030504030e0a0603050105040e031201090207080d0204090f050603012903150907031101 79
    0x2d0104180c28085401d5007804603d000c100609400e000e401161548042241c80d00017105170004107207944d810300d0500004004010051400b110400320302940c0d1400102170410030500245440d03c44004141e075041c0034481c2650554126081320349a40749401c142c0c181c16401e200700018a20940c170361034030400460140740e040e11056110705141c03e180c280210010040d55804c50503005010080c03400c030341d071102e00a0203004ca880340c07070002c01142c2c1d00420500e07007804551840f040019000c480385d40e50b03182c2e00303881c42c20707409080c005101c2e911400c0a40c1d520311144201d80d0302c007010a00c04124540c0603841541641c04c15501004a4070001085030303035030312800e215100c01541d684010000c0d501c0580003440407507c01c800c50b50910340e02189410690f001034003c810081c0d1212002240158584035181d40540100c0082c0f204600502c0c1c40360f403007804800031f1103002ca82820580d285031010061942c44180100c00d82d006498070b00b540c95111740c030600045902188011108100c2e40c4101b0240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 913669064 1106 913667958 913667969
    0x182a040b03060403091e030519060605120709110421121e0f03020c0f0a05120f04091503140d09170c01050f2505060a0204 54
    0x20944845515031070190344007a0821010a9000c450201126821006580d0340c11120401201c0c01c20035400280c0540b0070f035100d4050840300c494000c03005c90b001d020100039440c1ca035402c20620300d18a141500082c1d1000300e080c040c024859018280022200041d54a456581e001040412180894403810841024400b40901403100858a0750300680c1ca46150714034103244100500c00040342c0b0a004014a044207003603954007d5046401684a2a0407229844142c440e665036070110000c1c1203903a07010b0800a0f003140e210800030340700c08801002c0504e0509080003031500090018001076110002143e10000c08180c0840b80c00e460401c154020700154441e081d000f91075030303440f035208580c800403641910b51082000701d004a0562000d00e04565604103254446401b40607015a0044601080381e800e98280044d400d0b107080948590b00740d81c59940c2c0c245142040380628800c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 913489208 913669064 := by
  have h0 := BRFrame.cov_init 913489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 913489208 ≤ n) (h2 : n < 913669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
