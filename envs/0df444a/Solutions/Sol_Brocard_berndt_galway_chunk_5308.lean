-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5308
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:26:29.985749+00:00
-- url     : https://prove2.me/submissions/59a4e893-a3b8-432a-b3e5-35cfa040650e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 954496402 ≤ n < 954676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 954497652 1250 954496402 954496421
    0x506120303011503020a0207031a041103030301060e060322080418024807051c020102070510090e04030305010311030114190608070902071a0103030c02011b020a080c04 74
    0x3940c519414101c01200e0740000d0081d000a041d00001e00c40c1d0002d00c01c200c2140110780111110f0141c0818581401a1800030360b015280230700c08141c80381d034038038020040304e0480b070003601c1d5181c00030078210030f11245400c024440750710071030020342e542e800c08507482e0860701e081e209409280c0c2d02c900302407400041446000c0d40c03079507041c418441030402c0c00d075440304010400341d540c5407007030705d8003158000c00d4a409071140b07070844000c5030310b64001003110000340302000d80b0403c03114141074414000180805404040d00a40103070b108280405c000e082507500d003000300c242880d0030b001e00c1307032a084a04000c14094608400081d40e500041062000080c140d81e007281c402c030000d1206051054082c61000005400c150054140107031400c000c0130756a02200051550b0401c1d54103080d40c51403d803000390403120040e0384034000c014024007910704044409050780c5d41911a4580700b80b06800442e08001007442c01c00428500c44210405a601d400e1007400038a807070001004849000b00600054440025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 954498902 1250 954497652 954497689
    0x2120907030c03240c0302031803030c0d180c08070911120103080a051b07030b061801090c030207020405040b10080a1505040614010312030c1d0d0303020d0f0506 71
    0x150070700000c0c1412082e282100d07006021040008110030748100000006481d030010649031851604106406401444c400c481041c50018030350340700d0340f0403030700c91100300d902888132308003049001d07003400d80c5501c00d100c0ba040d0310b00e440101d04d805540340f10044c2c24541090840e42d002c07041c100440541409075400b500d45910340c02c1c3c140390015501004046040c08000d150b05c070041010642c00b8070030703416101c0f0507400005c180340c0303403803000ca0140d15034400d40400e4840302c88a100003012030a01894035003990a034655071610f103030b00c0c2c001818000c0908840407020035408222090242c0d650707010350760040d4002c1017503500500300407503008007001598bc003034262a0031407404100032480302c403500084020300b44030119895659140c8a0002c09006a500900015000c004000d01c9050913a00007000140c0c1c07000c002c100c0c940501a10340c40004440d0610f040c4900910800a040c403000300a402807180c10051b08000c1004106416103503a02d00e18100260b030b49082001c1c500c6e02d0400c0a000a100c07a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 954500152 1250 954498902 954498913
    0x40309080d0e0f09060609061305091305060f07020705090c0a0306050307060219210203040303020c0306010f050613030b0c070201140a050307051b01091a090606130c020c04020a0201021209 83
    0x9010404000348a203c4500c921092000030309a074490100b242c012140c0141066556401c4401510610099016035070051085d040010034200041d41030f18141a0410b00424082c1c4e20400000c4203e60014903103021805407080000343d680b42c490317805000360843c5503030301d44a078100e01001301242c81d951705c9188a40c2c010001040700359008500085a13a86151400081c2c000c0b5045c55007071096400c01141e048d032540c9402e000f0782a4044054419644a942a640304000312403c059407100c013030003407451061101d41f0420040c90203200409004580140142042e0f03603d8079140126041140da640c8480d0000038001d04540e40650403032003406080c100c031030030b041800c1801041800b005200744240080000c846840a040e4079040100b8640321000f808902c1c82490100700031041085030b460b0265400b004140040340c04520640f041e08058801880c910090f40510043c000380140c4005501500680761030b80c1c1c40c0c0f800204004405900096076800b682151600c4130385008206a001d40c010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 954501402 1250 954500152 954500177
    0x303080a0b0d02030a05031e070b01060f020a061b0e01020105011a03040309080a0609151e02310f060f05030601031e29031b06030403021203040309080d 67
    0x842205504a0001040001c0c0c1c58040c001042110700402000f039030601c6044100002c10100000600d51038070319656440e501c02e04c25012000ca4019000000e00300705402c0010700c0800e02c1510400c1d006c807520300c101c50340c840c4903882d00f0045464044507803200c04d00301d035242134a06812240d6451205400e2000308402e40c544452803a5110f03d0707600c038403401314001000c602418400d1120901410207402071f980c4881d201d02d004801401502c0d0216050181704031580030b101c18a22512641c0c50808041e2220307580752001882c020b50181010f000e43c280101c800c2c071050648541002080408030009c8241207040000c00b109941565006004000502d0baa1030784e01e940c480180c03a002030003070030701160600490200301400c80d11101e90408040c40d00c10403000400010140041030748090000b04030000c03c1e50140354a5000a0810304600d83c00a09007040030300b071030001954050b000c0d20541c5c000c4002032040f10311583c01640d040c1c00003210302c841400203030b03010300003d07450601505100140300700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 954502652 1250 954501402 954501407
    0x2003030f0d11071202010f05060f031009061e020304050c060915070f080c0a030314060d140304081903030b040902010e06030a0e010606031a04061d07050c0313031a010303 75
    0xc1c0c420080c01192184260210703049540b06450480e0341c40b01c010300c060701c00346800074003e01c2851121584c4909010100d44141080c00c83c2614440000c3c0152040e81881c0381c043c0c014000c507440c12280e26a882c0085079105100c0908020601170071074000da42d03420035080052510981e00c0445208841c1040964555661413041460f044603640e9001d486407128100711084000442014011a20014001441d03400118041000c9032103504c04000256900ca0b0307034181c0e0032080f1034044d0004001c548620210307211482c60005000d0500c2103034034098550044904204120350402102a80108014101034150003013201d2120250b07400c100c100302c00c2c1c00003802030120001e060301440d03000011806500554206520071240c450092050313a9035020b0050050040f0b0300160b61100d01c0e0a59020646810b00981c0211605070348400d010b00c500d840d80b07554652000d050f050901c01c04010490381c21070144080c0078010b10a203541c0c0091440d50600e1100300e0080903a90015900c4c5c000144000703038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 954503902 1250 954502652 954502657
    0x21609240b0a0c0609080a093f050703020d08040f0e1005210f06160302030c07020402130f06080406140714181807200d080709050d2003030f 62
    0x1c40b0391400c101014490f00385000140400000038041107000200e9103d110742040140046070300541080c10f2040c100184400c50901e000d130455130080c90031030041015106115541b0840340100c0175103903680d64a81c0020b880f2655000d00300e81c50000401c0030080d01d900d04a0f220000c00c12680d00d159203207824071940783c007080c290244074800c0c2d00c9940c0c150400c241c52201101c401101c081280c0d280055815220795400084503104500b403110041c16074210310034005d80c2e00580c5050081801c190f0b0703c3d820000650856070161b000520015000100c100740c05400340014401c5440d8001e40307007024100001547c20510303031490b05081d0001403048030799103c0c141505044c0301e0b807409511090310b4580c2035140340b00c040000e41d03c8a0081d0014402ca0480c200240c02103001e520758003080c98900c0e10102c003d100d107150051040d0000d0100ba0a940d003c1c1d4000d40d8070011740d11b4030b200780f503840d84005459030a207424165624400a4106090a40412100111420220000c0d8182007000c002da41191 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 954505152 1250 954503902 954503917
    0x15041e0506030a15050a0f0c031b1701030f03020f06100603150b0304170d02121005041b05030c09040c030b01020d140405120c0909030310050607031e021609240b 71
    0x290382c42000884c00c600903400050007c1d41c12400b404100702071800200503068814121744407100c011072a81e1014000e81410602072418094400d5507840c5803160b241084000c202602940202e40891211100501c150740c0f040038895500c1320010b0030f2510040440d90400d80c11690724410680500450360408166541302d6804002e005900c00f20861200c914020101c0b0550074500202c2c8075204020b46644d554071480188080941503941c0c0c2c010401512699150805440c841031410021584688003d40c8e000c1e200b00308551501c12004049001c6032135010440300060341d19a010011503070f0500000480e022549084030113410240c1400f0700d144568030440f8400c0080001c2c00ba00c0c00000d10407103511000040c40e0010903e0300c2c010311034aaa004465200030140c1500c8045410f28009058450301d5800d0f9484e602643d04200e135410807c2000c5010100b0b40c031400114001da1041f0600210113000049000b26400c038071a035007401181e41030800340031306038810b000602980c0c5012023503c1c1070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 954506402 1250 954505152 954505193
    0xd08130b0a1a0a080c0414040206091504030c270e030a0c1403030f0f090304031502070219090c140405060711011b0b1006020303060904060515041e0506030a 69
    0x8280301c642c1c0d080051502c0105036044a1039010001d1a060085000800b01c1c02c1510700b8070911401071100d0a00d0b03441190002d501c000c00344441e92281c2010911891800680c03a1440e140070303101d45603140c00f00e07c80e62214a086401d20034000b03040712201480c0700c1c4405d0400d8103100403010041c5282d00c0340140c55800042100c4a000c5a00340f00071070070b040c0400c0d401032090342d64170704241080c6241004112070b000d002e40c0305240070508104000013218101c03900b081c40c42d05000d000c0d000741000796001000c26a0700403000c45a1500c412940030040c2c00030305960030b00007110120800c0162219100004c4525188000d001c01c01050300e80e041140e143c1540702c10035451007141103005850f200003599141542c66180800d410400c144020454043d04400b001c0c1e0710901c0c0e40c2e15080f42c0c2c80c80101c2c2c0a41c0c1118070072003c9000110aa04807a402006074400daa1841c04541d012504807082c1d03010500c1c078040c900e2028850000b09209003508584e090300542940b404940301e100c081d00660083d81c90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 954507652 1250 954506402 954506411
    0x207030311070b03130c05030f100b0d0204020a0c060b010311160314031515070f1b05030f030904140721060b07080903070906180203041b080d08130b0a 67
    0x941c070018070141000d850103d1100f070300c0b81000284048003480040c01200c501c40e1984002c81c2e5840d00040008003441581d0041143e200d24404982c0500454902580c00040844003c4016607490004e07206c50300c445e5582060140d80e81c03e00b038083d11a0a0b6003141030502d400110207030307440307104100e1380482084400c003110542c441c6412244811080d0001103c0000803040c414004440c51030902d1840e4200da201040d01d002d40c400d0b0f510b0740710f050b4004011104105140d00040c0c4c01c05c0c0c440790303640c40e602c007200c5c0c0059640380440c0c106100b0000c880c150340c00c0000d0121161406104407040c840c0042d540403401e15118902070503809520000c164074030043c62018981803210f4000704064041d607411261102d0035031a2030005900000c01d070701c0c840c5c010401301061660300361040307a0844020490780540302e000c2c0d0912900075070000c0d20540d40d00c000d00e08480302d45c01ca543c100e10000d041c0e44004118188034271030024102480030380305e025200c90300000800170400d1000081e400c465130010005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 954508902 1250 954507652 954507677
    0x31d091b070812250302190c020f1009050a0f03050d081b07080d2412050a0c030c03020a060804030c06050705210601020d1b06091e060501030611070302070303 70
    0x40c28010f40c181409802100b4041104a040c404109950803030039054400103805400c005800380c1c0a15904007412000d050500e115291180030403010890001d084442d0342900c02000c00d4603840d841c02100c0108040c20b000b0001420480300002c0104106500d10b43d4103801c2d6902c981d1a000082002e0341040031a0000c16200c104c10032403400f1141d03e00803910ba88003000e18000e0303c41c0d0051001c5424030b1b454001e0002d80001950b400405042a20310859410745c200040c81142800d8154240c60f01c0c03140016a10008129140d0180554000c050f680d203140d103148100001c0c2c50054000c40100700c147c0c0107000010740c0100d8001c4030303d81c0c8990081041e554101c0215402d000f0818444014480ea6202d90070444540c46040e004070000c0c0d0a0700c00c001c0c450300c801d9950348000392414204450050315000400c01940c414031800f0700c00c88048400d01c0c02c540c0342c05240e0305a888160f41c1ca6940340e00400030001c8921400340e0390902d500140341041c07030580b4081d44a0b0705510000d010300c030700c059440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 954510152 1250 954508902 954508913
    0x1e090310020f0c0607021006060f0c0201050c0102090301050a0b0406080304030803010b07080c2a100914030a05030a0302131a18060903010612150e0712050a020607031d091b07 77
    0x541c5540700d5442121303102c3c90100c0e4000d40d1001d05000d840340e8103140100110b0014424028141c0c1d210180d15048a02c00c290ba00445140c0d1240c003035240d01d0b550074451480260340a009aa001e416680700204a64851a00f04811141180e0111550f40d00800040001403415010307681158549a691034071440d50f414442d80b6071280041e1150240507001080c0401040740013101041c0c4002c00c2000141c1c00c0420a010b00030342d01005080104030803400030801c10b0850259458440c0d4060152092100d840d590603255410201d03036100403a4000c55040180c1d1448a421001030048101881c00c2d24180c952480c010310904070220484c1d90100c018445a456800c111504040043c00030003906641d8200990711040400713040354071036107000070250000d195014403200110003030701802e111864550680d00700c00d200a03086403140540d041d5000540c4c0c03000f014009039800394a6108607049850001a00000a80c844038803c0901030701344001c810701e440300c503d40185403021882d80c80c44d007801d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 954511402 1250 954510152 954510157
    0xc0519020105062d100c0507090606120e1e0714010f05070b040204090206180a0510080f04030c02090a540f03020a150e060408210c1e090310020f 64
    0x4a50030040c0802c5c00d04607244c1c0200590032190090058800e456140d041d0202070b00d85510440c0000350311301c12081c000c00300d158402000c162500080303a40581c1c260000f5018980b044400a040d40c002c10303c20460a40040c940c603107409000d00e0074103c0a00c0c0c85c80085c01c0742c02940e4000d001d019001000408544507940490b4825400400043d140c007070580d214801910008803c0d8010046200c0024090401c1050f60036216140e0701c40600d981d0769454060240d0100520550810102c400d9281c00350b15038640307090090820ba003001c00d888200d50311520b40301900040d0400b1441d9064003854100c007400c1b0b0074000000c0103a0505001d14460100c802040a01c900701a050028580d540d100b05500011144007a510031112001c50032181d5041c41c0858030f0001c8000e0840d0030541c001070000301e41000924402079035000e071413528101000401e100100031101449880000154205409035440d00d58059046010120f4504000c80c801b0070348803442026000011900800c81865001110f0306 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 954512652 1250 954511402 954511489
    0x612090c12070609120b06040203090a060227010c2303040503120702040506060c07260d030905100624021c05070b160516050f010c051902010506 64
    0x2000c4514400700d6540c1c0e25809548181d40115014900001d0001510031303e56035415040b85031052695104800e100103540003d00401950040403800c200140d068400b1300415031009102101d00101603a00070b8082005025040c180158206100700041c0b40f003050101010b200800c1c8103411160b00e40b0f2510318007580c1c00030790380b501a60343c040c12940c0c0000301a001e00c6e07000320340c280582c3e1034000070711000784501c01b103500494211640502010184c0481c030ad500c00c4a10f00c7c40c4d04120503841d011800c1c1050b1030600320000c0e807070383e86100a120042184009250201604000c070301c0c42d050801041c01046003100780302d142d0440c10030508a000348200e1703402e1201d1840fc544c0c00071140b0b0b0300502d02da0110b00e08a0b1107006d60360101e010001c568090207071030310030383d19428a4454034000c41d203079050304500d04603000d11992640c144029002c0c002c004e01c10001d03441d000d4503480c1c041144850a84840900421603141034204007140d541da1200e0703220b00c2a01d18224581da140c0240300c0c400484411b5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 954513902 1250 954512652 954512659
    0xb0f030a050318040b10080c07020a03080d1103310b010e160306050d1e170403030206220b0928021915180509040302011d010b0612090c 60
    0x8069000d01c0008801802460340c03445900c20842c1a070001c01049400100042da0840c05030103200d249180108031140d0805000c0000d0360505a942d030010b00300054a810440d0821404155011109100e00815021030326503220700d419464940c82070b01d2500d100026000480f030140e110519400384280425002541140d2038025540c2c40d041200189a4195800d5100e00609002d080c059440380c40342500740e42005240c0340380040c0c4d540b50440d010350110014a2051854046440005c10b60a040720340440454812600c5501d541030103410031000402106440768490584d00310300c03100c0400180c955602c80f0461150b91100d0402c1442e1960396000d100071036030303d80000301c1440110b0070700134010761089901c40d400740c40020301c140010071a84112004941c0c424110700c0c141d40507035401025070000e81008801705070303920300180359030384151410780160f50740e40612001d030702041c10030190000942c1c0c002d0200c2900034001c1101845017261103810801d944001c00c0c10414280200c20110400a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 954515152 1250 954513902 954513913
    0x90b0d0c1b03020c190e04060f1508070501030b010e0a05150d060306060f06020d020d08091504060203010f120b0406090804330f0e0d030c0b0711011503020607060b0f03 74
    0x7450040c0d940c0364400300061242c045c40c6904000403480001340c400b5a1400c02c41004513442d99901c0c3d034064030818928443c015102e0905190401d800d00754103009041d1301000b05542c610307200014084801003242941000254501030b52161284c05503082142c100b910316550694a00210b900d4034095250144012801c0160010034042c254000b802a6040c0d161000c40c156944d407402d80c0d541d440b1070700300790250304028405081d0901844496500201c0f142c2075448040d02003a0002405008079030898000c0c3c3d0210052080058510450000e000081103a0350584403030703160000c1540008200411664403030000c0c100704803100c015203005000b65075214403c00b004000100003603044104803d4158030052141c00307014845d8a030b6081280e29038440491020f41039080c001621076982064003403144117203111000548002e019486002c0c1075a80031989400c413002d031802c0d68070400b0380742d6039000601000d20140c0c0c1d03010101c511095220030700042200040e004102200c80b0100869454040e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 954516402 1250 954515152 954515207
    0x1a0c160308120f160806150409140a11043f0b0901020a09030209060604080303190c0e13230c0c0f060f040f051c031b090b0d0c 56
    0x10719000c0c0c280200c0c2100070000e10340d41c880081809020803076003050200c0310904040505402034070b03081d4004d60058522101c900100c00924216400b543c091f0b09060f0b60351500c00340d10900c00401c90741000301003d043c050b140c2007000c210f19500890003801c025a0090002100035040451041c0c412a40c5840490760321300c0410b151007041c0d000507c02e690f0540342800007a0200018822149204015101e10140e036007943c0030702a0445008210302c2e042001040080740703406081000d0f40c4103420144c501c95030440b1030f0300b1030801c0e03e001ca000a414419002d0030300700d1135039423548800e0900004041c00969440f5070f20180d6940c0c0c0211003425041c0700141c1c01c1c080b0401003c0024001a000c92040b591580340d00030301d0300c3da105012900d015a0111100119002880040100d411035005008a03024008c0010f003820504801c3c0401c04046540d03404490781031b180e00b941c50300f580f031010306002c0655480c0c605c203c4003e20400f610442503d540b160000c448600900000446911504c0b140840341d85 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 954517652 1250 954516402 954516413
    0x30603020d0807060c090e0a0906020909041202122b020702040e031308030412020108040302030706050f2d01030303150e010914060603090d0e0109030210170703061a0c1603 76
    0x30800d42030303452a062201d4101034a01810100d000c0b140d98035503201e040e40d200c0c6540001064000303000c88ac800e808002402e0180d039008c010354080d41c0200c1c0032a0303803107540140c040d1801140da044030124200611020119070075840d034418680126007061425a418155200c009115020000350b00c2490b0404946889900001602c05d41d03024010004816880310303100c1355640034921800c803440240b55010001944034400c1150883e101c4e0040301e0a180481d5900380550704116410404c8580300020442c0006107000ca05a202807544070039079031b084951141a540840500014081c103840c1e0304a52111098410311000030000310181d10f0140d61202000805020400c440c0d1503101030460100c0d12034034103003040780e0059807410010202c0105444041c0e8410240701e03201030512020050000150b00e0303501025202c100581e036002e008031001c2400c0300308204081c0c045070401d0728281e000c6c000c160000d0740034070007110034080322900d400c1826800c030f2a02e80c3c0c0d2000f4584403100030100004000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 954518902 1250 954517652 954517657
    0x801020a030b0901080304080604230d0c02090c0304030804030c0c0f06080405010e16140301060e0f0f0708130f1b060909050a140f06010e12030a031b140a030603020d08 74
    0x214101d0b160328036a640c401c261540c9018234041d0264a4000c0c80101d00051440b11000d6503071481203009000400142c1e40c49030034005031410760b0001c600031002441c11490600910f950044000c01d80c0350449c241a1002400000024070041c14001e001c01c1480501c0f00e8522100004c0a00070890f00d10310342c032040000c003031240a65040341c1d5907090000900c510100440d0015604032100e1203420601e2a22408101c4212202d42d1103406568880b000301c0c0c20003584800e0762041c04d03d001c000074582400c854400e1042e000400510402c060342050005081e00e81c0041341040e034001c502c1c2a022000c80c1071919075060388601074001006985000150303650882051006c4491030b0504201a65410070070a082c2e61405044801c06132051000800031018180107503045101890111000782003400841c1c40c05101d8018a00540e1011032a40b85065260096411908012651103031001d050180500203030040460f14140590205100006d644258480c4000350340007419040b000740541812482e07603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 954520152 1250 954518902 954518921
    0x122202041a1908030a0f090e10060806040e120c070806010e07020d05120c07080c010c09050f01020f0a020906150d150e0601091a0f0c0708191509020a0801020a03 71
    0x144030302d441c0c0110355850030910100303c0d01000040d610b050301034007040b925040b4055244007400800707200802c1c000c20000300c00d442000a0465007100c24102607010b000d410000300203621841c2040d0f46407016800c0481e1806041c2d00d0b00078015111a400100a070911410346c0045404d40308801c0006628141c4448540c0a1401a001e03240c0000301000708581d54450b429900d04903145103004199001840e00041c100507005900c400c0c245011440400d007900c00c0390300400005030789500d051243d0303d4030000c1103041c840240024810100000c48140c4c0300d07260400c1c068450321401c80091081d4070340c40380c0c0d04880405020f0030f55850303000d90751050007000240311018070001da200f0041040c511703070061b940c01224161030b80b42e4500e18119210514080500b0a03014804040c00f08018840c5144050310b030002661001d0240141480500b0740b07400c0c400090200500d02103112480451516801c0800d80c0d2440980442c00020304d00100d40d05041c583d100c249203610000780c24900c00da2541c4206e668 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 954521402 1250 954520152 954520159
    0x10930080417160608060d0b07021b040e061b212d060d06020412110f0d02090a11041d070f0f14090a03060e030c12122202041a 56
    0x1400019050f6442502103043e4441250301402402183d00520a055104070000e00035529540d4940d203040403103500b0386040001d03a0219200e409000c41d00d0105054084e0b084c0c8040200200204900c1d945120190861001d1103400c64840052039540040340c401d5101208142400000c2803000c00840f0340444030309102e202400b08403165401c0506d0003038500c00d00f103442840151501e8081010f2040f0144040750707203da0800000800c0c604880c940b01007640076002c3e441a9408580a00c10124042c1039120302c5241080c40c42001680e450070041d411200f6103900081d01d6144841d2840d080c0f10b0f03500111809801c5040000c841000308a00520590069541e80c03085441c00c0d41c141c0b148000280c00002180d50400c0038030380d48294401500750008001d2900b240c86541c1c0d1551400c880711414110255040050b03000001d16080015426410140e1125854100c1410b2185c19031403029001c0c3c4407450010100000e498070a17044d00d00c103560001d20402482c00d6140c03980a01032001d0340ca0501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 954522652 1250 954521402 954521429
    0x40f0603080a0806181f09110a02060a0216120215181c0e060904090b07020f07120201050d0209030321190e03030619270f0b0109300804 60
    0x1c01d080074990f02a040942c808155110b4546c882c41000215040c40700d010003000104000034015128000e0845401030b543c1000c3e52a401d03860002d0030000f009000c002d456004021894007288501c10b4001c13026000746640342a440c80314022820328002014824030007200300203002c0d14000068440700150310340000ca5840301d90641c5030b40c0100101c4403840c404074007410fa005250307080c082c00505181e00005c00001307590140b42e4400902d0f14041c0e80c0e620050303009001c0c40b140e8103010400d00700540441046501e0180113680020801d2013003040304c980e1690046122020b9840401c10303143c2c60081014880880c9036040030107030301500215010b0b401e041d044020004c1544140c0300740566421036001642c69a0348503000d0100300c1c03204200d4030f0115003150000107044020080700800c801004010000d03180c03120003142050311021041c041e0f000d03161520425040c3c1c0c124204800b11201c44139182503401a0610009010266010015812000400c43d1040240345002002035a140d10047c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 954523902 1250 954522652 954522661
    0x4240c060c02011b03150302040f0207021f03140405030d0906020d180c0b09010903061a03030705060109060509090d0e030304080d05070c0e0907230d030e030d0503101202040f0603080a08 82
    0x80a84078201d00d5002030f01350146c41400581440e40041615200700407000d85000c0311940445e41d40540f50034074005d01e50700528511b040607814000c06003001caa409070390001d42007a484094807481806c1c00414001e030359a4070741080041c03035015110700c1d8251314020419a007802c45183d0206010807400c4074a07480360b66001ca2045100c100303076450410180e459a65480c11540e4110040081c210382c5030000143c0c109144599804000518505209030041e103803a52403d40c2c490301b511242e0700401e100d24283c030200001000000382c180600c1310f017440e0651143c920003020030304611a582044031035005020185901035000001802030904c0350040142c0b15540782c621000440c41640d0391811031b000000100101d10035644002c1c0c2c41232110074410049101d45000806035007800008902064520800341045d2509000e420307003285580c00c01c1851807800038041d4040125600814084010341d1040c00195210f0354070441c1e02c0f4194490130000e5036181d042c8095541c0100b00c2c8040018506d10004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 954525152 1250 954523902 954523907
    0x16021512010618060c02061201060512010602120a050703031b020307030e030321070e090a0608010e0604022107050613050306010602070e0403120e01060b04050f0604240c060c02011b 80
    0x80000b40c4090450710f9445050080c102d51841101c00281e030300c80c05c144451001e501080001500900b00d81e00c941e5a9612543c071012030000050303002d8000d42d0089022224100400c00c00c590b40380380d852a1a030b6480c0d41030324068004082c401440103d800344445010f81d0241c0010081000b10301a45071180e0742c0c8a580f04159880c0710f4442040c0c51010100348080440c950003120903009403103400c219240103e00c2c000700e400354203305c031046240d0344c4505003000604c4081c17140040200030000a1700881c582500482c0c401d04a5036a0f8911212000e0f0040310f070150244802c1c0003402c0c004050543e20004603003860903d0a55008032072007400b400000280c01400022440212592030111030010740d0b40c2e4405413240ca100c0440003090320785030b012580c4a8039080c4616409480b000350035503262400c00007403081c02c070b00002100f4080c0001f084148a505080d080000400d00282b1949450802e60081210b00c0d00c1d01810080c40903043c004060720054041d00310031008200324500c0c1d002c43c505039504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 954526402 1250 954525152 954525167
    0x509060d0204110f0304030f030615080402090a020c1e0607020708122512080a0605060f0c011418211e0f04060305010e0907030c0b160215120106 64
    0x429a2203800303050050010304068019160b1440390090700d0341001c020310080303000c41e84112412030000d04200f1740a0000d5401d0b120f00da014101c01c0600029000040b40060700e0040b01801c068800d0f0030510000d42d018038107404848007100c4202c290740447ca11911100744181080f228850a809102c0014408520005800301166940700040c4044c2c5142e05e08403899911041d150328981501e00003500028408400c002e15061007160b1440690320f0030315000740a00005041e45100d02d003459000c10240e40e0360401d550696080180c0b03250740d04803448296004200d28101300c1001e04150080107980c1c1790320420300a188a0a03420340d1400e004640c1003002c43d03440114a1031b0129401d00c40a08400700c40c011201d00088552117251504445940c00c51f5503412a5002000007621000107010b00011110010741041c08a8010b19049003103645103401d41e03025004002070010301191601451a05100c607005040d0013502c1300316605180ca03000c45071540728000301c45101290398000100144035090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 954527652 1250 954526402 954526411
    0x50609130e012a1716020c090c070515070c110310182d140a0503030108070f0914130c0506070b0105040c0f09120203010e03040b03090d0c020114300604060509 70
    0x304c503005645200303980c042d2400c1c85805804500c078107041117015840320314005015006064009445030340d00c0c81e084d485c11a0810034040b820014006101106030000c3c0c400128039880700d499580312021030046440c21041c886411441828a001c48900710306c3c0000d820551b500950704401101c904100c0509804d16440a60300283d80311110200031900405030881302480c10b4007601c00e190610b03129149143c00c00c0c1c000003030a03084521b04115140c60211900d0042a8070b54040c8011980e12a400b1001034004020403c00e94032030140c103007004190305801000d000020000f503220799845c00c103035040fa1024041d00d8012485e00040f1540d841c09981d000c14109010381d100d02c0020308102009141091320303c1c0803a0150b4850702c0c580d8412405101500c0a0480150403035100e240c010905450070140102041c140700c0c060b400341c80584d910444100e09000000400c582d1241401121030740d28000c8080350f103002d030012020020300b460406020f80540000c03138041c06160384540030815038050660703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 954528902 1250 954527652 954527687
    0x705060304080a03290f15030103120c05031903050a05090d0e03160905060a0b040b0906160618020a0801020a050d320a0510050609130e012a 62
    0x100080005070540003c02040009140c08501e0581c000124034482912440d00041e4441d82c003001d0440c2e0601c10340e2103c501d50120350307401070b40d42d0403160003a16210601018000001030060545018041c03480d0720419540242200c0e0f507041036140044180307041c44031036030019052401103140b001c00b40c001e95000b4400302c4040c00c410309010030296452012440b40f02d4050140c04c000e056102200070091005000c1090301181c0d910f4010100705030a040d070b40011181e070f101403005122642d07500c0c2c255061f010701a50700582c0e483c5d040c5990120485c840c040100f00e241860b0305001085940940003a000d44241d42e006092911035201a082c2d0092184402c0010b005011900311000d03aa00a884e00b54840c2c400300c6450000e598841c8000c80c80780c0580c04001c200d400600c40c2c0308140307100c2c0d1a03001c100e00400e04007243c00c01c40040d0701c41c0b00d10f000c0c1900c55001240350516100c1e866020002c1c61000310001c01403c509510710800c10606c01e2114140c0500000d40048140d0144411048503c80301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 954530152 1250 954528902 954528907
    0x3070c0611071208040312060902120708040b0a090f0f051501080309061c0204050414040b0f1014030f01150512030403032309060a051c0606080115030e07031b08070506 74
    0x1a60071145044c004009508101e55140d01c0d100140c3c0710b101e0f030005800084c0c00546d5618070034220401e0303000098138070000c0042e03850401002c107038142c00b4550065009003001c04e00c400c0d64180b60140c000d903c203000d00300c800c02401c10f00030818002050b8410390091030b2034480582c0c0e00c40129441c0d01070f04842d1908640200080303c41003040c60700521005862103c01410507849501080440e04024807500403c07501c0c40c244801e00851050b081e6000460b4080700200d86410256546141c6051061a95414004201b0401030342c09115028462000000800000807011102082126280700d510700521500c1d611141d0340b203000c401c071026660582c4500e010b118a02c41c00c0c200c494030340384101d4045881031040400c1540c8200080c80c2440039580d4003a2508070304241c1d044000e245805071aa101d250031000c2080c5500041d080b41100c41003c0c540006465a0b403054000e040e98440800c07090040000c04001c00c6546890708050480d403010700b405040e1120b0505942c0d10701402a01d83c465800e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 954531402 1250 954530152 954530183
    0x9030c100f050a0c06110301061205091002211015180e070903080a02100b09060d031206050913170a05030c090f030a0c032d061a030303070c061107 65
    0x103070000f440c81080a01c1c2c030100824081e1a400101c4a0b00c0c64510f00140b000001001101c1c0d1041c0d0300341d4000c00000f070401513400c120052540d52071490007802030f10381d00440c49241a1443d038401c5004010090a50901d42c5440080c0741c44007840c901942804c55030320751200d0340092007172483c200f2969000440400440c1000e0325401c000000400715002c101032151b0200024951502610504000d0340091480c4110b502d104426904003100d582e0017500c0000800001c0c1c2ea81566070f07400c4580509003101005210340050029248680000e03412500010902c01c2c0d0b071040e0010005403501900d50800260300d0350301204082e11401c00f00d00c0000b07000348045004200820002d100c0200000d2141580ba5180401700e820441c1d05101510f10700066101081030103d40007502c60600c854a4000002004088941d01006400f503006400b20760345201c0c1180f40e892010040b0444500202101d440741351075080200550300b01481100e980c0d0070130f402d81c0040c0700180f041d1070605510406a5984640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 954532652 1250 954531402 954531407
    0x20c0a060e0a12020706091202030c0904020118030507051906080c0310170105090709050108030f13030507030f1101090e0f040c18020408210412060e030a0509030c100f 74
    0x51206415101d0301503404404000f8150240c0680342c11226000740c0280b81c0b80000291486559901008651410032124401a98041200035203e0012582002c00351114001254498500d20000000030000c40011050000000e80071088031801c44a160750030800129920640c1e80a00c0f502c00401e40c118045504030760301c20301440d400101800007a240b55941c8000e43e10403045051031146507590f41e000e00141110500200d000340c00708079028012545030990107640d03803258548400c0c000c00041200d2003404841003070b2100543c2c01c0801c40b240396449050181e070b0111034180c1180c81204800c00e000d5654002c82c403140407600320841409041d9124014200c0f40540140200c07084440301e500820007151000003142890700350280140c8941c208408070f46414001c1e10009180ca0002003409502094581180c09407804440c080c0701d06480c130301d0850040c1a0301c100040742800302017882c8052990110140014010490844592404100c28051244014844540090820009603054a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 954533902 1250 954532652 954532661
    0xc0705061801020c070e1504060819060e0d0305071d0d061e2d11030c0c0a080414090708090d0815190303030c02030a23040b0309150901020c0a06 64
    0x403101c0000341c602900920098140f541d95003254204c41c3c040010710441c1c140660041c640f00034143c3d41004160304103142c1507680d08400526450051480c04080200090b5800805c1d01416407021603684000101015019140803030301680040c0c080035010080361201c440c1020317200d4000c0c003041401718803601c400c0041e00c4c202c41d24103010329125151042100b414414259590141c240345501d00c101c2035400c42c4240c01c1c40801ca03001900b08082e16444c644090101e0350040d504920041e941c0c2549000306007848110500904002000302c0c0000b4404036841c0c0e04080d010040310f07a0364541e61181400c1d02c7c159015a449801d56000303080b030420740d42c06508050380060f04c0081d0101903c0031080020b1100742c10340d004000c20302199000300200b42e010b0241d08503041c0c0c41e001071400c0c00d02400000301071020740e10440a01031000c0e00e121780254400000c9902a140010701281c0d68585271007241d503218620003408403a0480b400008580782d4040c801d0721000188903016106441603a00c5000290 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 954535152 1250 954533902 954533941
    0x220203040f0b0f0708060409031b030c15060918051f0209270108060105010203370e130204181e0c12060e16031d0d0c05060c070506 58
    0x101c000403403080411002c1c08854410b90003106554801e01c3c0c4050f005104100191040340964200202074001a412440c00001c070041c081104040408905085030041c400b4040501440c02665202e03072080d48641160050b6844000180074094007140302c071540c2c045002001e010764125060300c0d9079615102c0c009030b95030341d1464005410180301000240c5c0c005441403400c965540c80908240c040b489a9011a0041c204103020b00603030f40c50f050010b0f4681c4246c0100d101c40d03010745125900314014080398080308401d103015410018040c004040c00b5841c2c0c0c810031301d00c1404400f4810580b000c0e10700032201a16500302184038030480c03100e0440003a003031039841c0c0300103640070940c407008601c09840f030190035100ca503480d84940140d49092004071003498001c0009519240c041041d07000f202c40d16003507400814500003405446c00c0100c070482503030142e00c2800d24080c401c080400a5403003ca00c10585004005540f15031b101c2e001803109620462000074001d400102c00641003480c20601d40c40300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 954536402 1250 954535152 954535163
    0x6010f2111031006120207050a0206280528020709021c15051003020403050c0d020d05060c04060315080a08160f05031c021215010c0203030c0d030b22020304 69
    0xd01c000c05004000c2c2c004540b011941d81d841c0300100503203584a0f00700b009900e4a440c0031807510b0a079885180e00e8080100010f405614000b03070b034a50521b440c3d600c00014580f400300440300d4114182c1c00600d1540f024201c20f6498000c402c0d4403584845401e40b8071003108158004000b09850300c413809003c1c6d00000511b004551b40407002c1d8840914501034408260004c1000a40c09401c01007048210400c7d01c6508003014418002800000c0d070008100031500d1040395080d54054081c800161000109213004240d4001c2c3c4040c003017940554005002070312803507181448203205042c28510410401d1283c6401940400c40003000302f03000c0c000520018152500484410101d62101d48425009503412100f40d4400900301e000b9180d0200e01d6601030a901c281585000c20090502001d003c01604a0100c0c013103400303420100340e00030f0069040c640e601905407501e4100d03030302141e0385402540091001080c00c0c0030801150b807a00d66000c1c0c2681c54901c2c641545070404c5d800c41c50080d00000c008460 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 954537652 1250 954536402 954536411
    0x3060114120724020d0503010306050c0403020d0609052814030f180109050a12061a12060f06030c1302160f0f020f0619080c2a0606010f21 61
    0x50040082c80518060015070158000d2140014010400300802400d840210340180c0400000d10381d04c40104e904480c0c02c00b801007144c0d100d44211000511642e070009500c40d11460761201000b9145d04100c0d00c0500070400c0e10f001c2101010010303d0483ca850454114040e03410301840010401c0100c8282d40141c0001c90b8140b0130002d1440c401c0b035000c001210110031580d03440011170340c0e00c9840b450141000ba15020400c80c98032100b00e40401c01458014001a00c51011409072900720300c500020000c0140702c0c2c3e0102400000141d01c0301e2060310250a000381d003030006425802c00103018108984050300344903089400d0382c9807000030b40280c142800020700018842c1c021a0301c1c21182d034805802803181000c0c1c0d808178410015070034a88500c0502526061188552019260141004240315810006540c0c0da801d00106c40c64400c418140e8442010008103145030126a4140c40901100302c00304c07031a0b03450704070065035802d01c180e1020001038902900140c003824000414002810b07501004503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 954538902 1250 954537652 954537679
    0x60e010608030c0d0203130b1e0301060507050106052e02070503060c0d05100311040903021f0c1704120318050105040501021312020d0308100b04080309010f0201020903060114 77
    0xa003540c0059101c45466800800e038845803120610500140c1d0409000a600d00a1480c12140e400c1d000d5110b603480024010501c803c0c075000070716900d0701448070380c09107640c0e940c2c4921002c0c003103400035901a241076217066808076071401c028491243e002524422010788c201e401148803034505484103100c04502441a0020310740c1c5041055601440001e205175407944002d055000c21100000c00c42d03101e80290540030004200030032102c82d46000c05075000724905009003001e038a40320400300707298101240c40759200d4130080305500c0451984500d80d10b41701c08180c1c1d44540140101c050b2006403001070025a00131380701d4000d03440040308400006442141c00c1040c0c0319182110022201a12165000684040c400e40c1c000c0c442e1025000441b8a000c590700c954021500d1800040750040a00c40b24102044d01074200302c030071314000c0400280c0340303580d66242c2d0030b800e03141c0e04582d0034640811798505003103174400d0040c025243c07045009001440507030f1911842e8010082d4009090350483c0300d48040d030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 954540152 1250 954538902 954538931
    0x3160c0909060504020f1e131e1a010f0e191203030e1608071503020702030f0a12090e0403080612030c01140a06150804020a15080709051905090406 65
    0x440c82c0180301c0000c0c2c074a89030042c042c07000f0700310b01c01521400c01e0050000001901813400c824401054444202c5840e51954a5004001c2d020386070504500c10703c10013002c064181c211822507011310000d01c0190140400555828a03003440081c0461040d4100030034034101000301c0184a0010902200c9159482d8003c1d059200041810f400090300d40c40c0034401e41004018507421007444442007000c03240b9101855440d88081c1c083c3c0300419146500781d040007407203a015070300200e80003819100d00218041c802c0e0313030301c1844120840c2d651120340d03045000a4007401040045903c0d02101110558a60f03408039441800105a181d00ca24411000110404204064070f1b4405000c0000203441402e4103000c041c80c000140450800e9003049414070004a4001030804400000d040546031a12103100240450200f504412050030b81005d90000455001d03001130302562454070f4102c0402d4444081c010010024000144804800e500c200114180002c80380d5109006d02c82c00205244030035800b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 954541402 1250 954540152 954540161
    0x60c0302010225050d020303010b0f030604060e13050d0c020d0209060301150f2607030b090312330307050f0f0a080a0b220f05210a0f0201060803160c09 67
    0x1162980030502501c3e4100b0108120100e002da5075030005509641c50000101c680748910580505d8580c000f0010138241c2d195a004400a0510f8014401140c030300084401c16003110350009407550710941c4640340c0c1580c0241d203003840541d00038010748106203840c1c090001c2c7d081c0103030007141c05668403205491040000100035000d000b590f1070054150b0b16016030b40b820003d0115a070040c648100c9078030458014005007160803683e102c4049403d42d95421142400e500918202e180041c011208015050611700b28114000000c1040412982c2e0451b8074201440c45201c1d00b42e8155020b08401d01180c030300181152208100103000407139100d0160041020309250354000e84080d4800c9a8190401602800a581c48991040400040d88004007680c8104924002c06044480e80e260000b040c4401440034032120003400801450013034403080110034a41c44040d1410024101484686074180f06002d0a0100e0350403070011030404021404c10703011240c075428215150701301d40100043d01903440c082e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 954542652 1250 954541402 954541447
    0x17041101200a080903010f052e090c09170f1e0c0301021c05010b07050604020d2a030b0109020a0206011503020c0f010f05010902070305030f0603011808090406060e0a060c03020102 79
    0x41013511494414241401d680d024903134800b80300e0410b02007000001400301c01560f4a44804244001d0206040e03100c0e55201c03494001c500e2541c00d11060684040d00003941c00c08941a0304880482c50140c410440e0301c1e0310203d100c00b402e54120600366401c02911010701010900e0302015180c40548060000e0b003207900450409251a0801c009100c00110303a01c00c4d24010104038116601d400c402e9550943c4812000340000d100d5000d140d460341c24411400c21642004000041c0c1c041c50b035031981002c45403c9007510044411904a030000b084811007070003500d603c1c055a8005051030f909040c2d070104907801340b42c0030386d04156080c40031303404440301000405808000480005110341298140c84160f0f50160410114107004010110009911070100c0c0c1d400f0380b82100c1e5030b00f01e4468000282c05407000c0f40d09501ca50110103012800d10664000611524204540c2017000c140d80728410b0314903141042d0001c0d484110550108242401031141c02c503418800d1000500d13003e1289a008080e0f800c0d0013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 954543902 1250 954542652 954542663
    0x207170601090b010f020307060c050405040509031905090616050c0405040b1f0b040509060123180409020a0501050a090f0e010810060b03010504020702030f0114060117041101200a 79
    0x4200702c50407031149040d00c907428039210710f01c8000c204000c0d41e01c0c464008000c3c805696104000012071042003550040c042c005c00900040c144441a075640317402210751041240c040050851000e805102120304908003d0302403410104181c2d484000310181c01c40075283c6002d40e400c8940c0f82e03941c03031083d10300c2107101d07004140382400c08004500881ea0081284c10200104c034505000041d00c1c80152002c640c0c0441e0032019540c5c5460040311402030b410340c401129580ca22030b04159004c4040034207030345c0c7c800041c01207a50f40e84c4400c000540c0c0c1c1004000e03410503a0f1708802e0200794410002041101c0b0203080035603449560740c2c41c48402ca110382c0d004154082e100001440303e400d081c0300c0c02c0c005040710042030018900b080e080c040c0341d00c018451321303224550000b101c00c21920300340200c03001d850000008004101d510510f07043d04c1700046a03845d0007d0a240081c40320036286200550066411807145450000740c84011f41d201c0070100b90110503803150030141850311604000714040030340700d407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 954545152 1250 954543902 954543913
    0x706050403020304081504051f020d06090b18060604030f030c1e15020c0601050907030b280e09030906090a0e07180f12170c101406090105010507030e01020717 70
    0x712105d82840408201d001204019200b030001140c3e0009002c0204090f1104100c042c08003401210000d1080010044040742031402c00a80442281c0c031808503010166100820246e070411b4816039200e04890550b81f11006000500c0410079003680e410100b8802d041c4102c1d80001520b40d18080c40d0903041c2d018042e00404541402c02144000245440c20340c52025810500010b1079280c82d200705001e520b018450707400004030201e10903004080022005400c011451540d260819642e94404d041030506010034000094644901c070481d9126288a001650800c84201e042000c20380c0310322080c82c0d00c0f030821240803954000c041040341c00b92840392035640041d400b2100500500710a58045013424099010400107a038226000740f09142e07011030381d0600041052803e415038003c510120700140f0451060754162540c0d540400010044500c00c0e00c980c1d5508410000650024000c81e4000780e424040d2170b0009018541100b024203050060b81d2411780c642ca5900707010561902110120f81c00b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 954546402 1250 954545152 954545159
    0xb0a09230103110f1801020705100e090c16060906021b0d0f030209010f140f0c1e1b01030509010603060e03090a0503150c1e13170106290706050403020304 68
    0x148101c0300b0402c400c0c03202609101c1e1010302013105000700f140c06002c41c002440114003036803086c054040504030092501209001d0079100030311140c0001c009a0081c4000c1c00480e0040c800342081e076181084250101a001850307554140180c000300c0000c6458540a00010b002c2d014401034030641001c03440000c06609842d64401400c02c0b0412610409241c4100001c1c0d003541d80c003080600400b40e050070280040d0324400e14184052141c070315040400b280c049240803e204010600103410100300c00ca100d048084236044949510300f005d10000c041541040103142940250882544504540000500c81d5500d0311014142c41e248422812035410010784604c2c0c6103800102a130140105800901050780c008412400303054024041140c0c61902140d0760340e901d0050501d090b500c0b1003a1043c17a4a50b0901016040034640c00d014170302040b00350005800c1030760b07814403c400031154a514000c03980301d8040c0c40c400091100200320141280204919808a005030003200d00540c0310303a00440c0d58514 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 954547652 1250 954546402 954546407
    0xf0706140906060a0f2702160c0603060b2704050a0605040f020c0c0105030907030c080a0b0c12010504021c090c140109030312050a0e0604031e180b0a092301 69
    0x40200080e1040200c0842400912508200c03801918110080700880940c91b410350070040c801000048400e50000544101505042d9506070f00e851140158140140d05c40a0660a0381e440e80105104050b05101c0e4190b2001c0310f00040c0c200710f44402c117941c50a98001c003c241564411241c56040ba5190740d000c010508252050380c0c18209024011814000c0342200592122144582c6c02e040008c0803000c20f919040a1100303078000c640c0301e41e80340b40d11039031015242c1d01e0358428031003552005416030002d40700440820880d90002c0000881d620586c0c00e00c01040001c3d0418080d49107400c030856805040d0340294461018664014a84824494984025220359049516480e410044c07101010000260450707a800202c1c0c1082d0720205280d41c90740f00c3c000040c500c109410b21244204c009103c00c2c1a080840749141c7c1010103c80301108200c03027015901400b031883c80c00d845507880b60042007150151005808070001901d4064101c541e6070b40302c100c03ca11210301e00c240b1018000b012503103540c5c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 954548902 1250 954547652 954547663
    0x3330306160e03160306090c0e07080627073608070501020d050307030f02070c060c020103050106110a0213060509180f060606040b09121f1109090c0f07061409 70
    0x2c0c1c11001411213050074000d80040081a00c40204055110400ca10800c02c54070070900240c1101c8503800c0702480c024000420a100584d1000c0c0141440541500400000d2a0408002003d20103005050f00e0f410421100031000c034400e03051b00f003190007000308d449141d00c960880e035a5a44c0e0801070007500703203280e080c208002d41d80100e055601c06d0105904182e08041941c1d4410800e04000840b42040c01558010340304865004208a46100001ca004c64109c2c3d1640c503028000c0e07804001c640e89912044d100313030700b01c11006001d079803102e0a5a4010302c3c0c80d4031a100100c15141011900556420100362418015685070840070702c601d282c0c203032a5070200030920101810310010080c6003006004181c151180c1d014200c20040c00003100142034442641680d51010000100e840795200c01e0703c501c21441140d50712402403414050401254030380308007601d20007840100b92042c0713500c1d482a0201c50703034055541c818200c07c0c20300021700810303014401c01064103107080d0340040c246840c101d480e003000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 954550152 1250 954548902 954548927
    0x4110a0e0312070b06091504020406030c110106051e010306031403032e18180b06030712081603090b0c06010f061e030b0406031403091002030333030616 67
    0x20b50b010f0111101007111403000640024050710700141546030050000e031100c0b5051a0340c1c0d003290000030001143c0d64150b00030b132003c0d40b16964010341d40e110510380b1801d8032118450107502503409114681c00b809405c4002d40c071150b0505000500035a02d035100c6059803600c05800007240c001104212000d40c50880c060301034401c00d5101c40840e407050b0031f030188001140c007070440c6180711400d4120081503207a110f003510f007131045c4107200003800501d000101c332030080341e8060003802a0000050352080c40e00e241c151003a4400b00c00d0f414540b41c80c0070155494070b0400705038100004400009088240c880040c4450085000980a1907042c02d030400380c2c3c500140c1c0018108298054039051000c035006070705c80c24004500d00484d13200420f2001a001c1d081c1c0d82c001130304a4000c92404501014000000c00e000c1c00260740c40c14200d0712081b0140d0704d038003084540302244120900202c02e50340c0e2851851000c5640c041c083d80e0150354102c0800d24102084038a02c1041c051047d00d003003019000324004408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954551402 1250 954550152 954550183
    0x31c180512100c090e0c03070f02210d0e100506040b0f15030a02070c0605070303050117031e1308010e01050f10030b0603030706111e04050a03110d050307030c1109010b1804110a0e03 80
    0x4021520bd4480c01410071845800d290020a00050354400d41e08802d006100f0001100d6480b240281c80030024801943c181c1d101d0f42c07030a110b99069040c043c941da50103040090401e205041003482500e01d41c2c0c4000c04002d140e5500308a0030300001c4001080c100500030f01e0740c4030380c1c45125500d001342c11508185c020f240703150905800352155840000890b05d0b0581840d184295031003038102034031400c1c000d026011803001d1485c80d0214665070154000c41c03100511400038070403511908503014141e02d0030364481c1e504180502040c004100c1c1c1101c1203800c500090201c9252460710307110310f41110031000c0740000c1d103007000403800a103c800210581d50a1181030705c0c585420300d46170010740d201907271344401040020761b804c00030340da507440d844c0901e4003d0b00f10003903903540d07809031070001c09040401e802120500b2290100c40100d080c0440e0482c1038076421840039250011070034001d0b40e0310a081c00c1d0300d5841515054280750340d1900f00c0150842542c207480300400840b28100709414440800e02c100030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 954552652 1250 954551402 954551413
    0x17031008030910050a030e0609030720030307020114041508061002060f060d030c0b100e090d02100203060d150606030b040e1902031c180512100c090e0c03070f02 71
    0x660f0341c6001c0d080f80b19100364141181e5070640c0c1031080d00078100d0b07000c43d49031500403a01084920f0002200828009200b282c2071080907a07107001212506450401c0760381c050703001703110100055014183c45085008200c40c0b441c1450354034080452a96080c1d490140001e410f00e0500000f800c03e100d09180140c51400582940c4c40c4c035040000d00081c0080c102c91080d0320b5030031396070141800b03400102c0903160040700003110303407500b15038041c1800e501d44940b54844503910002003e400c03012400c40c200e0502503001d840c44c1e01c411401000070b07407c05070120394403000310904000025200803541c5000207031510007103a084c1c500b0f41c0c09401c49110002712030065080500d030b80561407010420500c0035060002d014880d005600200b0718084803548240700300020402d1030300d2150740203d2106100481105001c0c1803940710340910481144146400555600001118402d4252074000080b103410710b240903140c1a90b1039000e600c9904040c2c60031704110900100b4802042d070300c210074890203a0349000525 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 954553902 1250 954552652 954552667
    0x30a031d06190b0d0507030803150a0303050406080c1603030f061505040b16050f010b0f01090e0f06040b06070c08070f180c0c020a081f2c03071703100803 68
    0x41680c281d0700e80c02c00255840408071920341c1c800b14008003491300241240c0d5540d84030310741400294029258441e07082e4540c0510481c910f0455420000d99900da51781d28205442c120341030701e5050000d4100f07140f2420901411014140c59046555510301a41d000f003507030000b000844048030320903040940007104403140058080d40010854045810350030800d5501c40507072002003050200c85900a1560150b18604245072005420204180004031800c0a55a40640040da03410500d031140c041c0c80e150010005100035206040c20b41e0042c4084c00c0070a4101c403403030000b10b0741d82c00003a0460f40400c00b92401e0102c0c000401804019280d0a445003608600780101003103800c00115040703102c551241c2c849400306200300c1180034032a9001d40300120041c0c480107a20b45504000d0008401c003a40d42039401e048203840d0048201c1001102c401c40c80b03000d2561040404481e14044000707441c80200524000200002c22400e9101406210991a400e111010298019240d80600403035030041c060390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 954555152 1250 954553902 954553921
    0x611031e060a2102100801080705120f030403081b03090d110d0c0603020d1823100f06210c09090503120403050912071a07021f02030d0b03010e06011e08030a031d06 72
    0x41c9c05850040300d40e4255004540341d80340c603101099490030060702020400100300a046005458085802011100060422030340103669003c1d40802c540d205d20219440c001250310141c485c240000050049800403000e6140c031070b441402a40810b00195002460403024821441a400c0000411880200641c500d440d41040031812490017440c140400304403041d24482044541003510001e03506005101078150210003e184903c00d2a40c984ca50b00030640f81c0a05903d007140d10140e00403049016203040c9044c080082c140241c080f2624070007048055482400c51500c14803030362184e5079941e0782750300303040601c50f04200442040025a10503039003400403c04a0590b560944001c81c40140c961440b03000181034001c5104180c04501d0311941d000b8a500e40c08001000d0010948109100d0382c55040241422100094032103221500518011b100e20014503038241c01c2045492506001c00e42ca03402410b003103500a00d000c001003552400c0030400c0c049039065910100b102e0748050074a510345404070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 954556402 1250 954555152 954555163
    0xa1815120201050a090f18110324031e0109141609051302180114011b11040905061008150c1206030102130f030611031e060a210210080108 61
    0xb8103102001c00e0703085141c0c2c4100007100c001c04880c02c580101d6a91951240002a4400300708481103040a2840311000140d0f41200e003c1e809050910004000c400c2e9504210b0032119030240d85030082442c0b6042c540d030520401040d025408000048500c140d2420100b40c1100c3d0f1290380c22604402000d05141500507a10003c031025500040f03416618800005603004214030000d5001c1300010591805201d400d0b05c56050320030517903c0d0403130004050015039410410b10070560b034084c181507050000687d8940c554090b0312003c3c001040c03c010036a0361078107000341224a0301c003541c0c011400300300081040003103144e0314800c00c40b40f0100f0b061004c8009110302c110465000d11900340c40204074103440944c103c075010040070413031846442e1224503404604241340700a880883c1442d9020000600b00300c2141d0080060440180040452114914004000030f00c01580f2580001c8005a81c0c040c56828001024460083c48042c2407188100614840b03030b05903010400020718014407005100241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 954557652 1250 954556402 954556439
    0x5060307030203130c030305210105060a0c0206090a17240a090f0c0914010b1216120c0c02041a0102121308070b0a1205040b0f0408090a1815 62
    0x2000b59582d034900d485110180c0766001c00900c00c41d0041c100105241d88007004d81911038041c02c0d03070001c100103030f4401d4032003403401e008c0c1503406002003164030b00c0c00780034a092014041c40a4125410300c4252400110341107182c0d4840d00c0849451103130340381c44120602c07a015030b034800c03140301282c003a10b40110058600001446805000c0e41e0300611014000107094180e14a40c0c8100800e4000740c070742044501918508000c44807034003400c40040b41c0030070103500341c40e000030003440400c00d6a55140d58120500300c00d8035140040c0591800980c04150150191441d0135203191540085c00b004c0388107000448104a02c0c13140040300848019801340e0780810b42001e121410f034149030f2107a8040c99076101d034101d19805041d207881842000260307840d0400140c10b03603062a0302c801c00c0c0040000314000680b44100c4000782100b8040000814840e003008059401c90b0007091140d08154030400815698407481d00703c52103000050520901000c80b50240a680c041c4c0071909800051030100c00240c0000043d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 954558902 1250 954557652 954557657
    0xc12020a03092f0609030a06021b010612020901120209010b09060d150501090e0c0f0703030e012417030301090c1112030405120405061b07090f050603010606020705060307 75
    0x501548551280c2c0016182c1e90b0810307100c400420508002400e2883c4a54503100c28510402d44903a00d4540101030300c007500c2024020b051006da440d603d8030300a500ca24000305043d40d01d03ca98200c1203d09100d10b102400441d100d103074000006004000c40500140c4c080302610700000c03100700050310744040442c115110100b82d540c8a00c50503000801c00e000d503c0c0305407911480c107500d0201114039040088204c800a8a0b00000c0980310740e82c2402c0821f00f12500c01c0072510030042c0301c0080c1c5100000302a003d009240010713001603e012010300303581e20340f8121080c5540c010124242864287c0c1c0c0c0381d0007014640110b1404090850505860303000511941d5000c0c1c2e5140f040c03120702d80c001c1700c200e0b00c0180c80209507103007000c1401214140b03420a9a040d1010702c0391007809038a0301a00d00c1154260f40d4010301300d0b8102101600c00005d0005221a40c07034107401201e00029845185000b428803c203c00440450341d450900281030031110280d00440c115840340b0004c03c555100c8408583d007019103807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 954560152 1250 954558902 954558907
    0x3020109210e150918010302090c0c03071407030807050d271404020f0a080a0b03190b07020a061e0b0301050f010b0304051f0b101e110f0a2102010c1202 67
    0x107021801c00c0c1c0514213006401a1040001c002505a40e8410030b041e248200c50305091034480808244080c001d40000000d0396104105c800080780311008081440d0030000d040b208615102c4e42d4082c41504540000c40e210f60103101021401604006c1590404c1884031020408100c016994451415644030f120038a0784280f610b602983c4480c0c04940d0107229016a141d600d00c03c0b424018140d0300c04079111b15600d407600f8280140ca2401107a005c0c0320b4802d8207240d404140460701c5903651031034003400000551084d01840f0001401600510f100007140c01051840706040402800c1620305010300b25101c0e9150200f004881c424150210b41911000d00ea40d0344c07a56075a10f45249040c001c40b0280c503081c0e011183c000b024062301d410890f020b80003076541241c1c00310420402d4a42c40c4110900c1c402031040c201150307000c10301c107210030b40c003c0d41d0450480d14080c046407002400d00b80d190000359600311500d040f1201003407a580180015400620003008100342180d40245010500315566410342d400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 954561402 1250 954560152 954560179
    0x290610031104050409030908100e0309210a030905010e0312031602031b0703210905152208010c080f0601210f0b09060406050f060304031b03020109210e 67
    0x6a4042d600a4580584100116052405c01408441c070602c40c04941c2d00c6100243c4220b4486402842c4c0040e80400003541032102c0c05c0d04000900d1841c42005002d000c0300c0d220304096840410040380950701035100d10100750304100004152050000080e03000c0c0c0c0c8220020280d802240003103d0340b0001d505102c0905842d0305000300e085200301040702d600c00320803a07a00c0d207820300d020a0a1048034481c0c1d5078401d0744c15200c10011015540d0751484c0000c903408580810840c00c0a00d40e40c1c0c407040c0414002c6d86032405000c0500c090104090341c1c2001c00d100001c0a0144d100f00340f0500711b036520141071075001450441803400c1e80020040c40075040069081888620050904064021880707510091000c4903603411280001c0c170841401d54400d052510100c0c500382000c5c802e510a90724044c4c603200341d0581001c01e010346640301510841c1017202c007540300903032002010409100240700f0703800469032880e1400c2c84c0d0890405000721603041b2290705080003d10750030182800782c070001036600b810b60700310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 954562652 1250 954561402 954561431
    0x1050604020a201207300206040b1009021b010f02072004140702030703022a04050c2107090e0115080a060503030c0a0204052a0c0f0a29061003 63
    0x80030b04412080001180160420400707507909000b5006d5964941c1e200b40c481c918071900d5000c9030f0429000740e04100e000c030b800305004c000c61607800480c2c503082c0410156264031250490380200740c0b40340d401d03041d0800080f0854080c0203d00b2894004c0fa0154100b140301c0e01e844c40d071888280e0a040e5134048041e80d80d040b980702c030381004210340211250010b492800600107900c941c090741c0200d0050203010110008200000462000410451f0407403105440141c140720040c90068540310648505010940c5541000e0384494140b05145030504000e051240c4041c29040082e081602c10445a4006001d0900710703150003c103040803480d10449c10785950b850100100b0140d000190940000141c81401090020304000007034829142001507595003084c8040c0322640003040701c00740007452688030543d01e010000d0989080c2c180d042c1c400305c406828907540303841e4503204c003100e01940e1441200c15502c2c8081c90421001411002c00c2024908000001c0c2000c1071415050306056a82022000d04103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 954563902 1250 954562652 954562663
    0x17010f02030c091311270405040804090c020a0b010b04030309080607120207110405010e010623040b2809180203040b04030f1103030405030442030f150801050604020a20 74
    0xc00010fa1660303444086c0c07034482038005c1d1841e4940701014031002d401518109171056520650300040c4981c04d1900b03040aa00c0500000195102180314601c560004a0840702c3c074540202081e696040d0785038030354a80502203003040e900c184601c0d0000d0040140c144d42090036102480c005400050303a4078064070784180d400c2d2031110003d81041c9040000320301d201800c4061410786809448401c000450191f80000c060720280071529080c10a1008004521170003015200b800091b4031142d009100300b4900d002c00040742c0c8206400a01c80000c100800302d144000c60052031080344056146103000e44500001b554040c1000307081002280d40e51040500c184690700c042401d0106481e079906143c00d200d5682c0d0094085d5615417030002d01c2c0041e80074003405106240315445460469040891029066030000d042514428503849407080071078980c19204620001564443c032030103250600c00030700e007141c50042c12140100d10406c00c0c51122a0041c48062001400c006c42d80c0030601c007203010500f4803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 954565152 1250 954563902 954563921
    0xb13060503041a0a0b01110304031e21020c360a0608070602011505010305010305060a11091c05060f1902210f01092f0a11030417010f02030c0913 64
    0x11541c1003445807140303132500442d01e52103090740c9040d408582250119181e01c2907202c001c00e82040070a191820f0349051050450450191700020160306c5004540244099194410001030b08560401d4086181008103210061000380c000040140a602c03c5010050504e1303030444c1e10042c802c0080c81d03504060700442c0191400c0400c0c3d80c0130035616640a8040d00d640d4080c860720240d540808503c40d4800e20942d81200c0c0c203d0700402d019200e0064810080c0704030504100d01c041c0400c203000d01d61701c5002c000000070110b641c21401d4070318075081c05410702e40c020341041941036150040c080071004800c00582d499020740d60059640c3c401c030f1041020741600c0b0880075403116036002048043c4614125060485202010034400002210b081e200c2007440c140004003158242d8210901c0580d4020103415526424200074a881c070741c1806091035903300e41d003e62541b0b0300307240b86c201c0100710a0080d170054025001081d8210b0810310b00c030780854003900806902400807080b654840f184286c1010150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 954566402 1250 954565152 954565193
    0x209030c0a1806050f2d0307030b071205060a0b0f221502060105010c0f1406040501150503031c091518021c20010903080c160b1306050304 61
    0x70740d550391007a50402031040e010072220381c541500040d00f4102000d40c62020383d8010305607811000d00c2c032180480006207651070305180369080800459520100100c0018500840c1162420710b070040c40140300680d030300c0c1500c1d401c906003c203010321921000ea1540c01c2d10004030340161100450103c2d03ca040c00f803041040c035144400d0703880ca90418980714104003a10103c01100124004020041e6540c0c10284122400278280c54550004942004094001310b4070443e41403030b0400300302c075680d0b14005090310140d8199640303000801e076207141d08884030010030081d0095420a000002c440c0c1446020f00303081c4100a031904142401c0168170081060005525603003000a8070075002d10398000f202a4004902800c0100240807040384a04a504049540008003105001c041500c00402c010140c9109051051515001c000248440040e01c034000c03d8000501040c00106a60304190030160300107058450200f01500c05c161740350708041d05648990810390703035030340b04e51620118450001012000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 954567652 1250 954566402 954566419
    0x330501051c062d0602060a02032221020d0806040c090b0304080406020d090302240f0c0a0c0f12060b01020a02060408010507020d0e03070303030b040209191a03190209030c 75
    0x2070103001c10321440210f28107070207544002006a52048519041070082030056800940000c030900966001036500001401c056103402840d00c01000d80e14802c104200c8c0e880041000d04507007034130ac2801365451044107200030302e424206603201400319600500714a00958444162400c41e50003140702d640181990540d030382d9a03103094140b02c2900d800c0350164034018003c13400980305161040300c1007819240c0040041d800002c540754125186010068400d0050b070b02072207e914995081d40242100302c50392005003c90f903840c2d161049140c80a03030400b10112403500d00174000484500c075003004403a84004005071450b003950060b40361010740300000b5400203000502040640043d00b104d0f024460507001c40300464017003401694220094100300c1d805900410040010030320a030001c00b00804c025100528102e800e8000c2960700c82c00f01150301004090381d008000d15840c0b10b12410300102c5075004942181001d9003c0c8e03904400c13040d04080c25940100b07041186d50340900c5817444211005043ca0f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 954568902 1250 954567652 954567659
    0x1c060e0c10091a0406090605071a1e0903031501180f060f030b04091502250f021305040b010e06031c02250b0708031003050102040801330501051c06 65
    0x41c28480d00b03006112190500041c0401100c0440069401740e882c6a194030008a0424804450301e8024040039282d060340c601c1e00010b9614092b2100e4041c441271107040500600c0340980e21700c44c03a00680301c015180c3c020400c01152507a00d0010852120091030400781200b82d004043e15890925000368840ba0618100000e00c9904a01001ca501c6419141409012282c0c2d04200c02c5a2401ca0007800f100201d05000c001c200c8135a00a04a880b00c0d451203c101c4000c0810b07070522040d00000490b40c0b810b10070442c0043d468064000c12082c414000e06000510703087c1d54000c1281810321a44e078101c2440340202d0681d641c1800148400448404901c5c240c0c44000002591620001810307100d41001c00361782500001c0001102003070355001e61510f0318006099a8a4129900041c01e5221314900c0c00e00c0400013503002e0000384014516000003085810803049000221a44050807a094481e4608809034807031980640c00c08840007400e12a80b220103421490041c0e0402c8a07140c40c42d90301c0c090021 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 954570152 1250 954568902 954568907
    0x3091a0c0d0c08040f0210090915030203010e07120f11090405010603060b030d080f091c05090406050603160c03050d1508070e070801121509060b09061c060e0c10 71
    0x1c10790841c00740c80c24007005985600c25202440240c5002d4042d550548920000d400d005c241c1c0b07104c1400030710709140303407560f24580348085881c2c4525460380d9000e003003004c00543c43d090003030030788006c0b10340c003c0d00300e139031a003e1145040090410001c00c001d454503070940500040300200c200c180009040100c0500d8240340c400c0c020002400100c13007051a01a102d503040c14000348540c8038050315196a0b00c01d440700b0440c6044040d0041c18406144101980950003411154035a4602202c2d41c81d6035860740c1c1c490040200b900c0e45604000c1c01a001401002916598110500c0c004962420709150031305071400c0032550361055440340c00b000c500340448180305200090f10740c0121031150044d210059101c9400402d8114143c98210005007031500600690301900d080c1b000491044001180c015243c29080007581e100680075035001d965000b0484c4582070988405038041c3c8120390740885241c981070030000040003400040c0800daa150840d1a07001300070440140700c0d0780010600c20140c01ea04800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 954571402 1250 954570152 954570157
    0x30711130c03021c0b030c1c0f120806040917090a0b0f0a09140105040e1510050301060206060a0303082202030318132f120705040611070b03010603091a0c 68
    0x8590141c20130081c4103001c0c0c03980c0d10684460070001005400c03100c01ca40c08020100781d06440011040160075072000004102030718000129205000303503019500b80f6500508040d400030507580c0124205042c2200080e0340310480c2c10011210101070b034a4021550205081280f15000840c4a4000184074104c4180180141c40691529580c1604d081d80b02d4055040e41c2404082440c0820310600062048107104240154018801111030600b281d080000442c41034ac414100e001261000005114055050040039403040c0140c038100611031850b68000c1807003c00500441380341c0100a013541c50807d000d6007100304180c00604036915071841120180b18030030b4094040e0301c50100c180c00d6419119042c000c19403a10199850700408440f0085040c0700b0703031850155000c8040080105200148004020500441e41c543d22142c51768100100036054002d48506c8020540c090801000030796940802c076410b462061501041c0c0801c1880c000d04845010001000c001d1780d144100000000708401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 954572652 1250 954571402 954571417
    0xf090c220f09140105040b030319170f0f0714130801020a03050f01120305030c0f030a051006050f04051507050303040609020f040e0606010309021c05070905010f0503030711130c0302 80
    0x4107091595540c000e51040f540d001000500584100e0700410403840d090f03103e10800e800c003400b40c2c1d18060703c1100005c2d15031841800d140c0801c0e1f07400c28240307903d45030186440c1d100d9036241583c451030402089103214524000d1014081100c110450401948184140e0b940003040c1010120030036150030790305000c1d4004045400000345404005443c8240490010703040b200c0b415445040180d20f45c038200c0f02580014407020800c0010002c07012103d031040c0003584901c2510000203200c0c101940d04188004035903002c002084018021111403140c060119400c6850403100284105481090364006000302c6a010300140004401c0000348021500884a140c0c800c03590756010f2454074040000301d42c0c505c04100780070f6003c0f200080e00355003c1c1d0700000d0700300d00040010001681c022441441030524940403500c0360003141c0100300e119000e0007018054940800321410050a107004a41d990184901c064a41d00d41e40702c4000b071646a010246040c0080203106002d40000c50102801039840000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 954573902 1250 954572652 954572669
    0x8100e03030103020a1503060b120702010c020c060d150302150c0601080d09030b0601031b031409060402031f0930030e1009020f100e090106020a020f090c22 69
    0x2541600109004411070381a01c2d8000c0c1080103281c2403031081e440743c82208043e0300a0644e20310b004550001d0890260002c0c11100341203820500e07121400030700703540c94900c00f0425540301c8040c2005603695102690064100c03d07900003035100c9084104110085a5400603410003016906200b0107440c490050207410081c008480700b0f640c0e030724035051f5100e0031f080e94078000682086003400002c1030302810f075030807140500d0081190303003450750368400008c0307640752007004641c0d15184001c0082040e100719500201540c003030205840d107078020a494107420109444005650f07210307031200365410b40c0314068140d04501645c5d50340760403100001808100010103040c071090f12581d1a0407d10034085c9040360140b200282c004100e0750f846400c05070050020807039002131070a00f03380f0b19458940380c0d204802c2031f550352030050242e4075041c42070200040e000101190050030b00c800c013584600c0300c22440300105803a902200c0c0d9626650311060300a01c000703c1200d030440e46050700d40211048100c8203448000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 954575152 1250 954573902 954573911
    0x30f051f0f080a03030f15080c010324030807020d060212071e0212031305030d0504111005030714070204090f1709130b19030602040e06060307120f11040810 69
    0x80e80498008001c0344075501440d4000d550740310002c1d02c60f8000704c56490b0480004104c00c542500d8040c03c0311150341014038154030030500c005642d0313414094102d891024040003202c80202c003000c8842c040c598000a0400c0400013048dc0464484c0350042c01078039081041103490701100754440c1301a800542c4d00310000340740e8048905030010444080c14508259400900170044060000d48032500002d0140c8004e00045e2070181c041070f0148000d19045503a10000907461409181c0300d9103106140d011070303005040140112407640c0d004000c0340e400000f1820001c8184800e07103074405c41031251640c000d40080c01c00303030300800b044040300010555601c6500e00d01e00550b04a030b01c000c070354000c3c850500c3d0b0154421159400804160384018142ca01c00341c1004800107103201c05095081603940308440f41a4001000c0024800305481280c0101c3e0869099240d8200210004c00190040f451190860380d40c1c46050044107141d8401002e401400400a4460341e45444541c1c81d01c0c0d0307000013018082d041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 954576402 1250 954575152 954575159
    0xa3602030708011d0601030b2805030f010c0f0e06070215030405010b03061b0f070b270d090b03090109060606021501140114130e0412020c030c010e0d03030f051f 71
    0x1c43d9840c01c81500e401c1085504c542c2d80000440c0030741440e008032500060410404455855114602200040200e40a22700c6a14140905241c07000721414000b840c7d24002d00007291a07400300070300c000201c0c94039045e81c1e0142c502c0e00042c014400c0c0701c4000d40c4002d0008803a07841ca45510301440c4918001c2008120b0000f80200f8035440d14021914003070301d00312044004460786034003c0500141c1c03410002c6613042888507035604001e600e0585d03903d6074803145100030450701843d07130588840c2030703d1540c0940f10340e150520000d00104164041c0400b00d00011001031005502588108801c58001c001801800d5603101d020391200048841c400801620303a001141d0051081001031408038103075a040c941c1849840040351940011460101034403921b20000340031148008010b01035402100303404914402035401078501002d4000f52402600403c812514680c0c01c88080c5c2d0708020150341052058000b4501100201414041c14081d249003030140050809c0b4844da42d400045e400c030142002c0c030384 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 954577652 1250 954576402 954576419
    0xe041e0b0a260c210f120405010f020f0d0504060e04151e030c0323010b0918030f030a0b24030a02072108091207020a360203070801 58
    0x59034080c01e04400c2d00c84121840c5007810ba00018001c4481d5400c0c1d48401c40e5000016040ca40d0b145500508088036650720000301d1805c2c8240b10400320b9241c000d00711a01c039603409400781e0080348142c1e410700001c54040c3c404103000380205124450031070291201813842541c080c1280d0880d0090800044110b00103074201e0030035228084000b4190060392000b0340c5020a201c181e0041204000c0070246182e4000000401c0c2c800e2600143d84900410190f1000d6080c0d0407048480c00e2003a0b0710181e0521880c0b1000352200311a440c3c029800c0d840014409400803202891071041c001003000c4c4035000000c01000c2071142c2d2014245400441341d40601101e41500110405c0e200684100031050070400302e081d0100a500800f003a03807040580d92116000d07410320300b101008200082011034240c100304030a4030401c2c000c6030a90350300005102e040844a07000b04045443c0c81c0181328440c60420045580c0d08000c44a84040700184507504210b242d9071034058010350400c0e10380002080201e000444c5000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 954578902 1250 954577652 954577669
    0xf190c020f0613150b01030e0f0c0306060406050906010c06021c05010911030c040b0304022d04060503160b0706020d020304050706030605030a03140a030b031c17160f0e041e0b 77
    0x16001110451100c004c0700e5040d000f032061030501030502d9940c0c04da400c24004248a00c010b005500c030060046804c6c524103040c10080c0043c45188202d280520030301055680740c4140d81c00c000b0038070700a030040e20640340c204020311a02d40490504010b44041b410009550380216068032428103042c0507101d151400c10f415404152aa000303280d106220034800250004045c5a10500003094000310041c403020280180501a01031942c3c400c01c1c010440c0c0e18101030207550014501540100b01d040740105007000314540a014000c0c21840004802050011701e406464079010380701d60455072070410303191081d5105180e01c12500400d040000005452801180301380d0516019118548215004803041c1d140340c1c0030000c2c0e0820f240e03403244c0c02d1130191010400d285c08071a01c4110300c0c801802c01d04025082988103001c214800e0420070030006a01c0e00400000e1280d00107003002e0700000841c142c103031840d4070810792264102c0e141001e881868074014556041c528a011030801140d922401441800e9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 954580152 1250 954578902 954578941
    0x200117100e07090905010b071a010320270108160e06010f120c03200c030723161a1911010f1e060b0a080f190c020f06 52
    0x44140031020030144864a0000358010090725040c01c45503200c5200b501121400e81003000707250720104a1408014007481000003c0c00e5041c5060031035071569a414858031f060800303207608801216001c0b00c983d01c0b2105000d40105803100ca851001e400000d8082d44075109100320542841200c2d40110200c0110f04440140c1d1b8000e0f5110780a5070b514401910581c1d005000c4d0010801000c408510044181c45003403072142642c2d034045140c241c6008a0a40c0b485002d200c007441d44400c00844550840000072110700340d50140c01145c2d000000d111440c2483c5071444c0c0617a482c010780c03031011030508000820030103848000070340925889600f030219626011300400981c141101017100b040c401e02952294100075521000810b034604038018000030303511820745503d403522840b41c5030310b00c1c0035280c040d50001c0c11030402c60f0b9080000c41b2000a24000c0b000d40807034242203d003004560f105910100808030010700d01d006102d00682c401000b035441a600280d441940079502c0880d920413030804203060319 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 954581402 1250 954580152 954580171
    0x4030305063a05010213140a12020d170408030705060a09080703141917010e040213020a050415050c0c030316030302030604090507080a060c140307030c0309200117 72
    0x1c0c08280c000004402c0c0c00d030200c003290140300c1007030800600240010220800e1003041c0c0140070b440c00c185d900455410300e81940c07140ca00c40c40c1c10300412100c0540040607540450340ba030a19011401c00440200425000d1948020002004103442c4000801041168420b40072039200e40d4820051404440c10708900a01c8290304224420100e4440e42c21881603c00c044405407030703c03001e1440c4101901740015008086601c09614044100358481e186004040e01c1e0000f078114a42a0b000540c100f400c5a01c6400c11940492803078140c2d4460015100070700002407920f0b08000c984031015016412a20040016101741e011095050a0110076500250301d0764801c00810381151b6001e402039000101b0554000360ba8904000125100300030b241c0c01000420701400c40c0b4503440c1090b50540f180c0503c0d82081c8810030042945d0241c40c0d0003100d90154040ca400103068900b104201e028118a54015101c000095650801c0703a545241d0610000c0b402d80310000f084609040c0c10030307014001c4505160 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 954582652 1250 954581402 954581449
    0x20150c090a09061d0f0603030406050f040909030503040209161409030c09040b0907080111071e020d0809100318062d0605040f020c0c100905180403030506 68
    0x1200120400500300040008000903140380e00e42c1440c900b251220782c8600c910310a00744421104034903000724241c000f0184181c8091500d04040071903907030b00c518401c000c108400001d0340c481c03000b42c4005840103004100014090603c090400070182e4000380c600b03030b104103021800700b00c0560204900381c2c0c42c50600d4540100100400088000ea07800c807810081c0c0500500310001d1b030b581c1e11084071920491040c80116850700f4107064152604006402034a00c80e8908014040c808080713400b0b840754180d00140c940a40d03812000300c11408456103200a4100c02006240001c005010010b4004440207480c211000c0303203807600440030b4909030300c00003a2400a81c4d055101080d81d0790803112040350301410b8119941d02041202420500c1c403124a005c4c00e40c3c4020078003440ca407500a19021a5006d50150b0500da003240e840341e1035070421115180301d5109080089002c1e40600625001810000c4c190007280700d0214590400f104103ca003200042d1500002819924214014551010f9258020700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 954583902 1250 954582652 954582661
    0x250210020f070b0d06050d0f030e0a03030e060307090909120807020309090f040311030d05041b0e070315171c21020708070c0621060602030d0b0a05040c2015 69
    0x1c4196201281110015843d05c0020419849801144240501c12100e80316082d1050400500303040c901506a03115111501081000c02d038401c01802002200301c4040742d607619100c0041d0ba5030300701517010a801c0c504000616061040907000707503d00707001030f40701c40c0c00341d50301d0610482c0c991080c8401e0307035401032602010070410041e401c14180e001c0e209050480c004c040c600221071864006410145405454038204410042d50103032400103c1803a8055401c500d0810700382c0e882202e0000c0400042543e190207007100c0049d980381880043c80b0305e0440781210480508059164502c0340300d40d02400c04070540ca0205940b1514010300d44a101d180c0b02130180e003801c1005006035108901c152071100b003d01c502c41c081903030282480c00a01240e1603030580d800c1c504032080f1004c1c05000c1035264041c40e044c020001c00b600402120700c3e500f46000005001d880f02d900051102285402c9190494075040d803130245a80c1085120707488031144521048030740ca001c4180c0b0fa03900041d540044410f900381003c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 954585152 1250 954583902 954583919
    0x1c0305070516080d05130c0f180c0c2f0f0307060c0305070b10090507020c0901090903090e0c1b120d050604090212030a0e0301060e040305030705250210020f07 70
    0x10614103108902013460040340c2010601aa81e0940300b01d81c881c48661401010000407200b45802094002c12060702c140c503001000e00248010b00030090081e407030b440d0403460316110b00c80300103099500004041002c40c050380d035000d0030001c4028480c0040c4010b41144140e10b03095020380b15001c00140103181460a04104546200072402c0440c144081801581c0004080d540014070030800c6040d00310140d8641701d00760703040e50f4024242e003082d50004450400d040e2900c010503410350304072a80204404815183c102d60130017166001000481c01170040c041c403a89504000e040014440d00030518880400c041103031103c000121003050008200800070420000d50003143c1d0240300100005010030b5160045440210b1403480f8203000e8000082d03400941d80c02803410188284207030005c02840c1c0c00c2108090301164060009018400040300150002b40300301c04070b40448011527285049801c0c502005e64030641304010882c07059401030136940e0f85510000c0c251008112100c0240b42c000c1c44d00c60344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 954586402 1250 954585152 954585187
    0xd0501290d080406210608150105100c110102070816060801080d0c11040b04090c030c09090b06090405030f040906080d0c030206180c040c0804021203030c03160c0b0106021c03050705 80
    0x1045400308800310801c17600300d40f00d10401002d1810103840c4901d0304e00b4480a08402c16080a03108805164003071107100c0d403101c9080340c032661203004031300c18499502c0180d291801d03990240003240720f2001500d02119501540404991241d107074465140d807114051500c500882858100180040d0305000105420000340c1c2502c05000d000003d00c1c0ca00800881d0554484010a6807030f21440c00c1c2c10810800c903110b48100a21150a003000f051100c2e40d01d110007034501421152040c0c008071302043c1400307020700485002440450b0b400e6a00d60361804004083c021501c11100c0324000c14155180c0325005503104981903525a001d400e59980b10000503040e6012000e20450300d128070900c0039515211481410715210140d1a0001a4945072040013400400401440c40c0b0b03030000c0c0240001c09960704180c90300803200d049900141b82c02c481c01120f0b03901c0620b10180056125500029440d81c001c180c031043c50f81c6003680d42003180e84100c4144c007500c0040d140303800040c80c100102072629400031203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 954587652 1250 954586402 954586427
    0x30d090e2a0c011506080c07020409060b06161202010506100807090509090c0a210803070c1b1706040c051302130602160e010311010e0d0501290d080406 67
    0x444064401903801501c0c0a4200c581e004241d69903507520011540e040e40c600c10001d00312480d250314185030540100e801401500d00007070143d0f0303c43d503440c010400e058100c40501500a4500c0d0f49518088d400c1640b4480103113403d4901005075203440c581c0d144103002e8203206640244c0000119418074904890300e40c402480c4104019500b980803605945004009008500d2180140710359000e0001300106000150b002c4c0c00004104121411039030580b41006603a079806c07000a83e2a9511a002030b40e00c10307000800103207034214404070030300c42c1d10244101800b550448900d084040b1040400c0303076501d450980b400352208049081c10400740c41e01c004000c0b81c81800d00809070030044550040b0802042d40e40102016070000981080c1c1c44a076000e0200007000e00c1c03503200d00c0c03551441d00d800c441210851045410008203e1858001c8d4903400390452841354800b00030030040ba1955040c0140c0c0a00d1000001c0304c100c141184804c80c60079440101c19244c02c52800d03032402d031a188050340c00c81003d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 954588902 1250 954587652 954587701
    0x90c1c0222050105010314010807150504170313060302030f150f1305181216030c150501031e080315030f0604030c0c0902180f03030c0d030902030d090e 67
    0x3041240d04250700074010840d00c100404100c550403d40050180c0d06840f503102c0c103142004c0010082d0703c000185000883e000a58184824000b0120442d05489a500a8101e038004400c1c00c811104001000702514103461803080e40c180e8640000710280d100c1900c0c420f009174a036401050000c041941c03514800b01c0000c00450000324a48049003070081c454031103a401ca540c0d01c0811442076515540c2001c0341d48504098034000e0075161010055000f91010a520b0079106d03440001050301410383c0102e440c0c1c00c40a5405d060418420000c00b922003400111a582c1307041941d0100e4048504580201e190b0200d0b0140c15035940450482c0283c80380c85000360300d4071410030440304822060000324000d03802580c3d0741000e401070f0b0405401da4501540900c250a1040110000d5050504100703801d4910032580002c11034400c00000b481c0d030003401c480f00c41c1c40c01903030502181d0710b8069202500040c42a4156051280b100354140c03207003500c52141c08000003902c40003c3c04d00b150000a0112681d042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 954590152 1250 954588902 954588919
    0x1d0d030c0e130b03010e060405030d11040b040e0a06080c280905010e0906150f01050307020a0b071812020d0b0405010e01052e1a1b06040503070308090c1c02 69
    0x70000030b4540c2a00c03181080c0d00070b07559032154445003070a024034900d01a4040090909042640c0c6050b42c3e44110f003034008246989504240c2034500341003c0f2001807848200c0e4070740f200d44403c4644030b9640c0680d500b0b00046d1400e074000648400c0070a215035a49d90081400691814241c61b801800c1c0703003100780d00d4804034a0b601c00f041c01c4210b0301c915070181c02c18191921040c5040b0040c1c919009000e043c08084d10400c10307860fa125540c11040282c1400c0a29110b912510303001d0069103425900c1800400c0e00d10780104003c00207a01032041040b04c040181c81c10780150380c54034865007200180f42c020750810b607080e030228040384d40c0344483c0303070014412000061901402c0d091242180c02c2a6010201201600c3c044640ca404003100809007017216038441190a1508040120414242d42c1082100c01c0c0482c40002d00c1c80e1240b51401d0140d100720554550b46410b2520540302e40c030a0300304502048100020450804001811260f03a00024101c040700300c2034016620030070003201d01c00f2a4843e900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 954591402 1250 954590152 954590177
    0x302090109050a06020a23070306020a02010b0306152106010603020a05070f081206092403070503070b03010f1706060418050a0c03050c060901200a0f030807031d0d030c 74
    0x40102d440000c080d20790142c0b44861191508803041f48480d014050b010440701140e081e0b6070400301d01a41126849400141e42c0d0b81c406800f40d0140107207910441c1c0c1401500100140342c1058131021091603021100903290709c0000651140c0c40d05036121500e0540e10890050200c5c901a0b030007443c40fa04942480e6080080d50354070400c4c90300c04010701700d4075143d01180c03a040700741550600b1904a50102c0d90702d0312a01e4509403006840300c02d07403207400c0c0e038a070500d240241c1074070107019040107441e01030103035110240c0f11620440154020310404100c0c0c4602000020100c0c038200020030316850348030151116407580380800002d000c408d14481504081c488080b0009481041801c0000d8801e141c800410741c81c43c1842ca09160b40d1032802801400200281e0941e0b80c0d101d01060800315500e1034202e420103801154030f15002070b6000040c40d440f40c0301110414540c02c4400c3c00d00c41c0c12556010304c00c440f000d403074946035180c0081402c070030396112140f89841d2034000d070030101c000c903000d1400100360b824 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 954592652 1250 954591402 954591409
    0x12020c0303160219060b1003060b03060d061e09140c010807080702010f1a0102101107080f0903031204150902060406051c1508150105010503013008030f1008030307030209010905 78
    0x7000401140c210390740324a01b2405062180c802c40f5801001e0400300b00c3c0603e4544075448a21006140d540320f41140240c083c20031001d0352003c10140f44083c60354820001d4009a04014074180000380e480301441c5541002400d0700080b0144d20f010103030b5503c4400e0321200c0040e516804090041d5040d03540313444040180034071a10403108845004042503d24807451000607007001c0c18a61040c48031800c2c403902c048407280e00340840303060a034404034041c0e0300c80d001002c441035030080048540d41404001035204008000c83d00a60042e80105640c1b0751044501003070f0b0f0210b801026000350000018001000407500440250141a40100c0c861281620160304007080398459010514848a03561040c0b01e0103108004109940412042c00c0006505050018000780014865594400f107200f0740e00070070406040008030400110a6500e101f44624503040b580ba1304119100003102800b0000a0700c52406000036504940c40030010354619100c00d23900300d010394403040e005410f01030301c0c940010b150745 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 954593902 1250 954592652 954592693
    0x9151a09040f0c110a030e060f090901141215010501050f070606030311070b04050a1a0d050106050316080601200109020a03050106150c030504061b02060d050712020c03031602 77
    0x11202d03100150381c0030341c000007400e45110554181c1c419401440c42000081d086511115280c400b141d119803103040350011103455101e196922600480201d000140c038842c18902c06d00040811280e40c00d18203030040c059540e035201011001214925a001007006500990040c50500400844a8034054164685109a40c1785a004500040d001860007181100a03c81d01c1e020b445400c200c203203001d14000c0002e04106040c0180386466030701c0c0d13001141685d8032004440c03501d280310314144055a03658202404642048554403403800000c4009145a4481c0d02a584246c50584802102c05001800e145504040d011024015960785c01d405025030380745480c0758010b501c5000046055400d00d0641e04000c04810400c0c003d1001178001000026004000d480035241a80340018800c40c403d4500200050403c1c1c01a401c9640007854107100103c54000c1e5100d01d200d03485030014540f4101c1100b040317210f02811900301c0d030002d03c0403800b44c00c252039a01b41d164026204803010740d00b040d5590070945 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 954595152 1250 954593902 954593921
    0x23040303090f1e02090a090215090a15050d0627090c36050906010e070504050907030209010e06040b121b0a020d08010509060120010e07090f0609151a0904 68
    0x20f40d440d61a1400c520301407021035803048135004180800d0701154045042400e800140059548020800140c642c40c0c075110a0b00618017010340c03c0310070340e00680c05405a4807201d15a017005003007001c0410820082c0c01400d215009154680c1c4030107154004800043c00c2003a0300b11036071240b44000042010701440300107184141e0314040440300d1600350ba840001c404c0110f10314207007400d200402c400e018020030101d045030f0800000500301d0366650b004540e00d00c1150450f9078080d40003801d00541543c142c1c06041180c1080e00c55a00014854080110a01592085da540907038100f00c0d0038009048802c58075080480311406030301c4070000704104269600104610780060b400307070b0f0640440f03650200c034003401010240c50480c51030404400003400c000d01002114201e210320000752010080952003800700060807010380350f283d0307115441c1e90090700b03004159001d041d040040c041078558951213480850b48500c04058200e40c9030260341c6560300311b1094040c03e4004107010464950f103550040050b031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 954596402 1250 954595152 954595193
    0x20f0301060b120a2013030b0f0403030f061a0a05070605011419051522030309260a0b130605010803120708070e150c0102041823040303090f 62
    0x203e1205070140070304040020036208000d03040640c0007001e42400703070300071902d143c888010340d40d100f0310411035908140c40c03a48020300701740304001000710005816201c180036501c41e0341c09021034440f03025130704281c03001d80c020908940310140c1d88000344d80312000148101007007828400c0c00c00306541c54084c1110401d912016450f001e01a41c12498a4a000c81803000d850700d9925100807030900010031920034010500c004000070014003030540d12024039095008900409080045603102c0c60300034540c03d01c0e445038036001c1c20740480c0c5900d1500405607a90190410800411302c1c82e4290712606219840039100400e40d003407080d8244007145403030050724003900d1450000c603076804000d01084000a0010f00c6801003000d110184601c165001e8820048420300b02c072140b4180295036120441485010b1541d4003640c03000400181034109180364000d0480c01c9a402c1113001b40000103240100c40e500100c0401d801441700140000c0c1c0070760b000c020110700480c042c454901c12582e82008050845500005c0e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 954597652 1250 954596402 954596407
    0xc03090102010b0604060806011404030204180c05150f0304031106090d0e01030b0d0b0c0f0a0c1707120822081206010e130513122307120c020f0301060b 67
    0x6903540c09014100400c1000e031040c6250600d80400103021070b0703029245034108048514085148298031041d14042e5030006d00402401542000c5503505101d2110111082840020000303100e103803203a40c00018040b0041810301c0d001c43e4005140b100c0c2e000410480510480901048410a04002051054030240010080c20b1040078000d001c0909605445040609000c0891015200c2c0750701111050340c0321846142c0f82d1540c4407040c8040c012210108416680403801c0d807050703640f04900303610301401408da0084c010404000c00e203083c0301381d10000d0450341c0113070701c20b441d003d00ca0f41c1c0d1b1542c02040100da03658080600340940f896103180c140c0650314501d010a0b507070f008000440c0d40760f4110350f0908022401c2491b180120752251040400b6001099468000403110000b40b10200c003155030024190301c001c0c0a0f280041c00780d2000b01e0a2407031041c0d40400103d103045034003044549640d0422001890800031002c100e60181c0d034000220f8000c4003005440b401c0381c9090203100050305040700c2168 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 954598902 1250 954597652 954597667
    0x70501141008010b06070f0c05131d0a230705060a09470912010e10090308012d0306020307030e030f040e04020105130807030b0708160f1101020c03 65
    0x849000942c0011a15034500541c9615558840e011100702c035a02c01d440b10614000c40c2001032040600c0e6100b00e400220842e000400c000702c41d4005543c40b020804420283d0040780000c0d0b9583c043c01300010841c0c02c0304615200c440b503201000c800001c040e6411110b090392108080f03442d5809c816420004180340501c2400480308042001068601c1c0c582100c405a40e48840050303820300a04a604281c03440c0215400300709010401c4a100d80b002801d0f00101400048030039000701003c00d03014003640604040c2516034880c90064140142d007507503600050380d00b4000c0307002100d41d19600caa03501c0031070049442403550074000c1d40001140202070040e03e92030944805030981d4094481c0d00213a40040200d01e07218414501070f203081e241e020800320178a81d103a1006031514420b41c01d6100300d40101c0e050008200c40005021030560748610050b04003511851010b0f20320640542d404601040e504a01d148807130305c1403445051200d614940702140c000340d62151400c9a00921010700e035604005084d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 954600152 1250 954598902 954598921
    0xf160605070309030e06311502070b0909060a0320011d0604091503020607060e0c060315012f0a02150406020319030f020c0a0c09020c0a06020f07050114 67
    0x1554421002d08003840041c1d900c0e034000305400d0031019180d01c52403000c100402c400001c0c44c00c007680c0c8210248170040c406003055805600c01543d101d41c0100c1c00281e10782e64029032011640c041201c90251100c1e062410f12410007544260050a16410a03413150000010504441c0c000360705600c05003206451000150004100d0450098640d84886018007500c40a40f100c2007101d0481d0010340c00096070074504e240b03003920355a0720b900c080d5015401180c01803e01140c0c0c2e10411030190a00308880a0744285414404a80012124501d080203a031030169060350180300380684400a8450b00000b011051100180c001d55a0a9007404c66001403200c00c11400c1000c02d59100e00c1c8048100e505040c82e1100007543c070b118086201c0c0e0512700501402902c14042c3c1c003c0280308507a1041592100800c84249948169088040c0c030081d004003000510b8410301e108541044a070f9401030a03074000d268841c1d0000c0c1d80b000480c01e00c036040812028001c03c0c420b100b0481c8403810426644168240858507 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 954601402 1250 954600152 954600161
    0x506070504060e040f0902060705061f060e09060f0a09020a1211040302150c061612141b040308031006020f0304350601080c030f0a120804080f1606 65
    0x50024003400304000d21080b07800c010014040c1070200d41c003003000a010765004025101c22180250002d8020410f43c04011011400a105001283e81c3e2980c542c030010101351044000d1040c3c81c0030a03000600d84000b82040d1a82aa00c500301800c0c0741c541c1521080403428071109544201281980400c584000070351201c0140012101041c090001e008004030b00c8415104500c40203201343ca00601c9209004030a10540c0c41546555090f600c040c13801100d04850b100c8240461400243c00c14000c040c2490349224007501002168a01d801e207588000315a401a50420100c40107410288000000030b042900210f105002030644000103500c0c20001a18140141296000316041488248410310100c1c810303c0b511025582e8840c8245450096605000318014103560240504c0e030011450700307400647e5802c290300031f40c102c0704110702d0101542d0302d46020703110003802615050248111a8424a00703160464090640d0f140b502081e030603803001d10b03401400780140103c5d541d80000e00f84449c030b01c01d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 954602652 1250 954601402 954601411
    0xc090a14040e03091507020d080d140906040b0412020a02040f0b0420090f0f1917120415030b060703080f46090812010b040602030a1d041103040506 65
    0xc500346500d00c000240c031841e896103200d40a80d4003058641c00e55823225407018481c1d4000754400d6807000e0a500034006803014844001c141100d100c0480c500c840c00050b0b251155030080c0c0e1654081c1ca036661002071148000c40b100045204010000025a443d4442c24400f44403841f400914030f10400f0500050b2000c13104100001c0c8065419400060401c1040325140801200d50041d452407d100041888008451032030704074604000010003084000f0680040d80e006804241000d100301d205107540c0d040d855035103204c90000380406c0050305115500f00c00c0c01481400d000c80d110702c0410114086801100003a0001118031081c0a2002c90300703880c0c0390b00054071010f40054240d41c0264101a409610310000035103175101d10940588030070421501e980a5015018001d407299802c0207403490708100da1581d64504072000004800402c50101e40844280380c014505200039081c0a031041100001802c40b0320003002c240380102e964511880f01c0f42c0295910103074882c00d2500b0240e03e801340080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 954603902 1250 954602652 954602681
    0x2092508150f03032b140a05061c03110f031c0e03041202010c111002010b01020c0405010f031211120a0f0906080105120a050105070507050f06041a0c090a1404 70
    0x2c284007015140841240c00d40400342c05843d0169034100741c1c040300c1014107144001c1c8240341030407001c2e001e651043c6207070148507569020302550300d4110800c101c0c244021a00e05014a8115019000030302810a00c9589410308041c1e941000180b19114190303449100e000e40031034201c40d924050040c3c03034460100c40c41c103103100450419041140e06140780f4150003020341444115a03c410421054103030440c42d80e400608040501206060060f0181c40400c52007409400361085400081c00d00b44aa14100d5014840484c0c4203451038640c00042c042c0c0d80c0b6401c4c100008042c0b4040e604004005400700340d000d00030055a030b21a00f00d001400c0400c61300c220401c11030056400c001c02d5600410050560b40120b460002c610b01e0294060b00d003021000340180f45508100c20418040e07080005484104d00800c15505c911000d0340115455600841e0000c00e0401c019954040c0b058018110561000162111030301d480811400100b01907241d501c04025000e01c0c1c07400070101d0500703000d540400061070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 954605152 1250 954603902 954603919
    0x7080f151201050a2f071104021308010b010f080402030a020d140a050d0905041e0f020705070f030b0f040b0a09031119051c1409040b0a03031215060203070209250815 73
    0x9402405e2184510780014194200c612240c5446550b030b5811124944210210b610126644001182c01380c0708a461590100d01d08001000407640140c121910469009000e000200307001d03404c03c4290b814188003588e201c441d68003c06d80c0c0020400100d0103960141c0c0091007611040d0100800c80e6101d030300014003403402d2030720206080384c0640a012141e00c200780302241011004055400074010f489020f42180f01d50000040c1c0300512414200644c1e02070400e0398034990b904543c401d40b00e6010f48008280245200c002a141780440d4084500c3c54424071b03003d4003080d0160815417412010300c84d080c0300d160701d910400c000c0120030060f0491040c0540f5500426009015014040c94911085680390b0100011b8940311541c0710b5001102c00071006004207151030b01c904008140d00110713451803001031301d0207403e02c01002d0016005030480e4460350046150901950038000503c90103403074027a40c003085400d995141e01030f015030144403041540c2d1b005040c0c03400300d282040011401e9070b16402801007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 954606402 1250 954605152 954605231
    0x6090601140a0c140703081b010e030703120f020309010c02100e1506040207170301170303040b1f18020a021b09010e15030d1707080f151201050a 64
    0x3400c0d104042807500740f0041541c0b1034180600c910b1034200300c03201e0a004d0b406004c001c011400380548038505c0e03004000d4210780c25000465003218068800241185d000344466400644034546042c404107820001281c80c10500c0d014400741c0e007064400300b980d40d442d08003c4c200c141e410001207003104000c45003030001d50061104282c0360421009404868404000000c4075511190100d0382204da000c00707070000080000c041c05403203802c20b000d840005a0101020a50304400100313580c00381c0d8001c401d0030310075111100381100442010a10080002202c0303000510f042d520040c4243c0100507000160752220107480c02810300e9030720310003040741403003c1c41c1072041030702c0d2810000d0544a50901d2500d15423a101c140074480c40440d115254584500c80e800181c5607446000100e01c40d1140c100d05080e925003620070780300508216803043c8040308030b40004801c10b01040c50446a44e0303001d403131003190101c60f10301c503800d50b1021200140500e40701c0c044000e542405810352030200c01d040e04850042d911 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 954607652 1250 954606402 954606437
    0x30c0a031203020c0f0f060f01120b0705030a090b04060f0b18060111250501120b030a2405130203060f0906060d02010e030307050f120a0e060d060b070b06090601 71
    0x4220a96000300b503400300358008200d8007046124038826199017202c40b035020b00701045950700f1040319044d0145a00c41d00004035407101a501c00302d0310340d011600025a81c1d030040100c03599000203140c180200c5c4c9070b510100205140c48032540c041c038040c01d0003080b00945940e002c0182d800c1030307900d1401218151060640350f549000c801e508140b09281c4100c207500450b038002d28020240112044240104088043c0040c4044043c81160f0080c2c8881e2405c03401d0301511401c84c0c404404840c0c142c3c00515039034000a040e100c544068150100e02c8402a44000941c241200e03811120551030340b801203111415803404005280d4005c0f03406c80789407290300d000580603480f80d0780900210b0007180300c82c00140440e80115841c1602c0100a402c89071200007a0500e155200241e0000d581d00340940a001c0e9442100d03070b800c0f00d00d0b0b000c031525030680c143d01d500240030041e4002900c3c4504159101e03401304540c02110020100c0e2801880404503a0810100300070708500c02412a6060024121401ca540b18 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 954608902 1250 954607652 954607673
    0x9050f0d05101109090106080106121812021c0e1216030305030a110c1015060509060c011d0f06010b0a080c13050415090b092707090911030c0a03 64
    0x8948503000c10449910880c4000d20302824007044d0b03000c505c203000426803d0344102e0043c100c8026960365401c0c0d00202c03e07141c0440e112102d03000141e07071503180c8090104101c681d00c3d20039080184100d030032240c4c00b078050023543d00d409034503000001e143c1c9540c04524a04060180008681c800142c40300585400c030b03050505c00c4601c4000c01f48140400040d2070800261310600b0000045800c9035503540a0291480c0c4031320a41070300030a140d00e0b0100f803002d600700c1c140c0454265829070b200c2a1401000ca400c010b22a0049181c141c015074a50800d00150b440c250722200e180d40b4034200030206000c840c89010b041a01c140c2085030303051300c244002d00045512800143e0807075160a091595050000003004450240b500200d402c00d0900c0380d220501c01c03500035000e0458982c0b45040000640c150100a21240b007030340e90380f207055842e1414004000f110080b0f0301500450004030f811540e69119403109031076043c40140c0d1121404020700f00d0070304040c00058140740342115028081402c50b91081d41380b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 954610152 1250 954608902 954608923
    0x60e06040b0a0c06180309090e060402030303150f0406080a120f02120702040e011d0d0302120f13051507080901290d0c090b12030a05041e1509050f0d05 67
    0x3c000901c01600703101d5180d000d040b4241c410728401c907980030b20707040180070b01042c2e106030041240b5106140204250101e08d203401650300802442c9141c0301c41c440c2d00c588591384002990700201e24071922003c1d50762480b0b0710000384501ca001d0000f40d1042e00704403104070f580c10881020b1001c4980100b641c61350200d10f1050940000c5019604d502480c0042801007400014025080d80307001603d00c4148504200542648240c1007151007101011a088090b4043c01842c043c005411001080c1480c1d0382c0001d46a0001f456410034500c0c8203a51102071400740b800e4003042218200006110840b9400003400f80d001c0e03505c0d03009000040142450380d8100708609000f180d001d1102080c0e4843d9616000201c8855400030345082c00d030f54644d82c0f10300081c001007202c05d200d42480c4811a144020200664460048584a40382041c0c034266840000f8145500c1c40002224020b0700801d2003c41c0318040c258000495542500d46400c1c44c2c14024001900000684640b0241c034810001030300008040030304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 954611402 1250 954610152 954610157
    0x2b1205070309060c0c090227040c0c0602031e04111c02010206072f030c0706210c0302040504110c070605092101090215120714032701020c07060e06040b0a 68
    0x40d2449400c1134500c0554503009031b0f2400740006000001d03e6200c0d16550061a2426098100d40d02c1e1036042004403040e1560050114070110032001c01300c1e2103a401b03994001522546045540290f0280f8990131404890485054010345025030141c241082c194155581155221011b00800c1c0c00203551400001e00c083c0030811541c0c0800b4047c1301c40c0c0d0070301c000c0c414510000c072245c102c1d41e04925200c5d040402045902d1003107030070000350148102d8078000b0500c076811250190401c4070381900040c103080f00b80070041c1070f003c00000421751618800d2105c0d06860f820329603120300d09102d58504103600d541c00303401081024000200a42c1e5040c81d000401e40c810321541940303800c48082d65014080a10019611024101010541241403001040c01b24030a9000c00041d0307031201002e4855000d08071110080c0401031000510380350315410a044002c200b41c1240d00c11600d03c41d6060709a80c0004001d04d07050300610008c10245800c035550510f03102c000c844403800e060822410403d1801004d842104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 954612652 1250 954611402 954611417
    0x72d0605070c0b1608152d060f040510030902010509040b03330f010807050904020303090d2402030c0702010e0a09020408062d04030e2b120507030906 66
    0x7214001e4910b01d0181c0d600c10f081d0a800d1810041c200c249902d40c61100b00841c4201c00054031b4000c0d468103408001030f0051080c0903c42c0c4c6c03807081001001c84c003800d0381c8071022540000b00f040c0d52004007800d1006000e200c129601c0d030414040c03050001f512109103050604260300032006070307000001e80c2c0028030103440010f121140d99001a14094500b04602c2104c8080c04019046451000e4040c2c014090b44100d414944c507401083c1540b11401d12402855801420381071003140b9080300a140c019000600f103c1c01d00d01d004d800507881d803d6494045803800c54800742c414600711408004800150039003804c50640c500b101c12041d640c818010700a041245005209280799221901200681183e40045443d19180e0701201c1c0d8030324094806000c892060203050445c100b49002d041da4840c1031909402c00c0f5103640d41c00303030f604010b0780023101d5001c0003a2071500502c00320b8070220011011052086020103800c1e06100a03202e0700c40d560b42c03007002070030811207020a4201003000c1c200c5d4a145000701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 954613902 1250 954612652 954612661
    0x7022e03060b0705060a020f09040204030503030601091a1c111c0606030b13050c04030f0501092d060c020f01020d021815030103170d02070501090c051f080408070b0408072d0605 78
    0x55051084c48049c1742c1c0544045008000c0c4500000618071584003a20b9607a441502c17961500d113440c0c424807d00d8042c17002041b5071004130b4240342a00c080c2180b00e034004a0b0311441e00302da15070306402c2600e81300407140705c2082102c0c140c512809141d00401082c00d0801400820001180311140c05160030440e44d13403108041906805882e04543c000e581180301c000c908a21807400501070911490f0581380140711041e10201444250b50700083c00041c48a840c1e02d5100640e5890040e0420202c6141507026103403100c00340c0b0000b8001456090702c034030f20050741c928814450881c114207116025008805c4a001c9074030744524441102d054070340202503203824a43d0f401c1004c0a9100e65035004408a00104002041100c1504250089031040c203030034074019103900512203075180d410102400e00144100f00e940580c099030001d60090700902ca070a14122060302c45506220301641d00b20f446900005401041c455a524404207401d50052075400c43d40604110040c003c100c2c7c00c02038441580c410114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 954615152 1250 954613902 954613927
    0x3130602070c120803040605160c020108041b0825030f24090b06030c100807030903022a030d1404032d121209020d0807022e03060b0705060a02 63
    0x900030000043e43d07407580c5000303160006203604265021107070142000082001c0c219400036085103e101552a041d14424903001140d036000b01a00a4420402800c2d81c14540b1300d00b1880e4101408504008040145444490002450205075842450f1700c0302c0d04207000282c40d081e225407545401c010325905640304800510544141071017824800d0389400906410130262889441c8650000c42c00d640c400c0f02a2001d11505d0501ca07070b8031000017072005000810041c020351249031180c0c0648111140107404604036a8001c002060b904003681600303a02ca1251728007045620300789059490000010a80c041d40c0314194002c0340401010f0301230062841000f80e1200c820103800c00326500040103000f0482c10980200000d20b86d038800095103a2603070784100e006c24003807107281550141400341000c031181c4480005411180c401c907484004810b4003c6004508043c031414007014050b100c07401c0d410041d020701200c903907510103544240280100000f00b4000709420707501c1480c8030005640c034a80e101c1403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 954616402 1250 954615152 954615173
    0xb450a0c0216060306050405060f0d060c0203160b04140a050a0305090d020402280e030304091a030d0905100f0f03091103030d052e090f09020d05160b0313060207 71
    0x180790b09041c8690005810365054105001b19003058a0400280d01d07800b05100007244950030013034100f11000c65842c0000c0250740806020000c40c07060782e0401c0440380c4003210010b5901d609032021610721081c4400d01c02148140c140c4000700100070113281016659107610343c01c807000d0203000d04c240410070807550785400c410000d103d580140115610780c44c4d105503402041c540620074182d10f50458400541c9030051240b40a01d0390014015801c181c42d242d40310025000508030488a40c0c00001504140d4400f085164445002c1da12075246540c24102440710003400449500f040040b0020114a1190043d203000c0d030400c0c040c40c01007001411800c200e8010540e54680c1a01840b0029504c4020203207a404603014290341d80100c8000c942002c0082013810109100c203002d0320f04c404042084d0f2183d6408140d103c01c0d54400403030002d2854000505182c0310320001d94090b001400400700a24011001e040034182d00b865007801c60500ca00c08d0410314810102c010440d41d400030b80c500c24051007628 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 954617652 1250 954616402 954616423
    0x4030309020a080d090f060212031e16030f0c0f180510050417030a0e1c0203010501030c170708060114031005070203040f1215050a0b450a0c02 63
    0x1d030b071140e5100760080d40c1c1d0b003240c42280300095a442001c200c0d280f02c0300c610011180641e00070180c90103c12101c140951028000795152081c1c07620001c003c1d4102c84925105200c40c803140c6804c080821000740a507100c400400b2120351400d058058216005112140080918580040c1052500c044c008041c100f9030041d503485a001180c10246940c0031005105448500b100e6080c44100d4090700e96903030084000e0742001c01c2c60b10024021505010728580010f04d901c0300380200d460b1954021908680081e00180c580703002c2001d06202e83d002c0c4002076200301d007900004004181c9449c41c0a41c4840b010b0040d26480f41101040351070715542044040c0e00c820042e90208218180794101035070b2544540f05050480b404100005100002c110341da2640320b41120380c6c4400071201c0d0341010018034004142d26000342d40ca141549560710341401111031200c603004204064050100821146003090301e1603444a11381d0401c0e400d00c0104d12904076040072880c3c0d00811030b4100c41c101642041c800d0107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 954618902 1250 954617652 954617659
    0x6050c070f0b0a0c05040305031b1009030206010905150f0f040b19030b0c0c2e0c09141207090903091e0e0f0601051602010318140f0a1205030403030902 67
    0xd400e5001d1048507240782d030183c90445010407000d800710100340d815008510000d001e51f0002d0100c826401d90141040b121560f1070404d50307641060651240c011134104002c15801a40801c0051042034184d20405801101d054600820303401c00c08001611608840015409000e00183c1400c2d90f4aa94100f403903100c50041040c1c6c48150f03e00411442d0041c00d100075204406140c003c06c0d0080022001c0b640310b001d0003070152800c4017009446441301c0c0b90500074142e0001380c41d500842002144c1c40b030381b00e500140d50355150100e132400d20080502d14003903960b24800c02d19134038040100740c00001c04004503650b02802150301502400c003a05c00d0300b00c41d40301c04c40c80e03400d4210f002d025207a44030060b0161950081c03100c196854403031801904480456009000c074001700318000c819031180c00c0c00d0300c006205250220300e080c040d03101075180b042c0c004011515464802c2100e801003605100c4031343c81c61005e8004101c0d140994441410882100840a040c030200002040600d03220b60490341c1d900743c024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 954620152 1250 954618902 954618923
    0x30606030506281a07020307051c030f09050604090f1b02100b0d080301030302100c03021305130e2a060a020a080f09030312180601260f060703022701090306050c07 72
    0x1c0341c413044580c00240102d2090148031340c08501850962081404031021b1500002e00c9080d60380c5c02c1e241580403c03040f00c1031141d070303160004182d0303030700320003000541100b000100300004143e0900c030503604551000e03040103054101d85840c1581c002001e5614502d501320120742c415800300403540780c1d1082c020190010030000000700c09d150300040c0c003010366207644908000c044030605040b4100d008454980c4030620101c0c1080000740790917400c0d290344459100c0009440700c0c2030b000722854004c00f00d0f0050741c0741d204501a050a80140c214240e9004410b4031040d14044401d0402502c40d40c400000515008000c517a0715900b518200c2a207a40c09400b408580da64805d900d03085460728400ca81e1078241010140031070341c4188020032528104c8011114048500015119800141d820081940601e00c14540c201440700c00801c50640609000c1d00c0050351b90b00501242d15031118410440c1104c034601c01448801d03640d0001e4824112a003115000486445d0886607102501c10f49001030010781c40c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 954621402 1250 954620152 954620189
    0x110c0d390c081513081801020c0d03030b01090f18051003080a02010902040605040b01020d030e2e0c05030115030903051227190f0219060206040303060603050628 71
    0xd008045000c10030f02d40b000503a50544091142c00f6081001052503c0c00c0c00001402517580525140205050055545c50410300c400b00f441a402c007402500000d448880ca2041303540c000d0003410103482000078994240b803d0074440c080c032402c04503103454800d980b0000604800c000c00c15032005035a01101d2150748243c0150003c0c06840300343e406034403662600350700098a19140c802e0700081d22060f0050078050290020603401005000c400c10326074007400031010404201a80402d40040b0020320181d00c40c1c0a40c00f10b501100c0c542c09004c0207000d010401031103100780b42c40400d64414481e150200364140c86181c2103031036008030055508000300010074442e441c0c0e58402d100413204001d1407070000c08102100010381d144e04900440e030a4680c01001c1c480030465208071403488038000361110401401803410b00381312082d983d01140c01a003091060200300b55242c001c0200400d107900d82031000b420400c001885118104080b60200e02014900c07003880b841c2d0301440401401c00881c201d48030a00d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 954622652 1250 954621402 954621419
    0x18060609030f21040e06040c110106060305040b0a0509060f0403120c020f0c09010f030f111002030711010c080a050d060b0a031d150415020904110c0d390c 68
    0x10381d103c442c1030f543c0c2036115035a0400451096a088600c452003072590b0b07448440c14040242580c140d048200080039046e41c401d00024028200201182d5400140916049c02e010307060140103403242000c181040c080c0000d00c0703000a5034541000520300c0030740d0140c1701d078038007074070103612503030312071200c1401e10611480140d000710701d003200c5040304d070140e40c1c0e070b00f207100200325080109001d02141901000d0050001c02e1405001e4a4030f50720901c0e02c08042c01d03000340012801c46540840b400181e0000a5000801c19207000c907904aa0b02070130716894070002a070300c54000d4024407190f03204100010540c04020807043d04080c3c0100a11100140d54820064004001e03000400a510420301e1040c50041941e10008000b030019800e2185100740b5103e03955100c040704188040f002900ea000e2000a2036a9103901c00d040804104441c050b55509060900d6400c3c22004100c090030b004520b274130690560031341000c03000c000c80040b0403220001030750708549030b03003070001d074005043e100c00c582d004944400d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 954623902 1250 954622652 954622663
    0x61215071713031e0201060837020a0e04050a12110d1806030c090b0a0932040e070b0d0509060f070909050402061b060411030a0218060609030f 63
    0x164a00c10030242ea60310010a00000c12200020000341c646400031501140e0500303c0e5011000610010461b00c3e942d00e4040e150040000c124981107a500e42d201405020b4603208003600ba840c0c20241450020f5500000d5216040e882a0502000300c0000a000c000090210201d00d644c01941145c20000a401c0202000303154400002948103a095070720f1220301600d020400c03c1d20320800080e8442c186038044015001d000700c1c1e54140904500c000c94010f007040c010f000300041c4c0d961004c014600e0b2051b5180003c124a03107602041c59a404408900e005150355600d69840540c0c0c08184966000d01701480d041103a8003407240042e0101c1c0c081c1c80c881d02d941019000700901001c40e24991901102d0b0b82008906452407800700751005010000c0e10100d0b005030b030b40103000420f80b50a12450541070117803040006104c82e55504070204100400c01016824140c4280a8004001110380e40c1c0c04a2429003440d031030350501d141c02c032000507441d549010032a10b00c4c00c0081d0998540b0b44440304141c4c0c0d00c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 954625152 1250 954623902 954623927
    0x70503121e04090c0c1704080a150213080c041109061611060d05101a1c20091206280204090c02060901050112080d1a1207050a05120606121507 63
    0x942d1b07510540356000310144240c8040d03654800161110221035507c82c1160a905003100c0365285d02400019106001150048000d0100001400c4945190401c01c003c50301040044001e86c00c00780039500103a100d60080d140c094000429400b4135114500302000c0004107148820ba003c0070001e220b90031a40c0035001540a9985c5103803400d0303442e841c0e0f0110b03400d9050403410101c200c0414050858900f803150021032402c48100300c00600c0d0410410340103181d0f4003e2034402600c010011b190465030034210b120385031400d200300c0542401c2c01c02095104a02e10494210b040d803040c0040a0300c0c0d0300f0707608d90403a00140032031501006005030030f08002e500c41030102c032030314615464071000080101c1c80c0c4006049160740b0114081c50410080c540f40000d140020501910490602003504151104d200340628060b0729001003042070702c1d20040021269031500224080c1030b00115241c80794200042c036503004101118800c035190810008a0b1814506103a4014814014014810356981020310007006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 954626402 1250 954625152 954625163
    0x1a0306010905030129030307030c03050a0e0a1401170c030a0f060810060806010b0c0a08220b0d0f060f03020103110d020301030c030308070507030e09071206090509070503121e04090c0c 81
    0x35114101a105c3c051580040c021030342b9500d000c2c00083c03090f8001e10205d810b40c10040089400c078004580c5c4081240c00401142d9065051826150303080b13002c000e00300d03454000c002c0c0d05142c0607c0100f11400040c05002400c3d407165000a941c2015402c2140a0300140040310031141c203484820026141e42d22886842d40552000030030229900802c40b000070f04020028851008541d1752200c4940c0206002405010500301903004512146144001821410ba03071503169414822640c00312040a5010080e080c601802040704510303d020b5081140e0b02420000345445070920b80d12a43c1c400d1110031081c0910000011040000004489064a00a540d02d1049a035801d100b91403034400c245000e008034483c0404c0c81d0203803130300d80d02d8a41d00103d03e140840c054082000300c1001d8600942180300841e403900c04101400004101940003002e04800825044a4105004109125682e00040c0d01d4907412089081c030515042100d0040880c02070801800310300550042c40f130380d4a100c00321803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 954627652 1250 954626402 954626471
    0xb09010501032a180906021b0105011202010c02100e09090a050c04050c0306040c1e0e04050f0f040615150f09092315031c02100203011a03060109050301 67
    0x8a200c40c5084080c2d00400c8074629480e540c1007510102024007500341e80031000303440d1800140010f1090000d00002a1007a12035208c3c000c4100c42607083d200142c220304a80e200d20040d400260717a001002c080c0300764041d00e50a0055407040003c4070301200516400c1c0d0004800d400b4404101400116041d81c00c0c0110140c82d85400343c00c00308405c0d00c6040d118141250350500218545152960060000d0484c85c20400324100b2407601802e15800042c54544c00b14160307500c091203c2c1082e0180540c41194944901c0742450a42000c0e080610060005064903a0710200040300001000340034002d0300b00001c04030628108000010700004685410800203410000c000071140564050b10b0750321852003c002523a50706820820030090700089c021090480070b00d080d81c1c283c1d24144038185202d0031342e0240c00d043d80c020780c5001e031070300015282c05010140304000400c011850110402003207400c5000301d60b038907140e1400407180d0b0b5103150061507065180000410014403990200384a54040244118 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 954628902 1250 954627652 954627683
    0xb10060f09150e010c050601140a09020a050304080307020c030703060509010f05061e010311040806070f0c080d0b0f1806150c03040e04031707021f0504030c1203090b0901050103 78
    0x58078404a0300c6011030000b02c00c940b40d01080d025082c2c0e805902c1043c50250544401501c0341c0b40b6005082e4000754481032121410311903800e2034400140584040e0005500d007180816005280d44070040000d49501c00102c00316043c1c0d8400c0c4040c5900f00c0c001001c4a0702c2644a04201000b413000744c818403030541c0392902c0341c00f0018180c016903114550041c1041500c04002c000c005200c1d1800079954100340c3c0d2211000716042c0c0900c05800030f00f45800c020040362904100207080c4000000c3d0407403e02105040e080005881c0314211820460383d80400716040fa40302e80410704030300e900080d059101030005280d400b0a840b0307040d4079200d45c804450078841d00c43c0045041c901c03481008242801c2ea04100000d01c01d60011070a881c3c0c02a02c2464400341031140c0f80702c44a26050f003070b9a410700517045074070005151032041d100b407007400e07440520401c03580c14a0f68001c1c040c1c0240a83c0200350500312502014518001e0344400100d40e0021b414101514001e40010f00030002404212902052801040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 954630152 1250 954628902 954628907
    0x1e1104093b120d020909040507080106081609020a050f0a02060703200f250b01060315081506130903020609120a050d0203060d02041404020a231c0b10060f 68
    0x741800c108900182c107000700c1d44121500140d02c0340b040e0510b180d400300440145a00c52001310361060b40580042c1202d181400c90703803030940e40c46512081c803580c451020203d081040c942410b00311000c5d54401a52155041020761300382c003070210188105240403403d0f06583d500491158410b40c0d8070364040013240c0364a00c8000030001800c00b111607042080c0b0001e032030910b040000302001780301c105100303031025100ba0b1031060f16100c00a080b600b20864500421041d03415004081816603002d00ca08003a5040020899030303410303400c910140440100020602070b48400c1074000c800300d42000c060103138140170708000e03540392810340d03a94429208054501c1040550f407010345683d01d483c0c0d0381e174916002060903980d000e50005050319a03c40e10b0020f6100c010703a624440c040406119220070003903850036004009081e915680624081002407010081c0034200401e070582000003160f89000c1001528150441030700f8411001b42201c1024040c0402503103100e007501d00312005981c1c0c40c241c10586036403c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 954631402 1250 954630152 954630251
    0x318181514190305031611030606100c11040213230303071b0902030f07020c0406030507051309300306083a0f0e03011e110409 56
    0x30030304003800c46501d4941c5441c000c0900b03400d0964082e5406203454036511030301d0071a8000f582074072032400038184480030041d0001c50000380010403409800302e40380c00301c082000303550f05403914030410010741840410082c121180c2c3d0020030300030b070045485003100c0801c0080c2d20044e0081c0b0156003400aa402683d12030120314846111000d07002c0c40c00c005450ba2182c04000e40188150208003d12101142011484c8003030b40c818040500c500d8402c0c108060040c0c02c224010108501035820000140301007540064203000300c56013502d41002c600e1010b408000149540f0b800207090080c900d4600386032480d072101910340401c400001241d62844c21b24140c046400e6031061411a8001d16103110170060b0b01d003401d25034440c2024005928405d10900180d104803050141f402280c203102d105a03415600550804844000350020481d5640134240c411881c22150001d050480d1141c030500b1090f000342059030001c14400c0703400c0c054180d851008022812603100403507202c441d001e001c1d00010310442c0c80c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 954632652 1250 954631402 954631409
    0x1b180b07020a05060309031605060105091e0c0904090204061418040b06040f0b040e060108190c14010201110c060a050a020a0507060b0402040815010302030f03030f011203181815 78
    0x201401c1d89000306001c1305400090240700a030100740529081071880103c14440c40380b042c40074000940c100820403c0e20000601680c403541c40c007254a40184204201040e04400400355041d240c03c1c10500007409401e022100a4002d4280b150001e5480c81c088020707594804121520701c0030a21080c400710b810324046401070725281e0250040748190a09520005500c40002400701c1d500c50210003140075101298602d010691044004001c902000e00001041328602c46020729042641d4451201d0003140b1f000e500500142407907043c403240e000754800740c601ca01440189480b61240c0b2030480e240c080840d001c400e040d08107000200361402500c00c684025000703445081c00c016298542d400103140c80348030300d50015420030000c950400200300111003100111b6140380298110310600d4100b12043e00b59003950390007402481055011100709905460b2880f043c140000d14a041c11a0315200e50301403402841c0c0034190105540504035204806250300e0b038014040301c1e40301107003078220344854407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 954633902 1250 954632652 954632659
    0x109020f0a050703090b180306070201110702010806031006031208071701060503040f0204060801021e1905070c0b0a030b18160e0607050f030c0d081e04061b180b0702 73
    0x441c98425078054006004201e0092514031180781c1c88001145103940581704c0b0541c011a40b094100301c61408000305580160148000d00000b091070300030034100d000d810f00c000d0600074500c00185c8a40c0341048181a1120740ca1000e1054540d60700f0103c0f0b80d20804c0080100050718003000803a428000c155a03a03a0b00c0800c140300403175a103003401c102c1c0d103600007910032190500c8614000e00541d886006000182005200040c1d48090720550501c0c1c0255145040c890407200f40111139070070303812005000041c40d840c1001c0d941c4a00c82d150950540629801c2800c1e601c2001ca8008203a0364151312407c40300e1001d44030002d2180b01c00c00c88488000f401c66110380b02d007203104516055944a200b0040c08070790060282400c000a50780c40c1030402c0840c0f40c031800c0b0740c1e001013003800115a040100250f01a0036040100c150f003041c82140240c8185919444481000785001c141040405d50200e02d5030501030004420850003020000c00ca80310008007038402100102d80030030703803200f03400c104e078141507004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 954635152 1250 954633902 954633907
    0x91e0f05070e06062b0e0f070f05060307080c07080705071d190b01121b030b1c030c0c15090305160509041101020a080a050909010b0a0507060e0f160e0109020f 70
    0x50026160003502145e07281041c8248102c2d01c01007402d50103003108184142024102c501c0f090300415290861940c410402c045940030f04102684514046030b4020500713107003c1801e56922075034103075180704000700100041000034800c024050301050240581d94501841d800c203001c200f17090b040c031403010785210100402040d0f42c03203903011443d801820442010304000304410400e5103500e0488105104000c942d41c0b07400c03102400701d13515101c3c03644030000c100d40c1c6007401d410780e58010400b590307a640014213014103800f402e400e02c00c2000001340104070000d000f10808580b00e00003080301681e440225a0f40c400e42f40c0c1c552040c108100c100b400c0e540040c01111096031541c0f0754805150b40b5032442ca055020b05202c0e00e010070100c60080581e0740031a203509a6030b241c140c3c00e1103002ca40582c1305134a008800c2c00a0281c0b5a406003c4419480d04100c010500207090b000305420706000b06080b05452142012000c0c030b0001d8401c14004a50b41c008581c10180c0c0c0c0c0f440c03107405922a640340303d070116004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 954636402 1250 954635152 954635167
    0x30607080603250b04080f06011a0a26040609110109120305070c031406040c050907050d150e0711011505010206060108100510050706180312091e0f05070e0606 70
    0x20400300c102402c01c010f440740c150030780e01c032124840381c1c2c005e03000040700e9000154000601031080129a004061500b280b0540101c40343c00c003d02da00a904001e410005040750a100780c04812403010381c20140c89202030380b0742c2090314040000304081c41d0100e8240c015108007110b150701441100c000c4480581503900d014889580865513940700714400c992200101c440400494494500603400c80c11190007003406040c98200402401800d83c003140c41003607034a08100c0786580c00750075200000c07400034003c2013100c0c1a40300c1010b041c03d070b50030040000f601003040112055002d00042e4080104200800c00202540185003c040280c0103550141c0d04c1030011812551203503450a6110354160466020b00751108001b40c0f600001806060010b14045505400e00c001c40c4a1100c0805a5038048000c032003840ea8050159041c001800008503940d001a10a0229101240250422040d10303060401c00c58034201e48605074140080d0381a110f03035400401d03030f8205001524060310b0000c05941c00c0104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 954637652 1250 954636402 954636433
    0x11d030d1d0304030b010503101104050409020301091515081b090426031e1005120316142802240c0a140703080915070f0b0402030607080603 62
    0x54051a01142008440c1d103407058090038800b60000d103100e448044042d5142c50101458600d042c10248400c61810808105440c0381504450032118107940c003003a0304c01d0a000003030052481c501c0180c080c060500c0108a0b01d80329504c15418810b03601259a41c00ba00c03080060b6031544440104640b0541680d800100d61900311211907000303203d04d400d4424135010b020121007902038001c40d0040c224010003404501c011155110050b011280107206151030140c3c12400404007900c51756001c0c0020280022042405000b112029041e142d006041c048035442c294191401650030120b0034002d907041d4804410800d012000c4450071031505001450030341c2c003040071060f8403100030140300803101461101c041c42603001d001e890030402c0150182000c075003000250489030001502c9940c000c803505000140358001540c80300e0381c2c00d07101c4c0101d581013040c10104c2ca1003400e001408680c00e0720302d56010402d5400801e48940c0c4280c0c140c074115161548156488038082d40c81990540140c83d170b074802041d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 954638902 1250 954637652 954637661
    0x3121d0a0f0204200d0c1d301b030105040302120c10050103081215030a170c0f0a0606080d091403120a230f0f0f1306030c02011d030d 59
    0x3400100f000644241c40d01d5030800300600c106500881c5640418440c407180b2492003241104001414101c00c5240d19032a48412100c000b01500e10643c440004c020592003888558038024894a509001c3e1080990000ea921001c0c00c5071204180f120451039500c500f012300407070b401154550014010107018016404e4aa0044c0581d25400e00c516500d5038207521003401550300841c014421641d48180101220346003900c0202010545200154040c40c40d4030006032940c17019401ca140c020b040601d280c841a040c0c07103900300c0d0003028401d0740c030001c218034404034611040e90300c2048100b05e0f0320742c1c4902e80c07526003080d2070300034000ca001c800041210301d02184c0303118882c40004064034a451781d000120081900000c410704006804d005403030070400d00c10f559090030307100500f160604028050107145003900c103c1405000070380380428141c80c44d02918003600d0554145211a00140740c440340020000d00a18007a48010f40c2004029040700c1c10094400359010550800742d450190100c40324000781 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 954640152 1250 954638902 954638933
    0x80f0a0e0a0308090910031101050906041a12010911191b2f0d0201050a0c0f0515070e0a0303051c02070501020d0615050301031e0f03121d0a 62
    0x441180e8251140e40c49a0318140914070038010b5546810651052080354030004041d001c64402c0d48009102103150319011041060f02480c0c07180d5110142c42c0030403141e024139400291284c444154080c120f140c16005824006040c55042d040c6c0e07039813070b000e20058030308a849880b41080c0400903020080c0110203076060040031070500c2e0000b401504c01a1040c10791002050395200b200362203443c42c8546580d0070381da070b010700d02e018030400320001030000c0c60f03d0ba10301c003009040c08070000b880300000e4000d00d415078075990410341c01100203120b401d129496644c18060710f1814400c3d035002800d00c5008045aa24461003d844048141e05540d0195025401165420b00040d0340c040b40005206c05400107040d910306c11000542c8a01c03080000d00b00780c80c49030700300c0d5000700b03007501d00403a40a600c1010b99046a410800300c95005c01545039a40c042500e031750001d040300c200c01d030408040c103401040a07402903030309520070000b0b008400f100004881c00010303132440c0c0ba0001202107012950448045110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 954641402 1250 954640152 954640157
    0x70804021813031805061b1603110307060f080f0405100204090e06090303071b060f02160b100f03150e030c0f0c040209060d020c0a051b0a12080f0a 65
    0x4010701c40349106054281100c0542d48040000b0454080551011301d07684011150807100d02e080382418001042e9010759260b4180321070b0014000410a0010031031218404108d041104410351281440c0c414400a0210680244100040050b00380d01c110740c2d031001c41c645030380c400e2096140d911000d421010302034400d42e501e01c50119402540051840204014100c079440000c40c908042e80341030401600400d6803406030418810082000d401408801c5a42c500d03481941c95001c080ca42040240030f00d0380c0010450b407000c030f240a0500350908410703da05014042600240e51100e1280729240d5040c052048a182c181d07404000007403440c4803850001c03440c0710f000300e480c05007504107518642085031031031103940c041038607a84210814002c5003541a01500c040d813505580340c020405e0361007103c800504540d4000303821803603207800303100161600354044260360968001d51804040e40e00c2c00b5000e2442103100490008049801d045101b0701d50342e103c00740c0c5050410201b1107500e550082c2629005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 954642652 1250 954641402 954641419
    0x40f1b03050718050f0105031c120515030c030a171818040b01080601140d02010203130b13060c02090103061d1518031c0506010e03010f0903030e070e07080402 70
    0x41c03414020030014124007041081091680880042580c0015040c0403400d51004014845510003281d4000441d00420400c8200c00c1d4001c0200c0d2010600014160303e00d19140601640414a02d00203026583c2201110105012036080544071030545c00700414000304c03140c5100d010302c4a0406001140d900340c039a030750101032080101e010f036503c070030070303191145100010001000030400c0e40304d014001200c020046503040c0000d0a01030405084071600c40c1c541c1d1081142160710801c216102101c0c286c82c000700700c3e80e60b02e0041010b9000b040000c2004039141e030012038103e10500d0500b04103034008012103602c0c0d02e513480c1c000c010441001001862607030b0b540100c40c1c0060030404020b160034150030040300c515081c1c1c203508941a401075045500e400411101d0310109955140c1c41c0c0c0220141000242601c03202d005980c0000d1040401e038165003040d8008608264552042481c14040d07101440b0410ba50241d05440b440280582e916002181000c00c0300c00e0b104000705540503101410502 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 954643902 1250 954642652 954642659
    0x809030706060b0c060f07020c010513181e180f02311d100c05040f0627050d060b0409231005011a030606040b040b0a090806040f1b 58
    0x826510240c0040704001c41c0064213028000040101a03030044061020001508081400944491202c14203604021003c50300300384041060809078000c0c055a080c1c48048140c0407044005400605e0f40ca542c24028841c819045403000c0c01088500041151040e1641c46aa51010f04cd0409204283c0e0820440b605225880c6501c07040d10141d0000780c4101c0b2207000c5c9103a001410760b50400d01007041200381c072122129251000444030510315050101050300c04544204444034041c5d035000d51200581d2010003d89250000d05840e2001c0c81140c00326948030b54a041d1711070f040058401e6540051a1107540404900282d00200e64804020004540741c0026158005501c1411101002e03810312195085590700042054540e02520380c10306101ca50700d00509c0d03c20201c04050305002005001000640c1030791000d0440d400307481652601512079854074820300c102d4000d00c4507400030070102000483c101d07000003540341c400e550001000c00c101c2015500c9042d810215041c02881c0c0c820300b000031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 954645152 1250 954643902 954643913
    0x10061b0f060507081803071112010b060d0c110d2a080403120305070311090d0317100e010609080304030210050c0d0e010f171503120409051b12040308090307 69
    0x39801540c1c250341d9000c4070700b801800c5880e80810040d01790301c1d42e4020840940043c404943d61128a0000c1b03e000c620b42d0074032450640903000c2d050b031065000c01c00013008100c0f000070303620056408105995082d84200d0b842003880e070769a948401100414010b00f01081c070103280303c001e45034944d44100d40c80ca181ea010b58400240d9041900200d902c810485500042d45a042c800c0961103a128a030900000c04800e5100001b0b00c131b4049450301590501844605060156001e09004803004461a690b07281c00e1001c03181c20144e034050400f80104e10400018064816588201070324104805185040d207140c4c204040716005069035400d011041c0b000d00a03030342060040f1218001683c807031340c007a40b40c0007000400400740001080c0a2020605550504140340e6001e680d1008006600541240b94900002e10f41450304040300a010400100450340011130b4001034081d4203500108400344020080c001441c0c09982d11951402c4c481c0070005010920a40150b908841084162450b00000d516507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 954646402 1250 954645152 954645161
    0x290918060a0605180420010c02130b090c03010303050d2a090f2304020304030e1e09010f06050d0f150f0e1503030f09010905120604030810061b0f06 65
    0x4501450b40d654400700450b06103241c4815014402042c1c1602078605a90741d08401c407818107003020365111136070624540e030b4042c0142040042e0000c0c0400707000001c0c4802c10300030b04051001940900455400f142d0b034083c5640640341601d6240c0c550608020b405680d01c8010161075860304808094851040c003035980001c0188101c614695541c0c1f0040d0400e2060650b00c440ca44c40f055110b0520721550800c1c000780c41c90242c1c101b008031400350b03032a140c60808a41c0d041551060360340c0808010035481e008010340d12010003032030041d0b50303401040e0f983c7d42c40c10104408070710520000c20010041540343d0203c9508c11610301405040015881103040084515039000380c00402da9120018401e11480e000781d010070b42c2c0500d40303070000d405c4401802d000c242c070790060507156014800085010f0f041c0c0e030300810000d8040c200c083c0c21517194020108542d55a080c00b5907084c2d010441c060007240942341c5007078084041e41c51a45403401d00400404500501c2c44a46005072001040d12166100041d1316009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 954647652 1250 954646402 954646411
    0x150519030f0b06121506180415030c180608060f010314100c0905031b0604061b02090c0a0318050c060c010e120307020d11060a020714010c030f29091806 67
    0x4041c1c42850005e2840894001034510f542c802c020500c403100082c1d0700c102e103000c9030034002c1e0380c04549031054581044541c17900b41c0004090300080180410200110050189650407400f810b01c0160f64070321219071942020341c0c440010704d40d82801030000c100d448110b04003801036101240c612003610559902200d041d4124400004c100a10070061460200054070350f44114801c8480003542650014181c0e110b50300c03030141480700104141c0c0d50705100c441000b41840e0090514022480e0100b520222644440c0504c00821725010a40c2c200031640501d039081c05074000c0041203194900e804200703194200b5414601250748031006a22002003e0168004003806c64800d81c0d140d0808160117810140301800040c1001a02000c210989500180c116088812000c00680d600043d081280890300a00e4100000d9824103000c00b0510b84d0640c880d44002000072000c101480f03610040f48034000c070300400e014035101c4a060704452440c050307110316003110110701111942304440c4a001d0404201f01d9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 954648902 1250 954647652 954647677
    0xf030d030f0c02070f0e0622020d0501120b0c0c0a02120a03091e150309050d020c0405011409062812020406061e110f010207080301150519030f0b06 65
    0x100481d000030194003030300a10442c82d00282c4400303070602c5144090f0a00505c15000c20310f070503c001c80e0298407001e020380d804229203209003806848200d40d560113540030b60030082040b0310f042c0c00010444100085001c40c070768048400f008a88900c030410b11701e070b0405d52a41070640120303030503200180d1300d8083c441210212803000e45402421818064003e4200b0b9008625040c45501c08200c00c000c0c42c4100016a505044421038014196000324002d00e09040010064420003100208180d0001490b5900500446060145a0300c2e172a0049203040d0315005160020003500202e651850980d0209000f28204621b04044450308010503200c1502a806280c665000604410a50509000d2040a804a41088140701804180400e41c0001000d0f0103000c0000e6039040020100c4140000704003048a00d000350340b10706540c223048149500078400c100e0850031150034490b10300c3c00343e4151003070030f0010030301d100f45405a01c2c0c0030f40140410340340160100366034031a0540d45540d0074010742088020007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 954650152 1250 954648902 954648911
    0x8040f090509061807060311090a0303081008011a0d1403031305011a0f0609010309170a020c150901050c01060819060f06240203041809031e05090402090f030d03 71
    0x80802609242000d400e008000c0000560090313113440c00101e120032160b95141c0082d06612a0342540700350300504601a6004a84450000602d0345c01780026000300d08944050000702c0e50b424140d42200c0b14102c1840c00154810404a010301c0c001e00d10401250040800407410380010309598111740c011164000b103407002150300070520000b441003ca41c4041c00600104444005002800c401196411a03102d400009102d0300580d1080d0851605254490400c0b0303689641031000180e030741c01a040003401803140a804603103c0c0f03040d0300d5541c806200030140c0d41c600156000112071580c071652007040b00d5034a030800002c90000803c200483c520070418440804400c500c0d100065800103916815120305001c014021015035003100030304407081e004400d803007400c14402a411402035610050b00700d10142030b6101d0445a5070090307086980710b03070f65804c1e00324074461116001c21034040d030383c5000900070320910340181400c0c0d00500c40f04400404007441120b09000191504030a0034586e00044d448 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 954651402 1250 954650152 954650161
    0x409020403031403091e160602010e1515040e1c020604030909090b06040c1701080717030309030913020f0a0e1003090f080a0c0804031a0106210908040f0905 69
    0x42c500e050f036100344100602d0350522207080340e941c2624a484026003840b04519a02d400d2040005040f081ea003217072034032a640d60300c7d030000c1e00800400c00e60321140c0c06030244101541a001c3c205501c00d040700c1c4030070320241030713034500707020085c000e0030310314031541c03040800d0003030101c0c80501049e00340c1d034059000784280c0c82d10f407400908654290303004001550501040e480000c01d5000710952203141a02e0028030040c00784030840714014004031040e1180888400804c003100301049407020355420380d807105456042d030150940c1d40c5c8070031a0881c0c03040c0c000f0301141500303203400703411b43c150810419405418402c4601c89c02e036469200c42d9001010902025110206041081d00241c0e020801c0c10200700d82029074403150004202d4660007401c40d9800514081c0e02da0151314605000c94001d41103a4071203499107050814007040448001000b440000005685880391840c11808040c13001c4110300d450081280c0405403042da83c040b681400c3c18000400d074000d080f0141c50090002580100f59404c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 954652652 1250 954651402 954651407
    0x8030406180608130303061e080d0c02030d0e010c06111305090c0f0c03070804081501050901150503043305010509251101090b0702011d0d05090103020f040902040303 73
    0x1079403181c010700c154000008110443c0c001e00c825500c44500015201094202c1c94120010000b903080744100e104051034040c0358944602d000c4054a0400013120740712011800c080d50000d908020095041d4801d0703a80002d202d1194040a101000604022510081542e2034406455800c2000081480041504503800d845d80d032120004040982d000d402e01d04000038003000d2481041c4004903611400160510040d400f0802c8036507042d000507100b1b407160380301e00c103003a12800c980000d0180c04030710300000304003403419258140c1210300314404040d01c0c059001d0b00741d52a4000400035a501d400b10200361070385946480b4881410001e01c4000c000c0a03840381c3c101c10840e481030300510b000d80d0000081141d100032054044010610480c0c109100301d48254048400782d00c801111121942000c2c40308080140992803e801080349070021f00840d0317110b40b010001e00d030400c0400c4849500c0b140c1118491801040145406207040c9005072130304241507610a21a4443d40c4452102070b0300003800c01c10302d83d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 954653902 1250 954652652 954652667
    0x110306061e030a05270606150d0c0206100e01050108131a0c030627010635040c0504140a0209041104081c0f02030901050f0d051006030b0f06120606090a08030406 71
    0x10641000e205c9040c2d04030b424560392000105540d000300c1c100820302891456a205640e20206070480c180000308030b00e0002900c0340d005a5800c0d50500c810754001c980c036500c4ca20005c1c141d68040c0e50b100c520342c0e603103001c4800c01c00d013000301983c4e50b030b90100c84200c0c81d507040701c030151241c3c03030b0b154040f07a0b030b07081090601c885a01c911301061005a00202c030b2030305d50100080c0c154111121450110160015200300b900c5040c020140e1480c800401285050300e103a02c2a003061140e4040c5000c54039261b9100d052109403000924020400c000140026944009585c0640581c20024000203507040341c100b88603e07144d009170440300c01980050800700e80c40c900740d03c1c40c6003140c07010303e80054a503200400180d40d0b4001c810286050080200d50446c0760100381c020b64444110554040c051410a2a40d0a000381003034010301000a040c45200011400c00f4125040b0007800549204c0c0303090a950076000503101c0180045038480803c0180940e03542d18900d514010305603241c06150741c5c03460301d01c0141008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 954655152 1250 954653902 954653941
    0x1020c03070f03020d03091706040c120302060723070f050f0706081b1905090a05041a040e0f1608010e0c2b080f0c0709110306061e030a05 61
    0x30703400500c080c042c0c105030010800482e030741070380c000800401d80d14003070710207261581200e149504001074600c1800d10014900c0d028070b000d00f0443ca0000e80b584071096816942c580d000d000341c0d0040000c01d9545214000c06410442c410444000c0c40c50480032b030388640d0740711410a80724101403d91a03c04e0040a018105a020508000b00129880c10501503d1102d005003060700690740c07603950309120300c07100c0115203507501c160a061507a1400343c2006811600314a9070540590801d0b4404071702030a0620450700c40001c0e0001010703202484104100150450564641490041082e1100d202c003040021907003c0d90044201d82a05041c2400c940c00c56007c1400d21886502070340520a82c0d8465030b4080c4d040b188001c11500c05406a0007c04190610440009181c2080090b03606008000e0002501d8200c1d00401990a11560307088610140c0d1088514003034000c0d410400701d1090300c3d055000307221081a088a003410100d40209601d09500200c401302c1445403102c041140c14024401050881d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 954656402 1250 954655152 954655159
    0x30b011e0b04050d080d0e071203031a031b04020403021512091507080603210315010201090c0b09150414010305090f101508061e060d17070309030210080601020c 71
    0x50524040c00141045800300380580b51a0000a416188500c1038010402c0500d00f103003100c04092741c4004459025258080a4000a1038540c2071080d03041c03c101c0003180c031079000b00242448044100001d001c00641034000d80e000358200800401625800b0385c41414803550410540c0f01d00c81490368000f0140b00030180d680031340040000c0e42c248103440c02c0c0076410140f1403600d0380d090354a45011925020410a412400c000320313000c4041d0105107940194455080e01454240b4603145000590980720b688100901c0300c0c1201c0c0741800f0640b600e002608203610001c0003c8461640d07050700b011030350f010390000d8170103810030840c10b44156054011660010b0580e401056a10f080e003200b280c8580341c510140c40c0c150740340d91441191030101d070b501c84094000c11090b17540b1802c1c020201c905000032004449025404000000e40c2c81c9840740400054641040a80c2481e41036181d00e241203a11a40c0f044090150340b15011009d078031207106141961703246844040607424440c0000e071030103030302c100010311 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 954657652 1250 954656402 954656407
    0x41d010c02250306050612030309160f0501020712060213090b15030c070609080906130812040506041806090204090f050f0c04030b0a020d09051c020601031e0c030b011e0b 75
    0xb4807000c070300031580480350011000922900c0b00c000080d80c1900140c0c0003030441c0300200600944840100d002e42e41820402c0041c1419907031004000e08520b400e00c03a41d4050f0b008040204000c09a0420002c0e010307106d401c0c010703d815280d02401030b942c00260010945175680300071040c04e81c18070031683c4185008500400d401c618081504240a100b80f07c401020355072150402010000b980c0103035413048100038006912101200941c1c0c2648204d4440e407102c2d840380c0380603109050461341c05c4606a074005040549403030b0808440c2100c00110078a4000c240795030746000241280b0510140c0003410040e01d002c40c0420401480070240c800141c0300705c00014203003040c400c411003144215811a81e000914400175602c261804000b07014001000c5c1000e42000450420132602080503640321580751200c040d00050180c0482e40d0b0402408000e1800e4441680304c0c101003201d1020b6520503105200f03c1003116103964503003601c500284d000b000200711340340b4004455008810464090000c0041036030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 954658902 1250 954657652 954657703
    0x1c02100c05091309020103090c0b0d110a0e061b030708030f1014010e0103270c120804030b04050f011406040609090f0201051b060709060f1704020f041d010c02 70
    0x14000b0b0700031070f26250349640d109490811a4081d400c41050290021003604142d075480d92903000d10b60025800d10062840c04010324140041c80301540d541e08500e56403025a038081d1414080c2c0340d07206281c1d0000f403100f441001010a44200010b1410a1140c040c03191a410464440c40c8029805040c10022400d840000d101e009184100019128070034601031010201c03060040e0001c21007507001c1c0c01070fa841c107400c50011a03120b1845914072481200701d003100b1692158904c001c1d00c05c01c0402400e0f80810042000886c8003c403480d50424020010f8420b4040402c404608460b4000d18031641e0843c43c00c2008106d03e00b034420340700203100c0c0c850148803603182a9a0030680c045040402414000040b8440c1c01d0707071070600b1802c15003292400403684a400d102c0e90192407036081d403140400041c80000001000c03440355035503903408400080044400d480d96800c11010234400307844607070402c3d940c0036454101c0001c2403914004062030320000a148134540303002420305064141c0b5035074010350030b400d56 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 954660152 1250 954658902 954658909
    0xc020a060c0b060103051b0415090503060103080f0a030e010f14011205031e09180901050a060e07030522030c12180e040203010b040509031c0b060a0c051c02100c0509 73
    0x50f58440424a00007130341c0d6a9807001d6445207032a0000078210030350045808a00e040c100c9542c07202d144002c0c4c44007141135a0b60030425651f000240070003000303c102441801d0b56412070034083e00ca08030b01800c0209002c03c04000c0a402c4481c0c40340004002511007a00011749010b41e81c11601401100c6214501030410381c64169403446101000b85a45044411011b03203200a0402c0c0d4520741c0001340903d28040c0340d0b150303d40380300e41c05564060140d4030300303400b050346a03541d44a08070807105140c40040c480c2c1d41d1007d0940041c003005110803100c084200611440203480160102140d200c0d032103109130344200d41050340d000d0009181d03180500c5000d61400c0881c070345088034003040380c0c0301c1222451596511b201203805884202d003110340003401d200a03c0b40640d0048040e00100b8481e40c07242c000c0500148900b0203580c50351901c01c1c3c118008022090f402440350780300070312442c010002c49103174070107400d40307900c503141510000380042e08085541c112001807030155002d42011460494203120030324000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 954661402 1250 954660152 954660173
    0x60906151611120d020c0f010c030f090e280c05030612070b030114030d090e070318020607081207030b09061c0b0901020a090f08060606031f060c020a060c 68
    0x8940308122465500740811084488090702c0e1040508001440b81c041035615507101d0070041982d0140c065400b958070507040490440360300c408144e44152800e0000d8400b5550540f82a041d03600b0010396403008140c41c1032212a036030181c0c0d011000010f0004805000480148103511010314923414007008185480d0300405690f00401c040350345259828646808910340f11450b808840840004800001c1c401e61045030f40801c54425021f5483e8041c002004552003c55405602e0340010481d02141d035580c401c1c0d001205044000d80f2486c200202c0c0e40005009070406081111400800100b004140e0014003070560094030304c2c203050018070310301700000301c0300c0400070421401100720041e011200002d0640442082c0e40018481d4040d04007008418041c0d8024595000071030714401000512541c08004174080b00c030341d100900442e48611040020341c0c0d20190002401803400e0305440c18503140e00c4907281c0100319944404a010226105110500310194848020300c02d00340500d07000305000100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 954662652 1250 954661402 954661417
    0x80a03061a0f13031406011401050703021e0304050d0609062004140f091602060c0703080a0c05120703060311040203042004020421232802040f0506090615 68
    0x41140c80d043c1049110300e500806030700c041c00b01c000e50004084201004148241a2009030040045100011005640ca48101400140103911810001d2200201080d01042c19400001964035069484000a90b280d0b01810151030312170742c500d8041c0400c1400e01ca04426419070088074a080c9418100999941c0914464070084400742c08222826035150170601c40f10b620000d01845250408441c120225401c8086100151166a011800212441060f11040d0740e041e03660902c035a51322803200e406000d154103654140803061101803a140705240c0101d00c243c3c1c03181d50000310b2a20f0b600303016682860503214580035910410a00010648104038403c90000c1d10801901d01034103e000b1400074400c0f50f005000d40c0340300e58280500501d6055101160314010961020310030320002c680618510380d01c40c0c40f64550b01024000c141038a80d00d1107805202e88012070a031a0060540108041d2400740e00682c42640d51241000558600841c509400c04c82c1900d850500c1081da01050495114021 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 954663902 1250 954662652 954662677
    0x2030f0706021308010509010c02010e2508010603031119031b020f1f030e0708060103020d0c0918140f0d110703081204050d0c0c030210031404080a03061a 68
    0x2040310a20810340c04698500450102c00550540d039110304a000b0001981c0c146c019500f052a07e41c0020303c14040c4010101c0d0303080c09408034141880d040c0845900c02500050414074421000540d00c10a10462004601949a01405440c00c68280c0d05043c84943e122207014991011600030942c040701c2090007184024510211203103a00000c0d10808c881754070740358403038644208080b081c3c074104c0c1004200452610700b40045000e4003201500c90380c00c0e001d4175440d0303803001c00104058600310f18140ea0250042048251a40d291042403050780c2035a42034010010300c1250641c1040790381029030780038482040240400c1141c6202e000d4403040f800c2c2010040180c003440e1490224014401c1030000c66008283d50f07a2089484e04400080d0804c58040d2542c0c0144c0149000703050054a140090540c4441c24444484c150340c00c0244524480c01c4a40405540b00100103480c619440c40304d01030740c012602039807540031041300101034681c560406440d80059030460f440594401054501c10b07003191 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 954665152 1250 954663902 954663907
    0x503040b0a0e0f39090a02090d1b030309230906130203130311190b041416030b1f05060c01021314040c03061220060715060501090602030f 61
    0xb1096450101040301224141c021400c829100007846807000540900302d03141040c03500d15080c1c0b41d04100c0441143caa0300540f103400000c6001d50301da03004011102009000b442c41510360703180c2c061a102c1c0c800d581010f0103420303402881455003004041000704405107101404440e0f00c2a0b0480303103000071a940780594032180204850343e617848010030300c101c030081c4110740742d103400130366800101e4910f0030580100d50000203e5610750804075032b62243e400c034031010320829002e80d612502e141c40000c2050b41e1140f064102c402a0080038881c000840070002d03041c03c2640d01314144864415000340c03180007600c2d205183c008044c50380b52461011200112003c070b484d01012107425003e8030031003414110903603c3c9407001c0741940b00542020b1002d0001c0d201005220301380301040e070803074800f80a480f6052106076000c4000a82030b240811000c3d90100c2c840751150304240124005400c9000215680c21850020410101440c801d20008000c00d103411a1410b162203006510b9204895008a022100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 954666402 1250 954665152 954665171
    0xe06090310090302070506070323040506121513050702011b0c021201020c01060f080c0411091909020408010e0f06060901050108040302031c0b03060a090804051903050109050d020d0503040b0a 84
    0x24001c01004206c0a0402a900d00c00ca00e40100584070981948490304244004507202c403c600040d20203880020b0402d6103803c4407074003254020301004114400c0360b000200d4004841e00c49110120384000c201c14085118140306074003038203480f086140c2008001d0007411044c9400ea001d40f08100454054034181c2e1200404542c003400385c89009813405c0e2131340c00c20900007401e4050107020011258028183d4902603000c03000c0200f0345102c0c030465011082c050200d8805072a00381c450300294000c0c21411010280e07110104010b0782c01c19801720043c0d9565401d10240688103100d440701c5049200003400280c6003001c0003900c1c408060003420304000d490701c005070404d4000c000325000d00542c4022141007141c1a95030784050314024003a18082c2c011800821110109400b80020f20340d4040c01440c101070511040c000e840304421104c494140300740030000003142080c420340148a021703801a01c92145a16006880c01c0c0e0044020300401a0400c1044003041000045075040300c2807100c0880d00100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 954667652 1250 954666402 954666407
    0x6040501052808160801290d0606050d0e06040b0a0203041406090303010302100518010318150603231b041b020706080703020703050910022109010e060903100903 71
    0x718840c203031030107542204440e080c160003e80c001d10070030040410340480082040101c41c240744c284507256240c603024111240000d0704600b09082c1269146007203090420084404007640c14503031008000c00c3d00001e2010302a1105c1c0034510a950700c002c01842c00341000d90ba9070f521305e10700a06071410260b001c8045010826200603440c4680030381d204441ca1810802d00640c1c807a030081c4000c9104020f030900403d10f0b60f009100b6030f05000c1c1440100c40705004070f04015400742424810750340c084510070754084005001d4201c05a44118403070b40002d4914294500060104860a100041001070400300b47c0d13000d000280304000c007151852150f1900c040903001c01d0181c4800ca82030303046181001100341000b0b07170000b0b100c2c084460351360310038030252500c0c902030301248501d0601400103041085080e410b420024040580030100344100c40d0320342d03c2081254210120f580702c0c0120980b00090341002984e000300d0484041b07504840031417620b0300007000a640c407140300c4112800e041d00c40403d40b05250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 954668902 1250 954667652 954667687
    0xc0906090904321614090711010f0603060e030c060106050705190503030a060501031802190e0c0a0f08130f030c0b0a090204140106020303040b0c130e0105030105150604050105 77
    0xb01283c0c1000c0d141000181c686030103150f2a030062000b845200140c82c905034200314030100300e82146011107050341c04c44051000b81000246081c2c1441404003a4060303000003440b9642c0c80e00c4840300001409802e5207009800c0d11551744000c030300b55005001c1182002c0010a001c1c1c115000d6017815035481c0d10034a4068288900c0c0600900288881d010316810f1201c00303c020f52044150403400c0001c6904c8500640803203001100244080811248841c01030601c10012840481c18803219681280d40381b001c0d00d910b02c0e04441c00301c3e260398003040b40a80b481d002014820b2502d01800d201110b454400b8001000b0700c025000074080c1c40d1912170304000c0c10300407121038403c960000c0d00c618a03840c05409803000344c81480710490007645001c0c6141c00c00f0652540042c180c3d48950302070740c60340e1210346800d0524000548600d01040f010880c04080b5507e104170140240300e9602d5040c0f07190324150405086070340c0108000078410032030b40303140c0440d5103840c00c9805955003420520385440c00c1000904400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 954670152 1250 954668902 954668933
    0x60b03180a05011802090f0411060a09090c0e030f030a0206070507030e09150a0806040b07050903120706051b07020a060f020c13151e0e06010e030a0b060102060c0906090904 76
    0x25403038407003401340c8002944c40048a0500980d1405c03003984034917443d03401c904011580a0401880c0c05c5505195141040003010054000c2c43e0206189032100540c2040381c128a4484000c11050b03440340104e0300b004e120501604203201b01541c10100390310b2002e0740394100101201704111001940b0710415014030130030544c5490250030803c0c1c0c0e1401c5202c0751441c40c5075000492144d01d0130f0000140d035550010301c2901c20341e8030402124858860309026a1aa04402c080c540d260203410854000351800c070002c1d080582c000c68000c03455003003006c1c5401003142d0280c4201d541040412960002d070316515012000c48a4610702024240464901281082d210201090380310700601d00c42c014055031900500c41014805120104907651070041c0ba500030140f0a0603289800d55002c10080c6041c200f0f81580d0190040c10025060075140c0c00007802c2010029045914000f80801e00c199541d042198070b90000d0080300c16450510345500082a030302030880c040f81b260201000003000c11000c1a602400c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 954671402 1250 954670152 954670163
    0xc14060f030f09070f0f050f040b060c0c01090906061e030f110403020310061818081207081b070b10050d0c1404060e0402010507050a020916090504060b03180a 70
    0x12810302e0701e98020354040c00d4034403020900c9620004074115008020303100844015040059107a0304d0714040c8241c840a000003684d000303075685411107598442c40010481c550350174001d444070f070107080f001500050064100480640c40c00100340200794004140007045801c001c6500c0101d018080110301400b045076502040703a05008101e590394481380b000c3c00c00d680c42103082d2801444c440c1450300803034406102c0d4008405c4856071921200d881e940c000c0d0001d9200b560201201d4866072500480c40e84041504a001d04031141000102a400441d158010513817a0b0070090f0141612810b01841c0201a405401c5018400200b01460b40d501ca90000501c2c01801c1e8070310401c09800e000060600620a11710385100004440c3d0352490144076a00559604007404a01902e4580044030030b80c00600c4121041c0c030501d04048056544c10005034429010342c030116891009501c401010100d075a0b11403030060382805e02c1840024094004d0329400405040300708584c0d952224994030300405510003810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 954672652 1250 954671402 954671407
    0xd180210200f070609080610032303040b03091509030a1b0b0f09060906010521010b040905030c070503030c0a12120e06060f0f030a030f03060305150609130c14060f 72
    0x1c00705404600c21044606a465080317101e59100021900c0310812200e5894a8006500900c001044164038135807002069171039080741d641000007540341d1350050b0010440090044200b003034980e0100301d110481c1c880c910003c1100d00b020a0559601c0c0903d51300d410610110340e00304450000d40440c1c8040f0103410a080028038141102003a02503071081d2445002c6024420019015540000e40c03503040340d801034000000b00f580c48400b1074042032401004107171552550101c100e41c2d5264061f01120074041e40c0916521212034408503d41100c03540154000e400602203162543ca011600f0288690032a000741c000c0c50503280b0844580d05550300d01d480b010704d00301501403101000075417544169001d440e8042c00546c030308100150b00e00c60030300b5503505901507503828000a110701c001c40400c0046050101c0d03500d03242e41d41c0d2800c0030b440d0408513003050364260401c0620319180b040c050708015a9a18104228020303141c0c0440c00407140108101c10200700c40d001500d803260400c5034031041c8003208054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 954673902 1250 954672652 954672673
    0x1e04150e0403030c0f0206070305040303020c030d0608011a0d02040209010207030b1f171c1803050a020906060310170a0204050403030b03070e0c0406120f0903050d18021020 76
    0x103030380000a9a00342d001a141c401d80c0320074180a10000c0c0c1d00300445400500b00c9035581c4200302e01811000740b0860401d40c09110f41102300c0020406880261110900405c07100d040051581c00c5400c44074a20550603011004501c881d111003410090a03501903401680e103080700710060345003880552000380550003040403c4a01040c44c1c0c00002c00c9007404043c9240c0c03603030301c0b8a01100c50480800385c41c055041a40410f20011100080340301100c1a41007492015611005172800a070031f550040d40e664100d02c1c403400440c40e005020550100040b200203045080c88140041d81511900400100800c20000600204000c00032035403440e074024028030040c50545070003800380540a640d40e000e0f106150380411880072804100c0d10521525a402e424280b8049041380c45000d0101180584c0790707200c0007182240594040c0d0700140740030b038580c141e503504001240d4044038802c8100c8040c00d5601c820880059862514a178101c80652034140c8500f0008000078642c280f180d2140392042c49000311a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 954675152 1250 954673902 954673919
    0x71d10030b0a030803010e011508310b0709080105010906120b071209140606010e1c0c05031507120e2e151406071703090a0b1003061a1e0415 62
    0x86040e40c642410a400c2e2044d400c2082d00c1c4018141d0361034a40100c2c6040368500700c500c104500c240004804bd2102250b07040f621011000c0205072041d00c00120074050500005109000d62401846401010840d491900c144420080d0700240005c00c0003100c0c002090071188140c6040a0385040320a0401044c446403421001e03a0909a103546001c0c000ca00010313200c0d41c060542c0510f0030401030540100c0b04407140e491090480170040c01c90f001441c6240100342a00d04100c2c040b40009440316034002410070b018050040500240f00b07a00590401c49103207051080400c1c4005103812201c202c403000038034000030100c00c200300504906040c0c90080008440d803c40b1845404030790600c0614420024048240900c030300c200400500160b07800412015024680d4000316413140008069071303e503164954441c13003000341c26241502e803800a1141402030006501c0f4000e07408490858004542211101142d1401c40d20300e0640710740080d90f509425030ba141d540042688081c01c042e25980c454035030641c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 954676258 1106 954675152 954675179
    0x40b03160912150216050f0309040b0d030f0302091c05010609060603140417070b18160315150f1d090a03020601090509010204030b0708071d10030b0a03080301 70
    0x109408a51b090018010b0450948091030340c600300c40007008140c03084040071900c280518002000001c0c0c111417210303007180241c04c02603102c16800c800108041c00c2a64840145156000700508001d4198440402d5840100c3d0030400305456000c11021100e4100720b141c201e000c0d00d408600880c0e0540b584140c83c1503040100d80c40c040880d96850740800702513540340802d496000440078840800c2c04684d03001300c071148440c0991861600c07091030002c0b103001d80c003019940e14102c40e0656404003070305001800d0302a00740300e0026130f5940307080500040d42d40c41c10004a02c40012499400010407040b91264250f0f00a0031140d007070034908801800090f041040c1e40d0750802c00040012109240c40e4032a09041d00e0f0b28080f8544282c2c0500302101090302150305002002200650781d40e05030380034a40201926002480c500d580002c120340b15232a400203444110041300008215404508 = true := by decide +kernel

theorem cover : BRFrame.Cov 954496402 954676258 := by
  have h0 := BRFrame.cov_init 954496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 954496402 ≤ n) (h2 : n < 954676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
