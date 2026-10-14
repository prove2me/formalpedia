-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3209
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:11.237188+00:00
-- url     : https://prove2.me/submissions/2cf78429-7f7a-4a4a-a6e7-7a77300ff240

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 576978417 ≤ n < 577158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 576979667 1250 576978417 576978427
    0x3040801050f06120d14090a0b0a0309030e04091a070e090a1b030519050919080d0b0307032a0b0f070201110c0f12070b0c1006060302040b1b0f03 64
    0x10380044104403083e0b449007040c0400e40350403a1001400c1030403004c1544801540070301310750605050390080030059a10401a50011520040c03250240c04110003a480200c1e40e04000e24004d0054008075181d603015904e01404107000c20003104038135030000c446102c8000d054541c820200c0d41e05900503502074026500f84140b00c4400380680c4a014407c903d82c421510602094404400350361096415800c68503500c1c0d04401d1001d5107a10090700a50f804007103031808210505140c1d00e903c041c907416110b40002040c2801c03070300e09a01074121210011070103003130a58103583c0c9008000c8201000001c98520114a0200c00d080509500340580803004420340c80f00e40e400c04c00a00340e844048100d0000e101c0d2a030a01d01003400142502d8450f00c010440240084480240b12103400d800310702400b00c5c07046030000a0303412142c2d0018800b105c1d0440180208211840300b2005072030060344500200340c410041001468040c5060b0784840320704198902c07a00d00340454152400c44403580c101601d02000038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 576980917 1250 576979667 576979681
    0x3081e070c0e0108120304081614030403020901080a050a170d0617010b01031a0d02190303030606020609070806012105070b031008120417070314100f02031510020304080105 76
    0x1201c00700300c41c0605414852683ca80003000d40b182d10400041204480902c0450000350f40302015040103141c5068120002c1036581780c01c45002100a8031001e40d810008083c003d608180403440e01418010005044d40c0009640302036686480300006002407001501c4030300480004001c40d800c802080c1000c1c4045600d038800001d0302c2ca00c5010580042d0303c1c080d00c500107540a0b00802c84030800702d031240c100140002c01407219920b45000201d0740f00003c100b5070400c03880343c14841d10240d8081d030fa00103200c40c200200a45069005006442c684e40207a204100940e4005881030554450180c041903014038403a407441c102c1c200d100020800c2c0121107002ca42a82442c003c0d510406001842d405515038403182d06880c3e190108000041c81c8080100340407803000820004603003c04401241c0c4103699a07140c00760055a001045941070300005c6024034107140038020f0b07812114a1480441c03840c101001c0040d800f0062002c440c0c01181411001200180207005403401090304400900043c83e0001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 576982167 1250 576980917 576980933
    0x6080609030d230906150907090501030b04141807050306040b0403180b03041103011a0303040b13080f010e0d050a0c142d010f05071403040c0b040303032306010903081e07 75
    0x40360b1604511001500d06d415291a03034595001d8000c9481703050001d0300b0200110084e01c8504141038100da26a031500b04030a801c4503100c0c1c800e192143d0702c500194802c80c81d0b02c0c2802ca86501003446984204140004103600c04030f60ba4006615080400c3c00c078180414a4400f114560300070120440c2c003204001c03e001c40c490302e0001101e0101d000700142e43e14941c00010554004004503050361060009003d0451010020326001e4000d11f0b01c0303030025694400b03541c5812410028a00641d4440d54202051003041050100b020120b00345076003040141c080080c500c074147c0d4005032040440c0040c2525032601400036056420032080d40c00f1640c1d038134030000c0c4006005070107241115840c0201c801c45440c40d510074603000d0541c980c0c03240310034000c80e2481100d0b41c20241055451050584000490a802000500003588652000b0030f00e0740c070810010210078142c001d9501e07502401d404100960780d210b402001600c4c0d1102c0c0f082e8032040d5120414150340d50078400402024030005903002880002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 576983417 1250 576982167 576982171
    0x60902030105010e010605250c0b0a260420030601060f09050a080c090705121006030b0a0602120a0302040e0705040e090f0c100e0405011806080609030d230906 70
    0xc0e4001d211590303032001c1c07854810009200c0c0c40005503040c481e0204207461661120082d42c200d890000c01e95001c1c0d00c1da10030302840b81c0d0003140450300003d102c9003025048840c007244c20b46410a9070140c003c032204466452040103200a0200300850010040310761020620100c8501c0503088803480d686558001d01040741502100b800704401c0600000c50386000424032050744c0000f4007900f241444501406015540030300203c0030301c802404040404020b8041340c0b40718041c80c841c550015807900c00040c00722400008814060940788100b030043e40e030002880d1001c030350080000b40d910302a00c00110000e0003542c124546000380e86080c04007550f8400302030801e1300c9460500003280d03140c460481d41c0d02c1041c9400142150000456058203182441d80282d00300c9850030418800c140c81000501183d101360808510004111205140c094440c81864050440c10b8000c01d07450070a95483c95880c06010b0078080c0e41c980362000604854032040e0b80780c46144001101c0701140c20a8084148c98640c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 576984667 1250 576983417 576983419
    0xf050a08091510090b09091b060c030a03020901110d0c080a0504180c030e030415050306630a0b090906070f0c0210030f1506020a14120301290304060902 67
    0x700360700c1c169145071950105e0701030540d800090038491040c40742c4812300c6480d01d94856001c1c400344525411064180010048445203650059950034218000b400b002c10003280c0b92025442142c04504680d0014031220000390007a0029407210614401100c15200b582c224001058918000d03180a404540043c852103000381c8040c0a0690981c59550756401240302c3c501146c14a000e0429005004200564000070050920300401701e6901074511701040d68810b502220446110820300d03507004040000b038224082c821a205801580382003000a0150321071243c403002d02c080400c2d51188580d0000c0c070001000303064580c845ca4001d04131901d580d0304403812000300e40725078004000c0758400d0b01c003481219401445000360611011080340100042c2e5005c0481c02d03035810070840c1c1e030384030030100400510307069009203001d0140e89401801d105030a501d036079880d03000d00c0c4107010781038843c0c0989041d1844810390481108240d600700c0100c0b0301800000030502e07000010701080c02010b810117103103680 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 576985917 1250 576984667 576984671
    0x6060717040b210606030f0103030c060b042c0303010b0921060907030c0b04030206070b060a1a220806011503110711030609150604020c070b12090d0f050a0809151009 73
    0x5118018001144000c1f41c1c7d4aa14604a4005100003801401c9402115018110000c0c001c1c01e5540860702310b404124030302d0b41e09407031038850b110031003940e5044800440f00a0061803c5515140100020b4055511650710136640c010341003454034003108016108004203130880340da90406030714081d00c4038030f40e020980b51113a40c401e002c112182c0d490111821603034042c10261802590382c0b107001d490342d0041d0069900450782d500015814490650700b030050070000344404da50700001c685c4991140c0c8412404e04802d4203401d01003041c0d040100d51541124000c1d01c041340d000400c20404c0700108041a180700b2036400100b00c46052002045800c3e0741180c054084400640300d00394481d85d2241c0c0c0741a0555a8000348000030080c1c1841e8025008024891003201c0540b600c6181c0401c4680280302c0240d102040380e010803050300810441c03480010b10a043c00c0c0c0050341d05070380041991060440d08001e02c1004030209088980400883c004240420010845130074844c0f60003c0c0501c0502c14641114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 576987167 1250 576985917 576985921
    0x11040524030c2a07090906180507090b0405090a03080417030702010c090603050402030d110a0b0406020d150f0308180907030f0b040b010509040c0504030206030f0a050f06060717040b21 81
    0x81c000c0f40303881c800c0440c0d00007044241e26040d00c003406080010001c8803910740b902c140350203801c0894010034207a8400c2c0c014181d02820302004400b00c46441035541c0c0f00354104401e02c040014080b80c0c1c0e410403a014034081d80b4555441c2800084950060359007155000004200049143e065001d8400c2011a6413012655035642c10228180e48040d18080e505401c0b031100300404900075800d2081e00c330242025a50382400302e0f02c400400740310454054820b190001406101100c89214500e03100c03880450034400c1c0344c1802c03081001c4d184c2c01c0c000209020b0000903200b606a0801c010300654084c0141110240d1a0080005000e0041c0c8100001c0381e81c185401c0e00d0051a0501a0401006040e99981d080240a01c1040003400d1078000030810b004040002101588555009510545800f4400c602500b0010030a508641c0c0003091030200e80b01c1c82c01440b4042d60707107030211510140c02184c0040b440e4030501d00c05d0100d1065922164a62000007505001c204900e9a81c014100301d0030340b035003510307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 576988417 1250 576987167 576987217
    0xe03090d06140708091f110c03070c0b0309070e040203102301080718020d020706110705060a02190e0102070806071715030a020d08130b07021311040524030c 69
    0x1d015525580190000484a070200e40440d61b001c25101200e000032070100c02c1408401880d07400140400000e40000505100340143c18061400406036480c2c000e01d503103404544283c0f40c0b1303514040c4004441d01d01000c1001e658080202c0c7c001c1c089003038020031100303040800d440d04c880290740c2450400141c2c034000090504000c100c1400310b54510181606402d11020107400a6118866000b25a43d082c4903031404501c09201d011003504000e00070503640c0c042e03070911a01e440340c01009845101e00400800648000e091140002c0710303214242007411500d01c000503030070102e285c0c02048503071150348100710002d84c3c0004603d40c00d250604c2c0c182825140c1d02e0a40070480f03156581d41da0113500c035008a00060412081d030040c0203000f01c0e9200e04000d51941180180c0394140d119100504000c2402c0c4290f1402c2d00801c000c6400341c81041086c0c7d0620701c5110080d004610909109400341008a0030100380b241c6018030f6680201c01450b603d250208102d40e9a403c03c444890035281c12640c40041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 576989667 1250 576988417 576988427
    0x6020c0f061c0b18070f08150f181f2306070f05150a06080604050a0f031b051e010504020d0204020c0f032805030106081609030206070b01030b0a0209060405040e03090d061407 77
    0x140f00115100b23002c0401791044c0030203407511550080e004014035000000720b1080c3c440840c0909166015080c10b11164164800e048040da00b045103605030758207841100840d42030314101c406500b6180c3d5074680e5641e00300340d07840842030100a4954001d0420b20700070700c00c00c02a110b02c41c4a08100c200f04c240d480d049201d40ea25002c4070002c015600001406001c508203c80040816110b8500545010f110090322207089416000c111190b030700001c9022440304902e49010031010b5140000c10162900c0d800044180349240300c0030340501c0d40000d81d20400c45040c40700c0c1060054601c02c8035510748007061403844050b0f2140c682c03020300d904100300d02e01552050045034102e41070740d07440d0f44032034035021090800c020445a2002c1800754840300000142c83d64009404007a0041101e0303100f40d851030800e455a0340004002c03c460b14410041c0800e60380d21b07141906d00751070341580c00007405624214031600d90700c20610500e40c040d15203200b1008103c0560001c1c0d14020400c5400750564035490710a542e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 576990917 1250 576989667 576989671
    0x201090b040b030c0c1608030c151911090a06270b031f17030d0e01060609180b0a0e1605090105070605130204050c0406020c0f061c0b18070f08 63
    0x2800c42c00400200748a1034a42003d0408122141c00783c0713035041986840c964882c3c43c250300c41f208039040400c40d0310b400c0c84113210005a0303804080b8003800c1031500340e00244014a030503082800080d5240300b0100251420340590ba11100081c0810710003e4841c40b015000d8402c0c8891003c480301a40c0204082c038030003a0314a0101c5400003005d6042d80c445034141d01c003035442e031007165803440ca14500c0043c2c2190f06c80080301001c41c094020310783d04e4800d0a4920140d454640544031540c1c1002d200300507855103d0b0740b041c1160200003503614500c126a1105016018181e240b6034031140442010030340303000d00500c0034024401c2a102d101c0c40207110a090300d803070003005051030108205000c50030103e426034110740e030f100c49240c0001c1ca0326241a8001001c46d40c082d034080c000b842c40820305000141d01080002c0d81c414045900c1c2d00a1050000003c1d0f440c443d070511041381c2c41d5404082c610000740390b00300105d8000000d25407003d900400c840e242900c90111540400100080502c030741040c00362260358 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 576992167 1250 576990917 576990929
    0x1104270903080103030c150f0507030c02070503031603031d010e19030c0609030e09180f0736060b0a08011706073501031406010803030a050c07020d030c0201090b04 72
    0x6640340c0c0c0385032021b89034012400320981d0314940f8041d122403501c0c85c6100d8000d98151100001075103051242e0000d0482c2c0c80c19010381d0955005410512980e9000002c0d00e0b00302c0c805000000f0348505030319003200034109481c801210406400001a400841900708003980b107008411117607a80e0707500e40c91401164440340060b001c194000b4824001c41c00d1600030a10050090402200380c488a101141c8896811108c98101c80b1700744a160740c2c1510b080c0520401023101c1c0c401800e01c2800c0c90b11804000924203107003110007011240b20900c40300690072410a500d07001e02c00b0003c55950700c048440356840010f030a8005882140042141d0300c0c80322103418030301d88041c0180200c0c0e4580e5410b407440204000070404101151081e00702103001e03452200201c01d070300d41c2440341551661900c140c6091681b143d0700a960003400043c07120503000001e03681e1040308a100400c2da61985483c56050303106400b80a07400201d19a0b000382495081000740c1c81d8240300703a036407840f99640d4a800c6582c83c0180d000351 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 576993417 1250 576992167 576992177
    0xe060a05122b050409020703030e03070b24010210020309120d0203160f36090603060f110a0305070c06090318090216060f0204091d0d03022b1104270903 67
    0x500c14540c01b580a00904c2d4402e040000780314036003540403891500200411604050345070704011914180c0e07400d43c06070700884001040c0ca0110000040d444d0403142e04141d8126601100081001d80f0401c10000c04140000025903154000080400694022281c0031401021002150105032180c6900e1712036034440d40d0b548420140c1a1540306059103081c00c0e40d03110030001100320032400074007140b000080603940300c00030301e02c0d1444ca09041070718465040c0103a810714000e12007501a0803070701250000e481c10314001038113982d0500c0542d0b003110448005400ca52410111404040d0000c0c500400e0350050741c4541d07142035544d002c80301030f441480b840a141602c000c0e00072002030015000700080fa90070410150a050b100d40301b600840303c101e181c100080b61050b90500c98403800f4000301034aa4202c0c43e0541c0340071503101166041060081d545132183c7c0301c403098105400126403204444100c030110f0950b407242d031008446007031010030501000d115400d5810564900c807a215590005030b01d42c5403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 576994667 1250 576993417 576993419
    0xc091a03090106150e190b07080a020a0b0403050c06060d050721080a090302090c0405150702030f060a05011a03150105030717280b09010e060a05122b0504 68
    0x11821050304060010106503403281c2000c0b6102c0640384400c08049055920100e290701040100801801002007121114409100520518211004903000d660300302d083c441c1d48020b804c4c4220b160244401340641085c2480090004056000004007016490042100c006032a2541000f6070706458540040c1705a01c00703802004100f1685030a49929140380300b010017800a43c0d21074440d0741d071005030b00c5000100a40310a0046213489180c0c070381c001d41074141c00c84c1440d081002084017012420004118042c02107000b1003150740c20031100c0490040c0c4410f680c0d07941030500340080640003c1c0900d84404102100e5184441d12600941c1d200780456039802d100b098180c0d0040d1815800070302240208100300c0c451400444210301458000c92000508000c81e2030203c00702410040000c45030322506090000903041551000c060b141076602010641405880d9040050501269580500e4010220062901c1d1020020400c02050310310a400d80d0500d4030982480301c0c000103c41d9011000c600c0602c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 576995917 1250 576994667 576994709
    0xd0204030c080c1315080604052404080a03110418060503251214070816210221100501051504050907080a110f07020a0603200c0a060606020d030c09 65
    0x1101c0b8842c0300e0391502e20410358039003401b141854021030b001d0703134141d0100e01d03401d001c1c0c00e0300300b0100340c10680201c9004c290700703040d6a0304903540f24019201d030070152903201c0c100408804001311002481110901200f0140520841d00504810303c2107902c20b004000e07640b031a084c00c407900d48102d010510a030300b010b1400d0101c0d003901d09440e21000c1c0c0e84849401a2402c00d07071420400c01c0040c00d0b101c401003a0710003108402d20142c1125400c44900062075407200c407803039099080b001a480381e04403800c0301c51403d4441650854000004203502900c1181090344210f02907510450590300b098800301c4824400344601d2685124901c20240c2010b080c1c00024a024820380415401400c40517010488281141003807026401c1035020581c0000006042005c61411000c000000d00c200c0c2428440755408648a03441c4c00040c46111550080000c2d15a1000c5401d000d8200038542c002d0040021944802000390f442d040c4040401c0881d02d48a40d01403140d0141f0f03003c104031503030440b611542d010122 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 576997167 1250 576995917 576995921
    0x309010509091306090b251e12060605090a05090c0f0a02030c161721070312060b0307120e0604241a131b11120d0204030c080c13 57
    0x40040c03d0060307030750b00710300009001070003041d0b68580180d01340400d40c00e04800700e10704441c2041c0401003092010b030195204e076030840b035601007e602585031002e800ea1202415959080841c00c0c24071001c2c502140410411740150242803903c6084e280c1001250700c440502c02d004c0010345850709150420303c2070641e03880f03c0c4402800710710a6841641c0c20400100c05061410070b82005141d401c1c201ca11061020001d096001e040726119100107201c448002d050035503c840704440c1600c044600000e0500c14075014410380c080d925812101045120366907003ca4055030070a89180b40001c0b44c085045040780c256020f103c0c06400d21601070010307030b22150f0f500500c9100855410300381d180741c001e803801481d01c948150348003080707583c9007800c000098904202c10340004848180c485e5140c4601c107068000c0310300ca40100c0100508206400300b607202c0c00d0920b011701d0610124900a00050800410640e40e0054821039200b1980030300841d4030b80260a451303101e448010740d0410300b465501c02c800d038015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 576998417 1250 576997167 576997171
    0x703050705060306011b0507170102031306150314010c020c0d03122a021c0f02070e070201090c081c030501231c03050903060708090304060c0614010303020c04050702030901050909 79
    0x50625200d9281e10b00d6081003c0c40f001b0b202581e854100b10020044110140d10003001c4a1700407008503c1c504d8409900307410305488200241c800350351a22001083ca01c50000305c0081c60b000101e04c014061540961030280000904440050003400341203145410030607480c140459041e1642d020320b910803050390009004445c55004500a10403140a5500703094803840804030300781e805010121044552034a480e0030202004080140040014203c0756001c40e071001134601e04241c00f051500c41140c1240940803c1002600240820f080058441d00c00100d040c1c18003a0404a40d00350003a401e01941111824486c08003484001a00250240004111900800401404402800031031402c1c40f41c030114004003100031550001e42c1c801e883c9400c110130b9612070084d1414000c5403828031400c40d20b034040c030b1040d0010722080811a03410002c3d290818138415280160300701d502c0da968240207641e04545110b840c001d51400000c629a00e1020049520b44203040c0c585500e01030136042400f00040d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 576999667 1250 576998417 576998419
    0xc1e030b030313030303020717031306090f0c0f1a072301110a18081209010f02072301081e01060c02030c060d0209120c090708090c1201050702010b01020703050705060306 75
    0x41241c0e6054a0031841d240c3c003e180a5940140c440f055894100044e2900c2440307038400320b03030501c1000039611a50b01c0428046900c0000880c0c400b999203060318035000d903004010902b0840d04808114108080100340884c2d41040e000d6010405a1580c0f0340140b04c2c02d02e02030165035035000c682e451100503044101e09910300c680005504170240c6c400c4402e903001410050700044040c541d014034207413451401d10190103003c02810041200c0c8583c0d50140c4aa02001c03818800c5100f52010b40d039009102e0200203144007a2165000c1700460401c582c02140503042038040b42c500ca01141101440c6002203005100040070b0012607401d00f0001d560348540b034032040b80d042c454080102010780b50580601a0070601040141e244c10120702000a090303c580c540541c00e902c039005640301d40c1e483d0f400c025005809424000311640394440f00508000f448807034150403407400d0b1000c2d03030b9140c415400301d403042c1101ea001300110031480c03004a8490669100c0904a603112800a01091410b24001d5412000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 577000917 1250 576999667 576999673
    0x80106030c410a02010e030c0307111201060920090f130e01060e040c0501050c0a0605062d0909070f031203020c16060201051006050d05090f0f0c040c1e030b03 70
    0x71501c8003140c2c03480c51141c01c0204049001c41c9442095409015100b40107240402450400d02074a0101c0c0c0d0701d008003000604003080c07041c1e40e580980c4070482e250307807800c1200000340038043d01e880078800602100d420b401680340400d0303282d200c6e04051809694048400800e80c126252030403040101001010080c076803000d946002c481c440c85824803581c0300608110103034140e0f0b40390a050a451040303056011a041c003900300a20100d90001084200420754031080010b4191036520200d6581c08005072086484010004da4003404030180d00322240c00c44048480613516034496020703d45401052103100488018a602070001580720715514940301c11034070340141028142240039203410284201c1000319035049a0034060198280181580403c0007407944140c3da01c0c04074001d1a80c0700b00c403a084001540e8801142d9250004c2c4088503d03881180211504240551070704c40d103400139403c0c190700c5030740f42c00f446d154464004c0301400031f01c5800740360f0341d101542040300a9000e0a00c4160080d4940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 577002167 1250 577000917 577000997
    0x4020f0a0e0609060a020604021f080a020a0912060911060c0304030807050a0f0f17040e0105041509020f12060904050c12070b0304080414040920130e0607080106030c 73
    0x780318180078181700d90840d4002e21b000e0400d4010321007050040740800304000c82181c1c00070603003500050319607000800120010382c0c8610040c0112014903590f08940030a00008402806212950304008541130007001400b10404194080142030b12810140b098036400c00c1c070007000403942e4400034082c114020340a4906c45035065a4200d0558007180040b2408023030380101506100a07508040030714100712400c1d52400742891034911b2080c03c140324903881652240400000d10310407a03140002840346400641d00d5281c03c405044c101c0e04611101c0101c01100701c005002d5140c9000d02078000d070b8020303001d40300c800c80782401c0c40384080700044251801d1107008070004070082035400840c82180500a00d03900d0310f040c9408508040c0581011a2080b8142903214020036666810350848007183c40c48000540208400719610010075008541080e20308039103011209030104010f03202d45001e2384c404211b6038035002d055084801c1214203170005040302402c040440e90300c062408103659440007004441d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 577003417 1250 577002167 577002169
    0x30f0209030f0106150207030c0e0a0207050d0f2601030f081201030303050a0605030a02032508061005030f0a0f1101030f0504030f020d021504121b060605030c04020f0a0e0609 77
    0x34600e86003002e6180c0d9036510410a49100411445480e075492010702441b0b407a544809407548001e01881030310f030044101262409503d0390454014560250a5075108410054050480c0f010046142d0104618061603c41c501d00c00c0d00d520400044d0814249030f50b402c548400030030003045101112800c10801445408120b440480b5008503c642d4000c0350500d23103035100e2400d032512940000e0203a803140060000503a004a00f050b103251640311240049040c824040400e80b1003030b400744407140147c100b0f01c01d606041c44850b6041e81c0d07080c1c003100c0c4800c002001e440c0e81c60000c0c03200a032101e1001c03081040000e032106080070440c44140340104521402d8202c0500f182d20968003140400d91000c10304603c00c1e01030000d80c0b4003142c0d50000d40041c103510340a820302c021008000801e509007014607082d156008811055213601013014800e5020389a2034014010007a502410344684100c80042100d8900b034000ca5500100030030300f10b420300f40701c880c05a070a20600b0403403c3d440442823104000b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 577004667 1250 577003417 577003423
    0x21c09140604050601091505011e03060f0303020c04110c030315061905030910110913180c14031b0103023a0f0209011e171806060a030b07030f020903 66
    0xb1402100a45150351410101e44229850074100c00c5020070b59600c20856603030403040d01d090641c40d424203003502404504007100104003c1e0072181c0c110f14032600c00300a05600280303030380340c81205480401c104401d0000012850040e040c81c03881503402000051007011102821070004400a0f0040c0d0070182c8004003003590b00220340c6084006a0b002c410808848010800b0103001c00c12100f08001d00d00110912000510442942a004030215010210401c12070b5010b62400c1c08a210a4401d40e1410318204c142d14200d403082000c81d0260302c82250803442c02040001d050112002001c021401110054000e50031112202641e03150751841c0c4507000050803030700e80b4840d0f400100958810901d5540c0c01c101c3d080c1070000c180c864814010581181d80003000660520354040030180e1034642a034086490400f540f0102020056001c2030108a1124400d80380c0c0a0020b0740640700c0650390703201400b4000b025444044c1450360f83c800884c60480c020350100c0306802440002610b40300341a008685 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 577005917 1250 577004667 577004671
    0x3020a030f03031b082a0318030708040602010902011205070507020d03021015060f0903080904021e1c05010b0a080c0a11011a0316030b010303030b2b02090604021c091406 75
    0x30100d0f450400b0003507020302590341116403400d18582c040450b28140c1006d81140030050502040307044d500d10102c3c0c01c1000b08180c03030003650700c40701706075849403188002030203003100d208220f0116414400c10754040c43d043c05454030459442e0348080c100165038003003041000c244072082d000c0d4004c2d107c1064094070355010700801041c0d40c248400600d890520001e06103c40c0030b1540040020aa005000040d007000481d108038904503002358407098140c20040403114507541d550a2481d00203500410050041e01a06900724116001c0040740e07610108003261744603101c20f110009501e03000284c0040c61100c0640b52080c224a05101e2207a400c2d4016400c40d4107a81480c0d030781e001a100300840d280780030000800419000c60031036100d12718550b618140038506010040c145502c690803083c02c0e484806041011300341c984000502c000004942e0300e042c191001060340203003c043c000561070704150088840e002c0886031003110039200018003600802c030f980402c0701c240c144088501c83e404400c021381c2e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 577007167 1250 577005917 577005971
    0x12061c0b0f010f0605040b0301050d03050c0a140c01030b090f0a0608070f0f090c020a061107020d06050a0c050a090509040f020907050408061609030b1509101a0403020a030f0303 78
    0x6400c0d5040044000003240191300a0b02001020071041c01031140001c1968116441a80d5050341007610380303020340d8140a5900d0351903661240700e80c0e28003405401a0300106400c14101076030305c0244a4401141a6180160303501d80042e0140085540c4c0c0c05000ea04036031003450320300c0000c0d8240e183d000c5542001c1e015130240c0e03004214004148560105260f20350700925800f18108001c281e6000017940742d2604400c090700b29580d4031b03141c0e11024114411581003d9004210704404c070010716010006117819210000c0192508590349001c40c0204116200c5040e591a0000032503d084100000e50034001c0048071202179140c1204016166140101d01440c02501c41c6500c80d42084106841e005004000e100580000041001c21b03503008020752054039009500c00c0d0303040c0e48029000d519613120300160b80d00000d107001081000040d5160716410758a03030410042030702c00100c0e0007041e240200e010180d030040c0c0c2940b040000804045002c040e0b02c1c4241070208460301d07840030018003c11510050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 577008417 1250 577007167 577007191
    0x4030c050709180b13031e052206021005010e01050607020a23240f0f2109010606090b09010c14010e06150301020c0d0311040e010b0d0e0312061c0b 65
    0x10f0010083c60301c11050303100e201c1c29090141046140c9005040d2001c1c5005a00541c50428542d000b5522520858443c11320202000034016038040480c0e101c4040c3d0b1180c040140220429180e01d1010742c0140c50480e00e48450300444d6034241300030481164005001282c0c8491400d00c00500f04550300c1c0340c4c00305141909454aa50000003041c00050580b0903d91258421002021078070840710354180c402c400720515413907441e044042d0801c4e00c00c1c880c0114040001d02007009890048400014003481820458001e102d40c42d65070704165a9181280030b40b460314401070041100d00c1d440f610340701132580d00544000c00c006402c0c20b055400c417010f800e5036030b40d0b54020384204002e04c2d14080041c842c9403001d60007186003100722003c2648a004600400c020113413140c2c07112103c500c02e5000d450141924000903e16569901d02d03d41c0b280c1c0c032171110000585c0c200508a2001240802540c6803043c07a0360007610240d40d4036041003803002c0c15042d05642d1182641506010600741ca8000f480f54904041c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 577009667 1250 577008417 577008461
    0xf140109060608160f0e0d0b0712060f0513060f15140c100e072c09030c0a0816150207051c0903082107020618010b010804030c050709 59
    0x1840151841d42e00000e09010040c03052281030500d141c0088014951440c14089200130400d04070f6103103c801c1007099001030070300350180030700001c03240c0140500120344407180011000e0840006071170042c4546e0107461040c0c44100414100b910300c8205a0030709103000962981c850380d0b0380c40d110440e03402400c041c0030f04209945040741c109640844171a600380e40349082c0001e1440150751a0910036105c0e00701c8e41c448440038202c080800020006d81810314031503890510b1171851210b00004001c405500d00704141c0425560b560100440d002c180c0030380050320007101c8948442c03505a011311010f50500410449007800b02d0741c80050403e681d0041107025a130b030032481c2080341c604400369030404140c4141c8042803c01981025030f00c41240e0f400f00071151143c0c070720700040000c030126500300092499800100170055601040b010f1107842882000c003008940040410300302d8481104940c04030f4100004540403d01822108081500c03d208031540d460b01d5429000603160a1001050107c0d45548 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 577010917 1250 577009667 577009679
    0x9011e0506031909050a141005060d020603071d06070602030937080909040303060e0108031908090f2d19030509010915080109060b03280f1401 63
    0x512100101000c4a12034218106258181e180c000001c540e490700030358500d4074a04106041c40b444000c103801141e00c648582c050070440e912500d0300031686140b145030900250041c40c1068604001d0f94028101740d00715034a003a01940d28034072200d281c0c10307401d000b10b01c0d1662076620380c0c006000d464802e840260300c90815503004e52511030391b803175200307a8400c4a414032000001e0200c1070145603008055000349441541c1400d212904c603802d14190802c24950408c014150076400040c00c07545107155100c0740381c0ea03030541181c81e406018614490300114240e0000b200c0e210341440341e00064890103403800c4200f100f071103a1504500c01c007809a1032820b082900c4442c2e858000201d952032102c0098905102d04400744120300a10100060030300802003001d04099118550007009495801c0c0310340d0061511031000740000c1401d100d000d003004e081000211700b10380b8901c2541c2c0216081d44c04040000311a0303116145908000a4801d405a9148020400c040702c42c001d50302c141c0e110703d001030900c1d41002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 577012167 1250 577010917 577010969
    0xa06030b010611122b0501051018150516060b030105091902060d181a1e040f02060c1f0b06040e0a0509161503051501051b0c0901 57
    0x1a1050003805010a000300000a004c601c6031040c0243c00c80b45941c0f6042c5042c41d0314480c000110500031000102a0382e4885005a071040b41600c0040398120030701151914200c40344980e03200590320422056008128020083d06100c881160608001d401d00713203030405d0400100710b44030041d0b5041d40c80f00303840440e41c1000e118858011541c074000c0d000c000e90300360f5007203004c1900300402070086100180c1030702001d1850b0301c14011401503d0315051040d6a5081907045260688000340211f805000411211002a89001524507983c1c450591940e640d4890b03134460340034a2816608480100440d0504c903005200301c46030304031045d800e00c500800d96559981260a19007038180036150400061040c00c80b450a40345e0311440c12203010909170303501e12282e410308201d420b40c0c0d480c21020b41d40104142c0404070b003145c80120389070350402c110b9803800c0411040c01c101a8500d804035004105000385141e906005900000c644c1c8220307405105440c0118010207004d034000345422044020b0103007401490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 577013417 1250 577012167 577012169
    0x309080f0d0b121203061f02030c06060a14040c030f06090c02060105032407050903010204030b04020f031c0e030a0b0108060106110309010801121a010303030218030a080306010305100e0a06030b01 86
    0xaa03003d4403d41c1c91184455560f00d55411a444c040341c0200c0020529600e90b0341152514905042503442e41c885400060365030342200740c0b11034181c01441e0003c0e6940c2030519000080750b60084a8400c60100303c01800000c0080d052007038101038803000c500c0640d08460160600030103c5600000b030540084100a04080040e00401d100380c101e0500400340d0844010800b2803c036100e201101031f5104e5402c2901c0b0341c0b09450344141c065001040000601c203003824840d1050b80240c0d0900c0e80c08080404040c1c8030041c0f12070707120b00c0188008140755911f01ca003a100700b4220024085034108600781d120908081400d0f40b1000032988104014000640d10404880c0084541c000541c1001e02160010b0501d0405008003203041d400d15826600b400f242e00090350078410403410008965859050060281d0320140c54031502c551102c68030010b5090009845d12030700c0c6c0140c1ca00d070958644400460240402030641e000c284441400400d20a1410385040e008221851000505a25519001100c8401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 577014667 1250 577013417 577013419
    0x70501170c07020111190503031b16080f041a03041b0609050907051c0902040b0d02130905070302103c0804051e0705031002091f0309080f0d0b 63
    0x4005101c01d65500105440070641d09007010058544014105450700600b000c40c42585110180c08205010000c40114040c0d40c02d40e4018059411810100c1290b00c00c0c40d40b0480103412451b0514049000300c1c0140443c545028005450180c0e0780c0a2400c0e4a200b01c2d21403a07440800100780020000c00c819503a0784886140d07194042c4c0d030726108010704005680c0c81071900510b0035034005600c16116504072001034441c02c10340349903038040e060703540024603407250124000e42ca8a101030791603140c1a1440c1074480d80c018034100c0c030324007070b9891030012f01200c1a040b20544030b2410044010f030b40f142c3c0144400d0403541d6a18014031550b41c014424580100c401018500e5100f00755120b030074103a50030102d035250600b0326003465191481c049203015408000b4401240b00c4c40d040c1e07003507103d01054107030854104a040340c0410440c040c076401244500040a58004409548640b0340d0640c580540d942c3c0c3c105050000c0c034061140c868100c558401d44007000104000544030b401c2890780d01c141c2d540100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577015917 1250 577014667 577014707
    0x906050d0203060f0901151e0e010b0d0f0f0c020318060a050904240b0d050c09011e17040807150c05091c08040b03160503040809040e010f0509070501 66
    0x24954011a455020242021300c00d00407810009107a02d00c00d410403090b4004048555403441d83d14a00350002e0322500803d4a030500c0c1c1c0020000c4c1069942e2070240c142e42005461a01d0100e4110740032009051941c0010101500c415035400c0a590503c80c3c900c1030100e98000c2c60752442c2119130b09001901405c412445030105201181400380d100d030944105183c01d6600207410340000f0304028160001610500c0e40e40740d009004a41c0c4114840981448040d000c401d10240d00d5003e240c021a000301c1c90303814001400c0b81a200101e21000c40700c00754448180c104070100003521005024281e600712000d4a2a042c000b8981040001c0041c1d200c82d01180c3c071341d081103450318202c3c00605a1140e19400341c4180040c1c01d01400000400e40e0f10340e0b10300c1d0b2125243d40c0c0e681c1c0e10743e8403600303640080f02c0c110340c000001c0003021041d41c002c100700c07403181703a109041505e4280e100040000500c40b41e603000c10703259610041b0304240349039440b810380a600d03004020205c0620b46070004002c14122140c00039501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 577017167 1250 577015917 577015939
    0x1b0f050f06190e0303040204050406021608041d040f030e120706030218032a13020403050c0a0509040f06110910090513110337050901184701090605 65
    0x42800f209880d08947c1c111004034168a071030414074083d02582c84081d006200c5000500c0c100400d55000708116a00b0051907010300c01601d512442c5000e04807005800202c1f025400400248980003000000000a284c0030008421206061410b0042e0700240702096001991241c03992a095502e654000100c0007402440041c1c0c03c00c9003124603c002d00c00ca0304401b00000340b40782c0e0328244081300179a94284115140d99580c00c0c629501d1101d1180c0e5030003039415981c045824282150103901c40c6401a5030544000b880c3c0c3c1c1d61000414111798504550308040c850000142d45480790a404d0350b0f4269070301c0c4100b5060204100220458040284999180c450320301c4c00b10800c0c006a80e408500350010708500390b02c10b8108070b5174181c10710140308094100151800051050b82c4001c2c01307890441c1c000c00401c1725502d06d29804400d00e21025000500d89100b1901c41c6180090340054000300410300810601c250654a004000c404000f615002603c00180640800f621a02c001080121410700541c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 577018417 1250 577017167 577017191
    0xc0602010522120c11040207110a0b0403030221040504060e04021003020a0e19081203040506060307180b031c0f0e0f0a06320d050708071b0f050f0619 66
    0xf20504690030418441c891400005102c25003000c07840318280079206654540720b9141041c0e000e80c0c0700d040b541c0710302e101c1c0c03d0106403445a001910f064a50640080074400034121210983c0c0c43c41520044955204210100f015201e13405020300421148051803258106071041001c4050804e03421801c05205002080c0c4140d84941400c1e0b4802c4140c4c0c4903404082200c400003001002500840154810008100010085c010045100d58024000d640c0581c54040805894a4081c03290080103208403141e11324090580d070044101120040440c1e28142040e0801c60352031200120300c4020607201d20150080170b030800b45d0040264411078a1540503e92140003401000071070086408110b0b40b020001b51500500d004642c02c40c6000c07420141044170328550401c590312248441283c81d00f0407002c10409401100701c0303809002d031358403407980b03c0c1c86c88803c80100100076003003034800c21105000000840c00503c091303007142c0940b2006c1e1100b85010880b2701031454074020480744840c03a00384102c0300c2c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 577019667 1250 577018417 577018433
    0x232e0e010f03090308060f04020d06080a120509030d1b0501050108030a020705010c02090a200c0a060612110909071a090109061b2301020d140109111606090c0602010522 74
    0x711082c01c40e0b40b226540647d201003402402000a403640c0f09140042c04503140c400000c01c0f88041d0311a0700000c1c80c60148920450301c9008021160b60541d0101d0007002603a800342030403082003503205c41c00b050a001e00b521010309652080e07020940c1d640001079034603010b90341407000001426003801c000408241c541c0c003051804000405207214950b41d4014007070300d00000403100c9100d002e8100100e44034000030f07420702d4032203061100c11203001e803501100042d209600d500680100303070010141c5840c0921030040c0300107040020f14101442c010f102c000b18283c02c0e4560005109840d403c05d0300e0320307a130002c0b0003d0170340360064010206004158400d86060034140f47c0500801e58480050181c0c000c0c04003000700b00642c08408003e9a50010030060303105a255484806000d070341c03200010081e6680d0003007004035160b84000782d10280b400c00a11700c2d40c0a40c0350490030854851240050303d1945602d48031040d440980011005075121024800000740a01c0010002e411444c00c2800d5440c1941d6147c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 577020917 1250 577019667 577019671
    0x602060c031305150603010f1404030f09080a03110c1f030903090e01060c0b15030d05070813030b0109050901020a080103060519020c1006232e0e010f03090308 70
    0x345403000000003800c0480e07000e03180354003039400411030b607003045a0115070f11800700464407140690320b012001e00c0181d03900d002d4440220a001000a03c98455407404c85040180704654403c0c05441d02d00010160020440d88030020300907030343c004c999418002c0084c2400250318086126002d0b40c040b80f5490080c00720460300c003074503034100024400c500346415541001c03158040990390390b0a00000036096041b801e440e00d03a0380304803880302507a0f4aa007450194a4600000241c1687c8400f0024102c140a03000403c0643c2c0142c5046e4202070390584c0c622440d24443d0400c4440c2c0c05880010014003095010341034005a2800003981400c0e1404001010400305100c0507000d03d45070b40200b240010f02c180c84107030b414101d07a4103560b250a40104541c0c0c42c1032100c601155135140210005413042001080705d1a10001a100c64a003240d6804210355881005600608460810541c84818981da040404407031a10386584503030b130710080005000340922103012414036007450344050000ea071240c5559 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 577022167 1250 577020917 577020931
    0xb0703050f0313050304030b09010b09010e1b0d0c020a05060c0322080d05040503090a0f0f090209030f01021c0b0d05060613021b060f0106050403050c060a0e0d03090608010807060206 80
    0x76489a4030300307050f094030b100d50840180c964000002c000c820701421030322551050f15041c0003406290846018850460824407554100e40c98120110300301d85140c03030001c0340e89042551074a040c80440f03449141210585406600540d01a4030381204101050040590084c2d000003100d09602d000311608800201240ca50404096010038180c2000400c00a803019042d07665001c000920b801d250a65803941b0529840d031040f031102d076000842110311445582680e080c0940d20404038601900d01c000394015034009540f50103481814040030301300340f002e01401d02c98800d2590140c0740345640c01d821218042c0e00305016031400c02d03600c4046440001c00c160080e109440e000401c0050f0400040280103542c04090364461280620380481750026940b030040340309001c0070000740d90345d035400d440034442da01c001012504184001c507850300c2c111028110300660307802c0c5903c01441d40c00010301c4018104000b107000c124010800d1041d160b22000b8075000d4a0101d004080311420407101035940e240092282c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 577023417 1250 577022167 577022197
    0x40b1608010302041521140a020105071415041208070509030309120721021c021e060702040c030e1b0d06180606031203230f09011d0a06060b070305 65
    0x410760a00e03517100e400028483d6400d21810740a241804102c42d9172111025281c0e0715800b811551445070100c2c600040075816120781f03140448550b540d081e41d160069490707440e4058500c4030103081c40d00d0034903144100d00c140102c1e0400720600c0c1020305840b1001d8591010000e0a010201d01e6403800030444030403c50407140c1010102401011070318102040d0020850107541d0441c0c00c201000358005e11032070500c22121010b0b2001d18103d144401011100b02940c0641840c0d0b200303202c1010010407560701c07070000e41000d140001d282c0118060b108a100500e000070b0b17682245030380203007061000e45000495000010140002040010310601f04401c000d010030b07941c0ca458509020022070710100b5903500510034003080340d89003080d28600c1603005500e004203003000e49030402074103440b0141e4860f48003240d031049143c9403541c456190388001403070080650341e100209100074100d4090f5000f014034500081c11015040d19000090741c20750303030007c844840e091102c4000650030000b9a001c041c082500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 577024667 1250 577023417 577023431
    0xf09010510090e0f10060810020f190311030f060306090610090c0509100509011202041206020702040e0f010501060e1e060702031501090f05090307020907050a050d060e040b160801030204 82
    0x201c075007800e501d0780c501301d0203100d8160990100e00098200800703d424000695404e1503100c001c0b44140d104000215030b080e10100a103221700040c0031921127140c5940d10b000110f00440c0124440355030f1050303400a00a080850400100c1e18041180c10f9011000001505560420301071002044082d800b840c0760158864018201142c4602e0643c0c01d0340c6801004000e90141d642c0c000391040c1c0c000c1d0600b074002401000580005401402214101c3d041506d04081d180c0e1a0f49840000b5000000207da10907190200c140054004000e518011400d0740000151549492000341001140c00002c07402444014070702003004201c03070b0302003125010603a00527035201210301c0000e08200b102012101d5041c1c401d0008076800d00c4070740c030103035007290318a208108907101c01000c0c0e41d880c094140000d500209400002d00410701c504050407814585050507410001c00d082d040d419260560407000e104054481008180107064040c541c00c220b40b10031518442c449084020700c2c10605000c00303806203440d196 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 577025917 1250 577024667 577024691
    0x90b0a0e1c1211030a020304120503070c062d0608010c0e010e120a0f03210e0604030c231c0504030b01030809012607120501081f060801090b0f0901051009 68
    0xc50f00302c008020101da813442c0038000d8400a4105841c241c0e0141d0302c00d0240b03583d450040048a004680c00e8480300084076590355000042c0c080f480804074011030148065407012410052088499041030002c540c080c00c182d003039401c5407020000c240030005400803024507a60403c0308400000b00960b81c41e00781518031003045150800d80f010040514582c00d12207028194442080c40181e00344c3d40701c1c81c440324124010130050312203014000c031843d002040800c001a004405640f2114880c00e080d61003a40c0c21310b00d408200300c1c80a120b0f4900d3300000c101c82c281822042440c01028154180304e802c050a588940449820500002300b03080070004117810b060380101d8455401840302d50791448880d0b500d585400c0c501100352050004107160f581485040361070350044c1410b84100c2c100030a10003160b62116041c900040e40ca42c5109a81c4444c0803c400c6030030f00800781094064511850103042801141810840007044e03075019034500820f00090240c8080f1380e404880d00000d0205078065210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 577027167 1250 577025917 577025921
    0x906032401030606060507080d05070207180902040b090c040e04050309130618060303020d0f05040306020c030909101a070305190e10050c030703030e030409090b0a0e1c12 75
    0x40c50024050303010042444645144400c410306a91144000b4000703d07544100946003401900c1000740045801e106444082e422540040e501003860320454030b240b603030340040b980f4000790349102085d0903445001510a50400d130040d00101c0c4020342d41a0154070342a44c01c0072550103540a403e00300394003013001c5000d11038200241e503010701c03006110141802c00721107048014080d03171068082c0c1c0c1c4a4407140803807990b80d034401c100440303400d5005031454611070300d27023100c160250b0300c02074040c40001e00010006c00ca651000d010304102c050010750396005e911082040000340100020251000da410500c00f404201a03110142d09481c00c0782da49911040c40c040e503080c0540ba24000d0200c04007003955402562201c00e002c1c4d2140290350405654021900440d014411010380880e25801007001c1ca0000e07109910216100030310341c0a89091944611079001a50100c2805031410051071042c8038280c5c599120704d0810798040c40042144079406420041c6402c1c074205804180030160601d0340d0495003903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 577028417 1250 577027167 577027183
    0x120307030e0a0e1f05030f0705040c0c0b01090e0708190b2805010306050a2a020106080d0809070b09130e0f01091a13050a0f0501021201060c02030c06031005090603 72
    0x80f648482c0680340285a6515002c0b681c4900102207694803400582800e02141c000c10552059016041d05402c003402d001c013805400050f601042001c94150020402406000780030786001301010a0710380301c1d0092a803804549402080554028140c0c144d0780304138044d1407040c0d03568003d00c0e0340c4e030a0342e031444444542c000880300444a2100c580341180000c07034a52017141624850541042551182c00514003192050120803411072040c62411501c038114031801c4011110303503c00829003e0f02d0b02c0340c50742000b0300d0340a2800824040e00900a806c1403d00c8580c003d04203401196091410001c0024003120001e0610604d00795101c1000b6000d400c148484007420f90801d000f8044c00d4040e02d0312840015101440200d84d40750ba80100c3c8903902d4512101104d203070824002c1c02020700944035004e0006190360201c855644c200a4101c4242c40442d000d40244401d40369507a0b0081c2d5401030605000802e005c5901c2020704108004111140c01c04c01004e0b60803c2d1181c14050f694030004c13914141d56 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 577029667 1250 577028417 577028429
    0x91809031306020c1504080a0b1306021909090c080a0b01030f02040f18050106050909181203070206090c100e150301030c170d020a030323010e15120307030e0a 70
    0x10300e10100c0c5603600044c0c070242c41c410968940b81020170513644801140124098844160496400803020403440780c0309a80107481144104a01d0115960303813000c030303400020440d00c6107869010000a1940043c61200140380e064401e01c030321008000000d160043c002c00030170541d99105410380807079120b0741c42180c404a01030001c40d5556112024682d07503000da0b10900c110070036001382d003500c41e102c2400f0f81e030304a52003911050300305891401004060b813001465154501c4100307203840e161034410088a0122048040b917030750360f13007000740009040c040c3c020101c000ca03611480405040c0e40b918140d03e00503814a18040120780c06a60014a01410260440710b4071340010001105126801d038002040b07502c08541c0815542949508a0702c0d206d54620040150300540d1558000c40d010b900850040c006040785010701e90001030f400101c041080e0803045014904504020014800c418484180101200e81e4400042c00001480d900e1007035107002020050328100c40449620740074188009894 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 577030917 1250 577029667 577029697
    0x20307050709020d0609060e04020f060d060b090f0d0f12021006080f19080301140f04140f07020705030718060b180f011b0b06120a0c080c010509180903 67
    0x1650b4100c00010350090240c0080140c42d081d0006050350051050310121412010800001c1d0742d19002c000e00540d4510f480b58000c2420002d049032b00200c2c0c0302d00380c040d0550301152515010881c00303001000020681c0103000b1078400d50640041200725480b016003c0d44602407822003c1d048400302d040181e008025405e0f60b090907400b16100e01e010800d0303804140c40004035030450341803d036a6080815891005441204100018840c40069561003680e5140c0501300250741c0f0020800314040b01e990381c49011009041c2001c1c80307070420380d2a60481e04134001d48004d012041c2800300207600c82c1050f20400070110039031441c24000381c081e500220020004564542e441e003804a0310818100c4c4508421403148034458980303212503000701d02c000300301803101c5100190710b0032560321a034105030701034055980140100f944154983c01003000854103440340040741c00040c07a05a4042c130304414950a5810710105200c80d0580e62502c000d01c0042d160381c0d0206030500d895190070b841c2540700b442c0010380d03400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 577032167 1250 577030917 577030919
    0x120a0f021c090b070201111903060e0903070b0a0b0604140a0302040603030f08160f030b0a05062d0705191a101701050705041514030906010e01080325030203070507 72
    0x400160b11009034280221503504095451450803400c03240d030700c0b949641c1c81005024520700320b5032600754804100c0c041e040000e06c0c0c64503908041000c6108031540d440c1540300052100801001d004015008402c280040c4524a03000c00040c1e810b01540c02600342c0020701d56511141a0788401d0000c0c01990050800c2000d030352a03050082c9605403104010011031500d90104448d074102c20210900c0801d1a43c0310040c1c0c021184040340034045122500b0751040c0c02000200e40d030703a1444020f10b4041003480714900040500b0a40290b031040c84d20150b00050402d00c03c01c4003044011492175220200f0740c800c0c1d078140042e890000400095980c0c04d481601001081000e004403242a44086d6001101029194036080760218240c4004035010b000184040c031007080861050600c038825620b050900b926000c80040c06004d26410450f524079581c0e1150004000040300401c0b61340c09000500c019502d4425481004d00000ca232603440c40354100c041400990502d4030a1065854040e401010b90701c0310303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 577033417 1250 577032167 577032217
    0x7020102070210050a020d0f050705070608060a0e060a0e04170d0203060906040509071a040803180f01090f121a07090302092211030c030709150b120a0f02 68
    0x35000501c0072070052410040100d1850b005006680c205d00050b0f001346000c1c0550001190400011421042030000600461000074024406280035040c0c940c0c07841c9040c80c10700304010768a00940d014441401100b010300003547c40b10345117a400d50f0312060000c0600d07152460300b03c14020b00b4505400c0c4c80000882c5003445020710360011760007180200c401b019a52140401c00086030015140000e9a50164504001d080540d00c00a22501208180c0301e081c50350300e0341794030b0071584481d00c0e645041c03461480719070540c80c003c8895101e0355403e18141c000c450a0a00d2014900124002d01c0c2d20400c002d01408108508001c00d201112034032122400c040c2040b99018000c062140001c920074805c00002070100802e552031300f80711f4050302400124030391840e114124a60f0114051517018090076104840c2502d003040b454005082c41040040c0086401c0210514816541c1007980101c0041044140034840504180d0300090000e10020b2604c2034666a600203104d0300b0b001c5c040403400c21b4000d0500e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 577034667 1250 577033417 577033421
    0x8070e0615040e0f010e07620c0f070c030213050f07110a03050c250303020d140a1803020406091a0d0506011a070f08030601020f0114060607030314070201 68
    0xe024000b05804c01662542e5001c8200c003003c9840000040c102048080c007400350b004620020309164250141c0c541d144030502e2495103011031104000070f2100c928541c8484042c0040e20705500b00c0021014500f070402d880d440c1d5106161064581d43c1000c140d450510100c45259401994000c16001001c410030480c003014000480e00112003100240015040e40c1c000c0b5000020512410050074422240c0e035400d40c6c1c1ea400c00e41c07184055200d0703090008961211088065002520107204981403859880c000303250007010305040e41000a890000f100c81c02d034075400d48001c0c42050624040101001044034041950399001030340c41820f08500181007410f80d480b10380c2c4003810751041c0c0d26140c0707100180b2403040104003004015511000040000d00c0e0046180c0b640d113040400164030f0070006481d05c7e00110583c207826140283c0000c14001e496804000030003410307030b158000380506459003002070303850305000b010107000e0000003c000c0c04141c4603900c1800c50901c2c0d036001003180c5c00c04140082c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 577035917 1250 577034667 577034671
    0x6101521051005040b0a05090a02160606170712030804060e030d2408070521030c0604081b0606010804060b061c06140111060105130219210608070e0615040e 69
    0x20090b0300c5d0510841ca035080208002c000d031000902000391700d468080b0070200039030103242c60603410201d0f055403800044150080b00010000d4022000cdc9a46c1c40c1d5000c5400d1034400e5002d00100240c0001d640c001079082055554001d8101100040101e8140348540c1144078595824039140d15050300b801c1241d51201d41082c412007600e480a03801030b190403200e0703910f01890141c154421000c03460032900c0d142910421220103070043c15a8104420010180e150060a44046500f40d2000c11809040c8a02c07100c1040a10010303030040c5041c0c20000c0010307003132aa010300041d0111340ca81c804507800707449d140d04a445078aa903440018082583c001034800070149402201c0c90754030415900b65a030761007200c40c0f0140710280c0d4040c0882c0c6e4070b0002002941c0b49205c0b40903500030380030300c00c000340c400446005501001a40e11040c100000d8160302c40402c03610031a2100c00303035140500c1400540c50014091003540d407040d62444142e183c0341c0000e03c40c6044200400302c00100018040b8644072607031035040c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 577037167 1250 577035917 577035919
    0x30204030f03080f0106020d080c07110a140f040504110d0302240906070905060f07020d1a060102011b051e040e01030318050d030f05031b0a050c06101521051005 71
    0x1507662510407c0343c03a2407051550740001200b05000c40d004481800017000650702c592511000c4000b09001304030311300440d90159075180400000355020741407048407420aa04112800c000300e00c0c00d603807203540c0c60318030043c280c0c003a50b03c1d900c3d01006c00d07000b0403068000f0b200c80c200740380d003142c034420380009441821548030040c1d000340b6012690302801703080a142900c60040a0505084501151f44000c0d004400c00b13a07482040480200c01107010200c0a9600710700c6070048a01070320702030001900f9140c3c000700f055039a0340310342544150247c0c0032041d02c41403004001c541e060104544036541483c0200d801c58004201901c000100b09600544000403045844440100542d035400410180003515200170b03011030100c0b402e290801d840b0b04011640103900e40880301842d2600c1e150001950800e410703a1001c03802c00900d0405905c0c04000e0b00d03070b00500c15101c500b1054100b01000034902070710f403421410f01ca11050b00101200340c40700b0200b4400c044101c00c010038940944903200a0201d03105503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 577038417 1250 577037167 577037191
    0x140a021c02041b02070b0304080d0606030906050708010302010e10050c010c080106020f0604020d060c031b031a09090705010c03120e0c1518120a02060c060114121b01030204030f0308 80
    0x81060740c9083c9608a00307038a1a07401070a629071038600e4030f41c41c40d4001002110200000c101000a01e1f8461240d9006020785550000c0d50803800d1a04008658014001e00203011007600100010303a844500700719040e070103031603480300c9005400050f5214002c0d1402d42134036509112004a0081d0302c1800d40c0c2c12140c855007111000545000b5040c4c407140207550194000010609030b0002c10a5900103c841071828540003407064513200140e4ac1c0584e1000c54003001a450b6918520400c003001261300300f4020848850f8210708101d01920f5840c0100d200311070601080114407414103000e40351080821400d00760512100204441803610340da1840509407048244a4040400245c50010348003800004280f05c2142d504000411400c0202034049075824801c100791400103846034800b800d0f8620824005000d9541045403038400740014451080c00360481c0d4146054940000030320a0000e84425004501d4045002c01240a0304c500d40003d0030340d4030301001420405512280281c40b480d4807103d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 577039667 1250 577038417 577038431
    0x70306111e0a050a0c0f0813030c09020405010504050f0d0206160b1620100e01140108010e0d050f070f050c0906010206100b0c0312011212030504080304140a021c0204 73
    0x1441c000c500451680d40c00040b01805900d20403406900c030541054020f0f440280c6105296484001640c070a200c0300d281030091010820811200030358a801420202d4815400e0500f40000207041e4003451040074494200007a803c10240c541720b1450002a8001e0403555950042d10080b0720421100142160860b603500c001034075804104010010101e01ca41d00c0c1e002c00d100b2170181c552074012240e0124000d000d43c0e04201c82d200324910602c01001c12003000441c40009030340044480ca07074140c1c8040ca4690401000c1c40180e0004926001030312940e050903030f144c1d40c8031244070007140240031004010449403010001441400074030003801d8003040750612003968401004984442d000d80e14003d03d000007284c280414106100600384800c00c0f01c044034141a00d03001402c042c0d800c02c0c2d2151100b07201005480c2d0501c44103407510308400059040c24051814107a030750188031b101c0144064080c3c11840034030445a42c051000030042c0b40c008083d1003150415541e4090786840080c030407442540341c850303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 577040917 1250 577039667 577039717
    0xf06020f012c010e01050a0b030601080706051b0f030d0207050c1e1e060403121707090e070323071101060506041517011e140f060c07030611 62
    0xd02c0031080c0d080c00a000746618001c000b1801031002c407030048459500c50060f050564400d01c19140300300310560012418000c54011706040ca00107800003c00307600708000500800760080700301c816002c10341d0302c01075008102402446c14444a00b0300700c0c1031400006411000a10300303401608415000c1c42c1075038403a0600b2410401044240c40c1c0361240c04101c440050403074a007040c0c1c071301260001741c100004100303402e40016400d40d20a810448020541e51011400c0d40d03441030015601410b03017200003119052002d809008405107205a24900c990b180014250507c260410403c0381560720500f000d42a04040840324010101c4198000915400c00c070306d003d03041405031204a501c081d140038981410070154405c1400145541004d00c41d034000c50f910f480c6145002d20b4001d102305020f035030044c030040a0f002c54426107940085c001c0c4038211140d00140c0d4540f2100e4107064400c4500c0b6030340e80d0300003411506001c6176920142c0b8007450080d0704e0310a80905c800401310700460403080340d0400304030301c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 577042167 1250 577040917 577040921
    0x3081b0a0e0609030a0804030f05010c0c050703020409080d0c122f071a07081e010e13051f0f0b040c0c08030919050a020f090105010e091b040f06020f01 67
    0x30824400030304150128809810410010000d05a014040d150100702c06e071a40082d41c1c1c8241d00031143c4d0081054030317405124017031280c202c0b040a03610b005421110180c0340c0a03a25072407030001034400c695070030740041045081d40840750012202201481070130014180680501010880849920304004041801440d140c8a01446a1242d00b20414a141c988604140c42e000250300f15601c020540500b00d00b144a002400d100c0c0d00143c0d6403c1c11361510014400c00c00c0d000d81c0c200b01250341e0460060000c43c42c00c0204543c0300a06154803943c0c0501801d081d0300c0c0c64100c4400001480d030184d44400030b01c00355080b0700310b00c1030740751800d0081e40380070014081110501d803605030028581c142180300041c0342400850f00840c00c801111507201d00001c0d002d0a036003046004440310752180c4100303021810715000000000200311145807056250000181071700107407002c11840b075007541c00012081011000507460030040f460310a5142d40e190b8410440105440c0100d070301500c94515201d1040c9414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 577043417 1250 577042167 577042177
    0x40e070f090b03070906081008010e030a09050108010e0609070e060d2711130905070b120603011505040e03070b1602070905130210050d050a2c1e160303081b 69
    0x16174407091903e00d411070403a640d0704044c1c403246c008191104006091031090040a4505481d072000d1035a80103040c601070590040d986c4001c0c103100310f45004000042202c1d141c0d0f42c0c407003815110712403195503c01d0100d60700e240ea07451107903200d9008a40d594680e481d55000042c0000314504030003212031f0104204d4845052003c0007891414022003c2815042441812400a410010120744c5e4506607031114202402600129070f150740c04035071030101030307030841d101908580f0036030080059042041c03410300c0304441e82c015280115111038080f200400c08004503051b03d60401690300c940c2c202924092941290705080b400184200800410b0103103240c800c541c040c0119101c0702c060b00c005582800711504242c1c0a000910070140807542d02d442d598040d80d44549100703d00024500c0610b08402043c110000081c101c801e0345403001005c0d02000100f00e010082d00c10f103218040d460300c001903854051004030343c01c4200f4244000000b01030704603850798048e2500e13440d004882c1c020054149054051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 577044667 1250 577043417 577043431
    0x10203160c171917040b04080606270a1e09050d08060907080f07090b030f0a0c05070b010306090c05060409021c091a04060e01110d06060c17090105040e070f090b03 72
    0x41c00220b20300003440c0c030314013000140e0050b034003600f0b1613914a1900c100b90803603031050201e07810100400280c0c0c0b510042213030304070410442035120b4200082c00b00c5038604d802015032003403964a60b005082440d1200b000c14031031414000505c100982442c1440d01e0346410400040454038820100304103180c2000002d1045c4141c1e541d0801550380c802038003c803444003030316940a0105401d00495001c1d002401588a00c58203200031149080c40b05041c0200c4d2051004c020801500b030142c08009007040100d1811250421404900314105040c05040341c07d9a6201070382c00000002c0011300d00c981c1da006000614032040d0422441c41032602c2101c00d0710f00000d0010408040300761480c0a20320801c0406400c14001c00001810701a5600250308661294075100307002007002c03407000c02d1035049000b0310313014184501e03003103100324031941d10141c92014a40007a0100580810a20320030b074404c105550042283c0d59140b03005090801018108071700b61600c0c00f0010f400860003040500c10070007102d00441d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 577045917 1250 577044667 577044703
    0x180b090705032517041b05220b040e2a0415090c170c0403060615091503091a2a0f070f0804030b16030903020a080306010203160c17 58
    0x281c0300c11a807024284880c080e06100740400307103038005029291050300c52403199180001800001b8074209400c0e10b1030340302038459401401c10211710a844503120201d01794207800401c1020400d00010081c0240551005e075a2140c5aa01c442640c0f03e111101609096001800c044280c440d09001c15540307111419107829030040c1d01046908150f81c06080c100c84ca501e845025004194209144480d00b07071400d5010000200d0240b0138440d161094100400348880d0740040c8401c50700300508403c109100b24a440c07960300380030708501c0c0d002c1e80201c1901503020030306155910545d000f001c2c6143c3c01f9144010030300c10b500b088051403c1034211203a00c8540f03004e0101c0c20283c4031078002155030302129044070117000e80342c0d0160002311010094401f640c803030004030300a803520320450401d100b00668400105803c1a0304403000c82d0700481c182c00b1882d0041e4001e0342d01e98443c0300517855446024142220003140402400c00e00c03400c0e16192080d0b4020740b01c007001c89034546114942d910702a40c604d602c180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 577047167 1250 577045917 577045951
    0x280305030103020f0f03060906061201051e0c040b19030c03020306220605090930090607080f0a02010617030a05120604060e0703060503010b0a2607180b09070503 71
    0x1143c070005035413201070020100c410f41c100303440100b400c1501c00c1c0d0740c0c0304042e03024a05000c0c0500d000e108085d020184840204144e240c04000500300b0060f9103070f01c030321030512071000c5204003424008840282c01454056540c6080e441018500c803031400702200700207498150381012241c464001c0724040c80303000303100c40c1e0080074032030320403000701d1081c04503d41180d43c1c0c480c00662601c5001441388184040c1003d00b0b2044640760010010702c02c1c0c0d45118100f5014041d03c42070107980307041940c1000c9400c0d281c030340d1a11554031f051010f80c8203145000c12104408a543d1012641c1504060145e440b882408040070021136112070740c80c054844071801182c0240540f90b5505084006542c3c441e00013400402c81540c1e850512075280e8060314203000281c0c4a08041c08a8202401005010503003501c90480e064034082c0513640d020100b185000d0350300c0e41b0840c03000c00e40a0800410014141c030110003140400c400d084100140140170a59004400c1840018075660241050b83d100c0c0f00e00d215515000703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 577048417 1250 577047167 577047169
    0x30b0601050c1c123803011811060f0a030f0f05130c0f14010302090d0804031a10180b0316080312060402040f050d06240e091605190302030109030228030503010302 72
    0x100310502d645c0301340104013014403949036400740500c5516218042001094503168184505100100d600d000d025000802c02c2540c400c207070200315007100c4414613001802c0c14003c3e01c0342015101c4240950101405c0205108081100f018401001c521580b454001c244d42c07040218852600da00c02c80c0300c83d1510b5282c03804a540a50010800180002c206400540c002d0381c2c0d02003e81c01940003940d00e500743c81005048102c200c038040da003010a4006c807503825841c06c1c0341c209819086120304007003191954402c0d0b0880c6c0302080322501940c01c03040104039960300e40040e69540d4000680c0e00c1144440c24005c10181d040901c21141507440114000d0303111410501409400b48451004945481c1d6803203200c000c0200125104545c010003c14441c81ca500d42a015480f0060150120341c0a401c0b1008241444130002c121204840d420341d00c207502d4600d2240301900303030f40003540065015400c0040f0002015404202828441da01d58010101042000d01c071040c2061034010040116200300011702c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 577049667 1250 577048417 577048481
    0xb010e0a06120207051e0f0309060409180f0308070e090c07030f0207090203010b0702090901180209072d02060c03131518110108010b070b01030b0601050c1c12 70
    0x142c42907800016250a0043d0b6801d46010801034100079003420380c0311810042001031144d802a20113480c019801c1c18011400a2510b1180c0e00c2030503419581c444070045440c02010188888981003903040f110401c00c0e040141401c2800c03100303032002607800b0010701d000d407600462842c064200d032405175041403465a001d40310000000d4800f001e40c4030380200003415280c503000450180c13452419880d2502450720510007001c001504003c010f17410080c0c1c01021000c00044025103640483d0340c0900c5445910007070f200d40d0311004140b010402c08031854003e81c01d800c003e610305905542d08840321581c0c0c5148585040c00169444018042c0781755401340440c1c0700740d4542c0c8083c05020780001c1e1064401254158813450202d08a60942e5103084400e502d40c1c000101e14011b109441003586000c00d01c1e42c400100902c14007000702900701074004941c140c2d00c5001502c04410406041b02c406e0500b291861242c100c00c0391190001a2400c1e800d105000b0090147d0031506000c1c6515001f1020200e1a03048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 577050917 1250 577049667 577049687
    0xe0a03020c09041a1602060106210c09211101090302030d080a06150f02060106021c0c1109190b0d020f0111101d0610060e150c060f01090b010e0a06 65
    0x10788442102894104015490510382c00782504116803003451000032000b170301f801d00c1644507001740203406a40315038440780441c402c1c900f140700c000001a4100030010035a01c20060f60800e4035001450314091102c07000718540c62800c1c90040b40a1580070700f502c801107032450481d0000030742540010240f006036502071400c01d50865000a00030800e203442c3d280d010990889210183c00042510102068868051101a000d09a148040e206250005a20b0200e003807140c0e520780100f290410188091003801c4601c1e03402c1450080c0182c0b014100340140512003080c40b2a068111854004466002d00e42035912145d01907019240384141380e0030a0040d41c1030029071031609030501a5020114144045100e1003811044001c210b9419420321501d003881c00b003006040030805104070340c091048075005102c2c00d44003c0111103103e000310010421007298081c40401303662502c10341d02400a50304510300030718181d8003280010411006803100440700f003000c103134540741c020b0303054001481a07a206500c1c1c1d007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 577052167 1250 577050917 577050923
    0x1080a0605030102120609070c05331510050703090911070213050a110f0708030612012a03141504020c24100b03150d0f030801090e0a03020c0904 64
    0x868680d01c10100e42643c1c80003a124100380115070401c4a1468004d030455000aa1468505004086695159a200301207861400d0090700c480180c044c9503800c4070b02c1e020a00c45022401054181202000800500c24044904c20907040601800d102d214600307441031280c041d515040e04500d00381c0c89a00410845e01e0032010031004000d900b026880354180941000c1c41094000754900d8012002030450b04240450f02d1070070b40070005480b45080200c00d9030082030300420380030740e244c45803400541f5142076010540e0303003942400704405001015003d100d80b050096400c8041090b8140c10850889004800c1502d10051801c0464004241c0c2541010b1a503070103000145004070300e16800340303020082c02d060809220f07600c407103071001c6403411001900501d050301d9441c4c41c24280300a0079462b010007000e01e044000318910101247c0c2c0c40c1200810300941003130b40c80880c2010350030014950242409050081410400c02c0800400c00081c02045c803a0076502903e02c1c0d240c00c0041256002000e0420703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 577053417 1250 577052167 577052171
    0x601051314040309030209060f030606100c0f08040303022e0504030219050106090c03051009090c0b030f060f10021203060a1502060103060e192603100501092301080a 73
    0x2051a4032001000d040c00b40d40030b0f848806600345148100b0414030401001381d80580008140305503680c40004d0900d412190480e800c2a0112111401301d03812a01c800024103684006817415090203c808000c2043d28003039402d84400c91404900401c80d500301c6003000100d561410104a10301030568000d9400500ca032042d00c0003141c0241000c02080401c4c241594165580da20403c020400c0b48503030765040c04035040c00c4c08285890134020785420114801c8200041d1507404960070800c0355103d40001d0800c80e03201d03580300d0605508441340d9160485009003c1e40c655206410a46001d0410303080d420b08a42c000e05540e4408a6501715580000d4401e1b40c01180003407000c1003203d0b40c5003898001e0340084c1d00030282e641c03460034210181c80e20080c038114950401c12802180c0c0300c107245d8283c450782e040a5408182c01c21243c200307490140032010010701c02400710600220140e518043c1044440076660288000d40301c042d4180c0c4c0c42640017030507d180c00c02c000c0c0a4401d5019025460340b041500c1c0e40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 577054667 1250 577053417 577053431
    0xf06051f030b041a1f0c021c15090b06030a05061609050406060c17041409090f0d0905030c0102070e180a080d020a03230c0903010e192306010513 64
    0x3c01c1c29503070300c41603038500b000b4081c840a00c0c1c0e0409070301009542008480120200c91110300182440d460032034003030701404103621403107010610b901240340125031140758030010883c0c2c003000e80000c0c0001c00d41210b0041a00300455000e02d00040d0390300703001c0e030071102810700750310360392002590400e162500380c062140c2401c0002c4c0310b54551055000401040d1540c02c04c0340141c0c5403116425082c959000d08003001484240300c07c0c24003030f42c2c5000008003615510026151500d13103504e80301c0c2111f82000203105404c0c150304190743c080c14080403240140c0071141d58904000069031501018000d64070641c0180d0300041440c5811450340c0e070403a01000c295140c048841d00c0d80303074069101e0380303100e1480780c0c00007040080e140d490310074003044000640400f8618610022640381a003030183c40c0d50214540805c3d040003958080d031040c00041c000b103003103d040412084401e0001c4940b00000c6d0381800305da54074000101483c002c80700e980110113011b000075a09043c01c01140d04442c2842d07000c103a42d40d0f02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 577055917 1250 577054667 577054669
    0x203070e0a08030703020c06040f050603280f0c0507030509040c05120702011407140a0e0604050d030309050c0409030801030311160905061f090306050c09060417010f06051f030b 78
    0x400e000107040d040c07000d035a13034000d281400380c64403598001150088100300010024928582000810740c0c030122002c99982c0c480c00b200b085001080000020306110540c0391042c1112203031300081c41007840120900030456103440644880c080d441000d030100740d00b080409614a4154482840c10307a040c204541820100e40e4821140581150b88002503035440180c2c03d0138a04443d070035030780241d8914020401108684d80040b46010742c00480b42880410042c400b100d50b5070740305950190501411100401c1141d040027000351205240540703450150040e060300d2400d081c0034100003283c00d920703054156441d680e4111400b840c0e402c800350b014000d0681222610151003c544000d115003200803c140c14038500300300008040c590440c901c00c103450400f102c51504101200308580c0c00c020001060365411000310302520800c07280960024001402080b6000c1000b9107032116910340008120710489078540c80304a40c5280602c0c4c0d8030494103901c6c2c5600100e14060007025289500d804251003078040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 577057167 1250 577055917 577055929
    0x40308070c090e030a140a0915020703080d0f050a0b0901060c05030c16030b06240708090d0b0708010e060f060c0f0a080406120b0f01200703060506040c210203070e 72
    0x2250340700c09604001044403605c1d90200300307030f090300600c8002c2c64602a0482c40c080d002e4034141c4254545502c1c120485100103009002c800010341d003244000d980c076081104a94010a031040d82500c80c94504404610500094400c0010f1108060201c0d1724a0f4280581600c0d403519256088800d803204002c07000002d0400e2103602e5040b420381c900800150304510b4214072540b001400103000d803102c0100b2800d000c0c0140032a180801d46600032569480c20f90811400034441c41e0311040c0c01c040c80002c45020001d0340e0904a01c0340f80280d48090203647c8078101c0e511440000d554150740180c070020080c00c0c524040b4024105c070864003044840701d0202ca1901428020f281205031540d090108080001641058603034041d068503000c09c0000141e880000381214200d07010990400c030416003c041c00b80f003601442890a49030f64229100a42d5a00c0c000c80038ac1001c07501203025504140043c0c002d0b50003107100c049900d06200040b000c1e0807a00183c03034000c0d003000301400c2c104500c00208403010b803284 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 577058417 1250 577057167 577057181
    0xf050a06110909060d11010f0203040807180e0316021905040f090b06040207031704020a170a1101050406171911071214030a0f0f1b080a11040308070c09 67
    0x241464584500c101020043d940e60024402ea001d81c02000c14100010000501e00064500c2402c00508000c10090b040340b96001b80d03000507102d88649032010660009064400920b80750102082c8892800409050b0b103d0007005c44114111340300d041ca01c4018a00348120421381940c1c84c07006281d4940d5200004c069511101071041420307598240c20b02032150721a0144d512803000d83e01545865584e80d40104006064220303020b244880c10081000c55550140d54002440320944900c640d480721001c8a40320710300300c00100c0d224a06544240784650044041e02d00301c401d25124025907040360400b0070005800184001c0d1084803005e20b036501d0174410720490074401e290010b065159502407a01c0002005a0b00340c00703091205070010380e47c0007000402100d9011010080c0411308609030800000a80080200041c17954204070003114030011416a01255400e1503852112075117441c6a41e90843c0c5c0c10114010b000d080411091000c500d4a50040070300714030506242e0348195581c2c104104503984 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 577059667 1250 577058417 577058441
    0x50d0f1803020105010f0f06050c01020705010e2407050306042c10050108011401030320070308091e0a1e05100804170906190224180c0d0f050a06 64
    0x40341802040c59030900c189409428151461001c0c02e05124144000420b280300300c2081100000b00341c0010642034040c0c50741c2991010082c0f0040c90300c0000c0a0b11016522035103054032070a420103800b1043c1c0b503500c0d1800f030f96460300e4140c070f181c07234407818031010f0320542108940c19200b0405c810b60050078004001c0d08521240090300748104204008800d03240181d0014130668104200c01034080140c141440c1102e606003040c1c04200ca40c000c030800654400ca0f42600b05000d511800010b12402400030040c002c000c42d11341c000800ca5102d1340c0f002c81c03145100ca41d045100302400b80940c041c4003002c0909500200c4c1403000705940d0708001400d01c00020511400140d0702c500740f1041010651070000400f060f1941c450030150303408082a01c5000b00410f0581c100f0186145407c2c5500a0014400300c8186d0800000007541e01d81c0900b881482c07e075455804000c1103008107604407004105004000c034002c000940001107074849403945511070100365070038001d509140c00059818820030501e148 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 577060917 1250 577059667 577059701
    0x6030f0403051c0b04060f030b06221401060e06070f0308060312161103030f0307031505030105390304060518061e010b0708120a060812090307050a03080406050d0f 72
    0x4013070018401501c0b0745902c1020704207140c08042c0001204045010b5004134181d41100009050024000ca150818245808028941810b0b8030103c0541e02c80c042c180c8205440d8504040755a0040c0082803044c0ba001500d01c96820001da80001e01ca00c00f1540c12400040444208024038507000e0183c1c0e00142d600301040e0441c41d0990b0030840b00342403846004504402850420065140d50651480002d001404140d40c51040c140c030046280c0e400400b911000d8000c12691404070065801904107002400c03144241c1c0c02800c240f412186084c910400a0304415070850719a51345070009404046c00f0501c01c10110001090070040403c809482204190900c0981442021803030068040c103030048001002e04004040c08604004200d809120400f25450100d903a042508c200800d40ca40114a2501403480c186805d842104003414600008400ba60b01a5030703070300100840d4080e14800100048070501c0100305840c0030301c0240c409444030342c8003c1404d0b80444c503400129612000c1c2040800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 577062167 1250 577060917 577060931
    0x1704110621180a0515070203480a0308040f02090702030a0f0e2107030213020c07090e1513020303030f091902031c0302160c0501020f03030606030f0403051c 69
    0x460940b0150408a0035801415510300c0a0702c60648884034401048003000241000c1203000d403080044400c0b5201c52860380e448005c0c0c1c1540c049500c84250031032505084503200e12140c01e80f01104090101001c50000e2848941c540c2e02510207400040040d00c2181145422201603125100b90300e10492250380a5a0340b49d101101c0645113800c560f07110010008002d1500d640d94440704001620240d4416a400758072848031041c03450034925820080d001640e501c20000d0020b5140c0103440c2091034201170300d42c001e888042c0042241c1c1440c000c80c9080d80b1504425a000310410001c2340c101c07a07104481d194000503030300031901d1580140c3c3c120305101c1002080101440d0240441d035002400c81c0c048111149a640000b50f550759218580c41c00847c51148003404140039a0454001d8000c903d01651003e01ca4241103402014910440e07026028040c160010f02e0742c003204403480307484018021030845c3c4031200c4a10558500034002c80900008000403000d00840c186510b07000c80704500045814 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 577063417 1250 577062167 577062181
    0x10e220615050a2a14012009030c010e1027060c03030b0d03080c03371512080f0c01051303030b0f03030f030a021306030c0806011704110621 62
    0x5044d448680c0c0f94408001d01d0580d00301c0442d840c2d000f0350280c00170300f5258690100b0b060b00d80181400c0122030410010040a600c92018000160074080022029580342000e914010f44240020030000c070f522000c0c075009468200d005214401103144607001a09401c0d09030725140341d0b403011581000c0b0100713a180c039858080691502540d1040d801c00d8a040072641b80c240d0700a031000d140600440081d650100c001030621120300c0b1440030510140780e01d540c11241c03a010051001a215040c45111420182103072200f0b0358130020002128040c1c12a200d510640303032513603c1950443d05002491490811517203078692401d0003014003410301d913203090070b80350f04503e405411258480c8403680552500c0e011442f1580d008002e82c0c3d81c1d540006043d59680d0345104404009120b500c0040e2410082c3c0b0748041078541d8154490f10708120303903844595541e16000d005644a0400e041c402c400c18108600180000b08403442c10a50703100c0181429051480880340503155104001e050359806a40c2020007450f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 577064667 1250 577063417 577063427
    0xe120f071a01030c14240d110306040e01150314011e15050915010e12120304120903080901050903070b0c010209130c1e090302030601140f010e220615050a 68
    0x24185e240d01802588521070100350080c0022034200c030780310803008920f4191070000080354003082100904120303910079503100a03016002030700d040703000360301c0c14110303c401f40814442c09542074200c61301041120f00d15610140201030a4107580199503c0d040b0701e9600703c005203500107102540346d0000c203090704d00342c02120f004031240e0300003849401060f0034808071809000542180048c01c0c41c1454580000e500461095903a80204000e00d104043d03030090140401d2000d50b002e80d22542c0c00030b88400701500304032380f04422404050000402007010583e1580104002c040c0208040e0550b4416980e0b1980000c49801152080c800c994000840342401d240414100b80180d681d44420019650030344002080c2032480038441c10f400c490b42e07007103000082c020f500900065a0007803c0312060b684942c0001203038246400c2c00b0b40a26070600c000c003031a40c050016032040400140107000b0044091051078000c0204002c00d658240d03070780101151048200300403d41181d860349070241da5031250100245 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 577065917 1250 577064667 577064669
    0x310090e010c050d0f0e0f010c08090c06090103050405100501170c04060b0313030c050f070f0b0702010c0308060109030602040815060111070306051b0c0708100e120f071a01030c 78
    0x9140e458100d034080b6141c0c00100703407122042218000038003004000c440c1401843e4114807001d542c8940c44121031084815041001451080c1c4d4405183c0d0f06c9420200e60750b0310101002030361184c03040c841c1e03440551180e80305a61041c002d0b030441d00c0400c42c20011104450007a004290b40c0c6813207100d00200c5020400c610131800000341c9040040919283c0406c40c2c5000c00f600801a9110000e000f03c00d140c4580c1401d040070743c000007990204101d030700600e030b50b54102c0e110701042006030440014104000c90140c17003419806858003150800655000c45542500030100d0781400750141c80800070030300c1131000e40040d12900d40188650800d9952620389003000030040c60422484003900306a20700d0100e140802c0b60b0340000d012603242c59105851480400d4010000701440012820080708500011400c040315411019141001c441c0f40d002c03025102074a500504552011003003040009032440281039034111010260f003810115075800542120400c1c1c2032034000c1c007220040c01801504024a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 577067167 1250 577065917 577065941
    0xa090602042c070509010c020d020d1e1a09030901032c01020304050f07030c06080a021b10060812161e0c0602010b0105070308070e1206070203041a03091e0a08031009 73
    0xb5003443e4070b000000304100c800d011f0003400303490b8444502d000c6441d540c1d660014240e000040320000c01d00890b0881c0208032295064544038211f0011130507001214480a0003040d54a01a510b84000e03000150080e001642c6070045426150340201d40026005c40b2014020007600c00160350303407d007414458075284c000315407603000750400c05007040014800c5005204580f001c0c00e22041c0b980d100407440c00280540030290540d1203428600400210b004183c2c4c1d03120764001e110401c2056126003030700342e071440c51544001c05104c042052014150240b40803514251040c2d001c20500c1801a00050f014503a0300001c03102f443d0203071000d00c1000e80a004a60242c0020300e400e07814440c1d5510f00411206014100009000b04400c8411017034903140c007045030700000c0d0000c0356124100348500070351380c0d8043d200c3c03106501044840341e0107142884040703d01414284004016281031200584500c04452031200720754491249200d0000742c40801440c41090090614890a4a49039041040e215865001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 577068417 1250 577067167 577067177
    0xf0314060a170102040503061e0f0712093008011502060a0e03090a150306090204080c120a1e030e1f030216020901080d0e1005030a090602042c07 64
    0x40d58a5509a901c116840b90040308005942012403e0080c41244c1001c4d800d4000c0f98200b190700300313940d050506084021103544074186d80d900c05500b4042015120440040c445051104490005402503020240501082400034000380c009003603034500d105400030041100448600c0c01c035000403102e40100109014102015030041c4020349425004043c0390f00b880d0340f54450707802d4210400580d460b50034003501d1030a4940c0ca0300440c080c441d200f4000400064104000814007100c01e0003604c0c101d40d041c1006159800c000004c200c44c0709440040c1c07580e07500c07442c031800d00425182c0c00401100c103c00144201d030a8054200140300c03264600d0140e0150916031285a12518040300040c0382880518005072190042c440c0e081480c200000d000e0b60012031075001003141c0030080b603080d030080341da511803040c0541030320240000007103034081c880003146d02880060880c807a00d4108058691241c600145015100c56281070421440c040c0310709295482611001c01220190880d03410003068108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 577069667 1250 577068417 577068421
    0xc15020a0305030a020706090b0f0103050c060a05181810231c08041a03010503010515090c03072003091801140609030a1a190207200d020603070f0314 66
    0xa000b030310004d40903400059001581e1070a00c900e0342e01401e61154030160345003560400a420680800e0b00b0700054480e40101c01801440b4034240089504580041d161203040141140608500c0c0032000f140303070341000e09401048002c450304114180b20720006000c0b080010f09051003014045e548551046030403c198107042000da0b02c0f40440d0003111a034509481510b001403420013124002c5500ca450310f0707200026001381240e00140994103170b413000d400801c10395a074030342c0e1411030ba80a03070206501300b48900c0105903100e4180005590001007400c144c0444000840b07112424881821231030010b40000c030300c4983c0c4c0d1a22a11020304000c00c0307030b207414541d4148208e0740e020401c110300e864800d0100042201c00da4070240204504581c00c40c442c0d0708000800907010070701c050300321400100c8403612100c82444010034402d0301c00c0d95401041d11103110103000700d00c0c4804e04100c40e00c65840380b031060041006a6654004606c14a0160307154003440c00900340c040c00340c2d007603d51850180715a40003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 577070917 1250 577069667 577069673
    0x5010302090d080d09020907020106091802100f090506040909020108060d05120c10020406020c0102071203020601050d03020a0c090b15040b0901030c18060917030c2a0307030c15020a 80
    0x440c021000d8214180d5640e42c0303004104d100c020215904003c2d00008000c2c2041800c0380c06500000c100c580000d402d0128041042007140300b1616000c000b90b001420b68a000c6140380b09072000c0d50101e0700c0c0e050410b0415210740000300c1d80c1d00146e00c6146881d80719489007007156880f80b05182c00003415120700c00300380724941d41c281d25000403001c100442800032030708550860081084105051540c2011941d0b41d485400094031102c0f2140600d0140c0704802001528a5081d000724441980503409041d40342d08101c10854001c0750040260b0071485104618400315512001907030040c40800d00004480b070010081c85902400282e51019100c4140010403006000d081103a150344807d281c0001c0040440100b952044038004001003c00102400498105d8200c1e02c5e02040c1c0e080c0f420f05101c10450445540ea40303126004049025400091001ca41c25058460303a100120a80d1104c142c0513a03824007291070102d80d0345c01983c510f81d0b04441002050440d6000307031904042840a0a00d400f090b0b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 577072167 1250 577070917 577070929
    0x1801080712020a05070813081510050904031202131a040602190f0b0f0417030448170106030201020601030308220311012d051b0c03130501030209 64
    0x41c15803900903000560b0320030051003502100c001c00c0e80304040c40d8861015809003c4141401d00840c1c140b4403582910342c0d4460140c0030054401d140c01040b240546051900384551759802420860501544a11203c6100b44c640003404600181c1d24401d41201e25015a2100c13071090745c1c80403204544200020700496502260b010804658803038000b144005510b002d0069200c00000603064490903010710032440314074180b450065004091500400c48200c040480c0c901c0140c82c018070711100b96103601e41e00c1034021058819080c003007030740c480c80d4958902500300f01c11842c06208818030071280d040c01900c2680301a1f03906039054400800c0628110340c0045d41d10f5906001c00740a00c02c59000088001010720307100e00d050401c640d4186085019480d02500344030a05c04010941d50900903801c44840080c070700008103400302c8030345400b54142c01044000a02014250140e503d0448003c411300a01500050003011b10710f00085a41d100614803070f00782003c454004c1410503004004140c19a9507107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 577073417 1250 577072167 577072187
    0x30b031507052b0903020708240103030c02150414011202040b030606030a0f0204230f0a050105070507050307060c150606020304090e100f0e153d090218010807 70
    0x9081a5140000380754150403020040a04180300f500346000b840405074042400c074106c03002c1400312172881d0790061704030182d09402403480200758203a40040000c0f034418151201c10500207800101d117001900200c4819034400d4000355559001004030b1085964040700c407400c0070200c5c039811406d080c00d00e4841440c9201c0508401d00c2228040082507100c03803244d1000c0e00e0070740b034003804640da55514603410303003030000060440c0000c40352042c484000b42072214030a5801c10000b0040103541d414800152003940100c5000e031041d1242c0c0c900441c890318204007000240c5103d441d1000403401c0303450a02842c040c951440840c1c141845000c029030358000041e1015203100000200b410014180380b24500202c000c0c050054509015400061303ea8030b03800400703011024025141303400546407500034000030944400e200701402c10481444d68920300700d2a00f0100144c00b0361000c9684074600c0e10255807058200d50001540011031030010401c19a81c000b40007000e0074803c0c0b0b01d141200c2d01138000303804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 577074667 1250 577073417 577073437
    0xa2901261503030408071401080a0c0206041502091207150219080a0c05032b02091e060910030c020c120d080a020d0e01020c1b09150a050d03030b03150705 68
    0xc1e001d240d150341c144103a80c0a4084001102c143d6641c8040844240c005411103501045900300440c01c1c100c010f005182000b800d82d0020030f0940c5480e6100806c00c09401080c1070559824007101500341c1d207070b076681032180340302200519505007440340d60100d0003850081e0b0380540d4072040c001c0141c1e0002e040640c16464100114544501c25000191440030300c15200a150740070010312001020400b0804000502582d4901d140d21064040108202d1182003005644446500781d03102203100c6001c070180030a503000c0c1a01c0d0900080b10007050707203101e1905682020a880c0d40740c0e10b101c50750400c4001030705c1d80100c5180a951110300c980030f46800d1150088010404001b0016a6184135901202c0c16400014010032808001c0307058a4002e4100d0382401e13810780a1190302c072341011020300010024200040440080351500004000c9041c40c49a00f19006041c2000001d01030b601c0844200a103406501d0200d19843c602e020942014003904404c2001c0528005004070301d641301d420381c0ca181072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 577075917 1250 577074667 577074691
    0x20105160905030715211b02280204093801050105040626100305060c040602030f0d0b0306010b190309031b02150c0319020d0c06050a290126 62
    0x14005000c9810b2845031000783c00400646c0071000c83c035420b030780c09008040641800c0d004001300c00340c0102d858030f294000107011360345148090148880c92201080d0b0040c070040001545034403d90721b105100581c142d0044100c10300074002c401031021a02980e0750901956040602c4bd030510700007801901550250f40c00304044207080780030503002040020031004a0040c0101945494828041a020140411250ba00400000c10982c140361400d9409840c59a009141401c90603811081241c010380c40304000c0f40d498035a0b802160f2001e20125003c1c251a41d9040d80e10400225040541c00d541065441010325101d031100100340c0c00000303a80c00b90040b080d0100000d505000040401031606055541040001083e070080c0400000503c81c1c40301842d000c031903240c4281c074240e8031400c001301c528010071a44180300c40064201d91010f40e1000c0f2103034000804042c0c40c14680e03c2600b411514401080000d54030300030782d42e0400ba00381082d114059030b080015000b00b440030460340000c1e1512292403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 577077167 1250 577075917 577075949
    0x4060504030809010c060912020d0315031407180c0f020606090103022412060a0f0312080c0f03090a0c05030703020d060b06091203090906010e01020319030e01020403030201051609050307 82
    0x103841740031541c90300c03038002c1028000e200f03c1d405d03c4110740c2101c810303800140c890b0200c000d00c2c5501074094a145441290f180880c1075141d41c48142403003080c20010b80950041c0200803452503003509030b0400c0800c0c5d140c000070f00106c680c00085d00345982c40301a0000d40d40088100902a518a040076041d203034141c4031780518003580641c3e000b2800c05103c20f401405408680007528600f2940c810307104220480d80c20461580c0c070302e0003240840107400007034600031102d00d02c04040e0b40548403a42e00700c5154102246003000d00c40c4681c0c3c554100f0303154040d194202020300414411440d1f45c030006440210041d24140380b07582e00107130320049410390003003503152154004412540c801c01550281c000c081c1411880d41c0321006090345030b40c822003403e48681c030031a0124219521508000709400c01c180c000b10320340580c214000600c80d03010494001059201d82c00381c9014003080c00078000451117500041410704000c0d45420000003c01c1ca04e004000e00901d00700069076000502e24210760217841a05448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 577078417 1250 577077167 577077169
    0xb06090c030a09260919030c060f0903060e03120703020f042c0423030306100e0f0a0936020915180106031406011e111501180204060504030809 63
    0x1a540c4c9407007106040c2c0c9155440300110391448024038040034100c440c80c1e0000311500c40c0d4200b4000c1030101030906403c4070010f104003801110545121200c60400701c110300d40ea980e0301801d803010351400813a00c0c0c00105225501a105004541e000b040905042d4103004021a0f580d07010f00592142d00380040d41c10052640c10300c3d803841340440f4800e5240868110b4949428104c90300e05600115a104000c0030190020840c004000d41e4001c820050080407040d55003501164102d6651030031a81c08000400c034044196201c2030000000c1640d4100821001840c1c800c0d521000c0140c0d06012038542c101c40d009180000003c250203070b840d4102c5403000079444018076000359005007c030b01a00120700400314112504228489412070f201e0756420701081e0001070711030752a040107076005804241103016201e6012030004a040e02d20300a0b1514880c9a00c64030f00b054500324006540e42c4011402100510154891000264025822450943c502858404020708500c2144006410440d020800c281a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 577079667 1250 577078417 577078433
    0x5060f030607051b10051b04060f110c09010e15090f010e0c13030501060302040606171623040501080105090403020a080a0e13060612090c03021216080601030b06090c030a09 76
    0x191030806800c4614217580550010700038442501d025a100b04103140304500d00d072041040705c041e950a50ba40d05440007210328240c0718003100c109a0000e40c0100013000100da155902028000c00028040500604001880d201c0384103600752124040c04880303040082d541c104008050440e1000341d0042819a100d011078010b0780500001c4017100e000c0d04400000b80b000541003642500c4c001c803001c02c111070391550103a130085001811025101d60f40e100143e2028110000500d107401179041242d01003c9009411041d101d9103400c003a00140702140a00140d680002d070f00e80034100549a5000a00b82910041e5035180020030003041c802001a61181040c840e04a100340c00c80e0142407612000d031030381d107240060401e90003440001114100c07800104401070003a813442c590407483c5400514115028001d00e0503062444c0d25080c81030428020100e03040300702d008001e058001c007902d21541145091341c1a28809031060380b00b03118060500c402042c500b8100c1e41c001101d00c00001d0415002c1c0b8049030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 577080917 1250 577079667 577079707
    0x30c0d080910080106030f0203160c14070f0806060301020a050f070c0e090a1104061a0906130b1819050f0111010c03020a080a060f0312031118030105060f03060705 72
    0x500682c44881200c0340303641107a0698140c0388280c4090280d00c0d52600e00104034003040341c60905007520003503120002c5004a00c4c920525014a400812105c2480c160307a00e480d200b03030b220200c1486218003c02c94003500b4000345030442821002580f40c0f50792000d00410303d004a0701614003107400060740e0010041c00e1a00b4000904c10086d100c1094503000a10948804d030070303001503c603c208403031041d01c689801d1207140b068451103140066101c2818070b8290b155082550a035401c41000c11407901401c100e40d42b1074009000c202041591785c0e440ca400d00f51250003050216004804140510614840e004001c0d815104140c5a8042c050b0740140122100062507010642d594a002c0c03080a0035580350300148203241d02500e85400d103498644402045502c1481071540d482e85d921011300001d40903d90b215002c1d52103103400b00d4180c030105483d4086074003112198460200070359a03804030b800e0a0050b5580444101e070000302108807080841c0d1034010092044042020010707481010640c00361100c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 577082167 1250 577080917 577080919
    0x100e0a122001050f0a0c0206010303020304300c05030f011104171005071206050303090d1407151d0910090e0a081908060a14012a05060a051005030c0d0809 68
    0x3c081400c0070010240c0385507082e83c144422508160069000f07900000700d950480394190700075031815141014000c004121281c142081a224400007243c48004030070510109010301c461080f1300317140500301840d200740c243c0c2c00c0b41142d040400340300580d5140b1041e102245c2c02c6030400380c4000c0f0030702c0245040c070162101c0f47c2a4149020184009103500c81c00345a94240c450b40c0c1040066115020140c4c0e03805020011a801420080d0303c0001500b00744d4030074640c0181000f02c6e101561507500012410b5070343c4458400007038443d41c01d0302c3e044118400303040f1141c0064400034041e0410811004000a0b14010420441e03162101084e07484420048280d80b15000307024141c45400f08610884500e001849004c00101400041042480c005602008036103001c08850030007400107005559065003100c46440103099000070031500c1a0038008606000e1089020305001d150004002044803000f030441451420241003d03c082e07140000c034448009421100c90700008080c0c5019038061248a40c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 577083417 1250 577082167 577082171
    0x3030f0f05092e020d110f0c2a1e2806020312010e0c04050607080310090608030a0c08040b040b0301092316021608100e0a122001 57
    0x314010390000d90085000c0c004500584610b94411101c1c0320301d41d0500020300b04095548084181c00000e40d5008041190842c000403800c3c00b50391080c0480c42d004521507a10709403002900d440c50030810302400c0c2d00c4908801148009001400c2e4443d1441d500310f82c0c1c1c900070b40311244619800c819038040380c44092030044c618552200b0895000110901203c0c0b4a034441b500702030b0100d0b0007800031050f0754500700c0e00701e20035095a10b407015220000ca000790144084400c2000049a03135201d102c01040d400d070141c074409a0324204410454880c250170b9001700000e9140c007078144147c0501008a074541c0c162450081082d008500b0f014045100d00c0c0d005103a00d04001500140c26803818002e54100c0b000c11340100049071040c07102c40070008100820328514049203000500c0c0520550101703103c14000d02c1181c00255245004003403900094210811380d030710100c100c024404480c000c049180d40707041c6c080e0517070f840d00c0ea484800104444034448148021288484190200a10030300d49034460306c002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 577084667 1250 577083417 577083431
    0x1020307030204030c0e1e1909030801140d080a050f0408010f060509130809091e01031119140405090a0c091d0c01080a050703020c07031101020f16090903030f 70
    0x4040e000f0340c4248821070720310340d845030300042c1d07280d401e00c090b846034a2070b0070490842617624140c00389a203801013510705107174070713055000c41c07222000c0c815086150301c01c3c5c40d0700e08154148804260640107020005116020b81a160702c009200c14040c1c4504600f01d0034102e890701200d0051a40c24015600100d81662030603c01c140400301c40e8100204880080c0d0b80090b050301c4510841e881c480940401810034003003040130103040d041a80d40c1c01d42c0501600300c40103c1d0106110410700004083c1c5c001c1e1350a141c69074140b20a407800c4481d12a10505a680581b00c503858588040d25034030064000a11540c3c2c1d903000034020600901c8480615580700c61860151611462000e004014003407071040d010301c0c00003c00103074040000d001d1440101c140c44250310741c3d40360060b45002e408010000010980c0900100051800800140f8051031142021084410f5550f00080c90700700031420b007003c581e204070340441d028034102c0601d80990304500710110b01c082040c00c041e4041e1010b40400c100d20713403801c01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 577085917 1250 577084667 577084681
    0x19080a1805010f0b0a060c120909020309071a0c0a0b0402030a1203061415030a0c091208070b0c12070c021f020c040b01020d020309060315042a020607090501030507030e010203 77
    0x1001010810400c5001c0244110316801d01c02146520302900011910064400c0080744228040702000c82c0a07127884a4180c1c0c4412000341a60800d0352081c109521403c005e0141c0c02c100458038801d50740901c055030401144444681e60741e02d000c078000e0040c80500e40850190341b130501010100b00e4112004850240340342000074020300580c82142c11020060610031705600c0c084040d0f00880102c0c908603403d640703504200b08014500c4d2801c0c9803e2000d1070400041c805800c607d10030310300d80201c0d122901c905603410316424440c1c0003401a100d80e4010802c04002e881d4200d242c0b03030410741d50328201441d94040c0c80440c00f45181502000031481903444540b11440c2d00092280328034605031401d1019000000059948a0300c0c0400350025810900c4030f03110318205107000e035038002d01060b03586445440080c041800c4400703441065180e120b000716038030100001b95a410102c40c90a1005140c01d01e440c100080c011040c60158030304140e2124045401da80c401c0c0c01c01031803000c04500031592814654 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 577087167 1250 577085917 577085921
    0x50c0c0f0d1e1e0b09070e0403120f06120c050d0203070e130b0a0605030d030905190c1706041e150b01030906050c0405100314010501050a090f0b030f0a0219080a180501 74
    0x441181c1c1091241c0004905da00c000c21100102d5039070074103140d8191100e550a42d141025580900045907481164184a0145000303240091001c241196171125140c14110740320507058100030700480381c0a10500060310000740d04030444a0541d800017884d250b0184a601c0e000302034070b0142c1281c240900b031003c0f480c20707a03128030304513401102280c20026074088250103584c1c04400140c19a00311042e01180f40520401c4494010f101d103080081031030300c4500300d0014907160703541e90078030b948420104000c015840d280b82c031540392140d031401e006591035035a14007a801c0c00303140d60000c0e940741c080c0200664000d410000803141e000c007003030256140184400c00300342c00611a15105500280d01c0905160181c402c5820041e145800e101c82c582c00c01c40155055800460080100481c1d040f00080070048007560101030050750f03d1a644d02d0800e014095208140a0329408d5031340e20403c51036004812031507902c5011034441c00c140302190707900c0d107001c4020030581034903005440200607030004210043d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 577088417 1250 577087167 577087223
    0x72105070306140f040b0a0f080c04060605070b040f0201050702060d2702010801030809061e03060f0a15082205010f0c02060402061209070b0a050c0c0f0d1e 69
    0x281d8080020a9031543c0c840e20308032002d02215007100c01d08540c0e00490810790407058540340c0141c0a906403503920791146541a85540c40060703550403400c01c2200602e040e000d803c00401d03240c45c106041000903114010003100240005018051800202086900403015142c5886c0c006080d1038503811241d400c0d4001d41454503100b0006a9030b1071010680200003898a281150180c1d1403400c0340c0c0c2982d0342e0030741c1d03035004240803036002809005103406401c00c4040000200450002c580d2030741001414041c0c05032358505d0f8584101450002405110300d10040d0001d014018903084840340c032009000313040760840380c8000c407501204c0942007003803000c150030180d9090740244040140741d440101c100d07164001901d0007940803504001e0741c0c00705590f01c61429006a503610586018a64503001011141c1c0001900c00115401280701040c01c481030011400c0c154040e81c141a5200c19140094060400f10400034400450b00d05c0460780110509800501c903580b00c5210110282c402900b24902520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 577089667 1250 577088417 577088431
    0xa0906140a050f09030a031a0a26031804150806070f1b05030912030c01050f010602060906102913080601080f06041e0b0a1b08090d0503072105 63
    0x52101080030540c0b08400340d131103520302c00051410303e08100811000740c03801a07107034000300034104900002275440e86000b400500d0181d035a2030819101d014490150b11118074400362030f4006000400c410f0b010f12562981d500c10071200011041107540d01c2003c00c1754541c00240c010710809003003003d0180c015031054044015602c03940710441e00ca9070002003510101e00000d1444e0070030b1111010a007001c06101d0000c03c144010f403400c105c0156901821504120380100b041d881c0540104803807030b01801701c1d030782000d01030002c1c00d079910302003c02e03545a1103648500c0c2c461022000c80c000840b07030110039407096140221000c07907035440784c4011092080640d0103081d1090080340f0000074011000240d51034101c041e00081c0c071b403d03621030315030451030362100781828603000c041d0702c4841c00074504104261060700c01c030b040080c0e558001c0006070105e60807150340741c051044c4c50301800007184000541e1140c180c0706182941d070740d558590089401500310070b11014600003035202c04514040c25000130f403180704 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 577090917 1250 577089667 577089671
    0x2b0b060a0f050310020a1e030c11061512030717030a06050d050c0f0a03060507020f060106110a020d140a0302010f14070c02040506060405181f0308040e0a0906140a 72
    0x148030030788101c140000307108042e4940e0291410700a0350210340c028206451282c200410421001c9109242207442c1c81ca9004c002551010f01217030740c64000b03015103000d5034036400903c80b0307180006850403c070042580c1c05100d04181c0d05c52900c0a00100200ea8085522000e400c4244895100c1e0314140e0b041629240e07045420030f00003062a081440308070042c0b680100c003d01d40c1c0c101c1398083c042007d500320205600070320a41d01c080041a071600420380103035a503038000c0c0203803030030700c840b9509042040e00880d0801a4414610903002c0c00014500011038040b601c403100e000c602d140c90940c070b00e128402e143c40d902440340c11405141d01940602d5211900b003a081c03010740000520fa00100714102c2d10580492001c1e103829015041031f40c0981e61160000c1c09403450b0a40311000101042000040c0128811b21001006462245e102540403651501003009000905641d90340202c0c0c0528080d81e06440c20310703000030300d1032541e540040200340d03080315041000c4484d03030051403645030003103540348040c44c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 577092167 1250 577090917 577090919
    0x30127050606090c1818040809010914130b0f0a0f030501060609061b1412300408031b16031106040309121a090705100810052b0b060a 59
    0x818982c03c0c8912a40c1072a0740340d072400d48140d0602c00043d03840140d464001300c4503850000034174403e1400d01e01480c0a043c0c0380b81c0b254003110005101500f1504020b5440d50000403ca9180d00d80b082400c1c0402d0788090045034010000300890128140780640035400040701d40001100000760046106680c0250000d1044a0301c841040c0d800001340d100d0980006c00900c101902c0070094100301c4049803056031515101c2038075651017841c1c030180050b985c0043c400080d240e00c5841d0482c00034403610100c000b59100300304000c3c034101500c4c00000c0014241c58400000070360b0030741100d04401c005100700140c40e51070795020945140d10405103a0100c01103910a10404919480000d1180c8940d40c980c0d0784003070307290401e102c0720303402402d80800f1034400c25981d0b000f4140c0c5540920076071140e401c00000b0010103140030200011a4aa00d611106022400701400f54000070040b030f20081c0ca4007540c40a000101e04114103607002e0321403140e1882c0e00e1424500c10200840e8000c15402640102c2e00304c0021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 577093417 1250 577092167 577092169
    0x1c09080d0e1020030901091703011833030609050d030605012f01110c030a020c061804090305090d1401050702070806151207060507060f061211030127050606 69
    0xe4034070005a240e41501c0110754016030310b1074001503174040c102c080046014000e03952401840b140c0000c44030712600000c80144100e50f100c13240c1c4031160045090a000640304100281108601c001210a010b40c0d1900d00a00b2549218908030003198000b40800c0b048109060050700c59800c1040b940001c1d080c15800a602c2d8410004000140000c3c68402e41514040460755040f0380b19800c1c50070076549a020030318104400b000036000c5040007030050356446030001d00090902104080b0315209004c180728040d1410303145105800c3c0d002c829180011000f50604050320b99004945801e98400c500140d001c04000405025103a0f042601e0000e0250351117086e030990720780354140100001c82d402100000c07a42d481c421000180201c010b00081207000c500004a410002290040b001046000900404024051090030440b8124000422166060a182d43d203c0140400041d102081c0340f200da000c1c075035007940b1009100d0500300d85540f008402d072022441000c0500f8007561340c0e0050f40001845 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 577094667 1250 577093417 577093421
    0xc0708031e03040503090f030705040c020303060a0f1503020a050f07032105130308061507030809060f04030504090e0724020f0d05030402280608090c0a06051c09080d0e10 75
    0x5140d1003001782d410202c8000a02c1641d0852050883e4948141c03000000c10307031a580700304200c0348010b0b8060b41c0d680c41e014050000820850742704d03401e400025002000311030307100300303501003203006074540545da41c000c00904607054001d02081030492007001840034105070f0400032450200c00005c000ca2042c403040307603c00c0c007103030412144d031520084440750440009202d081c2c030a034400e200412030711203106046080d201982113480c00328045a410421301410100400255a020213501080542c502d482d680040c52400f4130702c40c1c0c01075a5100d880e140c55164051040401070b01034948003240642c4024a101c42c918241140c180150003103660ba100c40d00c0010401909401480e192149142c443c0d50910040d08800c41c4101c1c10081d034000300c40d190f80010200c01d4000c00003a076a00c409400c1c5072405d01e0810030550705551003090b80c1e0008108450300300d4241d81d01d52030801c08003103c0c10742c0788900d803014019603e002040d801000500341d24004681d4070040c40c08903c007040310100c018180310001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 577095917 1250 577094667 577094671
    0x9080d0f02060112061104080a02011d13050c0d09290103170318030705070609060c020a0b09040b030a140c06030408031303030f150501110106140d080c0708031e03 72
    0x5800c00d0b80184136074000c00408111640c411034000030243c00d105044125500b19070807580103030300700020721000d56034010341c50b182800e2406160301e01d8200100008440b0a40045828090740d198800914402c1e85202954140342a5000a00c5501100d2400c03198800822034902018040c8010782d0840821154603503050f0307540140b0340b45900d0031a00068105402c0202400a07032040c540800889800600203018010302c2400180002070070408098417116007604044100700c401c44602e405607544602000c11103220074282da035205403610200d4050182c0400700380e0144134082485041000b14801607001260b00f5040d500140f5a07481000124403042c3c9000d45580800d001180400b545421100b05007482810005500d000810300a0309941107103070704040c1e546002c0400c005c2540c03c42080c000001c000d00c02001003509042c41c5040707461284100c0d40c022111042014100945041111030b03126800d011100025650700c020b07a0340303901c07202041e8034002c0501080c100c0c60007541c040e28 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 577097167 1250 577095917 577095947
    0x18050d1a010f05150d020f040f1406030601270b0408160b0406021b01020a1a041208070906110309031f0b0f010905220e01020702120a0c06080c070c0609080d 69
    0x8844c00d0900c0030044030303a801011640640f0303a030802443d0301001c0c0020050004000d14401c040820785090b44890714440e16202540c01403104008100300c03680d100990300c07518001c60b011149a003060020001126810b40c11005015078009000b0409000c00540a00d1611803000307428501c42d01e451060181c1d000c0ca1044034056404101c0c0d805041400d0596800310700d206104541000080751601c0321446144120f040c0718040000a02c01400281c0046000407006410b00039801d05111400818401c004c0c8500c908002482c0522050000140b017103542e004001801c41301803404185401000c2c141a0154040161504c042c1900300e083c07441c140d03814100c05844a02e103d40c58070b0107003c80c4409848070304150400703120034030580c2e01c03c42c0b051002000000000584070110345c41442580e00c0342030f0030100d0075400031400700001030096400c4800d48005142c080e0454540f00640b00250051210051242c0000000800d14a9100408074201c59a04049032124111000203440e5104c03000945 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 577098417 1250 577097167 577097179
    0x1805010614090604111912050a0e010c03330b0307020304080f070810050703090f14240103060903051201060201050f011203091716030c062003030718050d1a010f05 72
    0x1e0800b001c0004421070b9081b050070082c28041c0042d54490071070304200d0b42c003422179649080f08503664400344a4081d9020b51410f0400190044c05c03040014540c541020030310490800303c41805d008032800c0b860b0002c1c490080c41d641c0380e04140318069166081405031040d0341c46208090b00b94600001500411900200080e0103003400c1300508070301a182c000d04038000e160b243d516000001d403100780c3e960748540c002c42d429003d460101c00344500348015881020b00c000101070040200031007910300306045036402000040e40c0c850034070301070b11540152001441001c01c1007000141ca260113403c824891009004540403981e298240c1140351041e244d009400110030000520860707103544a040f81994031441281c503001c0a81e400341c560004141c10840d10400c65003020001303142c2100060240e007030420302100d084000380201a60701e020007070a5400b080311b50743d0303950303a881c20b038105020181c0009040d5404042d8a420310b50002d9103510b600034801240c400c00041c0d03910041940c4070944200400e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 577099667 1250 577098417 577098427
    0x3080f0c0d141206041b030c03051f140f06070f02010e0d03080a1d010204031109060102120a030504080f0309010b0f0105092101021902070611060609010504180501061409060411 78
    0x590303440d1960091100d90402d6a402600c0303081b6000c2131056040c103005550120b03200076010300050580e40043c0a0800385d040b4024400c41e0305100094010a0340d80640480b410071025100096402028107021a0050790005180e0305100d01c1411807800705000780c0fa000071003084130040c0072955680758000b0700050302e03540110318101c1945d0400202c8200080d5051b0303480355058007403422030303019510440340ca40701c41013007103610f050400c1002c1c1d00030300c02d0000d0420843d840058681911400e20781c2020076a80c0d00c0010104800341040d100c021210a032465100d1400c2c0043c28002d066103501140306050401202e500c1c0e42c031074011545003000260001e60507410310342546024400030745884040355002c0c405c801c0c041002d80d110650030016a8010042d00303150941c05440c200c400c0d0310000071504a0020401d858a076850000c0c11201c0540d03000407100031800e0002a40660228014419400c04000080c2c0d0341002e141400c980908480141d180d40707821081004480840400a46062043c05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 577100917 1250 577099667 577099687
    0x30a1103070c0e0703060b0a120e19170403060f09021e031207030c0605040b010f0b071e021201090c0501030608060f010504110c01150320030a0210050403080f0c0d14 73
    0x109544d08000b5030704000c6180c83d201d0030040c40e6a004480d051000034400200201400c885000d4446c5440303100000d4100060098a541100134103000080c0c02410142d000809080202048400071034001c0740402a09000c244c05c0741c00b8060360b40e42a40300c0c411108100ba4070100707a40300f05140e0035004008045561524844d030f20140c000381019414003031612142400325155014152280707104600c82900d41d07041c402d02c40c100180300d030402c0c002000103104000c001080051a040700c140030742c510050388030907840010201d403070000c02c0d1002e40d401c0140c0b9000704004120740f4400d480742602d05004241c0c480b45d046e41e845030102e54001c0101849401000315052a80c04041d00703000c411041d83c6007106d00440d190940315810380445542c0881d4000f007041c042106450200c0c03a00814000c1c80d0154040000b0340c0c0d4802501000e4410250b500e5010015805003046800465105035196103520b00c02c080b03041150441c40400306507005590031101842d1090000c1c0b41c01c540d00d403c002d8100740c1081 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 577102167 1250 577100917 577100939
    0x1230a020a12180527060d0f050703050d020f030d0b131401060305090a0203030d0207080702180106080c070f0213020c011503021f02030406030b0406030209180d08060d080f0f0309030a1103070c 85
    0x9008240c110703400840c0c94001c1848c0c0c0e0390a50881e0301030b400401c94685180703030080c034111035104c5c01402c43d040020f2089210340c0c080b04448245003e41008100040710000082d00c078044103060002ca645059020413201d40d11740032850484a054608000a58903030085a0300c80d000148000e62542041218a1000c4c0c1e0550241460a00600e034403800c004495002c62070b82104440300c811410054401045001c0c0d0140040d644040e6040311079003000150b95515000742013261000b407107143c030900320304070041440c1c0c10749044180102c005d0201c000c1d600003042d6000203501059000f600c0d201c5010310040340b8020201c3c0c0a4603168002d510b46031030420114010310701c00b00f8859009455040c0000560340c8d03070710503501414004100b50020740f10302c1e0007103141c135018183d400148003d041c04c2210307558403190003000481d08605095070740d00c0002d41e044082d104850082165510202c10300c1201e0f40c0010240425542d0b584a05280c40314013400c003980d80c061120024440840d00205010040d014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 577103417 1250 577102167 577102171
    0x501080715030f0f090506100501050f07060506030a052a1206180c030607030b12120901030c0c0c030c080d03020309030a050705240a0b01230a020a12180527 69
    0x4403000148180e0244c0400050f101c04240c281c0f210b6004400348040310180444800c02802c090030824500118a0982e0100340103008015183c0740d6030340009681501c0c144500c000c0c2d690b0100a070742d40b00c00c1140c2410015070081c040c03445406034002080d0810f0810340404440c5030b244100601c415592208080c010b03000c40d9400764100c0c051500c0e803110944042154170702900321901e0100b04810300200344904000c03000d1b2050310640c803020101208001c40c07400c46200307220038a008500c124a0f2601034a8600054800134003202e02c02e40008207010072122800e003500d81040c1940d500b5040007030b0480a038002521013268a410402589401720b00030001440c649104900b540c00000c184c400361044944444400128000c800c010464a440d5a100e81c180d030032400d08003d02c2d10300090196000c0000b0009003900903e13800100000710b94001c0040c442070b55480080007a81e00e00401c8000c04441c1315800841075030740c000d103000c14180b405602054070703280464029581c405403910700c50401940 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 577104667 1250 577103417 577103441
    0x1812020607120e10170c0a0903140d0305090601030b1603060b12040309050103091a041103030c0a06050a0b030307060f110403050703021018150207050919050108071503 74
    0x410070030301e80041d07a580006a00e24200d51954085011814140001c0382150380903a020801e001422240581c0c200a01a0b04590302403681d54450b0080ca03c19900403503190006484035120012403000d400002a400002d0f6946503002c2c0b00d1521180c10300c580d00c003000c0c00024000c07505800007030312076a04190f04007100460f41c540422502d40d55103403507505900030040e21034000c5003841000103041c2c011810100400080c40c0410040416403030f1004a141000442458105000046410711901c101c5082c1c885d00010140d83c1d40310303440304406548130807210742225000d08000000c0c030001c805214480341807001034051850241c49503039031401030402c600c002c00c0d01540e4803025562484140c018002030341c4a100108a810304600400a40d40c8040c40300c201040300c0043c250b680800485403c03800c46000340b017000c0d00d910701841c1c02da04004041d0801900841d41e00d0801220070151141801c00d291810820001e90344c03100c1d41c094a84125000d00c00c004254400c00c84a040e20a0f4460450926 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 577105917 1250 577104667 577104679
    0xb04051e041806050402091b0904020711030d0503040c080a0b0f04021906230a210609020307122307050912070303050a020712050705060a03020d0e030309010b01181202 74
    0x482e020342801420011400d031000ea5407201000218103112440766000707034501d800e408042d00e000d1000d031381a1050200450245130003140307882c2007101456a80002e40c0d001410b0f142c01d00d00304000148107070402c42c0c0580d90154482400a440040840c0c5c3c0802c0a80080391200e0344d6a55401e9592200000381040344c0100944903900b501661246d8440090002640c40f0300503082d43c120b00314400810780c812107030710301d5041026008190700100042807000d4071080c080721450744a80c0e001c000701040d50264081c0c50000041091040e030202844442d00700100040180034800c103038090401c0d0004401c28078420310381c0301041c1d4160140000c1c102011008113070041110403261000d0a101d4150b204a020500108541c1400d54040c401c3c2c0020301306515219001d81203a07150683d54038028454a8010780c800100c840000c0d210781c0440d0f003044150304003884000741c500b0f43c842c5e41e940211a004001d510704071146e2080d40c402c0c984800203010106444a856051510100c0200780d816001c80c6d01903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 577107167 1250 577105917 577105931
    0x10f0c200d0210050d2a08040f05030307080a1d0618030403200f030f030a050708040510090e160503040813050d0803040506060d0807120201060b0c160b04051e04 71
    0x80d0711510f625003c0c414660b43d194540c01400c0815080d1200c00d80d841d5820501c03140340096807010038000d081c403811316260622441d100c1d03080c030b00196980d540c80503150f8003000080208503900460600c0c040c40d1241c0040200640345080d10148809000c00000d440d00404003040b01b0744540500600c6080c1c5810035a450075650342d98a41000c540c0c8091520300320703d07000e02c000d00c52900c0c0c0b50380c0301d041b40160058240c0c1d0f5440d901c0180c682c030494410b0000c1c800085410000c0c0411003054030045d00340907082c00100c1c901d140020300a85200c0c0f02c0e0b6034032040d41100284404000c0c04900c240607869440302d03070641c1c40d07a40d18030743c0d680c1044400c4215036400d1000010a03555213422a100180a40b0f042079403420070f81481810008020130041c042d0f65441711079400282c8250072103400a40080b08240504080d90b0201e002d401c144d0f100800c0300034003050307000400c0c00c017103054040c07446085c0c020560a44c1d6648513404a026030720940703034405840b91640c50069200d582c0c2d65580341c4001d00c001911 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 577108417 1250 577107167 577107169
    0x15050103350703031a0f06030a0221071107151d12060106080405010501080105040209160e1f030e010b0307120503040918030210090b15120106090506010f0c200d02 72
    0x758020001c1a40041c0d19a500980e40c00d0060015285820054030030745010600d680101d40c2e140310141000040c0360b800154804056410f03107091100d01a17810707400c40700c1e003000c140080040607009561280341c0200c0c1c500140c0082c43e001012001c2000f901c81e40300003808c0f02e201011400c07000061b250401072a122807404008180b16442c0644070a8585107001e017898180705003140d905822002551b850301003408090b80e41e0000c1250700100e044016101460b084404a41c203802807011035801c0f2003204c01103200003808900000041005950030090065002000c500fa1490303c0c0c00700d500354018200912240a2011510350564061000c5a1074299543c0160382182c0b4004480d80c1c0321442e0505900c101941441102d20290301e0000c10701c001c40c4c460f104c2c44802d000c080d119181c0d02c141080900102c1e1103440010790b104060314001c002d0b5a981e0401080a01411110035000a20500d02c800d44540070f01c0c62507205a400070620031010003096035000c28200785801059004030f0604441c401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 577109667 1250 577108417 577108523
    0x60609060f1505180405060f030f01020a020c0a0b041203111603030801090c080c1312050601030204050f0106210603080c150a18170f03010e010315050103 68
    0x5200881048809a10785409000c01d03402c0e0032075800c20000104022103010b212500b84003009541294001510b49803000016100002c0c11034a0342c03d03010340619000300312010341c042c0c17200c00710360703000e403070207a0750210400c0020711450048801d40300e0180000e03c4141081d01e050540207109050801e00040e11490287c6041c0001c45003092400380780c0028010075601200150050443c40700174080c00c00c0c0744030041c224800003007050f602001c02141c5e90106c001a220054000c0c0740900c041042014a030502c142c64901c01d010581c0150b046c240881c0d11210902c803454100d0b041640d405a80160090b500c4031440f82403c030044002d5103a46001c00401c0209005007008d6902200400781920341c0c40420840302001443e40c7d40c994500410b00070110034074a10408980e5010b1b0361400000d19000b04466903003c0c0c46045400c09c040440046412240442e030300d410307640201c01205000031600803d00c15907009000080070041103240503007803c0003620078003c4800b0284d441d00701c2c0b071594503075a8007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 577110917 1250 577109667 577109669
    0xb040f08090904151104051c030302040528120203030d0b031e030703030507020609150a0f0e0f010f0c0c0f0c0314070509060303090a0e0a02070503030106090312020705011b06060906 80
    0x184128031913880160001e0188503e0745016441003100703040c40d15020009000b0305103180e00d8601c061705064001c0405100e681202d000c5e050041c6103903000221001d03071071103416a03403c1d5207858000d040c90110305045105005c02e05954002c0080d451f140d024010400904100d581003074140c480d880314206034040004004450540c00c2c0001d5071948030608000f41903443c058004029500402d0078005070910100d5070303004000d421108007101d510f03913a02c1c03c80101537440501e054107140c0315030345500c68000308080107022000c0c0001e000c2900c01d081018103c4405141c0640031480b141a0320001511100e0900c40360345c02050307014622039490b1510009400c0c030703501450b11034101400903c4a4500b84001079000a400c1e0300660600b00110302242d48404280540100030046030006400001180c0489105aa008040e40d0312544c0d50a00641502c1d200c2c041112041c0b414030b03040f080d452000801d03104542c41603444900d2000841945041c841d904003040c0d0710b85459142c081440c10312401008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 577112167 1250 577110917 577110923
    0x307020931080a170c0a051c0903050408060c0412120201020c0a0c0f080f07170a120c02100315090209060c070f05012006010911040806090c09130b040f08090904 71
    0x1580c0301c1c00924014001410f56801040000b132100c1031040100780d02017900d800c03400d68200b05595022141070a00200818601482420306003100300c001c25501601a0040b03981150440300c0c1600d03403009040080c0036a0045010241050307010307401007080c001d9032400280342800018904880b2141c06814003891000540302040c000004014410328040d0540042040c00064400600f10520f85500e8000b54452040d2030b000d0252414603100040c03220800c0780d94400040240400900380203004d000c07607460300740d114580c2c0000e0001924004d02a0904c10b0314804180c081d11400c1c200c03510025008844400d41180060100c564010803c00c0244007401280811000305c41c071300800109503010004030010074a4042d0314070041000d000840a064031a007103000710f500d1020f5400b4007414020b550202c41c3c2c522560044c4203d114000c6422042210f00303542e10ba02c55034584240f1552074040340b00007098030a02c2c2c00002e000c15400311003402c840340b2502d00c261815040c0300010700a035105031429 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 577113417 1250 577112167 577112183
    0x6020609061906120f050c06090d1b120605040309170c040903050f130503010b04020906071202030904020f0a0e06130b07020a03020301110a110706090b1606020a1d030307020931 78
    0x1c080c814208100316107d101100c070180781c4501d050200e541710350020030090810380f2201040c021500845a4640035040151406001100c03606240c00a40130540e001d0300841e598504c040f5080300038140740220b0101060060400001d004c050200034810703868168204441401012114031000b0000d01801e0401002d103180d642c00d00080500316070034100214480e500c100900840f5440c2c800544201c07030307007003500e04c100b0107a204000d909620070740c0e8909074807a1000890f012008111000b80a45d4030850b83d44502001d130314410301c003451140c100c0980504036040c5041110614100040071410720151820b500240d40c0d0b80400c2c03c1d995072500d11480d144000c10003043c2c2d01d9101003e40400c000c500b00500b4464540f68010307103511958041c0140d80c2c180003030607038030b000400c05200e0500356018038115540c1c090a9802803e00c0d5101000b04541c1c07080d03c0c0c3d4281d0900c0c000082d100d6032900280f0810403038894195444446410280d0300c8503c20110a0800024406443e8240d110f40600303c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 577114667 1250 577113417 577113443
    0x1902030601050604030209130609171209120d0b130c0807080f0408030403080c0702030d27081509120c010f0f1503140f0a0c06090602060906190612 65
    0x4050038104160045800340006000c10405a5500d0740700940010741515003089411305030904c0742c0508100b0b0b0014100490781c4160440c07007940c0f4030040502d00358460040390151100b40b10281c8541c4000f49082c018a824050f0154514465000702d07a0f00300c0c002c21401b0110b14095100c015591000e903420040b44143d4104900f141d0040c03402c0764002ca142030155802d14081d650101c0b00e000c0a8009820490b4040c0091110032540b800c940c01a40c00404a031052a85001e004001e41c900e101c40c08948040b03146a629064800351035681501c2081d8064580e440101d2020001b41100400102240c8a540c2288003841d080a0003090f1000304080082804110f058800c01039a10818501075140d1a02c0902004200c0802c642001d40e61320220800e284d4906050281c50b106000c000080180036490030b840810407411545803c541542d2070b0600c0280d41d424069031916000c480c1d502203500840c000030310000f130f00508003c0750550f002c000104a62a40190400030207407042c11151843d00d441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 577115917 1250 577114667 577114669
    0x140406060806072102030a021b0a0c060c15150e0a020c011503030806090402011107090518010c090e06041d1e0303090709230403051c11030c0703020f1902 68
    0x40310b03a43c40549810007807030704c4010801810402210500000c00d090340131002c42d40b603c3c0700350120340100302500c062001d00050b800400b40c44104005040b00c003600503c2c00001c985000b6a450307a041500040d10509002500b140d44010f0945a1194084003420020108120b149580344900440381000d0060b10740e91200342d031900711800c62120525441e0001c10820000fa440702c82150b0250064a920301343c0e40700d510050300e0f11014454515481d003d00f2001055030700c0e0581c452480341c1460040a0703041032001800070300300c4480310390794000145903003028050f610142c05400c0e00300201810014542c00980c4102030b001c490420128910380000c80024406c020240300d140c1010030941c095440c0d800c140340c40c0c6540c0c007003074442c0b54a003640f00c0442b428120000402003499000602c08003020b46800c0c03400500a60128000740095000000c490108034814031039020306400500711585180c9030301f00340304101d401541003102144106112144e90a009100310720380038508c1040c007440c180e0644 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 577117167 1250 577115917 577115923
    0x5280302060a082e090b030f010c050702010806041814030c030406080f07090602100c0203160807031707120e0f300f0306060c10140a0b040b010804151404060608 71
    0x91061104c0e040401c0040502c903980c4e4207080301d003122000600c058aa001082c1801c007000200002540f030181c1c11180550020014421a4800d0345c0d0165142d0381c980030002141ea9947d0803074134410340c80020900045400c04443c1e00d46880c038007240d003000c00d0b07a5810ba01e1940b00350080c0000801e0a01880104040c01041c41c0d00701c4581d05041c680d2905000c03000f55140480c9002e0380d8280d4550401c40d007402e00a000b00d440c0400052030085003c5d00c02c1c18141d0541e48062011800141c102c00a0079a050200e9503190190205036140b0200d1551a441034001c2c0c214411018414000c4940c0c0f08811030040008414081c009900c46982890451014420407854040c10301e44401c1000f10000794190401240c1d40b00c034044130001c1d2130b92544070001d40780015886c060854039142034180042081c0c003952803842086041e90904c03c41c0007003401d0000f95404801018085424000410f000481041c00c1e0b035200e0044200001c1c40401c0d05005002e403020540b0255520b9989801c140714130711040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 577118417 1250 577117167 577117201
    0x40f08030c190305040b0619170309010f02150c0d021b0717010213170f0303010f08010b0f0d0f0501021608181504091a0904030f030f0605280302060a08 67
    0x541010411480c140e04e451844000060555220348c0503410a1a2550f110398944e20140070711a40c403481300ba21024120340c1e00d074130440c1140d010030001801d1080d02880040d02c0380b10f181d0809900172058a07400c0c100c4405030401c05001e0002502801001c118440d10300341201703030241090080034407629003d00310520555a0781040b070207034010084240c40036400c05a130803c8030703208861039030092200f80105041400100f9080700d45d0000100016044070101405001d54022300e000300b0564042400304183c070004d40710f03466001030010400d140401c40c0740d80410f1585020350005440c003015414a0a01c54030000000c1340c00000101d9186459080b030b0100c43d103240c105480c40103010711028444001c90245114260700399855954412a00f0721100d00c194651101030452141c1d4181454041c6c4207002c2c00a05200080c03510440c1490180d003406020100c0300e015012422000e04c5102800302c109102c1200c1d0f40410b40c00d0300000040e1101c800600c0c1048455440e00041d04210800c10860901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 577119667 1250 577118417 577118467
    0x50f07140a1511040b0d0902100c0507120308060f0a21110909070302090907030506010612140f130201030e10240303020d0c060e120c0c03060c0702040203040f08030c 73
    0xb03070000c10f512082010f411601540c00810405450700021722090002d002060002500548600c1100310f107580c0250760141c003d4811000e4400c050f4480c0e0350469070362090b6034054000b801080c0811050300702031fa0420700322540035142010785a1284400e07250300102440b01c0964656600c981c8051000010b064409060111400c0001e81044100c1a030345071520700021b0311602e2a01c010940c80d15040000c01e0003194014180c401c150b0352608058210002d00c3c070060030710b90414020326000d0100c000034a104071443c4c0c01030703030043c0c0b220b20b00b00404500c100c2c001c0b41855940c031041d0701845000c1101c114844031124022850b1202d0645100d4008080361221030760700d2444000380b00003500400e00c050200c0b00e5160201c03080700541000350142a103801a40b41902800071000980402c1000903c030b4200b09070203c544400f50382c0d09041d50741c5003c5480c0449003a0520090b0f0051905800540d00980160750221301c255a81c2c81d10940e0360320a43d404502c100740041c8880300c000d5035a034030100450f2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 577120917 1250 577119667 577119671
    0x30507150203040f0b0a0c051f0507020102030f0f0c07060203100602070506041d10050907080906010f05010e1018090609140601051603050408030d05012402030a050f07140a15 77
    0x4a829004d00b1500018019a04441404580407404910425540c65142c0d0030a0844000000075140911000f45030000303c503070300d0308000008032081d005000305d80c003901c0940f041980325a900c145074055001c02a02c4a81c055204004441c045145400914041c0200c14a0042232900e0301401030b01c0c1035200c1d80304038010501448100800880382030540a52030740c0071b460010703940e120703000800514843d4002562000554051103481030b84802c44511a4005608981c0243d8a4028111003248544105c0c0e00062600f1940d051380d00301149400980c4900307043c1030040c2c0140c41603460070340310117400031400569500300800c490802030103184040002c1c140180380906103400020400e21030b2040d0b07580702c2c0002c0f4007150101440360302194018011304081d280c0300c080c004c00b004007a2400f88140240810700715109510030070780600329a640030309500203510f03011b0341c04001d031201d07001641036024010050180501280d040000da41e88100f000c800f8010078016860031802c0013060941890000e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 577122167 1250 577120917 577120919
    0x15060c0105160f2a02090906100504060528030b0f09100b06030a0933110f1b010608101d06090706030e0a0f081314060405010c0203030d0603050715020304 68
    0x2942104004811200c1c4c800852201091406550702d541a48040290095124000c1140c02c2c00d0100d0a540128020b100c84140b442c0d85000b0082034850750b004072580000620240b12621301706c0003c41c0c815401011521001030b50f40e4691080d406400c6861624001c0a03508100e0f0380303c070500440002c175610b40c00c02c01c48100700c0303404a1940c1c003005042d16915662042c56a090040c0520407410f1000102a00341d0b0790710f40540703c485d4030349498034030480443c14518144104a034442c1911030401a40941a04003441d11541e4030f582c8010b07104a01895507030303a402140440080c005208000e55040000c100394400c84883c0885c004031072400b000e10b40042c01130041d181e0001c680081201c1a5150101c0d503810700d440400c0c10600880002400480c9083d182420000d080307018243c7c2c140d03262150b503030480d9610301007080e0b07410002d2010303484101000180059030081d0545804a070002e01200d08011070140001c041f298541c1041d60315511852041149440c040444000090140701440c209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 577123417 1250 577122167 577122197
    0x10809011407080702030c0f030405010f0201051b070206070609030e0f040c080a1d0106030c030c0501081003061a030d0801151803110609130608150603031215060c010516 75
    0x1100700076001204016400c000300e050313140308005440e400080d00c015101108040c400380da550758803a100780d5011800720208040a18018800c2c5482443c004a0080c0600c0c084079000368950310440c0d049911a50034407660000c59014803841c0041ca20a8840100c4500b0920400520700c03502c0002ca07209500b0b01074070100a95102e60680d030807501c80540452214210414180d104500b032a164100d50701c3c1200000503c202480c6990490307001d0f007480e0000b1a15000111a10390080350051105810090208001142940302c9540406201c2c00c580d4440c0c00b103000070342044603100784040050329440c01440200603001c468508080903040c444d00340c0600d01c001c1c0d4818441807002030310b0710030031040d1100103072a604122a0300c2200141000b540001d40030058004018034054030b0a58420400d0702c030391000700c1030111801194014000c50600c20f4048100b4000180100300c03011101100903800c4c0c660b12488040c00c181c8545000104491134500c840e201c51450b401c45040400040301401188 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 577124667 1250 577123417 577123451
    0x10509060f010f11011a090c03060d26040303030f05090318040207020a1a07110904020d020d1511091e0a03020907020f100b190311041806060b070201080901 69
    0x41c09100703007000c1d1800c024664065036042042c0310041080e50030040150301849030291a06c560540c1151000c8003170304c464202008900048440540040043c000500440d40c0780506284003440c02260b00d401100c50300030114242c000e680f040700403a0301c0c0d503902c07680200240516580701e14500011410b1015446803440f044051103400d60003170380e0014005003551212000000580100386520128105100360907410350f0186006807220b0500480c101a24607040c82140d000b99002003807082c0f078005a4007005003201d105142296072440e40071091000c02e8050040f040301142800610b5200d03442141400759404450316050b03064004a40c50a404d9625000481e05607601951000c0c103036034500000364504031801c4610541d0b403041620500c2c03205100d400564034204192642c020742c00c2c1d00c1e0361502d40284180030081a0585000c3d0428103810207500805034518003070280c140407083d80e147e51046a10030740205650510000d01c1c041956044074959030454200b400030040d509070301c00c2d20b82c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 577125917 1250 577124667 577124689
    0x1140403052203020907020d1206030503070210170405010606030606050301050901150c061107141c050309010f0e01020a030c08090601031502210411040204081506041b02010f0501050906 82
    0xc0004004200e0b01a1402040b444002465014040d5011801c0150340a5904d4401d440840002610403020704d0034280240512400c40350b1001c0154181581e9a00304400701e44d429170100700b0040ba0207100104d4418042186004900907000050902e04041c001400d84205400c25000d000041004110310303101c0c0d10409046030390a42d03106806040c80102114200c0351580c0103050740d030402a81d10f1140060900410809103da01c49a050000d0004001d46500c82400d550110390160f0a500103403d0044c801182d01c00701500000030b05012807088035048581c000031100300c17a0340c04141503147c1a014805c40340d00003003908181d01c0d586080303c4401d5441005001c000d290540d012840c3c20303040034030b8068840a11228a034283c450010a003641e81d145403c0310140da0000b0a000782c07120a0034184203d9003614000c0018116842900e0741125000034090b00d0940c20a580c0c0c2c402d02e42da0084019280030144c01d03039001003506020030300140c09540301078202c503204030042c40500080303984440d8000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 577127167 1250 577125917 577125937
    0x22701080d050403060f060b04060e04050a090b040f1b09091407030f03030e120c0109050105180d03181208160f080604150504020309010204261e210c0114040305 71
    0x100c0d111b140e55416001404241e445800f40010220b03002ca2641e4100b05454800d60059030200701d02e0b0fa90068500c181c40e03c020000d032485413001c5c040340c0441e02e504e8404040e640216025115a41844401d4007215541d60085110507540c003040001c02000407580d40d40310901400629815080d0740304c2d02c25007540c4031001410b256a43c000802c400c03005200c130085990441e04200c0c0c5850044a105018012044044407d9440d0070006844800c4058032030504d09090001010107001e0100180c00070640c8148100700f0075111000c101c0050701d000e01c0390604400564568041d814580001c41e03440c0f070303502c21400c2030005044000a030640c0c88041315a001d034040354081000178030144020710b080300c0e07500000d4020b8000010804241d01c1500104210345106521303400740d00f82c005804041c00c0301030310810007541001c40540001001d0145580c2659404419690b2010326801c20070712140300c142581f8244180400e896400200c2803042c50900a41d441d4003071050728182d03a00910034400c0b24405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 577128417 1250 577127167 577127171
    0x6030c070506014401020a09030302060a0908040909080405030102071406010b090114030c0c0708071a0915090310090c060806011d01080709050a090504111e0603040f022701080d05040306 82
    0x18a103400703000e04003c95004c0707080000c5550f0ba514000052442106000035000b5100c0c40002c031740203d0040c8903100030190400d6200d800c00381010800e03800b07009511001d481e042e00910002c01d296400b8401029031074480c1800e50b0344034203060096800d00c0c405074800d0720451000c2c8051200c50340c01a40c0b0796540c1c0041c2d20321981c0c0341da034039a0090a9004105804002d8403980c035010032000d100003030044c00c0e03501c000000d00d00d995481e00700c50001c3c0b1488500e9a008043c80c51034a02d01296400035003640030b001020750f0303164a00c6016071000c403040060306079413005540400b00001a04480026000308084c60061000d20b108200034440e01d241c6000e4034104044500001c000b248240720520103044010700e84280300e682d034910f100241c074050350152a405d40e07203c4a01d1803842d00d03148460040d50b0300940159109411020020903400040007651422411021000141d4905840b44400c003440100d192010140e40e02011031648160025407a0780d00c0345c5290302051360000c05840c01c40b5445180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 577129667 1250 577128417 577128509
    0x328090b03130c0e041b0b0a0203040e070c0803190c1409101b111c050d0305040c0f060f02010f05010501020a230708071d190e0a0206030c07050601 65
    0xc03c200030300d56400103400f03124000c10300003045440040b02c45541d041054410107603449a4640d50300f40700e00c0b4642000340c0d1080200300451854010055403000c403e007410070300740015441d44403880d4400c80b6100e143d2071440d41c40c41200c40c028414148802c03a280b0f0030394507000d0300c03a10a1443d485091081440b9084c00140c03544002d20034001c0f0180e220070820403840f222443c0ca014401b0b4040c1044042c03148002c40603161785219020500c500300c64108004180792015640103400802d80030380113984860104001190382d0307a0319105240107185030355400040d00704a00c4003d00b150618003000b58078505007030040015030b07030018103c0320082e0014540490200c062100d8050400407901e454010300603400005210080460001c0c1161050521030a485500030151509200e04032800b9200c18160942b07030780712008540c8658010220141190f49814564000810035042162850980780c2d0010b005800c020381401400e00608004001400505605004d501400c002c141044e141c1404144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 577130917 1250 577129667 577129673
    0x100606021605041d1c09080a02010503010e090319050711090129131214240621010c140c0d21050c27030703060f0209030328090b0313 59
    0x7076a00c4682904d044a0716030391981d41010196105818000c0032800b1450b001030450760100d400c0101550580d42c00c0e155038200420000b8512020301044020700c410311a02402003603090b00714680409035180e0076100c06443c0303040342640c00940343e175078003e0f4400001000f00002140815140c1d4408a42c056594081c1100c80300080c00f4040440080440a40e00050400c902c9211503d0740b6010b52030708820041410b02056564003000d0041101129150314030090461441c003441e0000300043c1074640824440d142c1200d0034010389428050741e5514003a2400c82908000380780030402846003c20b042008012100d0f8440180520100501070038255444140002500351407800030f083d03004106600344031203011030b06d8100c0680140401440c414499143c4114144030061803030003801003217110300303541d18080a800200c40c0c84201c1502400304000c29174043c0013615080d40408031222481c04600c912034158092814480c0a1001888090106149840c1220343c0040c41d01001081c2c402245 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 577132167 1250 577130917 577130951
    0xb09130203010906081908030402010f050415080106120603020906090406020405030610050102160e1302062a010c0c0209010e1302090a0209090601020f0a0201140d06030510060602160504 82
    0x485502014400000401c080030164803000968100d1030072141038222841280c4c40e1840e1440016008100510000300150321490048294400c5d81c601203061990b102c0c1c0c3e02841c8504400f0010128641400511103240d222000340104a41c0c01024005246103402007514500302820032801400d60794005418403090f501150000d080107805c072946885c00c0d00350807540070300d64051f160050250421044010542d41004c20644400d40101c141f1901d8141e4920300a10103240100d1300504103016080b980030500c3c40601c26905014502403680995440c21821640d1340500d80c8140405002c0c5000580c54050440703066825400b40d081c8292100740c00c03d45408122031000350711403264000c001128041da0060321071002c09442035000c6072a540c0059071a580074118200072640040d03401c80140d0311400d12080c0e030400e421080c62802c0760003d000015608181c006884d00d07802240c441c04407104038481c1a0041c040307480074041c00c103411301d0340c40d050710710324446c1620543e160f4211b15410402c071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 577133417 1250 577132167 577132189
    0xa060e030106050a0608090c0612070e12030d1416140706090602040b09040b0301050402090c1b0a080901121517010f14060415081207030c08030907180e070b09 70
    0x1040d144981780d0300c0800030074104085501070820f0040c40002085810100103a46003941450518242c80d660b000c0300312881102c0fa88500d50114400c0f00c0e07030030407840901c001c202400e00f071000410441803400c9401a4900301624003100310608803c191341c050340c410300c0200280c1d02e600c1c0c100c0d55030080d400c140d0040c04a604001d841c103440040d0010310b5407812802800c4401c01540c0a01045000000f01401c85204980180d013060307040001404180d0450001e0400544000e40c0390007655407103070002e251481c40c00041340e204034005601060382d0b0b000744911040013203080080c80084850b841d10400380020340310308115000381c0c3c61203000c54a400e410040c840071000c078040180c101d40d035107600d40810041e21110f00461801d40011440b8500a034002c094810101c0108a011a00003480c8044d6002d50360542c10020700780c002c0000120b00c80015406a40d480c0c005000e4241042c20199141e100079105040e00c600d411550200c1c2c410100d401000c03100f1940c112500c4907000d03c08950b0038401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 577134667 1250 577133417 577133419
    0x606052107091707050901060e10030c11010f060e09190f210e0a0506040e0f040507080a0809040f0903020a0212011d0a050f0d05030a0c03020d1d0d09050a060e03010605 74
    0x142403e00d070301c4003100060b8481200c80c102d481d01820790380c0f5601903c005c41503d00e840c0d003291003003440100942c000d802c4112136803154070384400c90900401380b4900310b801580743c4003075480c0c03155001c01071f0704103840c0402d4002c0303043d41c003824050701c02d01000d041d40c6c40e041000410f04411020303580c0c140483ca0508401e103100f400103d51044540000092524885220040c0704d080305e81d0001c0f0f41414000295010f0b41d8a8411042194892103950720300c03070500800484280c883c90302c000c18103800030b10000d038900b48102d030880e8445010b8001c0000341d40b102902e00d06038528114241c40840d90008100360303000d4040d54654160305221411a001d011004482d1a80c003c50060119103080000354520019016030705860302000714055068407540c2c114840030009101f8000710301d1b0600d159102c0c4019005a00780140b52041580c0d00c242501c0360340c040302d14000125101c01200840a02200314107038000c0c50324070302c004d04080000c0e4220350f49014100800c081a086948241c0b8258802e5001d018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 577135917 1250 577134667 577134689
    0x90204090f2405011503090609080c150a0b0612090a0b070e0312121b0403230c0a061d0d02060c0d0207090b011d0d0c0e0a060605210709 60
    0x11814007824503a2000c2070044540c5510650300211002c030b200c2d1034141e0380d9080e5419961080f8180c101c01414110384151065903449010400003502c3c080100501b413a041c1c007811740d4110941046111580003080b201c1c04d1400c0052464859070740400701c84c48101c000c130400803240c9402106134905422904000c0035816003500348402641c004880d46d4604504400b2101010b040c10b8040c0800d0042403d078049088851020914504144900c0f00f442c01e01c41411a060640c0c03500c40c580c00402400c40328a80700c0c0c801040412403401030045803400503080d108110040d1410b40300800c03081034201c4259200000000d01c51850f507951841e640250740003061540c4441c8032048403500d65204501c1d400251207a00400920840d4500540703103503a2050312001d100c1c0010403100d80d0700500046682c0e5000c03c9115a0000051a00342c0c40e40203170007068007152407850300d408600f04440b1140c0015081c17040038044030b070081d040c421541a110140301301c0c040998840700001e40b092001500219214a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 577137167 1250 577135917 577135943
    0x1c0c020105060316030c03111203040e0613020c07030b060d02040911030d1d0904030314040609020109140a03110a030803070c170304030203191e020714040e030a0309020409 76
    0x15a05410030340c080d440841c107440501c440f04c0074040780f4200c288401020030811000410100e00102c5001888910251000224906581d17140307045034881d800c40b1051207104018000541030040c100b2011140b80e000031441c0c2802841016a1b40710580300082c5003d40da0000a051501c40c0624100d015501400070b000000d414901542c1070300389416454001e00c54580d4000300702d4850b0940211940d0302d081400711910345d40003445a8604018010f41c1499114864a04d405000e5000303107110340c0c01103070f00145407074076840014181c56266111184004454411028a503614011001140d030310250b098443c0f0342d8100480c4d04602958000340c0044404810401e406401c0188846184d02c82c482800c3c50a8000045d80707118041594090010782c0240619016003c00690180c208452420300900e01c82451500e000b4002e4100545001030300013a03020844450702040e000342036102254280300410130a0760003540c90151800840c1050740302d03440039003591115442111078035000400403002d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 577138417 1250 577137167 577137191
    0x1d0d080c011107060b030601060f0c020303121501091509061119030908160b070b0601030912030c1202040317160c030812071e14040e0412120b060f1c 66
    0x9604103c50680b0b60328201400030710386281c0824a0340c140c40302a01e40c0c0c00c1038140d544c011220441209822a058442003140001120a02920900c1168007060440b100d1000c00c00043c108074550380b007080c0341c42c0d01800010505400c607c07038101352015841c040981c0003145400c1403400d5610758180701d82102c1051070400307140e0720801044c280c07a040d40840d16444030615185140d140c45215407603900e50140000380000d4a00b00b00f941d0048030501d404174030210281c8407100c07980c02e00a82d82c004030303541c0c0c0505c840d1250840840464407404941c21400c01c3e20b1511281c0c04030704e1005141c030625100250000c40310109070a0341030740c42d8205009070391480e2203241c403070215480566001c0300c4420384c400240ea040d201e00f00a40800f0b00002c0d0b0118814001c42055509843c440342d411007200051001040280d0b281c26031602c16400b0342c0f40e4851400502e90041d207001c2c0280030800207641040c2e2420000e8482d40119448150712002095a0301e031403407030b01e1179034404e02456240030a0501d9005100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 577139667 1250 577138417 577138451
    0xb0c012405011b140703120e01080c0313170d0c080c071b08012f130e060301061815050a08060f15060c0109110105040e0a020a0e030d03090c061d0d080c01 68
    0x5581c85007c0d56954410311320302c2581e0072400c0300c540c81d00088900c00020300540c001006035810040602c40300340403d2265440e0079080c003184019210300200490b40704411681030140000400c1c05081600b030608001c0501c0b000e42c410528003070145c103010603200091014040e03030503006043e084001c00035100380302d900f1850403010088200ba02c0c80440d89034403c84040341c044500203c07041204c4008149000584454075200529040d07255694030800199903070002503926501590460000340c1030011611600114050f421440c003803000d550080c09200b0f80000c66075003042044080d01225500d80b4450740500007240061070b0040c00103e00318110071130540000300d4052055440050038941c0c1001155580039500c01c500c2806603450101d807100d4016801080c1a04161030810401c1714548040b87c40c00303001e43c10034000a9035400700d64050102c600f4500c0007400c56031524a81440c590200320320504000302050380724940d802c20600800c50858101d581c0c800041c00240490750b145020004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 577140917 1250 577139667 577139669
    0xb040506041b2603040b0a03060510020d0f32030a0f0b030a0b04020f0a031209142d0306090c0918060408130801060b0c012405011b1407 60
    0x5030741c144420500b807024072000c80807081d90442ea02201c0240707041c8804818030814030440c2c58807408208008920340408a009008a50062310041072061034001440035100e01410b00c0000c5411540307800050640c0003a44071080d610900d020150740c0b84040c0d030048040c007040000c110380e01801811409003c208805548070b064030160030841d80c074464800038103450095070a280c2c1034100d030307490301e0001c0c131412502500503001402031250746500001051542000d50015034541c1c500541041020303902035407a0000e0100c00034030012100e40316012801001e82207009220300e07064034800c000c0707641400842d0994610700800f107440700d05015040d16256842d0605650080420340c1c002900a2282c40c465483c0d424034800800f9603544685072420383e03070844201540c5040e0031480003c0d10302000d021302c4010301501c1d500d081e0340c0c06403241aa4211000c03625502d40c00380044143d00c0f0b1160000c04a038085500a0800206880f140131045440200f140002440d00c8901e8840000034a400a9404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 577142167 1250 577140917 577140923
    0xd080c07180f0b04050c091201020c030f040509070201020a0507080d180c08150405100c02120f0a0e090f06041805101508160909150911040b0406140603090a0b04050604 74
    0x110481e8040144010345e00101c07400d0403030200400101c4050706200e805c132040c4203c240001414440d8449010741981d1141c00440d0002c4e84c041001c1c401032402c81007050300000b07140000c500d4884620005029405540006403203d800440c03294015659608200900e2820a1402000c040c0500e44100145c0580c024508184100e40e035251f80c85008903892401036820800500030010074210800141c4107100e4080118001c05449d5a58500f110700075081c000c50074045240c440c2640b4030001c1081c4020750485110712046024081e04800811006421580c103940200f8007504500c00340c564a20748690041c060700c10380540c0984109950300c080c800a10000203030940541c0c0e0070f10540d03581100111142c00c080145410003440c51164000b00c2c40030311840300085543c440c5000d035821518540410303240012020840c1c180d42c50725105d180101e040c101c504114403402c2111720401d50341c03500d25035400b0301c030000082078442c5c20821003004516405100c50000e41380614001d500d441e015103040b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 577143417 1250 577142167 577142171
    0x70b0a031b0c0c12080909041103031605060a090206180f060706060f0b120a0e12030109021c0c090e1b070305190302030115082e05030f0105060d080c07180f 69
    0x4241d8020500300d544e241c41d0003e0182e4204041902001070750540070340219200c100d80c2070006001e8070140007070b160443c000460f400030185581411401c00c00010011100c2c1c6207003145d4900140d4480081c0d586220801101b001c046041a004c00c0d01503c13001d103482d5102c40e000c00d43e00c0400585800500907160001784a003151603032411a05018040c841400c14441200e40001d00903020340da10910201d8201c40c111020280c030f050004000307a1003030308aa84026000200000300e6440710390f00c081d00c064444406c206400700c10714018088141070086002c50203100000c11003c0384d1044180701c04100c21403402c0d94414036841c1c0a0010740c4540300b550394230000030f158000380c18080e00c00d90741200d42d04104a03080d914a40c40860700820002c08002607550412411034902c0c980b1200c03686601c202e11009181da6052904151074000b00c010284001d070704181c1000f03a1915142d002000e4103a000c2c0202e42c440b6001c84c3c0c7c240c207214140d00205d8141641c2922000700284a411030122003842c0101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 577144667 1250 577143417 577143419
    0x21f06061403011a030a0603120e01020c0a05030d0f11070603020408071a032809060e0c04150b030421030b01030e0a020a0e10030606170d11070b0a031b0c0c 69
    0xca010a000134862000c40040c0780b401d000081c8115802994020150b40c00080c00340d8923540c07820282120310a800c000034a201c003034036040f940c0400903841400c00c21202107590518104c006a622040c10304d4001c108070a5031a019080d0b8003032002c4c00c141d0700c00fa0041c1e40f01c490300d801d4001c0023900940320b074030710a00c036592000404035801007000c00c0c1e2000780c91a80c0d10755550000210f005055a5114200103060401840d4811105224400d11030744510404103140192420722480c000b156406240300d40d10380000320018081d0042d07480c0c1101c000440d240e03100d507034508040e03c0d8203101414100f82500c001140030500d6505902202980000740c07010441018a0f21180b980ea007540c140094108031a14000d00c0905100212558001240d403034142075180c03a03036100720665045034800c810003011142c1035801850305210643c6a0205842c0968143c0d800e41e041c1c55640e00544a8000048000641282e03240d02c681c05c88032040b40843c002d04c00c1040c80c0d20f0300500341500c903442600c00c81000b100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 577145917 1250 577144667 577144697
    0x250e0d0f0c06140d05151e0103050901110d05040201020c180919080a08101508042907080421050a17060a050f120a050313080604030801090c021f0606 66
    0x10110b16445050304481e802e009036044a040100400390004852421030142d441035a07a4018149120101c0d07087c405c102040408009002d0321000b41103200e450f4181510041c000100009458070000b4400000c20342d510746000607802e0164421015401c000742c20102c500c0992203240650159a00000715030800d0840c044200b080313514070314000e10001c0200001c041321031003079010740d8108860781c04020029645040e40840d03100d00c505408080384c0e28208002c10b200c1c0c160f031078200c02c02890300381881c0e219858008082c0040014001030501c0304010100d8140705511854903500704c0b04401c040381030b07605544054038503000401d0781c9000a51a09021807540650060203000d14000703803044c8011340c101810042040785165941e030300013501c1303c00c80c0d644170000c001207115039015502960340d031041001004034858907074009501039030002080c0700020f03600010050441d60070a60000e20300b941d000049081080215001140d41170b40c002c214940203165010f001110300d075031141030409850803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 577147167 1250 577145917 577145927
    0x50906060409020d06050a08010917030402060306090c07080a170a1b050a0c021903020910030f060b0105070204140711011a040b06070b0a0906050a05250e0d0f0c06 72
    0x9404580200d0140002c00908240d50050441801002c2c0d001c10000d0311007010400c1c110140c0d002d2122a13450300b4030036040c4080740011007038121f0f90f015100e2035440c258002c120588000303400a8021180d1a00080611600c8000e42d041e070741e400317005c26555101d2034800400714210700c0d411717401d2407281c0804501d41100501c600c001019201e915080e51400018060780ca0340c000122207414800c4068050b0016a2541c001c101c1c960300082c3c40614850950041c403450750b01c02414030b81d11034807102c4240007042e80510882c0340750394048804030f020b4440b040103c0340344c02070360002500700d070400d44d404420700c210031941032094020760340d012002c0c540342e0605070a964200c60000d0070171030841450051030600e078026440d801c0004d4005c901e400c40a03503400941250803a1000c45556071040d2010422035a0301419030498002e800c28040b50500100d4024408601014995603058170042c1400703581c0038034403031802840020450881088181001000b6003104442101c4003c2d44010204860b8010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 577148417 1250 577147167 577147171
    0xd021e0c07060327230a0803040f11090a06030303050c090d02090c07050304090e100b03031813090501050a060501031b031a040905150106091a1e070b100509 69
    0x40100314036102c402c1c1c000780b28412420300810011881541c0300c0d0a080921240d640c81002c9811054000044207104000a40a4059250031500d01c03d4080741d801c905503500207800c500c0242e0324180038a04420002c108035400c6030001400010021120b8181c0d00c020202da0003034600340407036540d92518020754841d261480d9445040900c100000d0704240c0d80a50b07001106202c00780c0380c800b5946403070745142c0250344044105500c95071041c050300e0052021001c000e040c680c2c00c0c0031011400c0300203602d900985034000c444907184032102039241c2c1c4140440f5074110240b00c08100203241d45c103140780603203c1190079000c801d042c0000002d16511900c0f03035564003540303402484140f0000e000210090302401034403040800038411418880e558030f10a0782e04051103400101040c002c04028121903e005a0043c000c0c451035031020406004804082d88110300303600c20041d505d2404084440c01400003c100ca900030790081002410412590b030b05c54041d00e0403609811a0b140e0715002c10564401c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 577149667 1250 577148417 577148437
    0x61801050312160503031303020f0d0f0f020c0a15110d02071203020703240c03050114010507050f0618070b040302010e0d06200301060e040612020913080d021e 70
    0x10b03038001c10b8010703524041c00d4494140000341e40e8814080c0c807070a10b9508103444d00001ea10003209801c0405404000101e101c80c610000303880901c5103008007800380e29040f6803a000b1300c162004040c100c24401d00a8205603040180405241da48406041d4000340821030070314082030302c4000600f0b040780000703402514449203900a00c0c1513070410b01c50342e55464480d2400c409600c50440301100140e14107000340038040703054014803483c6600f804450161045c00c141e410606103004014488405214158800c292003030912a40d640700300e00d40742c1c0c0740042c140c00f0048a40520401d1240d001034207100214450044011142c0940d100c00c018803582c0706510000340807070340c4100d82440c2410594004d8001502030b003000180018117000d02c0248120b0800e00c203c19410020040c001150004241400c00b0b0003034a04114407130801221081c000c0d81210007030f1250728401c00103246c840c0c140e20103210075a0700240f86615032601b400071b0030294005035004071500c075030221106440203400f016140243c1c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 577150917 1250 577149667 577149673
    0x91b09020f0a200d020a02010e011d0918030c0c0102071a0307080c0d020a080f10060e191716051c0f0305091206040b06120a17040512060618010503 65
    0x4029a4051102c0041c1580c103803d96103000711a40c010b01c020000c014281e000f40111820620006000300c1c00114403505100c83d150844800400d500c981700d0b4100401d0310001030b2a121203419503c171204526504600707200c0018580d46a0300c0114441c4a07108082e021642030b5501c803801c00448151898a01620f0002400040d803000d100f0010150082e605085072490690b0707804003d41640e0105064a002c41c0c0c8030810303c21216030b07150089910107841d0307180e00b004d1410003000911242e1031116a034405e2401001c003020038105002000020036003810018291b0031000c00c910740311a200c02500305000700c4500001407038100302c030f02140e6440d070f20143c011010032161384401d545400c44400350108201400403903215195000d41c0e07282c640040f4002c0072549001d01d0175400c68036004080300c0c041c00c0342d240c0e5180a10000183c1c030300c00541c00302c10300d4a01c80a1a90325007040c042c50344011741c0070f0512043c030405040c4c0480c009015090a68852102004c015450541e81401b84a270075050b82c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 577152167 1250 577150917 577150927
    0x1503021306290f070b100e072c0a0323160302040207050705090c1b0703020303030c160f08030906070305071b05070b0c010203061305041a0408070204091b09020f 71
    0x2c24500a4030b140d1509090141807151083c2240c88507009604100c5810096030b013800014508058800002c0009228041c0c081c5000c18004003da0480351002001c8124910204451a0f074244c4402d600030010f41001c0c62543e41c0d080411030007040e200003580c1302e43c4203101e00c00103184c089800e00d94080350b807110619061543d428040203622400e4240c609028140c40421250b80c1d080800e4010396882c04055180c0f0000c03038901414050b502d01c031306003d0380040c0b070410040c0c501009403580118807211454031134030070214000303400907050002401580c1803560724003000350000144d40100315590469005543d00da0090341240c0098580c1c50100e402d840c5060805c0301d60601e1106820b109506807403d682d503805224213150082214407030565008803c0201074242541c0e48191030000160600c090700741600c41d44445401380c034131716020185960000e41403100e200c04030780b041607002e002040040b0103414800321250004015007400784007150001614032442c0240c41c1c4414001f43c00368588 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 577153417 1250 577152167 577152209
    0x204170615150c010c080603100e070603091a13030801140901150504080318120a030e0d171c0c0c0c0e1803040303090302010f0801181d011503021306 66
    0x4801503250b150140300301007081c0c0002c0d0358280180e498400850b182d8002d81d0a00c2d6003010700b80380e0300d5500d09040c0c0d450b102804602c0c48000807420100c503424100040d4890450408110b1620307403507101450002048240594800e05004003c01503009603101800c90b40c135014003c084200440105a114003100010f01c0380c082045480720210582c1e05140f40b605035240c90443c00c40d080008040c0c819048081c0a0180d4209107000754a4200c100c005004241420b5402800007000420840e015600000d803e50030072891a4884500f54140310b115515210242c080040f0310200070007410345a0b082040d4603004074094400f10b8802c540c014003900c0e9081c101001020300e0b85000b041c40600038250504580c0c440c4050004002844c0a0360f10445628150300025054000c00d075101c0701007080d10801000095600d151508400c6e62004000c41c10300c420043c000200c41c0203218490517940b0701002d540d5900010300a6204880c0300703880000b038140710420348008445040c407990642003280c3c04c0e40c3c0d00c0c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 577154667 1250 577153417 577153429
    0x907030f1803020c040f0e1b13050109050a0e01060803070602031e09060a06050a03080406110a0204050108070f0803070503121321030b0f03030a030f0b040c030204170615 75
    0x824060894005506110031075824603001100005034051303001a0b02107400343c1020300490030b005440120600180310000200d0b07a0351143d110400d9451403031108042d03071070354070510a0780a80704482004d000c0365864405420041070305640c0c40754007030302c0d08105103150342d4180261002c0312450f502540c02c2c144a03071103c00196000801c800c1c2039880600c1e80ca010f8a441c43d4215004110241c02044da130b14000c40200d00303c1e0365940200c0c0c400e402184040002a8800007210280d914a142c10b2043d0454061036619200c840da60003903110341024004500303148001200c900309c807920b00182200030355954480d0307100d2023480c070040d107260000c01010700003000d695201a080381854002c402d01c14119203c031040e0007080c03003170200c038020500b072580e10751903050043c2c1110540458040b130309080c0c1070000a650b40316007240300e410700d91100c502d8401500e0076440030300d151502402c1401061101c0900900031340c0a4040c40341d00d01054030811445190004040303125100801590702125200801c01c81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 577155917 1250 577154667 577154681
    0xf070f080f0a0b06151303110a14150d1d0d180b030c0a0908010e0a02102c0301060504090809010807050c1203221b052b0303021201030809130506090703 67
    0xa003a01081106c8000d403110200c03a4402540075141e01e90041c8008420400c4501c0c0302d0707000b07000c0058030040e401044d81d03d21a4420900ca000c0407120b94030307080850040040d051280c030141b00042a18030701511584c0c00700300c030030035401c09a5070300c0402003c003400166a2040740c01031149842092001881c0c201d40503000b0300c042091410f1003214103685440301801d50b41800c170302100980043c1410381c00c50500078038a44c2400a2420001c02424043d00d0801035010700d02d0701c0b00d4850003451109000c5840a52040c3c01400b0003400178014046a8103261082e58081c2514a000071302d1080014003c0384a40240c40325808800003600c1c00e2078081020f242a608083c01d40f811416200d01100340440ca8045250b0303121340b01d1030004501d1140401400e070083d996501c440c3c040c08800990780a0b11003805100f03030701c14052008130091141c90f410114001d024810341c07803a100d00008004001d22182001030107000c0c0003181e51700d030b00680744052a02668015100c190b0803010b8913000c252414000c1d00242 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 577157167 1250 577155917 577155949
    0xa02060d0905061f0b070b040204090c1a041a03011d06132306030f0a061808031f0503010903051602010c021e03010f020c070b07050f070f080f0a0b06 66
    0x1107808016a00c40300c1c18000300781c500d1a03110040c018204404908010004020201001c00758103124058882044640c00240000c4c03007980d8611540d070401c00c0c8011558003411080080f10844007864140c03e00344e50040c05500002404081d1421805680d030085030305072140351250a2a903071a1001e10701203560040c005075801f02183c0c1201c0019583c92052005c4c03190201900124075401001d02c542c1d00d03501411160003600005105c1c645410001440c0a4559020704000754200010242d004081014400141a0200081400700e100300904d01c01c81d41d114004100b5860b9961001094200c8220180003404514140400c00481c514400c003110305500605000201125540c0001c684001e20f1031300110480b1910000203190409101e002c0c940070180c002140f4000303c21038500e544000501c9103500740540011640100001072000c43c84d1814200308880d030f0b40391641c0c00b0b1514002d2074002d101c018441d1030715680d030120703001980110310354012414024680351241030000b0002c4241c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 577158273 1106 577157167 577157171
    0xc062107030b0f06070c12230613080901030f0c020105090d0c0c0b0306011103040608070e010807080601050c0304050306010b0409110304080906090111010e0d0f0207080a02060d 78
    0x3c214541200c2d00c03500c0b25072600d0710078402203c58101d07020034a141c1d50700104014002d078610540c010410325546113038000c41101561504216052030100b0784c035400100101350418010586103406140200301a0715600d20402507032109141c0c1c0780140e56820030800700000c00d0050318180861442c00150841654032032902d800c625010300071601000001041d0b150b80200b8002030b1401465080e41e4461f40c3d503c070003030020001102c0d01000324400902500e100d6105805041c45006280c41e10003450311960011107040d008023601e00c409100c20080820302c0d44d4200440d83c02010161009035031103003020485003d0700c0040d03102c08403c503014014400050080001d6811940c030507034000303454903107580040f24405120000590719501c5c0c00103d06400902003600c1e107080d040741e180c0c0e110a031a403c900703c0ea40c60051080e8880c5030840601000103262071001400e20a400c4800 = true := by decide +kernel

theorem cover : BRFrame.Cov 576978417 577158273 := by
  have h0 := BRFrame.cov_init 576978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 576978417 ≤ n) (h2 : n < 577158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
