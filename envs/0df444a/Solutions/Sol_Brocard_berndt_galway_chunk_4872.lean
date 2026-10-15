-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4872
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:07.433437+00:00
-- url     : https://prove2.me/submissions/154bbfb6-3dcb-4537-be00-0cf03e47e6aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 876079136 ≤ n < 876258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 876080386 1250 876079136 876079157
    0xf1c023903030a0503160906020c0f0111012c0303100b07060906050a0c080f0903161e1a010e1017010917091503090a0b090c1009090b0f100e01 63
    0x1d09660060b003403480003d070040180f0684091161441c61ba000c0325081080301c82d864804040d4642c40d900201d82e2003494400c403440c031107034045c0075820780701c00d44403008001c440010049080c0b04286114000214400c6e410301e28800b140000449015416510503500e13032502d07156400040da8064241111354540701d5a00f10000303101400b0700c60055803544800306010f006040003d00e10a40103104900c840422010b11441c90030100450b03c0c070181c0001020400702d21400d00b4404c00e111042200c01081c61858440c0c1800100001002a10745102030440309990311421641400015a8200f17128154408208055182d04a2903d9141e03408000411101c185442e402962610b41c0c0c407078403151000280005003850002c1843c59400300d81b010325420360820b4070302030b0ba4510078000010f207042c3c05440404d08020040001c1c40102800818050440280000080c4006010300c81c101440f070803c0900c019914180c14100d450030b001400d40003ca19a224040325001b020518031810b100c0c98100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 876081636 1250 876080386 876080389
    0x6012607090501090513021003020c01231b03060a0510120501060503090d0224071b150b01030207030e1e0a080616020303090c010806010504080f1c0239 67
    0x3418014040711400040941c54980b0101c00d48000030450290001c070310a024006984034440c409000c2c00a190040c1c0710611650054010700089424600420b40801f001200824200c02640f140042418040c004081c0290500c00fa010650f00c06a1002c0400c505000d04d081c450707110000000306181c1250f03031005840c2038070304440d02038205000086e4000200042020104081d0085041e070340300420300005614000100f07000349440c0c102080052002140b811032003040f03036401d4050614248500b0b80c0b07007440d041c0001c004203066070a0796410078174210710a6009200b03a5885ca501a118603085039440d00401162000c1c0c500040820100e696a12a1701d8680c04003030000380c69550000c1840d0b05201140c00881c40100311035800310340c01082044034060f001700744408201d400782002400ea440300e000503501806507400602051140215000c0034034000078040140380b0b00c030b107501d081c0100702e960100c5c0c545043ca401d0080d0001b000c3c0800b6101840e41e80c000000441e10819882c10140c00c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 876082886 1250 876081636 876081643
    0xc011404090e071a090a030204050402061e031e0106120c031d0a0c0f06051603050909070512070801060917070302060c0f07060c0c0509180706031a040509060126 71
    0x3030911050364800d02091021050104d90141140c00700e402a600340b500c448009000754116000003801542c4031004202151030300c0003500c10300380f41d924228900c2100880c4089040e041181c40c0001c41c0d9400441080b040c0034000054161900b83e42c49845c1c00e400f00800e14054096a2101c01c100366998090042d014512040010280d15820181403c01110f06101030401c0c203d40100940c0180c00c4020401950400200c900130166141552034030000341c1001d844074010740115503001080c00341040200e6034410020903038081d4003140200c03d42c031055421070700e40c1d00900503480070a000380000e000702d80c5181960b40910b0070000072280205e4903940400c0d61034110106611256214140d41244501e09000c1d00014119074500240e20401d00c2d202d50500742607502c6554003612044010651041c0c5895004810b0160700c8115803006969002c010010301c680c5564944101403035960581519190081c3c602544410000340000e90802480c0506510546110b096007814550180034404090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 876084136 1250 876082886 876082901
    0xd02060304230f030913060b04060c03090801020f041511030904090f0f0317070c0206040302120a020d0804050102012301091116060606031107020a0918050102040306050402120f0c01140409 83
    0x600103036440303141791001d0000c84c1d8590103808158a080000500c03a603020f100036201241c40394070703181c2caa00d0880c1c1010f44445015411507841b550001808401244025008000f140d0082062070a0300d008000b007201e2014031183c05007030721342081191084514241d002000b54a00944550755210791a5030f81c1000c0301c1c1c080000f100410001c10b1094a2854116180c40c7c0c03151541c182040c0c0e400300360380041d40f180701e0b9000c000e1060500b904a9501c007038040024039119a0b0103001345000c0c07007031401d000c605074100b4814580107600341200c16140341d0407108082c6900c0859080c0b4490740c1d0a004070a000341040c4940b030116140288403500302ca440800a295440707000301c100251060401c01c005041d90030624012002c13550400a038001a2074007007200c4121815404000b480ca468181c41544103802200003902e00d6001040100610165a000d40c1c05144204c03584410700050140090700e4180c143c5850302d9503002040200f6543d4028404103000d4040a001d1502e40394031a250042201d40a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 876085386 1250 876084136 876084163
    0xf2904050a110307030515070905060a0324120b060103090b0703060501232a0f030c0709060317090f130b10050c030d1805070305030a0801050d0206030423 68
    0x4600c04806104004421141c0c0704400c3d40900303581820743d21000c1e07403118088404061030f010303c00040c000500c114415400342400400d175590340d1059080c01400781005602e40d0301c1d0741116005554452082c92400d00888030051100329560340240c0390100c0d08100180542d042c1030300e4121400004406c400035500c107407030a44000400c1405c6c81e000410017581d00c02c05200003000304501c102c0400c01c100c16141840c0d03001c4d00c800902074201004145030f140d0b02070110341901c1200d6001c010700c60f000c009400121282000c481c0d440f907949845009644040c030020302409098400392400452000040c95036450180014150b04401000f0a12040407000401021659864601124609114a601034404514003282888a0041d0309600c0f8464680c0b070140040d52a9007240000f400d80810b070080c90b4000003507600c4a03569040c42ca0f100e9000908000000c0ca0540c00480c80e464840340a07451640c01400c01800c0d40d4560b502c000090074030b00701c01c1e0004da500d031900c242044020001407203075552 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 876086636 1250 876085386 876085393
    0x110d1e032003130c0603061202040f060506030a020c0c060a0e010c050a3c200a0b07080307080c0703050d0504111525020d0b130804230105070f290405 66
    0x303142040d04d601e500c2c0341c200034201030034039100300300001144040c080155011600003c4180230544c81800601031039001580001c4040100310104c003065003c0c00d440d190403400d0f15085903096040008900c034560508010402000c54100a94414000409114820390841d0548010743d150342202c03080410641c1603200740d08003004140c403000d10300c210182c00c501022070900754403695507190f6803031802076800b00e05030f004110904598400e140d01d402007105266055441c402400c0031f590980c41143c280d40410050b0001c1080309c4604802c42e00702d0b03600350b81d92a0074442d0942c0554040c083c0904103440907030882240701c51036664084142c041350b50101110381d80e0010030000f85007010568100481110500e03a04001603110172521346c2c04a039111801e082150307100c41e0311545100d001800a08003081c0441c0104e04d80c2c00e07643e4400c2c090300c1880400e086000956004407070501c551040280300020380c11040001a92412890744a0503488240810704a40e500c0b04e104c506104440c05d480c05d51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 876087886 1250 876086636 876086671
    0xc21040302040c0c0b060f13020c06070e0a0f09022b061401052a03070b10030320190c09090309090b060c03030106120b10110d1e032003 60
    0x580b5101e01022940c0c581000c44041e515515071445c00c1d040280f00c80e02a4444a80001e01941c03044c0d458100400b42210440d1241d154102181e5902021a08507002c40d56807100c151107443e000c18041c0407110f69040d00c0d20040e05040382080030b07400030008148021280407944032805242c1c1c65501d0070104070240040c955140c84c0d86010303110341000605040c05810000201071502004580c0844000394440c1c44d0b001c08041c100c0c034a1407040314809400303911190103100d80c81e61402400ba003203900a9031402815211400c0d0360446489070101426903078401160034155004041d40403000314010851161200d0b55030002c10140c0c0e160f103c0880009150031014403c5c0b84032840740d1030211005407165410180300c503d21594a20040c002c14080c44480340102d00c4c00700458101d94580c0c400500b01c40f1004445d0310001d0405000ca41009074076004215030b5100c032511481c821040050415021950303d001d910050300208004801c0c40400d031417058610078221a10b00042d03004034410700e00b41741002d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 876089136 1250 876087886 876087889
    0x32101031205040e0c1e2206030b031506030a0606150806030d0507110d0804060e040f02041419150e010f0f1d010201060306062907080706021b07030311070e19020c21040302 76
    0x10301f2a0700504245464519030040c81d4500241c00490006c80c0400c6401680700c83c1d0000b407034280c0005008040c0c9040520100e0300c9903000300010040d03c000d07112204541c039044105030f1105d07000c12902d000904103200c0000404c0b8a860b18001214000c1c081c124000ca45460351411a4401d8110303201240c8088521555030404e48a1940c000c41e41402c11030809003017007842600f1400b811107e0384112a501386100c503000c082104100141503031109243c0c0002c000c8405844642c40191690205540c1c10800e084c00d805505041c240350f4040d41c4601040149075802e21405207d404894115940c0d0b80740800042d00740c1c490346000e0550400c501c10000b04240020b0424800c181c80380706030728030030b2080e540003404510941e461103a200c48056120b881200c019094150b408806004511942800005060304034482c0f103100d20004040e94442601c0301c03024010703600242c0d203907100b000041c01103d40d26813a030ba000c0d0030803043c40015644c40c031a4070004840850310300482042400c20008040045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 876090386 1250 876089136 876089197
    0xb0639010b0f0607150e070801060603051005040504170c120331111c050109110406120209010302090702190308010f061704020111032101031205040e0c1e 68
    0xb00702e02151050302e018400d41d030321454070503e00c5403402800d403101c2135801451001c2c0940700180c14824000c200b513543d03d0000401511081e9100c81c040101100003040700d04050080c503100b950483c3c15852072003008407034209180c1c4064138144481c0600640300e100500048029802102060030441c04102505458005614103034007800700395568614240028102c1194815200c000301c41c1c070818204601c203641c500c8004200300030300030352808a0078020071a00c4103060b83c07003000c10341c1c003086216100e00d11100315003035481010f540f0880d64001000140390034600305501c107a061046da0080540550021181800c40c0c0085020503400300050001c2960003000ca0001c08040c41c14044102201200e064400d4004d00043c2c10001d8009008041810400c01c80312489000145140c4840d103000e0308681c450400e00003100c2d048000d40360ba180e6a44518240c43c160b90001208640c191501a00034010350f101500040140c0d1102141c0942104484080d0403445102030207009101c00001181d40d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 876091636 1250 876090386 876090409
    0x2c060a091503120f1205041b15020606031b19030512030406051030170c0708010204030507050d050c0619030b030115090c030e0a0f03120b0639010b 65
    0x300401d007010480c10f1a400340d401081d0017034400b800103098443d0b06000000d10142c50f407070710400000c540c0c0000c0c42c0c40003014082100d0354540c241e07605505d030b0f5400c064664000340040b62901c042003501000301d20300004000e81e5071444103007e903482c5540b0f546c0e583c01c0c91549540d4103e19203001c0108014441107010f6240e00c0180095454417035410507120280350110110b074a0040c904400400344070130030441002d904590010880241c000f01c884a04050b9888070303a945103107000c0c801c0005032004050081d41d06581d400000380c118682000d051006c0418a001c00796060312a0400e0300210ba243d010040a43e01c0b036400c01c80000b5441d0540240c240c074400b980e403a00030ba1610a10885107100c001d2505c094444254001c03c01418219040300078100a010480c094042c5021240c00c210340090084852480380c1c50f420680d002003149402154030880c10207401c4201009a4840c02394a42500755070f08060001400f089081c9081d11560080814003e440a17951482610880d107441c015098 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 876092886 1250 876091636 876091673
    0x40f09050f0708040c0308030a0b0d0b1503010207080a0810120609030e0904030c03031e05010e1e010b03010315020c0604060b041104051c050c06030405162c060a091503 74
    0xd0f00e6003440d94413150034444ca032101404050b07020002c550b0350845608140000c0000514a0310810154102100b00c40c0c82900c2941c0c10301c280c0100300324a42018001c0e82d05054000340410300b001d00c6040282c80b03c1d4001840300508244045021a070380a2504600a64a010b603e000501012510300580450003103000b0fa0310030000e26040000082e0f1209045004941c13501e030100c0e546101e00c08010010302e084e10b18501141c144000400c443d00c0b500c0200c1e00c0340d03441c904010110844104180e240540c01e02400f501006c0400c01440424200060070100403c88c3c2c0005190503031646c034060400c4c100751400c8a07050307113408601180749058001c9912000d00000340302d00d070a1400780020200081031101d84d69001207000d0b044144807003446079400050b400f43c2030541d2444c0501e4003503101d00d83d080c03014903d8184d0b400e0110f20400744050080d01000640810782c04041051200c0c8846a001407449900410b50200401e18119900802131050080e03070401120740e0841ca444082c1d440a5002103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 876094136 1250 876092886 876092897
    0x804030c06111b09130318030b040b07030c230f030a0b04060603020901020c040b040b0301051609060c0c031401110c0c0126160c171206120d0f0203040f09050f07 71
    0x50314207540707400031139801030819054020b2041c2c040c82c0548170091101c5000018018044000080c040c00c0c00203c1d20941c46440c20074200d66940900360200d0b203012841c82c000400c8640b90b2030210107004106651020602c042c1401d142c599a04800c07698000c503505881180c80b044000c1c900d0829005081c0a0402e50a0030b504003800c200000f9990b0540030919880313a03032103256407119501e450b803000003c00c202800a000c1c500c1c0c0081a0503414085180040008503a207000140c010b204100711050300d907108110031503161541c3c6921202c1201403244401655a44aa0000104080004000d00c01410014100000500001410008140d011040c00090f43c14203401d0b484940d405481d44421904000442c0082404044075503104100e0300034641c03c03041d41003101c0f40d004039016028036070707140c000241c459039848140003c1c0704024410070100c0d03216142c00d91100e400342620320812511481103a0509554440807c104240f03540841c044556402c280004000580c0c0d00560019050422 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 876095386 1250 876094136 876094183
    0x1e0c0e03060405120904020909012603070b0c0309100905060106260604020f0408030708040905090309090a0b04090b161716080c0d090b01080105062b0804030c0611 72
    0x7010f4940480c0200590130040008084c038180d03030b559040d00d800c3c2c040034103400150b44c4c403500c40e500309081c104410003000b1503a4040c028220000800c407002d2a501494507102911400c00c400e00a13000030340001e2a6002b07040302c4492904042c403483c107110303000700010401540f402201170409614880200150000101070348094507000403400e42000084d54010780d0b80728a01c5044a55005603004001c060100040881c140820300c006441034807038699040169485c0c48404556074881e00d10f42c0c98100000d080024540e85460388044070710340c0d018101190b100425038420305824011034441d94004402840340f2083d6a001031202c100305d0801910003042d04041c119002c10a248402440070869410300241d48090035a0a80f000925001028420441e60b490b00083c4240c013401501429841c1000084240c588036600300c000c440b101281d4160700a4030000e500c1c1c05602e40390140c8408000b040000001000c0c5d9826100411040d640c000c0300d218800b4420b410f14400c00000e03007800320300281 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 876096636 1250 876095386 876095393
    0x21903210207141f0c02180105011709010204090c02100507020f03030a0e100207050a050c03070b0409023004120503070819060f06050c06180703151e0c0e030604 71
    0x1090800e0781d1142d14071042528083c03001502e003004d0061160489054074a07011100d9401c0112541039610844000c101080044040000070600740304650010307190914041d1851218070400e41c0140212001600d06910f82210a003500c040303030300101c0107078084043c1d048594400c0c070031250070000310701c080d0403c1f10000d040c0983e24040a89841c80440e03440120360b1040e00c1c10030084200d1043d00c00199103440e5039050040d110990102e05482d18000c1c0071010b105071030080b4060056405c2240c9160030306040c100614001d41140c2804030350200c2c20305c0d1140761042e0084d000c2c0c2c40304c0890703040030b14145014900320600c20246017000e01031100500500031803a0308022160b070300c2035904290841541800621201402c1c00340d1001d10032181d03142c0089400355004004128580340c0808403001d681720190246050101e1004602440d04142814030010700050f03020030800d07500c03107004030f1202d100000003203103417440c0d0007506201350381d4592008100e40c202d0300040d03044104801418041c907240d08c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 876097886 1250 876096636 876096643
    0x303030c041e0e180a02100c03020f01050910091a0a1506020f0d03051f0b04210f0305090303120901230609060103110d0f0f05060321090402070219032102 68
    0x3414000104e001510f15103c0d120200800310049400412a07800000302c443d01800c000309030b1800f0350042c0150440301e40c4000d014081c00340140b01c0341d40200480024140401c00809000b40c046408812140c0c0d500241030580050350300604107110006442036007000003140c0445164440029508001c00c40c00507003402040c409041505803e0224003507850f602e0302c0100c100c11808414130720010b0300d8080380f1503a41c400139201b03503142e10f101240300750704001001c0851170a43c0c0c00100004900207010001a00c50000b41c070744808050704803410f11004140098480d0804c5034110810380d5901c030845290705a0980c200c442d1001071010002d2401c08001042c4603950061106e4107150b15404280c101000751070854849802607003040281090102040014041c4110303101c103001c1c100f401140d000c0c64040780000503040c00f80001520060880d040303020580061607440d0703021307600b841600050380b6101d070440300020145c0c450007552811890300414160b0300d600e52215104824000c040c2c11034000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 876099136 1250 876097886 876097891
    0x3061e32060f03030a030c0201060f031511090a1401020106060807230d0c11070e0f15150d0912092102040e070e0711011109130b0303030c041e0e 64
    0x2100c014800350340310008103107054180c1c0c40d025010712001410880d001e6050340031146c024a6580248030090b6207800c03200384151a8000580440150403904a011183d6070141500d0145180c015050880c64000a00301c0b180c60340c07002e91403c00d12004080d49603828468800500801c1c24280003030b00380700400405489070b12003070942041c4210404001142e5101c242ea4482400600500075040d002400921500d151612481c0d280310320300001c40d50a00c2c85205a20412411886078400d030303100010341903040c20102d4103035040345c0c132046078000300681d16006081700c0d001628041600c10300c074502950000c9240c2c00c1082000543c001c140400f20310440b0202e84480c1f064949940c0070382c1d50001030000c1080009440f610721410800103454850301c1e03100c07403243c2c0103500d81c0c2c290381d443c4144141c00da820851600b030a0100c10000500307546040b40100c040158100c20020b1034106c0b10340880d20b5580269800d41c1600c6001c20100500141688140424007140c0039440344d842c60140704c140001c401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 876100386 1250 876099136 876099221
    0x52b0903060c0c1205120f040b041b03021309141c030f0b1206040b0a093c0b160e030309060922021e030702060105150403061e 56
    0x140c00300c400071507120381c1c1990030007904508001c503588000300005e40140d10824440c070910580c40001510080d031546581c0c41550004015012540c95940c0c07034418102140b421030680c51300000100c050380302c81028050100c08240c0008104215003820065442c0070540000e41c1d030311000422034401c422101e1002188524100440d4284400000705c01405054000c0340e005850764403889000c120010b010360159004d50040a055181c512001c0b058582076640074080142158818140c0041c215128900078898400c90341007810340b0419440702030344450180c981c064290b05000035040041c25821031440f060400c80d40200302ca1000c2900d900408184178400c0300082200c4980713031519070200112001051100185810030990407000b0341240e998403550001842c180340c090103445080f2801100030b50000c0500360b01e0101040000302c00302c0b1550794100720600000001031100d0083d4003020044040c1390303e00e14819500441100c41c007004940c1380c031284800d09240361a40200c1c40c4640c085 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 876101636 1250 876100386 876100391
    0xa030807031d070914040803060d060e03160c06050c120904060b0c0a030201061706060906061317120307141e0408150f0114040e0109050703052b090306 67
    0x300d000040d0028501c01c0c0c2030b41a201d0350300d85515000d400220f48481650500343c41000210000700349508929005c5a009050301c0701040820f8041c0344c0501414005031155070081005034070351001e5821900500c1501e0700d200340003078040d401c100e960225000502601e00e445410710410710300b15a03036000c90a640c01040100011403008917103494104002400300004019034403204c02c20700c96560003003440e064005519211021950400c86031520a00085403001400680c0f50101048080c400c0030340300a07031080301040024010451800688014101d01449a0150342d89000c07140c10b003031140820034030445040041001c1e203034001340d8100240654840140d155825001e1030000d409040c0005a006840450009101040000c9883d00903042c1500e5640c3d40c1c071501011a5901c0b820701411246116034500c0700d80f0743c103040c2d0003850450251000844c4a440a0301c450b42881601c1e00207542a400280000003001e00d42d181d40c0100d981c0461414031040c19030500200144a2400000c10458 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 876102886 1250 876101636 876101641
    0x20c0409060e06040302030a02060108030a1707030b0a14010801090b010903120909050406020409230a110909270601030b1603091b0609060201090c060c0503070b01090c0912050a0308 80
    0x1050b60300c005220340da01c0c0c00302c0310036040c6424007940e6a003107050442c00500ca00700000c00c11000100694620291948400614130060200d8071042d031402080c800400d6500c1d20380f5020b954400f0740c503d000b00036888000248010f004001050208160843e161480c201000d1400a90b8061107407811039402a40e10004450340300790464142005900280ba410b090805000510a1540c018802c0b01c2260200f04080221b0400d40c1d000170508002551001c0000030008180f44000d800c100c905602c507119181ca4010300b0400a03600f01d40964062001c2c901a0020103c08800800f81c040000307500401050a03616594880d401100c2c02800700741090014481461094040d400c404403041d40400810400019103904440102203441008001090f0000028a040c018400d1070b01d419007160f50500700b41e04040043d5801848004c00300d5440c070080000c0c1d0089183d014500e4003900c035074280466003092a107002003071020644c014515100e918403040b000a813001500703940d065450b09042d22070f42d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 876104136 1250 876102886 876102893
    0x14190f020f011707033201090510090207050d02010b0a03050a032006070206220c092f0d1b020a02010e06130b030103120e0303070807050a060f2a020c0409 68
    0x5404840340004800010f402d1103940764058001100e104240d0411554001a01905174003807403c04410706200340c22640180b1200c2c00d00e4001c0e0b50b008080149140b40283d6810f1414100e90081d00180d41c19004030241c01e074410350a00560000a0f000c4aa035101c8a05540359692903c5115800405010351030b0800f01022444210b0000d40401c0e10058440c40e160042003e915400104c5d070342c0000310041648030211f099030410300c080d03850300802e4445e00141801020001060024001c03440f06100411100700300c03100106000c002d0110440b404d807100b01003280b00080e00c143c6010074804441940c403a598007580002c2d884a0282c0910b8800380c0854240003041c0c1c10f00c80c0050000801040d00d034081810f0865500640c102c910035800c06420b8180351034219101880e00c804640d03d600b01300301b4100030078100c0b070161550500480640b07520704d615980313000c111011318119107405911100398040009000001400303d02c0e034050011400d04218100130b40307030401d00120520881c0d03900030102c2803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 876105386 1250 876104136 876104147
    0x6030f110313050106060816031a0301020c0d0f020111030f06010c02060f0a081015080c1306031a040e1e0c040207060b030d0f050f0a0512010314190f020f01 69
    0x100100000d2803952810921100c441842c540301007521a0360800d40000350061240d12010700c60410741c1c000390100c1034100c5003100035004440034a00060101007142035035907428401048907011180007402c4030100050064495485440345d5070669152150301c0c501c12611004680e80310310f0458203920150b07074040040e103000c00701d0039000e0f40240c40416805c04103d070343e80040140c480240c4809646584020303203d82c0c900618058102003d6003200e099001500401c01e0f1600103100f0b86c6503a00781034000c0250117074008035a002d40c00203526001c070071380e0b0300d0040105000042d03402e460900c601d60b11142c1265850580001c04111400041e0003000c980c00c00b4800c400500200030019548d58045041120251140110b40b500c2409100d00e080310042c01060100c14148080d10750034180942000070b586e40d074020003402c4c0d080c000100030f480060000e403064940a90300c40e8040a5480020074822440c03d43d401141103140d0010494a401140e0580100c1500e158111180e1450310351160040390b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 876106636 1250 876105386 876105401
    0x8150a24200604081c090308190207020307030209040201050c060a1d010c021f06030f05010507031104030f0f082118030a0203090d11030a03210903050d1d0f060f0c0301050a06030f 79
    0x81e200e103010940407c05900c44d10090040b001500058a0603080c001030008a00c145040254558410542000107091081c1e040d80c2c82801410000d05003030318042100d084c090102c2e40c184040e82d4036090341c005001c02c030b80c401d01544041d0f0004c0048500b01c51b800303541d030085d207030005440388103003c60b001e07801c01e1a4121034042c0d130b8000c04800035070110b4a0450301034402a5011004203040c031450405041c1214203903011031741c1180721004440030503103e018100715a03800c183c4400c801004001030300000300c0f980f100c1542001c4007583e03079031078002c41c815002400040e40c1006504104084025658000140c1711000401c45088000b01480d15000c00c8000c04e4444903030300741c09284070a205040e08890081500b500407200880c1e855401c28624040305c142e50f00050201d081400100c013083c81551100c0102c0c1010010300c403482c806840e5043c0b80c5007402c6c1600d6403c0d8812410041c0b8025024240c40d0000ca6400805041d5410a03001400140c0350713018010426680381006100310109400035278 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 876107886 1250 876106636 876106687
    0x9130e1005062d060705060a270602160c06020c0f04051506090a03141b040915020c0f120a0e0306130308041a16110d08150a2420060408 60
    0x29170320071440c42e000c0c1c0c0300c510444c5c1701405645402e180c65410038000e80c0c80c40c0010b580d06159086d401490751000000c0d0802000003120b60320b03030100000021015040c010280002d40c004024154010b020440401c402c00d038580d011310304003800d000c0002182840d03240d0142040350300c552242500301c0441c0b140c20346980041c00466141448540e00da8011455801da200c1035004006801c160406200940304070590041c550010101400000c0080c0e0b03010f0140322500005640c0c00b0440310340058034140700099507440000340015151001c2e50044490300c41030f2826000b4061920304a4923058810380503003c0513040c4503a4000013400c008d161205107600d102d03140e0880f4400d0401182c400c0480c000b609104001c04d4084004503082e00c1c0c00100da0711000742942d540c0c85503a403001c0e550b00d4691030802726680c2182609501098252148541c3c400c180210305040b1a0200744c0e0074001c105420720f00f1b00c005100c0c5c1c04554003100c950003003605644a50043c007280d580f0380b6410240c820b40e12800100a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 876109136 1250 876107886 876107899
    0x2511010b0301181401090308070c06020d0c0207090b0a120f03050408150a05220615180e01050601090b0f0a140304051e0d0c120509130e1005062d 64
    0x24800f16052400300701014041c07848003800154a104c076600700c03000c000020b00403805110015500380d118005141056115601c054182084801c01c6400c1d200c036036107400056082404103000040c550f1149400c072404c1120491559450240e1240c0301d02c2100002910080d01420514181401a01280c0090250314100c2d0804928a01000c000e2807080d203c41584a0401006c04d0181c04615110b0315132010355100c50248402c0ca60701c400c009e11041121070700c0320307006400c0095503101c0e41d2000720850110034004240b10917880315960850380e00405203414458001c0d418040620060250350181154106099440d82100807d449800070340d8000202000b0020401042100c0886c2d07028940a110004006043e000741c5000c0d250408504a640001c0302911000d02190f845024501001e01c01c0c100709180c84031060200381607050050528620311b44500603004604402c02c1047c0200b0b11343c0d0010011400d00300000b482500d8090070031103a20b00c44c09440002c40c250b0020038600c8030340c0184403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 876110386 1250 876109136 876109151
    0x615081005010e0a0c0f1206080d0e0a0515122802131703160c05030d0512060f1e04110c0a1a04030801150e060a050903062511010b0301 60
    0x403005414240940e03a142034684001c1a1443c280d40144980781c1c883c0e84660740c1d0b5014602c4211480009030700190551078491302c0000b403241c8284680c000203c51641c0b0051050000e02c03c1c458801c050f5841075029821080c565101c8800c0402610b101840815007849640c450300b0480040210070540c540e10140140049000d0200c0c580c01080e00340c8000f000301102e00c1e0f0307414100030308120010f40f6800c1600100991451282d08a0505140c2882041c0b424034554031200801d107829545403680c0081103001030900d809000601281b680603004480c0302401800d41d0000c65003c00034180c0d005219050f00544200707a03690b82d0410845886c80c06541c980700d081000401d6619100c0400581310404016072410360300341803030119842160981c4616542e64030300a444038004000440090401c41e000c460b5a001d83e0f00d40c401812001402d9a4154541c580e150406040c132802034400d580b9007120081c40340300c0c1d142e0030483c06207811082c01c0c100900100c03940e071540544101001aa855480c042c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 876111636 1250 876110386 876110413
    0x503071202190c0605090120070c0f0e0717070c060b040b10270b030708180304080a060b040e0a1b1d0103051e0304050913020405090f0d0504030305030103061508 71
    0x3c01c0341080c014581030040361074900582e800c96003090200e01c0e945a40b441040c0404002000034000e9910412140c41c03095982c0c080400348ac017158006c000b08010000074000095841802010f19420854801d095418054005030544100714401000c00c0c0c1c8480084a003940c450748071a05184020306008801c6800e05001005103806640017585010844000c1d4203000203820b4220664005017000791958641d03031016540c54800402099104600019210301d9440030b10180c802401c6010017080000058548101906c4036074901034001c520300304100540100008040d0401504200c040088400040c000c05080102e034207c8150506200d0030f048a0494502c101d40c100c0740100c081d5444403000312020980c621040816069a5006000511052034460301c0d03183c010380070108002e48142140d0211701920421900e08400340c001890410b01c01b90f051042c0016518146442480c0504641e4041c0c100d003c10f0102030a00c0350345601c0449881c14444002020301940000c66180342501d28 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 876112886 1250 876111636 876111647
    0xb180a0e0f1e3408221415220212030d0216050105070903020d1101030219030207031d060406031509240b03010509010905070311030901140c030403050307120219 71
    0x460f8207107000c8030485881d200c40000310000804507503640da08540d548816142c854048408101c40310500d041c800300c2800207614004082c040001400542040300411915001c0c040004040911603440141c2c04400403001c14000003800e80d041701c0d01941135000d003c440c2e1031070003096401140503200149041300d034008400502204e510400007401580d591850032148041d00d0300c4000e410500260811300040d0b82402868586030041c50010b007802d02554004040810a050181c0480d0303000070640c051540c46061a4410035500c1003030998202d0001c0400e003217204e10701c201420540c0c2ca8101040c01d26001c0310b881c1c002e00302d589050244080c9000d200c4402030b45840080e80251228100082000c45c040560781200d00007000e90365242c0c64800404040c1c50000c1c05503013015554a044440324405101845c000d44c0c0c06000066980b240a00c81152020050195405001c09004005c0042d5010048a601281034584420201040c0c50104080c0c0926409494007550921450300100d81c4803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 876114136 1250 876112886 876112921
    0xb100f2d020a050708011401053601080f0604020f0d0f1b1e03080d1113140a06020109020a0329010b0306042711060c010203010b180a0e0f1e 62
    0x83d0142d84040c0d6949a541e4207c1e920320400c00340c0c3c914041c004000500d4410010100000b01c0110401d241d02ca6444803110300119500c034440b92500c01c00140143c00c0308100c22204410208001e12590400d40c000600300c0c1800030700f562041c850208404100070400401c07030103480d440010005031040c09640c6040b440c4090140940c3c10b883c0c0340c1000c4002c2401e40941d8103ca8002000c607250084036040307680944000400112920003c00c51103445409500d902c0008050340d01c48002005600f504001e0403c2103940030500316814280107030050fa442c3d00030902100d80c00040345030303400300702c00403400303c1008503d042103400c00b09070001480000b100000d5101d030408440421208010500040c001304100d2605620011245040d0000400e540400c0191520081000c1d042c4091442d20340d09a0b442608034245208000c52042801c007420910007090010846d1440012410000d44820014000b00a140201b08440124290064140b5001c00c42c4146450302d040910300310010140c2041207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 876115386 1250 876114136 876114143
    0x10b0313051b0f09040309060c0314071208130201050d09050c19080c120d0327080d140c0d020a0c080a030e100c0e0d080405030f0a060b100f2d020a 65
    0x500407601e03c1d881d14246403885990b16854980d5034a080c01011191204446012414003a003039024000c00034844000d07054207031140070481c008a031810402800e941c006045180e034045c0d10514680181e81110540342101400c4000140d01d1049042151030100c1180425421840712444444400480c1c40300000b81e40c1420121000308201c9024450741c901105c09045d00d03600f29030220b0303245078800d0b002003032140300308805a07600d410b0a503288000c1804c07101c000c640501000980440450b001d004801c0f00c504002e8030700000f032600c000d00d540d4a100e0a030011295660015424070607a00504420141d10b81003184680c0300c540c00703800503000309103a401d5040a03205407402560025014020424494000c1c2d0ba9011801070341000e120329006543c4040303030511411701000c205500e04020500d0202d21a0f0003c201d50050380c1095800c55000e84145ca008071940303090740c60600c1e004540d10740e01d0005494501c003400140422040400303000310384130000d684040e2100205941c00210707010310501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 876116636 1250 876115386 876115399
    0x21605190519080c090106210e030301080a0b0c07170705070909082104030f0c021f051c021204020f120a0c1505070c06050702060f0c0709060603050f010b0313051b 72
    0x103510b04100b8171510034480d4100240000c42154190541800741c20031000484401042d2041c140c8421401c40e00242c01c10000d070703484603050000f0300480911482d0401201081d1501c0c041c10703178035540d894006002e900391840c0c800040290401504200850007020307031220401400e4010300d401c44580d800071100c140c10503600030305400c0340c0e10030490060095a040d2500401303038460040a80b81038195410513030744000000c010354a2840707141c2d00c40b1102100d40d91269a0b41d250716021012603004560b4803040d0620500c80d034112044c100300c400343c200350112224100000b4100020355072944000100c00c842c0544e040c00c40411800358005800d0707481c50210b15000403400c05c0121080e01910602400c40f00201070100101d40c082c900034070b02c5500180c140c915007460501e101c0a15400001c00594543c005e0134108007440d543d108980c05804a46000d1005050202c04500510411300070b01220180000108120f0452440c800d1146a841030580d100f2041202c0c1c030801d65101c05521502440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 876117886 1250 876116636 876116653
    0x6030212071701050f03070321021615231603080a0b0306061302070210020708150f181c03020301051c08030f070306091103061002160519051908 64
    0x2e00441c800c0c940d1068a00c6810036507844c250801041d01020505207805018182001c008120b840c030340301d500c049940700348003409050528000e14041208030020340401010a052080c107424450080292603c1e11303003200400b00304d10441e60615155038610042202c0000d101e0300f814040748500400c2e078080e454030211035545807010010744049803000c0e58150031200c005120b40c90310006441d15050418001070034a072040d0b011130801e5060740c5804001da489228200044001000124140011070000c1c401d24140003500c051039a401500e642d80540d113500201c503400a00300803818401c801284c1d015000d008402018009600a0142c540240901000349424020394191240705550080c021440c6070303100d01044142c010083c1004d41055103690001442c01c406004080d0070b1160016210365070700301603081003c201c00c40f910050175900900c3c0249103a9081c10a81c404860083d14403002c650340c94100240428999080554000189900d40108d482c100a400040c1c0d0240701c00c03200c058 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 876119136 1250 876117886 876117901
    0x70f0b0a02030c0f031b04030c0f051509040b010215072d050a05031906031118010f1203020f15041e0213090f05071502010c0c0804050402130f06030212 67
    0xb48800c40f0082403a4030700300701541c5484941001194041d00c41684940408080d074044900c9502951064070f142e04100011b1003034050000042e0010030b0b080301c2040c070421201d0030f0300359140a81a070440c8596603640090003aa4000d20448003420917910704880107251001006c0c0c4621034180d5a004541c0801c8401000d00310b0fa41c2030f01c0303100c1140352070f80d900340500e07242c0403175242d40000d1404c111040d800c400c0710404c4280e40280c0d40514450010000081024400d100c0c40c601005d543c00c241303200d014010480130340c404110a099881c0d0002d00821032132141800da1410480d0f0b0303011402c511071824960714100c001002140528030444242c021341006506006407030307000160196008012081c0031103200d15660104403940c4c1300d2010340c02504241e0322241d04100c1035a01016401c2c040603424141141d082c40740b04500314590030400700c80d040988403903506000302c0c0a2140290750001b080352551003075030b00b410700070034040d0a40b00006031640401006508849950800f131050007002c034102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 876120386 1250 876119136 876119141
    0x10203161211010f05010911031501080703020702120a05070527280c030506120a12020106260d03061202151e0405030d02010203061003090314070f0b0a 67
    0x11818a2408020500d009071500041c018030412900300784441490b48050b03032407081c080c42000b10201100090f241d0f141502060541e4500000d8544998080003000442001d52164000c054803e18028900c4d640d4114150000d00c154403019500899072184280c0d460000100c0d0500c07a440360040c3d8030034070355510030710141288045a14242c0040c00d80107501c09182449101d034800500c546c0c0c80d2072580a980440b600b691000301c1c5e65115900c1e1001c0c1140a03425001c0e168200b141940d0003100320015585231394458030212402811480c0300c99800c1c010354800d420400242030500d6100c00e001c411001140300c2c50391a20f6100c0503e004482c1c001440c54024400c40d4119070f285642e146107030103650700b0020040c00c184003d10000406001c0243c0c0c15500740104c0141328810b0045981d9242003104141c80c4c44080c04541c411a8010000c1000545510000d041c44600e05c0c20007044120984c50151601030b81c050100d080840d010030718a00f03010b04902019041c41c0641d21211305510b440680700700313 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 876121636 1250 876120386 876120397
    0xc1b0a0507152a020405010902120c1903090f021207060e0105120115020a0510060602150103030c0f0c050d03030504060f0507090b0a050f0d0e100207020a0e1302031005090c010203 79
    0x41411200803038106001504000f044004021010450b0b246036400181121070030b8014000003a800300702d141c4a00d075100071140c0c001c2003079810319041075543d0720000142820642c60800f019241d9210508200c0c54140b1410120750041c0303500c03c00e5200000140c0d0f80c04240c816800015000e4400d09203c0d4091022100c80b00c100c40b0003840344e43c0c02d2020072408040070050140851081d5403005021032030510403c10000d103c00c0340491b1542c40c0040091514001010101031310364448010030000741c001c2c1e51400c9041c1d02c10b4050750004220b003003062043c0c01541c031451700030403138404004c03c1540c158010f6114920844041082c84013905101003151007c0300e00e0300101d24030120078025686850060b0444002518001d442c11440c00010b8807103812001e408944541c90764042001c103c82408102c03131840710502d0841c184502070300003c0d0003804a110b0a201d000c1c281000c102d28040f00d02103102203c0c0c0107000c6420450070104180c0c000c000446654029029070095844150310200c00c454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 876122886 1250 876121636 876121679
    0x10b091f0302041d0d09050a09140708040c0f030f03030f0b0306061203091908071502030904020f19080906060d0218062214010f060c03080c1b0a0507 66
    0x58242558244401018071056020500075011a0304212007810032045003044003542e80c1282c8a81f0b0301080c00340d030311140c0c1c00c1441c40d2410098008070031200c000b185503015001e481d00030f040da107403401d1400941c0a150040b05040122150110a000505661000c031511075501000018400d08146040340c82d4030b03c10f640e05800640209040b403074111003100c1c02d9182c00302a02c0c64002d0090004124400846950483c000c05500c2003081000c1400503400406075020075241d8481100d030000d40740d02c02e00095511540d404124585000c4548090f00c00c000d5070903001c1c04101c01d06000141ca0075504850f401d003a4402c05000a08509040140e203640550240070300c030409201079071890106500030920b03a00280f040c2d005a403040c0700c440c040c4040c40c40000b80040c0310184e510382099440d4050b040a00101d400e1b8070200401d50b400b451404d42e00e03425103041420f680782d0141d400f001c0d10902d0031283c0540d0f0800150f80f9520f002241c0300e50154070030012140c140766544144c44a0b85500300c02107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 876124136 1250 876122886 876122941
    0x5160f060f0c060b120105240916090e0901150f050f060c01090f0b150f0105070807050106090e010c0315060903080f121006030b090c032802070302010b09 68
    0x1d41c030780d41c0a0791066120900c148408180203151001103007401d0302a00d0b001d6002c2e9120014031070441d0340c0d244144440ba8401d10700f1079440c0440790101e13440d0217015101201100d461031003414841c0c8929030805c094400c41000245605084003240e0103442501c81d160800341ca00f130700010f510420072400d03070111800640303514455101c2504000960b000883c038004a95250741e02c0b4000150710301070540d0070750700c203040c29032060600079904900d00d400d980e445c60045039044000304203aa0032a00391a80d0740d61028085540300510710700079015060b40d41c0704030741da02e040902d460303182141904803040c44155a6400c10127420194041d0b865002584650000318554200a2011030030f280f005020041050a440b40340c074035181d00707406440404581c1e5002c4d00143c03507005c1c48400d506024461840008a035940040c2c1051090320599100140005510700d01c4407800d502590010340300c02d80c05101d031a000f10740b00d454508000c1d01a0120f040e84030b00c5008080000b84000d15a0341811003102c1ca0759100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 876125386 1250 876124136 876124157
    0x15021c140906040308180705100818060903041715010e06010201140f04030c020315240123030901060e010803040e070c030f0e15031005240304020d1a010305160f06 72
    0x741b5880c10000d0b1219818002d00d900805d058403811421019116150b4420090789401d400c100300010619449a038240c00150900400080000546e004c0d0303862445d10a2990170320300300b001d00e0011701c83c800540c1c0026100002511101c4520360a101d10801c0e002070008440303030740240c030625a0480c2d200403440e40480c00325010034070588295520b03910180c11074141850504118402d184210740c280da01d142c0504900c80744810a81034000444403c1c00c0101d8000d1038003800018207400c060000382c02c1c450100009249400035000003008061020419000796140c0411135241e9000d4010308411200b10b01c0440c642d07a1084005e0402140c03d0340e0742c00c42c01b9818100c00c41c1c0d4086007120840d071015540c200d0105c5120b130200107502468901e500c4860f903c0c605030500c5580007114100107802da8000d84030b140051240030031a039000d68111b0b400c80b0000042d16050364889008100403801d02d12001c000700c100540090010a240c00c000e050fa032407556030300d191102000a0f4000c000024001004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 876126636 1250 876125386 876125401
    0x702030703120504170a030311030c07060b0427020a0f0608010e04051e0109110f0a030f050f0303040b2e090f0b030d02010903080c130315021c140906040308 69
    0x20820b08080707440e00c5441c04e5030300e8124000c00d000310100c0d0041500321500c028201030300b520644801c0c000f551481400c0d8607000000000e00e01901d50f010304120f45a28078030900e981c1340e0384a241c0c3c081c0d1400700003441d034144444038100b51000c00012801500980000b20f014501540380c14125856981c81c0c3c040790707003001c000c00e003913100261040307801d031290861a045010384103010f41c503c44007400000500d200c403400c01a5000d002c00b40d615010300000b00c000c91880d29510130f031000350b0303401200c00c0035042c406141c500c1c9400c039031281c98011400040f06000421118134442030140103d2035010811008452829181e0088150980f2000c8049031007008044104c1d0041b0300e02c1900c81100140400b03032280440e04081c00c80401c440141d5440c024030003055001074600750044223030f05041d03003440b0969528000c01c403103901018101920703584450070a41e07c076404a81c0815103d08602c0b003003904d410510310240c031f00359501c1c1d0142800c020000e0744403a000036042d8440c41c0c26560720101034503640e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 876127886 1250 876126636 876126653
    0xc040501120b03120309010f06060f2003040b190212031303180602030406030c030207120302030907030606290a230405120c120a0503070602090f040f0e0606060702030703 75
    0x141070030441c5880c1c0040c074802d941e0a0000a101075903002c000e5680745000d200a038219920101c5c1d1003901d6281800038405940e110490802003030403400d01c68010166603c0b120038480e000c0c101c800e81407000280220f001c486d00409400d0000d4a4084089199500745047e80c0710080e0342c080407060b01d0140000307003140b04003400c00100e150090501950410398192034410f07608240c2c00c0381d801b581c000a0204070716a0300d13210380e0342c2411040c03404505020099071400d01041c80500e010b400c243e00800461003400003840004000c5030320001c00c001e003d5543c0d03541c800c602109110b0010f0381d01400c000780352a20340c0380100c83e050703078442d40c402740701e411a42c01641600480c0c14540072028003c0c800401c1d00c2d200c46008200c02c0301c204005040d42c0e10201c0c01c020344c04040c43c808020035001041038100142c8000196000c4070f070f0141003d6260042c0402094010301c0b90904958442d0400120b54803c5150382d02ca0403001100d84140e62084e55200c090028910491400a4050b80503500130030202c0c3c00c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 876129136 1250 876127886 876127907
    0x1a040807020405090a0201020c03010b09040b1b0403050c0907030228050c120403050d090b120901020d0c0806030c0105090307060302160f050d0806030714120a060204080309180c040501 81
    0x150259800d00c100d5801040468204030354440140c0e101203107000566130100103140c070004045009001001c041070215540910281004201119070302c04107140c0d2240f4215102a00c5552000e1612f403556400d140361340b04c403560382d02409810003102082d2264401e00840c2d044425000e40c058203400c425401080609140c5135a100304030040c4043d039613442091101d4aa040c010340000c039111401d605155003401c940314640020310441810801c0781e030320000301f40c50040240a800740307001da51704800240a4844c0304041c82a00e440e000c00180002c1c0c02400141c0500010f6048880e2040f080d001510a441180305c0d040d816400040704010a9210350001c1600c0e9690003416400c2c00500d03541c08c08502c400e40b000301d806030014008002c08680c440702041c1c0c0b240c000c60042440910b0898504c60b00c0010441940c001c8080007140110070004015126107158005011035849030f9440c1d40c01d0301c076002440e100741b290950102d0124000d03a5216080d005400a1201b5481d0514080040d00d08441c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 876130386 1250 876129136 876129143
    0x703210f0e030c0a0902070b0c07031b051c0c0b06150d0b0103090609050102070201020d03050f01090b2e0f18090b01110106180c03090c032a0b090a0b03041a04 70
    0x860f07500e0740701e80d201d84641d50b0040407071100240e2241010300e03200c010a0001000001d01510a222507404a603000311408212481240418403031802800c005003410800b403c0034990030071880c50003c0644d4442e294903503450140c98100d4180e2a01810003140030304042d5070751017001083c40000c520100c564003031110401c05041c0050441e4440e501c081c1550000d69041d9003d035408512103040d0750b010b00400000900728941000a031900c5000c1003c0f400040c000c2040c00c40d500c003622600303a2210201c611580a4083d10340b00d010b158922002c241c0f080681d0380e4000610404905481140140d2141c598145054030740106a42007601074401450708111003410016488048805444203108101c050514402c401b140907000c01861000c2d00c500c00180c0c81050702d064041d00220b000180187c081d039a1203c2d114901e03c00c5019162946660341005050307984511900243c15802d49004116089040d00d03110962a550710094209000c111009011003001c40c1141d5106201900702640c894072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 876131636 1250 876130386 876130393
    0xa020a17040f0203010615081302220605030115080703140a17180a0b1611061201170a080a180f14040f0e0a03030207020d050a050703210f0e03 63
    0x500c5441401200381590141c2d040607444480c1000d6007402e00540010b0411044449101c0450400041451500802d0485002903085113001103684034210307000403100c40c280b04610000005064801007050b480303030328407a61030005c20791500304811400c0c60880740c0c7e5030094040c4900d181c4901418105030038100e030b05070154010400005001c808120760307246180d68030320380f20207007910202e40a9814080480c4241303000304003000f030b544019088a50070191006035104110305031800b82e901c5024841850342c04503000ca40d000d20306079810700f428100c48003543c210205842d220500c5854031480540038114a00c1005802103840c06036400000703000503d00d40c6080c0b95540c44141d08454419001b203014000d070718a0001143c60203000c0c00031040130000c010402541480781d0b0035130352010180001c042c1900498140199610312160000c050741001c20745e03890202900c1c1143d00ea54540c0000c940c2e1245140ca01811000110595091a103584e281c50300c03080d10f1400e0a658400480308026858407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 876132886 1250 876131636 876131657
    0xb0301060510090825050105090d1e15020f040e090a05010603030906261311120d0f091203050304061b0f020d02031602010810080109030206190c080a020a 68
    0x116407038450a074402c0d0701d41e6920629820801e25a0909120340d20380308540c843d01c2117515603241c802c05a0b5045443c242001070ba81d2401c44007060030020b010303d010b041c46180b0080b102c00c0c800c94984c400c44091149105071b011070508000780049005803040308580c0d40b000d00c0103003d98803504130500c1d040b40d15841181c4411440b41e881e00d0035107606410448c002002150304020700d68000e0060074401e40006480d42109001354022500e88000800302e15480c0d4800c0c4000c03041c03110a401c0e2060143e8040c04141011040641d50340c0d50b48940441c4e600001d4449070101da035944103143d54030542e0701806007801c0e02016030f10101ca65420250094034000e6444400303111100b0f400300c825481411070707294034450305c0d500c070006810800ac8142203415500304119000040742c009588649a0f582428184900d490301010442c01f14040c4d04031101c658640700d52141450f80020300f1520504044150189082048240e481916110b42002011072040c6021a25000c5250083d00102c1c24914100765001e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 876134136 1250 876132886 876132889
    0x30c14180a0b01021e010b09010e071d0a0306020c1c050c0d03050a0e16030b130b010905070516050c040b0f030607030507031815050708060a091e1409010501091e0b03010605 76
    0x14091a01d030003001c4c0e47d00c1d40ca001246c00d04a8413240148601850482a4a80044050044107007110768200800e01c0a00040d515500e482194000d141c004204649a90307424482641e44c0081e122001c4428181c2c07401458454821000c9442d070492600142c40d04a00c03007442a806000081c4c00701035002c1e107890f403807165044200f0109045000241c000150310f840c6050000342603c02030051041c0c90101d42000c400b00d441041c2c42e904582e0704601c0000e030341d51101c10403900ca0003501c403150341f052907501410b814440001490619284111410014a4900c1c001c2050000f001c542258064001c4030011b00b540f4000d82c070059100c8500d0501050001900c07480907000c014070402280e503865244c003600c0f60504039110f00750703201d81c071401c01d05614146480001c49004983c42031402c0f0503201d10050000e40c03c2d8907409000d4a250075410300c0b403a010440d0302c900c601003c4401c000c1c80d601e0710000142c01c041500864840c1c280d10105142c81c012850a014050124800819013540d254a8001030a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 876135386 1250 876134136 876134173
    0x90f0a11031e1c030b0d02010c020f030d0503161b0b0720151302010e1003150b0a030e0c0604050d14070902090a060801081c0216030c14180a0b0102 65
    0x400da5184003405103850f020110049095903110141c04040c5010390419080e100c04640140040e024240310146c2d0b0090b200007104d01c1c210740200760b010b02070440d262001a0700800514001d4582403081e0801e00040740c01100c2c01501c0080180710580c20b850101c000c900c419811a40010701e51401d00ba105403c1c0da03604601511030345000210380d00004c254050402140d200715041120f44401a14083e0907800090000c980c201829110301d00395112040c4982c000c0c0d20030040702c40490f01c81440d1a5492860840c0740d004a181c5001103802c200c044a8110b50105240c2c42d40d00d00103005e64202130800080c00641102100b0859200c6070341000085841d008210582c000c0080d18000750341e9400600900090007070f03030b9204000740000240140021000481d85007201d840d07071600c4500c02015180101d18000c501e10600b40c1f030019000b800700900c2a041414021341d03200912102d039842d03a130300c24025078840f1010551803d0410402143c002c1c12140c0080b402c510051049031800444c5c0c20070f8040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 876136636 1250 876135386 876135433
    0xa0605031e060607080318010c020d3b060903160f120309050d020109050409030908010c1b2003160302041a1e03070f030305070b090f0a1103 62
    0x104a0200420604a050030070010091940024507030507424454007042a900601d54010491040800050b080c03400448030708817008400f00091252403100c00006c1e440e00c05d10641d0f200003980d210303422100041d00308001a41c40681030781c401c804885036044400c1a0500d44462544032504004180c00d954040000c6202a0605030400f01c9081c0b4041701c10b0078103181680041e51084650203a4800300342c00050000440700140c0303807984000781071702c0100c5480540f904482d6000349170801110a0542c009805010fa500d400c00030040c1d951203100544242c0c000002e0744141000d0f141000307000521882c0d0b995036120010191440345480b4070002802c0461992900a0004c412241002545098040d0b100d41e1801c40882105000420b004904200408141c056a18104001e914400c3c0c0f01045800001d107400d418199100d500da1030014965444880246d502400c1407001c41c802030008210a0500c00d01100100075101c0c8030b9852004000c8202005645401042420303003c5070422178600c01d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 876137886 1250 876136636 876136649
    0x12030f07201b03100905030a1b0b0a02070b060a21140102040e040620030a18080f070201120501050907080a0204090f0209011e1202090a15260403020307110f0a 70
    0x1c4402c2c0a042070503d420040b0248600d81e078142450b0307101041020045601600551510a1a03144001d0080800401d260401480e1f103502c041001414041c40d40500003052040030018110380b07814040012841c100d004a01c0707121414410208180d1059448440d4a0311414107000b01da85400c00603800c982050348210324500b00c038070401007000420300c20303040c80c420450114540c0c4002402d40b03921b103000040010169541c0c401007031103d490351102295540e580165042d98502c03c0341590501900550030481c00300700c14005c40100c060190080c0b038180c680c0504004500e40c0c62030b800303c0d0003d50241150140d55400c00012030401541c1c05071405046000202503600c81c0000c000503d4849a100c004d101d45007590030440707181da440825240354000f00200961a5844070000035240311155001108141c029640b50f44869084000c40320f20258080492044c3d48060b500c2c05000d110031280180160400c104400006a01e00b0720200014030162407074401d408980007080c1f000c01c4075044103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 876139136 1250 876137886 876137923
    0xd0c0f0b041a01080a051209060c071509080703050303071809050708040c0b03090d180518100803041215090b040501140a020f04091112040803070212030f0720 70
    0x301c030284009140c00f07004100d58401449410065210705498009446403042c0046000070640e129598803000c2d0780c141119042660741155039042c110560318030100d00d01c40400c4400c1400600c0002c04208942165004005940343d0703950310800300c0385034070412564000c07014003460206905000d4480c6a11600250329110054105400d0403c0d40d20041d078032811280e0720820030014200b0001c208420840064100318090041280c0983d0001c84c540d048650004090048084040d00c08a1a603000d200705400001069444500068503442907000d000c05450301100d0441c0010729150821000001640c0009800707401660b4181604c58261019107060703440d41c2401d80409002442c0300c0d00701c4841c9804604d498450b8603030412500446c490303070314034076a920b641c6c1404006130340840c1c40d10b402a1100b910140342501e460b0107590419a00d0000511407020a42c42540704d01c01101c2c01420260701d0102c0c030b41e40b400011150b400500000c2c20250305540c10304031001c0c80821004510202043d4071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 876140386 1250 876139136 876139163
    0x70f0308060108060906011b4103042304020d060303030f0c0207080a0201030e0c041b080114090103023a0501050f130818030d0e010216080d0c0f0b04 66
    0x1820f91401800d5240300e0341c00ca005200083e03803c00e00c0114038060843d0081d070340c07075542d00308120181d881004144401030030903c0080c05421180b12911075080a220420311036604441241d40c90180380038000c03a109144c0000346042d4a0010b025040010040000d4031b090001080b0000f80c03615036000302c01090711000c2c50004441203000e215071240c110f10040032a14500940e00d5540c0400040c0139040c1503035464009040001884401c212400180c41481400c0702100b0754450000d0f4101184001030710f4000100e1006031890204486610003403469120383d00310f0b020844074a4851452520107803175402d014550f186201e280c04910f04608640e02e80102250a01a095910007050300000d21000310410050100c0c1400d03512405400001640e210340c016044c044c0e84011110034607926110f283c440c0140c0f03170780c0003c504107282c5082c4d0030b9a4100055208000101c03480d805008850b403c1071041d580b082e03208140c3c030f007011402454111100181912003070524081510252108440c4861 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 876141636 1250 876140386 876140389
    0x1707060b0a060521040b3108030615280314010b04051008190903170108010510091b080601050f120f090a0c0e25020f010c0f02030717070f030806 64
    0x24000380d0300d101c0140d0b00c500c1e482c0554a1254540d401007840303208040e02d850001f8941660940d04044501514034101d0300301c500d017060081500100c59240c8503030040f249445103940c4481c2940c40e031511440241c0400b001c0c1c40c607441640c1680414103010503999884100451310824520390013800400e0300340d40d03100c1c2810140294440078078070201c1440603007002d000307906c50315035a6144c00d29000d20b0300147c400b545180c00c030703075240c010852186400130703610000c03e40078419400140507290840c4040250359841d07040d402510400b2604c501c5251281242d0345015000b1519a5401501454251319006484440c3c1070a5002525400c08050900c81000030400b140c1c0c200c20f03005040540101a81c4c10315580f88003211b41d50f0301a880d24000d2141c0840d40e91000c1650303122080740440300d18081403410b0b000096844200c00149003441d07091508852405001d08004035a610040d0301a500d003000c00e0f205c0c42c00c030341c40f4410301c1081c1d403200f00034407004a280e8107038614115100780d4444689060020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 876142886 1250 876141636 876141667
    0xc050610051f0504051203120405030a0f030b0f041d10092a09020c0106050d050303040b06061e16050d120f0b18070c02031c0215041707060b0a0605 65
    0xd541510341c0d04103910200080f40c120f41074030102c94080324900c03041c0b00444521400e5000f0f2080e00510684401c3c180420010048040c100010256488070314184807900220141c0309905101600409400d00320303481401c1c1500300f84000d09101071071240d00c00c10083c00a252003880b0f00c042e03800e166194002000c00184413001d02c983e03d0310a40601c029281d002c0289032500241c400e0140320b6500040c181c1c1c10344000e4000500602d401030201103038643d5070801a480b548102c1d021201c1031070400c0000c0c41032401c0c5054864003802256030740c60300324003144144055401204840d500d45900c0c50780c8000a0410007402c224141113a4a084014004011a82c1621000852141c005042c008282050b8960b01240441e98040030440080360301c075080240d61038500b001c4080d4050082406881d0240d6203408600d0b1000c07042d070308640c54107115105d0280d045200f40e400034920064a00412107012061000d40600703401142e000402c41d04620000d00900616070040004c0307480850314290245c00b14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 876144136 1250 876142886 876142909
    0x504080f07050a06050c0c0a0e060f1818120d06031205040b09040506012c01090602160314030c03070c09050c0a080103060507030b18090d05160b0402010c05061005 72
    0x400081c0784042c18640022090704550241008000707010591800c4800c0405c0014424480505418013442d12007202500300801111014054503c483c400d03940d600f44000010340510301040113074030a0b00c030001100f1300d00c504507220220a02c1000000d80f00c5c400030f0001411491000d20300050020b10b545030900142403040205000d014040c042080102a560120348410804440002e400d58840c1c0041e14240110341d080c140d000e40240c42d02c1c82502c0700395645404040242ca171410810b54885007281d40300c03030720f040300e5000d01c0010001300005011403914400c05044a415281041e0007401c00501d0f50700902000d8030904402102000341804034401c1c40d03084004000010310b010002c0070003610000c81071000404041d5104001004580f1a500001c10722070b008014182c0140c40b1030200203152400e0310b1400c010700458280300d2546000c0d070100e910245482140c04052140303501c2d890160300d40280181e041c0284202d0483c00281d051028501c2080d03454500082141400140030701e44025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 876145386 1250 876144136 876144163
    0x209070f0206010905070504080d02160b0f190203041505030609070c260d0f02071a041e05010b1008090c0301020a05041418190f0204030c180603050706050408 70
    0x401481081030381c00b16115041d03e4901e80c001c942d54580340c2c03080712184996070041c052401603901e8030680700e0b40401c41c2074110020072110302c510b0317850f0a60ba000c540315071a220f2000364010400c06d14000d201521512846180c0e00549080c0350350b0744070b0360350742c2804100e080b4001100002000881d00d002c0d13000c280c000100346071034070300c210701a642d9031490280800800c00041070140d180d03400d0010b40003254428035500d41c050181750480c03043c00b0301030b4001c040d04075803104008400d0701c61a590042103d05c155044070707448d25111711020920301d00008284058030a5502ca004032000c0d0b86994601ea4003014096450041c5807405411241c00e101d13840301c24034441d0f4010040d1a000982c010107440c05e5a0a2904114001b40315100185003203000030403000e91109407500300312180e11100580943d032402c5070b10600240c0209400c4030100e02c203600004127040754035001401b00c2d1640c3d07220a0541000b0180002e0791a440e622058603100d0694880c43c0003460000b001d1098400a100e0310441022 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 876146636 1250 876145386 876145397
    0x20405190807121509140f210c070308160c0b04050f0d031e0516050f0721030507112e09081209061c2703021e1006090207020907 57
    0xe80d6110310313501c011100803400702c540751890304c402c0c44402c02a9503040d0368141d04842461800b50405922081500011100406040081e01e41d001d2000d04a03a80d0800c1e240150440d103003150703110000c44d00f07c21581d980c080704411041c0c0c00540c4a085520180080881507a1501d180c0800c10222850300250f403800743c4c9007016020002a001601c185020741400114060074503078002c11185801003a8035420000400c1d2143c070240440440e00c00c0c8030064910070781e440280c9038032408407921300c0c20340c040701100d040340e5034200480e200740042d2103003500c2440140d8440c0f4082000564219481d400789003080900080015049440300001a0071502424030b1103187d441c3c17080042d01c0702e4050300707c00003440c00000d1143c2c1c2c07070f40e031101241d5815003041c605100b0030201d461800028030051100c0628000e40411903240803003462120b11009501d0f600810030540c022090044881c03031081c00c0c400e00d00c504402144d040344a0b0107a4406040d000b00010313128400c6004111410102802d09401d200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 876147886 1250 876146636 876146669
    0x1e0527090a1a0301021b0c0a082d0a14010605011b021509030d0e090a0207110f01030b0d06151202090a0e0c0405040f020109080601050d021201020405190807 69
    0xc0351281101e610114005001400c02181c0c2c485803074411003511035603410351000070b010300c10000c00c0041422a000b0902100d4038101c000c0d05000c0c410800780100e8095611007052000d03032181100310500c40b914415420641d81c6c041001c2986041d0b42c150044030786e000d000111018142c1c003480f5a07002060246003804030b4007244400c002d0440c0001502a004070044101c8154100880044600d41c145c0581110040140c84800411700d03819541351601c1008140f001c0f0743c0500c900d0080c3c950041c3c0181e150b0541c11844802c211000c0685101d41d418180c43e1a0420302503986e800c551030242d40194404206c903844103200350803a6481d90007114100d10980c0964002d6203440c0403090b801442c40c500000c44ca001580090700d031800d0045070341ea00074245000c1008111440441082061003a00c810303608030340ba043c4075a11504e003400303102e40010709038501001500e40300d030581c4581080380e400185000d4071a0081210014142c1c1c5064100c42820000c100040c0d0400c60327400206061070300b608245 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 876149136 1250 876147886 876147889
    0xa030b0d120212090a0506030405070b0c15060d110405270106141807260c0405040506010207080d140f18010f030533040606020f01060e0108060609071e0527 69
    0x400305021b000e020f00c13000b00000c0c041100400513400a01000f05066840d01055000107503180c603817451440f00d0300710328404a0524203190b401110003c6c0c2c4084200c1881c7c1c0840240002804000e11040400d80c1110001001d0541407905200500d82540041086410310301840301d001616010356020300d00e8012101d0189a00c540c8203074200d1028503014034000805d0b40304d0303000f2050665407015130541020030b0011411442008208a40040d5410301082c0d50342e100580e01c840c0f96100d2402c86e50800c1001c0038000b846541c00e500e5010783d00701d510742000c080c550300f1460b54000c0d8003144404481a1130301c030100c1d038004244101d000d80d42c1c6811700051424007180d074486003200700050703003a0f0155103c01d010790b03e2003501c050800314090b0003003101907940c0100958030f60014840e0b0f0015444c0c400c001c03500284215145041c0c510b071000030000c540b82c1009001005800401810400907114841241c3d034600e9004080b003809180e803406c0c0c5441c2c0c0a08211329001c0d0150b140c2d001501160b000c558039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 876150386 1250 876149136 876149149
    0x30709080c0d0611040f1206110c12030c0c0604050120180d06090f0c03170703020a021207030b130209070305090a1202010e01090c1d010b030a020a030b0d12021209 72
    0x3103a9000401113082940d0700300010590040383c00021018049040c0840c100074100090b00001e805103c0a00031109030300708014441c1700d00c0803240c441c6e230002081c9140d20384843d00210782145014090340c0c80d02c0042185d2604110701502d044600e42d4542350158100c00e040400041c0038810490024a4405d4204000d0f100070340000b503607401b540302d243c2d10100b40151580b04107500c580120806c16540124602010f010150740012100000c4d4a000d40c0c2c1c2070389001058403a07455060b0010030000c40b20f03808002120300f642040f41460310449001000007010f41c000e0078060280b0200e84c40b100101c602c10408071080c0241400d08061400041000c40c010000d060503515800a001a00540c01c0002c100d000d40b01c0c1d03280840466003040c42e01420006650781d000b088914000981138a0b1082c0c181d000c5c00d5103801c1c03150802258041c004100c452620f42e00400c4a6940340c1000916400304502180700d50802d1841641c07801a40125803207003e8040c0700228102100b00142e6140031135401c000307440c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 876151636 1250 876150386 876150409
    0x14060c0303070e030304030f14070b0405060d050606190f030b040203070c0f0f0c1502071409041b0801140915072106090f09120c0209220215030709080c 67
    0xc00100d4102c003012628140100c46c003843c2c110360b14415032043c6003406c3c3d0142005503881d102612824400140004a84050310706460008028920703182207182118090301010b010310340d01038002c001c00000745045a400c80c2010700d20b03848520240c1020380c005030848010707a51781401180104208440355900802443c0c5850b4810345100034801d080c1844a80f410395100c4c000d00b04000c8000204090300311420420302e084486d400c50344407603290b0141002d205541802c40760811000004280080e0344042d22440d07020341c5c403105100c21961200d100f400d43c2c41c0d040c003108280b200b9509000c5149014800456003401f014540071050400b00402824407100810060090040441c800c100900030b0b0000343c010043c0c10014018090320090010007440d09910446080c1d149010103207003c0e0060088d151a2500108041126a90110010718035601107407080e2900300402c5283c001a941c9201c07ca600f50080ca52042d100d10305907002a01c261400e0f00103a150750312140d062003c640c3c45020032103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 876152886 1250 876151636 876151651
    0x12010b090f091e0309041a1201020c0d081b040902090f030a02030c04020d23091606020c130f02030708040b0106141c090c151707020c01030b131514060c0303 69
    0x801400750a045541103002d20380301c084e4000e0a12091605170f04280182c4400887e0490b000300b00105140300ca10b00700c0c4503030065881190031002c4240c1c001401000840d42c019211401c1c4281c00070355000c0341801c1c4c3c0c400e410080f4044c1e030204969906040c00112010401820b170700912001c040398000070303545c2086204451256030001b61401c00b20703080d40c00042002c5140b283c52400000320103500a0950303403c40302c01c90288545811038074042040301a80c400c8a81c0c5d60050300c031054183c2d09001c0c44400d00c52152111640310004088a26068402180308603000e81d1785044a0600703180140080f0070680c0824104606100740740f6294441104030351202c0980c040010503080f020350403034090300c8801c1c805000c098011b1b100003202c2405210b0320482400c0c603510241c1ca01801c040c0d809112000792000070043c0d106c0802944c0c2540294000803030540d0081a81803841808200201a1030840c04203840981c17201604208520001c50040ca0300e4000701c41e038a09103100300d10010f68a000040042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 876154136 1250 876152886 876152923
    0x100c05070b161e1115061c030311040b0a090e01080d030b0d0c1203030e0105040b0406200c030909060d030e1c150509060603160b130512010b090f09 65
    0x31841d09000c0d02501c0c0032504443c140c03a516807000d12010b860001000030b11a21405904990310840c0b114403002c84c030030329009286420038141a044080d81d40c10052048062594602c0c1c0070302d0340c444000103040101401a00c0554500d11074100800b407500320792258500d05d940c000144402800818059020704e10303464000307003101c1094000f031450502004080c4c00d1400c210b02c0410100780598640103100d000f6181800380000c0449554201c80d4100d501500076885000840d0000e1b009812043d80b0569846c041c4028108084005600b580004a0000950303c0002c8900720b81c10404107096100c0021201041d03601080c3d01d000c2c0000f541d1408543c442c140c445200c580301c01c507441c0888191500040b40404842c0c001001c04003d040586119880f4032452000840f10320340018030281100d2408076604046182c02e1858816402400a01c200da44480402181c15141e0a0350515080261400494510004070030b0051401c809060080240783d400100301c0c04440000d030210b0454a5103864 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 876155386 1250 876154136 876154171
    0x6070503011208090a0801051b0a020d0807020312100602101b0507020307032a05060a020d120b091303110609030a0c170d06030501050a0e0a120e0909100c05070b 71
    0xf009184070b40c1e031079294014420400411543e10541c0010b1064000003201e13446604030764403001c124060170344001c0050384402c0310703264038600c07540c0415044049401140d0600c140c40b00050503d04049465200c5661036010400c00958100700ba104800204242040301c8152800e0b032413040c0d420700100c1802c1c8500055013500f1918208015002503802500c0b034100304140c04501d140315820050040564100c00b8004a40d91410204640c00c80c100d54000b0219003506103015176401e8078aa00f0300303c00b2561020000180e880700e411032842400c4808105600c07001d90f1402800103c14004120321f5680944c04100c990034000044501d0030f407d5040003c801b030700902c0c01c0d01402c18038103402c80314400c01281803044000700350042c20a40e07209000a01036179565800240841c0c160075100309880e0301102025001c607281c0210b2070303440c3c141e514184480ea0710340c2d800b0444044041d61310a219502c05101c03c0d001500c03d2080101c07150507464168034081443d201c031606210f01501c0d940940807650751 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 876156636 1250 876155386 876155393
    0x2033703050f030901020423102706080a05100e070507060b0a0605270f0607111203030901110306060a051c1508010f0603051221040f020f0102060705030112 69
    0x340d500b20030508014a94900d4a007999a010f1340043c415400d9501ca008028001a40900c0c004c2d00c20b902d0142c4116023150003c402207a8250062103009083c0c00d01d44216400c0940c4a050840642000c0c0c40d401742c03601b4a101c403034017100d1004040460341c114003481805003002075994150030211502e08207842d00400e0a0403802000501010f83e48825030a000052a50700180904101c0c45c170000c01d04034101404290001d01c6214a00050f4421200d4940d0083c3c0d00d07040e8060320719030f801802121140e41e80240400d94111992020300314a520100c20001004c609003d500941704003688820f0842c20118041f849034000c4414407414020081140b11400740580390b0141c3c02c042c80c400c144505030310300208501e50103141c003c2007425400c1c0190700350940a10302840e41240d5010703000f400c1200351100403418640000685002d515091422030080400d06000c2900407030140e8030081f1561400d104120100d1801c0e4082030554008034208804184c0000c00c1d01d0442d9080035000001d00850f26 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 876157886 1250 876156636 876156647
    0x30b0403020313140316050109090207050f0a06020702031002090906040b04090c09230c07030507050313030c050f0306060a030b060a03080f0904061d15011707030902033703 76
    0x34201d400d140d01c0b4400004222850304080c4c01101c5040c0d0995184003e80e01004004004034090306010410f54501080b81185649c01004907902580c192016007101c5007219003440302c0c0360703029640660003141c4001035150900c101c2c4040d0050003411490032801c0300c04038211580080007075118554920141c4070755100c1740c1010501644c4400c130240d10f0ba0302c800200009101142e041d80640c000c0240d040c200c031a00d0100640110302c00d050840c1440d0140c0e8045600e5400000300b103410380400c0c0007902d001680044081c0c05544a0101525a01e0410052010284881401034425400b40c414010582c4811010000b80c03504140e1a8445a0704c51001c0340c00912103901c001d1143d0030004010b09140c2c10301016058600c401c032014008550741f00b11035040e400d40ca0040c404024204800f0400c003490b14030040764183c00c1030604a0a880742c040c1820700100d030440d00400401d480d84500302c01c44c6414000c0f080c0381c440044680740180c0018150442c11030300713420041e03a64a180d8102000740b50094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 876159136 1250 876157886 876157897
    0xf06050a0e0118060f092a17030a02060f040f060c05190210050903070803280e0c1503010803120604150f030b07020307080f0a090905070c0308160504030b04030203 72
    0x64000340264400514280003e200b0940c041d0341d40c9191503001c40304003a590283d080b00903040699a150184082c1c20030030a18489000c074200e03039280240015560100e4147d07508204403400245403075030380c205c0021f8145140146400b40c41c00010041200080c6400f241ca0300c0c00360403000001d1141c0e1100c80a84442c40703003035440140440103e0120715203603030015480d041048408400d0040c1d0b1141003442d41d4070702078158003e140c8032042c000648000c0c1c3c80d01c003021015034649200082d103075415040c2400c13520414510b0815420000100405d41854101c5001c1c04410260052440d0b01d08003e41e5103e0140040c5c5e10103010300360300441d1b00c55603036803c071b00b900000074010f0318900e035515186020000100d200880385201d034000002d21070384c000700659844680107201030303261043c1e14042c0b04643d4080c49900c003d0226201010036200002d1187c24820005915400f800151508000d045684014419102c0030040a14200b010ba401820744085a03403142403e541600c1d146016801c0d070081c0f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 876160386 1250 876159136 876159161
    0x10031218032301150315060e0606030a06030b070c061d070b0d021c020307121a1c0f0b0712180219030501140a0f05091e1014090d0504030f06050a 64
    0x7000002e100c01c500203040841103031b00c98104160300c2c8100c3d0840c10165806481840da042065400290083c102140210303403040c01c1113400144641c070380c0d4440b40043c1040e20304800059031007080301c04104591164480100307100303a51148114840b144c03e039551201e80901030b2810b03c04911804891841e40503510000e1004821804100d0040c01200c02504101c4240001a032100a40683d03c4c005e88251881c10074a188140100008442403100c1c8100350000e10101f0592004180049960303e10908561840b403a19100c641c100100300410b040c4c030381074020801c5450900e06154460495203240c482540c16503c92040f04400220300000c0104c9a1001d4865400c090000350105000e4500a1068030f0600b020414030b10040803140803079504580c0c81da242c0d8010307038009680035150a5052003d296002c201d82c3d00c0c1c40750540039800c2e6285031103030a20310032241092020184048c444002c0c01c010740d141c030b14281850358944440007404c1d280c01074205030baa0f10104603440c8040c3c0002d42542803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 876161636 1250 876160386 876160391
    0x402130612060b01081f090c14070f02040e031326030d05040c0f0b030f09120406020c0a0611120f040e01080a03080603012c100510031218032301 64
    0x99030300341100030340381100c40d5a000405e50b00000780421044030f42c0d400e14a5240001c01d103500d043c9222480117100380c80701c000c01c3c0203400d256081903001c1c0100030101c0c9c5104280c1c0000c03240711841400283c0b816001c901c1c140d80c100f404420004150744003040c08807140348a890110002603a43d00ca05840603600041311400005250030742c0000b06c1e08074500031480750ba0b2556110f40d590144240100460007000065802000441c100541951445400028103800e0358901203041d41002c031550720075801040076030026107550469203068a582c5000307040900703107507a104480154441d21800550380c44187ca40380030661300e03400000d235025100a010840f0035031040e56150008903507584000b1604600141e04c01001411600b01800b03031116210800e40440d02641c0b0402d207084072402500350600c540d00c10740c0315400c1c840c0d0b614011103014221508130b070003266055003030070204009003903121000d000e8406143e030001001101000100c0f0b41014106918141d0050180034144069218000960 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 876162886 1250 876161636 876161669
    0x403200d17150306040c170705060f0a02071e0608062e09030203030a030f0f060503060601030f02121303200c0603180106080102090103060518270a030e0915030604021306 75
    0x2c05503a86d98143c4010340312901140140d514450356800150007040d4100005008030a0b000802d8000751010ac140d0b8010340310300c903480340c1219122150380ca1040c11b041c038051104205440e00300c00456004882518100b004150a03203844605010b1190100c41121050300d040410b244603005500155a0050581e079440f07150710001000b0345510710501c4440362802e11031000741e030107610651040720300150107803010b45d40ea20019402000c1c00c1004001d125001c205040c91024000090783c0300321001d0780c51000421160a009080294001950421400d41c0e0365108130f82e600011b1801107644111100e560300d696064180155007000c2011918940c00c102020071058810740140c16804020383e000c00c1040ea0724010131000c1204604064544050040032031403c3d41240000071801c0c261082280c03824280640c064075203109034405600152882030116124600701480c640c200c80c01c4240010490040b000003038035810003800080c45007460910610903080303103412540003010995044401503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 876164136 1250 876162886 876162893
    0x907091e06050f01091a0d1b0e090124030e01090c030b0601170a0207020a080703050d09120218040c170c0301231506070206030403200d1715030604 65
    0x450000314051141400c003240841c2d2810300c0c3c4804400da09050352011801d03071a103180d03111800a2051040c080080c1041112001815806400c800b05d0f0310202c01460b000c244e41d0001e14200d4840307a0384c1c0c850f000d01300c0100000024120014102e816600c080c9000015a400950080c0705ca0b1521140950038800002e06111124164104070303402440900b40641d1a41d0045803e0a482220746c00106051008119a1000d6074060110244090031901116445030546494102c059100710382680c403200e2a00b0b4065804040800144070b040e11168405100781e0000391060310440243d00c0041401c4001814066080c0e0310200608081841c0080d80e8000003c29032103144040350315000350b00348030b6011540e0400c2604a4024100d004950788140c503610011040c83e9030703051340550b2009040c0400f00c0540c2c0cad91f8005500891107a100e940c588241707500300d0b264031a03202161095940048000c050820b41004a0620564007420415510740d1904091003010b11000b0010313402d841100d0400082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 876165386 1250 876164136 876164171
    0x20d0e010302071a0f0a0203100608040c05031236060a030b100e030f070303020d08040302010906020d091e0b180f01020f1201080703080f0f09040c091806140603090709 74
    0x2131301c3d82214105071703951050542000d0344020f81c0d00c00042d244040382048840d224984e4103400511400d401000c0c01da54a0000c1c0c9802c0054040003200d140028600c8030030034507a600c1c41042c984a018085102e50b9020400e00f0b140418004c45026030340001e012002c0501c00c1d4083d07081010000e1083c154080e01550040801d240304d50f005e4000e104401542d0400c090028a50b411a54158010440904010741c2200c13003200282c0210195921004103200241d880c1c0003070480c40100390300c0050f244a00e07040145000c5038051140c00c200d000d0f07410000c0411101c1c0902c6a0000f0100320700c8550705803003410107142404a01500a0f254400304a001c81745501d100104151848000307290041d98951000030785440207440020024071080190030721085c089000b805041103280002c40c2400c42030804a000d8400c0c6907603542c00508005010f00c88107105281e00d01500c52904000c101d05820152003e1030302c100c81c403641d071040fa030110002c6c0b07010747e0030415040601107a680034000703d952340b07140407031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 876166636 1250 876165386 876165391
    0xd05010213120b0a1107060c0806130203160e180906060423011404091406070206100e0406110f071a010522050901060503070f09060504060501020d0e010302071a 71
    0x1054444190005036009051a940810302d400c040f205115480d1941041c0042c90212102d1000f018140404008140b4500c14100c00d1303040f41e103400c1e480b072415000f0000f410400d45190311013548140b0a0041158042c82065204491401c3c07440095109034001903070308140c42002e100e140c0118040000031040825400e00030002501d050051410011079a004100c003c01c9030984e54000c00c00401148d0031011087c1c1200101520000b061405500d441c29603000c1105514070f0707a072015041c0240c099041040c180c0c02421a0850010182005049a0401c00144c000390000d80c8138164554918007103002c0340c2c1c5805242015a036102d0700341c0717407a016180415503518071154132100001101d08080c04120410410007800000201803c50060018031000c0c01c009500d658452003c01c0644040104101401882c0780d13014440f850050200242d0f1120f030070250140d030411408009698001515102d0344041c1d081903078036401c0c1100101c0007402151009091569594001070111031800802c60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 876167886 1250 876166636 876166657
    0x60501080c1204080c011d240406020d090f060c0f09050307030201052107020601140307030206040b030a0902101710030506010626010605090909212b02120907030507150302090d050102 81
    0x90300c4484018030b60400d00d00c200600e00b42992240d000400280351a4000c25331030521000000d0000c4031501c40c80442c048005c021a6681d07074035241c000300650848000c40f000303149813821120227414800880d44404040c03000906002003c2250a6911502d00f00d100348a145141c511027203151481000790348100c284510b1412085551205955060100d1a403007641d4028081d0b82c43c01d4640001c02d02c06034002400750030650b0b074400454006039504c440ea002c5801050b035550680c100f02e0106821450006442840c80308075142080002840120714981103a0690810031800448a0010340084410040c4424120110400494001d4005000d0008100c007514842510f903a0403484070742d145400941c0181221002c03d07054041407011000300704802c09000c0a8240c5620403d17040d41d0a1360203c25403010a030081441c1e060250004c100c19884401341c070043c1440792075038491507140d260318000c0e9105400a039400c50302135406a0121000e4010140902c10040000d06000303001b90042e03100c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 876169136 1250 876167886 876167893
    0x160b07020a030f0801080706080405010b12061005040515010e031011070b0a1a100e06030406050906060913060b0d050f010c14091806041805010c03060501080c1204080c011d 76
    0x8040c014030400c41340d4161200e400040101d0703428035a00b598980300007881141c0c50b640b00c04403100c030340e11b81c5a20b0500c000d019000904142c00c04070018800b095607a042140a280350208000d0712008503a40c0782030340c03882030800f4141e64001c82d0100b030030040780307095401c81e072414886902400480c1000400041c2e000f0b00c21032200c1d4948150302d01c29070b2480102c4a15030310358041c04580600e0040c1082c0d600046a040108002c88007030089940c1e90000c94080d0344060396503003048620038061020650001080b5041c207145d00e016903414136850704121018242c540c6d03c00445c1034a4030b070900600c008641140480b00440c1c8009902d03406081500c01c810000381c42c07902d050b60902c0d000c006a030000d803402820080b088183c0d045c244007001c00140318a030f11648400303481650002c40700740741032518000d2002180110102d07034007801703035a03c1c0d61110781040400802c1000161052007510340d40c1030780350007d481c1a100d6050040031406484200b030429441e0240a8410304600b00150300207110305801e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 876170386 1250 876169136 876169157
    0xa240308070f02120c153a15080c030a2d20120705060f250503070c050108040201050702040f0e061017030c06040b07030f020d2310050105160b07020a03 67
    0x41c04034501a424a4801c00034148407121114284515000000e1b80342c501c54807a1684661320800540380c0b44c5081c02300c0403d44040c184044a4240020000c01c01c1c1038009080d840926134031300381032080d40c80c0c0c41c820395641000c00c07103090784040c3c41400d5603507000b500b0111500e16080c0310030020f1804100f054131600131451040c8206101003909811a4001407009091012a21120681d0b9100f400f5401140d1820041c1d14030b14800a94001141800f950003182c41c0c100134940340c8051000c0c4e0700490b0521160401300401030380c0c02400c0b00c01c01036064034041004141003a10340c0c06004e8054a16104d40100070411086046000c1c0d120221220152801d04011341040515142c1c800c018044049800440001e80450700501aa5803c408180360018402140d01000301c01c980005240c11361040e00c54110851045840b441c1100c41001c440385807500741080308401070032804600c911410b018011802d400c0c100c07140d2501010582d0808000303e120708c0c0031800252224920b68044021684e0f6004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 876171636 1250 876170386 876170419
    0xc030213050118060b160816050601150503010f170118142b180b04030c0608061f0305070e0a030812010b0a0804020d11180a240308070f02120c 63
    0x2d86048920045c1c07494a40010940d0300002c0c03503030341d42056410304000c00494100d01840c0d002c1c070480307602500180600354100042e85e0003085801c2075000030070805000510080c0140760140c002c032413104106220410783c100e0014003511005040140c03c2440c21018000c0c022001101040c040001c070035104c410041300d0210701202e461030a0010028000e80125020501a000144000c007401500c0c1e044c00796505d08255080d401074104807000c074808101004000e40041d00160008070450340e042d05903070010000c0d01c81705226100c0c44101034441e0041065580601c85000312241c002e04561503d907103034189628254040030800c50b5030259480002445406071050325015034203030762501c155845540030800783d0001e603d01034414403c0710f40040070b20780d02c002c00110b080c3d00180a01e4140d00c0d1501c0d01c0c3c400c8035505e030814508038022481501c1501c160b69401c5040d83c0d40020b569407542074034100f045400c50301100082d0440304100d503600c2c00300000201d11000300411945841407404000c1e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 876172886 1250 876171636 876171641
    0x29060d0222061502150a02030903071202010b01090515161e06060512010507090b0901020c1f020c060906040303030f02160507140130091209031106180d0c030213050118 74
    0x41c14040d90100800203d0041b18641d0011900003810804580c14000700d600c800c1100c0ba0302070b0601d800341c1e548a07140c0860303503000a044401030000300c400c03540d5101e07081e000d650b880c0710b1403c0e040d500c148090000c104005005500c401c154000312411131040805151140c000c0616024552250418896010a11005000780da00c43c00d010f540e4110b166140c84503071842900072010443c154090000b91902d5a221300c03407620944603081e0304414403076049200190800706041c010302d008440803c0b600c500d548990040b502100d034540b900045050350011200d0090249000940d030030b045003d0118284040002d9040a80d07829841c6800030100c0400103540d244040c01c503040701c5601070103084840b10303910f08140c403540450400100380d401c40c41e82e030307004500c42601d4168040740421405105000105d000c4640d82d903410b41d03160b45403824036070703170f60300019894141c09100d241c91442c2c86c000c01c608010100000e41c0d002c0c2026884040c5c3e48215005080c1c24004ca00e104406003085180703500050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 876174136 1250 876172886 876172903
    0x618060a0e030a1b0501050a05041203092004060b16120306080c130f0e0f0d0c02030309040e0f07030510050702150403050a21020729060d0222061502 66
    0x1c0011840d2060108098420492030440c4680c030354501c038010701c0800e000303000b0f20b4825240302400141c2840c191505c401c181400302c000504240c9070140f8040058101306c18140030700d14900c010f140d84054003000401510058010b8401103001140518100300d04803074401b20746100741002c8000d07044440044088400c644203c0016030b202d0440d60441e400c0c05441039404078802c007004070312010b1008030081510a8441c000ea5213911007004041030003000d00c001800c28070b007460001d060542c1d80c1c0000307590b405143c6105102c0c0395524114100c1900030008142e104040109071071209076a41409916500c010300d04250017400d0038001146103101140c0000b25801031038442c1d0454070340f900c080740c01c0d800071510103052000500c910030642480800c508031001d410200941e96140b02d1802844418181c1c0d000c0e1887d10b01c802005000b400d1a90b103955004e40151504440040e05000240020644540c036445400001014968100b80358100702c081e14103c1c00f2848416002c05022070340c0d031011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 876175386 1250 876174136 876174161
    0x906040803060402070602160c0f08010612140304080a0b01063506030c04020706020705012f211501020d021f050408040e070c1e0201050307050306040603050618060a 73
    0x2040098030300d03d855405810480c0c001c000060920b4506401540205000103090b242005070714400c02c0300700ea089000c503000e42081c000174000a0302d00b40a6012410009030300078200350856815481c014010000c0c0c600410024003140ca03002e40e2400c2c502040c0c1d00030301551f80003030070321641481c0c0c884c00c59100c01600080d6a00c8a03019045c0c43c466040c4450001d0611541402502e85400d131942d2039001070580b140c054900141d5410107460b21900b191404003640c1100d00c0941c80750070080c980c1080050150030a42012aa1090022200c001115900d55160f00c03003480441800041c0906400391005175600303800f16120a44c2040e0285c5e075568a04441c86446280f0007510b407800210342e001190058441e00400d402c160300c418401c0102034044031044000303042042d8aa007400030301008140d400380345032202d00700306609800080441c44014070880a01c1030000110f171054490364800713002541c00c0710950b1a20305103100720690070075010804446034820980840d044500794031400d02c03620340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 876176636 1250 876175386 876175403
    0xc06210115200f060702100e0a1112010f050a0f0b01020105090318010c0c080f0d0e090c03060105130609090e010612032132070228080705030909090604 67
    0x85920741c111403066a402c030302155005101c40b0f141d6030300e0304000860107854036801821440e03891501c40030440e5400070b000d0900e948030808400c0400d403191420611a20300b55400140003550b5036001e4094003072811002c150f14601000c1200061441d441085080c050300000d0041014250049007618000d55046200d0f4004010b036580541e041d022140340560107041000f02e0000c291111060700c00d0350741c04800705030413010005844a0041c400205010700e036041510b14040e582011030070340e1100428600c40d01d00d000020404580c02041520800c92400f00755551040d00ca4800920f05010ba200d07080c1c040f8145129008445010b0050400342c9101c3d800d8444484050744084580e04800d4211002c1c0c1c111042250b0580d1105000701c40004403109a050400080010303030076050748211406600c00f09c04034040c80743c2a9404203140b690040c0e00c90041407068640f503080301440d44e82c00d0380180041030001351300c005c20101001a0200040c1141c0500c402d68480548545588044038001c0ca03406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 876177886 1250 876176636 876176657
    0x3281b051c0b010c020909060106020607090f0e0a0609021603080705040b07020d1103061f0b030c160519050c0a0503210309030d142a07030e030c06210115 68
    0x3107154828016180c1c145420018030700c0765008210610310070340e10002c0c2d58102e0801405119010800150000300f60f01d03202d61214500380320609c003003420340114884241d07150302160f07114405030030010150100328011940c40b50403889a129101c0007070002c40104074a00c00281c0c1090003901503c08580d498100d45280080301d034200140b40303610b200c04030b82c0e9000d070282107003080e00c0402070148034003070703140c5a4001403210313002b901c440c0d40042d880102022001c00c10058140c0c0310f8015035107541d1902e1150211451240381c400d040040403545901d4110080c65410240311340061007071004c00080c0c410007002c0d038413401810340f80d04000703441c94014052007511201c16166240210f600030001c0081e2410f061108012070151110070400c0900d8005003000c0c0140d1495444140410780391ba0b20260800b14841c40c03940d0091300560354007500340110505905040d480501542d100c00b04014840c0340e80d131201040200f58400c07001c2000c40c3d03d0110300d0011404002a0143e8141d000098542c0306454 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 876179136 1250 876177886 876177937
    0xa11031e0901020d020f030117340b1c0605030a0302071e091e05090105060a05060d02040b0a0903120507030e0f04143d060503281b05 59
    0x3280103803540710a0340d030800207444c400000b1301c080e240040c540c080d825920b51508540200340a20003031604c6580c0c00441070300c9000c110250300c41e0700c007a1100b5400820030400c03125448040e00700360300106021000240300981d008a1a92000c1c01000c4d003803003000b4250705c40c8203055a8440c4400000c000d680803a10501c40f50303801103001c0701448441d6180b20491a140c01070802903d5a1180310254140001c41c4840232178141e010303041d44040c940008116510345207001503c0e00c5c0440c460f1034091400040c0b248108841f61301254080c2c84803c040c2e56030352a030040010105466403000361042c4000303400341044981301d0008c4030800c98050f6910b140520328801001051403081d514198050f503561f031300301e003003200040c9031038810108010b00140c140c4010200c00c0202c210510400c01c0c400e04030749180d56842c01d141844007a10464581070351a039551416069000d244041c405c1891112a800391812041d550010300c0c8066409520440b440050101a1454050b0800301d8041d8068002c00b08041e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 876180386 1250 876179136 876179191
    0xa03030b0a0815010306110c060f090a0204090c0e090a0507090b0d120315080708031b0a0b09060106030f0c3014010f080a05030f0a0e180a1103 63
    0x114440288403201082d0b882c05110f2500100c00b099002400030b010040050240354426500d540e0542000c40d46000c0c0210422a112000248900d01005012002c0340030038400700220301c2902d50240c81000300a800b41004041c0340d0079881400407085110340012440310700030503109131315030740040240450760030109160090800012001d0b0441100c40500303020450742c038210450303255140c8000408150040c403094000600b50400302c007a5026070b004101c41c2a0000c02c0351195055450f080d01411a0180041c3c01c10b52511009000c244910f0103121511602254560403510b064900f0056040d4040429045d1020f828151021425608002e0316a20780f841c83c00a80050349812041e00c0100401c0b2103080b01d10460000e4907166040b00181b2524213a24004000b41c81c40100400d00c09150742e44083e501d100341703900d80924540121f15902681d000d540700e0359089100070112a0000700450700c082120504950700d18200b400d05070380542e0340c9101f41c22240200d00742d100003444050f6004003410b6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 876181636 1250 876180386 876180401
    0x131706011202062a0d030219030b06070803250801060c0b07090f12060b0f0306060d08070b0c0702040c1106061512040f0b070215130f24110c0a0303 65
    0x30403900801100f400380d0130040031404800b0085880b078118038441c80c00d00740740c1281542c4481c2418410000b84465110070207845520368039034500881c0398030300100460b00f1801140c400408080012040c4441105001c03580107060001c02c400003041035070303440e084075040303801c2c0704010118540c028904080b41881e000c4541c07109242c104100340e1961201000001070303495001e402c1c0c1d6002c2c8190071040000d18007842c1c0401d68116010b5010142c18000242c550341d028065612641e5442c0c9400300b04a4610150340a80d600910004000e1402c080215900d40c030000042780b1440c40c00c8903420189006510840d17030040356000811543c0c1d1040d05000d6804e420701000901e0342418010034211200071079185100e540b090708a8a00704e509071074003a805100c06821417080d500002c0a0b140288200340c4410f07480740042d242600c5c402541e040804c0603484680d800b4150190120302e903501c11400070340c8071400d10001103007008a101c100005c402140246038a030b00141c0c00205100b80803034801d400444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 876182886 1250 876181636 876181639
    0x408070b070e13060617090607200703060603020f04020a080c0d090215040e010b0406050a0e06270306090304030201050f0304060b1c030e060a0c0303151a131706011202 74
    0x1052080184000780040514443d00c0e0500c5031140c006015440d403008a1410348034280d802403540e41440c5484503200d0074010304500802c682e011701035007085c04010041d01103802d100162816607460f42091401b8041501099000d074031070002e2000c0a00f4184211000201150340e9071031107032182d18009006500c100c01d60b0407080e4131031a81c5030141e1f48525520568100c034501440d541c42c6458155004103005034046022800d050000f00026a0002c0884180c0304192500110441d450307000518180900349010261000c030341c80d4060035800e03400312b80250319070880480740c4940e16503030442c1c0e0700d110301c2c000240040d000380400c07a01c000b0f001c4061508144580c4003c80d03016020404921070390703026209100c4103600f415144003070503004000605892010340704e85d4980380030a500500030880fa003400408141d03490004690071110101920003030304e10201a56109046004000701c84c0c0c014000703240b6040131100303001420390030081c1d0a6480b0b0b212180500030f203130b2808040210180300750100b41e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 876184136 1250 876182886 876182897
    0xc0521040b1c1103090a080c01060e0901050a0605121005060307030f0302060f07140a050a090e18010e0d090e04050c030a03080a0e0a03140a020f03040603020403050607080408070b07 80
    0x418089a01d1010b0030411010b14110480c188807045464140c80d10340f124201c0c1c00c1e5041042c400c1500003c05c190a02c590454102c0303030380e05180c407449401004164000c1007111a00303414804860011341005004a40f10041403120544070700811680c2088020746032182d500c0740114060602ca90303040780b40e00c40e4004096511950b07032500c0e490610180300380f0450050304420100702c3c05c1014500900e400c4116417030103210440d0700b00c0b18520180704100410040c05404520a82d44500c0b0f107070414013810f100040f00040d03060500318141d400350188601203455090001e15100150300052440e00300c81d0958448040e1890f241c0003c2a020300640243c1d060b00405200003a151010014401d00724425a034007211403801e50044803c490200c1c486c01030541144000d0340c04617038400400c61032156401c1c0c2d640d03502c088000060303241000000e9942050700001c40d000844d9a00b5a0181040300c0c026820390360596182081160104002c0701c1c000e180e40410310649010940c5906079551240050810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 876185386 1250 876184136 876184139
    0x1409040c02030f0a03060e01091a0405090c0a14040c2a030c08040b030f0106030b0306150102010b0a09021e04120b0a0209311505090c040f0f0806070c052104 69
    0x303d00c1039400460140003090300c89600700200c0000d00f182c1030061850005c200324405004251040701402000400e00c034a4940000c07813107214042c00901e00b0950000d0011240e40e640d00700c1d1620400840505c3c0e880365180c00700c4000d0060145400e0301400d0701ca01d4068844101080c0c1002600c0000c1d64190100204000c1440000c3d081c14000e00142c003042110a03128130700500004031010050300550704242c20841c01d03130200e850000720071750040f4210305201d00842e0f4600041b401800402072041d480f03a1040c000040e44031880d4003d1401c00145400c844820342c482016145c244103c0c03154850708894a5650000b0800310620542c0200c9040000361600c40014000740c40b451002d041e045500c811007081c00a40d0044042085541440240c00e20603000103c9695016031010b114081c010b031186030000d4400e086020468018010041e990003205807900c400080664017400f81d1507080c440d62000c140202d0103140041841da81c041c004004404a5015041004900171040030280105200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 876186636 1250 876185386 876185407
    0x1f0314070b040e250509130f020f0304021008070215070509130b041a18040c0312050703090506040b0304060c0e03010e1b0901050a0b1c1b0f1409040c0203 68
    0x208001c100e11036200072103003130000f0207240d41d18841c100000a0980211a00b0249801c142518068042240c008032840007040d45580a015594041410319100087c0566502d50002c00703980101c1c000e48045075000090441075405c1c0c607040d188000983c0c0700401c9040662480d452881c1c3c04010381c41c141c3d003420b124001050000c071041124100c5d0310703150100701516044ca4420300c0c8005a101100d01c0e400e204007008a03c82c50a0505100c41c000e500c000002c09209583c0301c82401980e122001c10407410f11040e000707005400418044000900603640042c461070140c0944040c3c8140382055841c580f03c580d20344c0001c04103103080c0e01c00d0103184000e028071990300388201d06843c01001c018111280c035500d615954400c803d81c45600c107002020061080da102d0010742400e0b2081e002035150f80d6400c1d00e0340c08000c00071048240c240242800c04a80e199a141c9144262107211a116540100d001e144142c810302001252080b00160901040220345001d400002014140703005a03803401c60706a8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 876187886 1250 876186636 876186659
    0xd0602070618200616020307050306041b090c08060f120616030c08150d1707120f080f0403180b0d0b09010f241704050706081f031407 59
    0x1d00c10010440d0600710503040c4145030f02c0f8207071600004a8001c00209520380050b4141c0503494031106a10381c0c502100f401c545041040901600e002801c0361054585403605244900205002002c62480010001030303208140c041c158003c0440e4603140e010303aa40806102c10f151810728080d500c90701d5079015094100e024131001e40a1080c5110010720307800c24880140c00d03640362000c00c030200a5000c00300b1900f060703050f812030606801294000c1c0d900502d030805400141c822050840031220000c0c011040001c600c402c9010612152101019184d66141c281d41c0c0c108129183c0c2a4110b00d8400600000c0c42442c0e1540e090f00100030202109845a6201600da04402507151810b0750341c0781005680e2405904e4503004104101e0382c02d590368109900400464055490800c0451010400c203031818001c1d0300d15911000028429000362900c0d0401642d6030f000b5200700c00c04210b0760004292041100465005410300841011005514640c0d40d01540810b0a0880d455402000f40204442c50901d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 876189136 1250 876187886 876187901
    0xd02210423030601081906050a0608070f03110a0b03040204050406020d090f1b06210605040f0f060b03060f0105090d02041805060903070308010909021f0504090e0a0b01050d06020706 80
    0x3941d44a1005a4200b4907260180681000c860f42d440540000c80c1990911400003031103900901c0402c0310f8441941c0d1102512483c3c0150901e4000c0c0440894410044520002124011450b059076210500300340300150469004d01c8815500400005026050582000f03403c24400c290062400b81110f03014011910284001c64803885940e00c80024803100d905a0000421014581d423007a500d06a000740c0040d0750000001e501200365000c1c0401c0c3c2500c1e500c92001800050801e0041460940349003009281402030304201c246031940c049441c01096059900c2013a004d400c0000d07248154006488a4122041031644107400e10f000a0068507140900c8210002461004549183ca46410390400b03900600ca00803540c010b11040300400e6120599a044842e00000014210305074004240038001e81181080b410b1441c4216035000c3d81c0c004014000c56028000410a1260300000700d030716511500c030302410400843c1c4c01440715150800b6002002d074031807100145408003580d500300598044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 876190386 1250 876189136 876189179
    0x60b0d0c0f1b2a0e0108030307080711011401030605070f020c030d1d04140708070503040209040308060616030503090c0f0d0204050c04180603020405090a200303120c07140d022104 79
    0x3c0b40c104204008030102e046003d0320242c1c0241d802d5181c00c001c0117151040003040441048411180040c7c240000e5000e4170006940603c101440d40e10303030805c107002e408207451b06000942c40e101541203051000c500c51b07068050080140407910b114540468040c0740391001648810340c00d400c220040e40d0b81f8403844c0c484081e40326807000645401c40001c0c0c01440014044810300c40c0800402005a848100459029030305062258ad0b40c1c0b10138000c210b01d8040c0b43d0707821030041d0003003000360203040e08400954440c030a420700300c03618040e20200740701c40c0004040302c4ca0340119034021035130014078054010580c04041072440c0350500d9942c803402c3e8090800141040b407241d58412003401035060600905a0080d10b80c00140403005c035643e0f403560442400800d200d4400b11010114884c1e903401d1045420403400541400307010300304200c540c1c20079480007400700e0706045c54001007440300c01c01240350101c0400c5a00608918800751440c3c40c11541c1201001c0b43c41542004045103000501e030041082c00003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 876191636 1250 876190386 876190463
    0x304060608070501090303080105060703030905160302090106090602120f0906180109050f0306060f03010e032101080127080d09060221060f06090303040504060b0d0c0f1b 75
    0x689582641840d000f80c20050401145130000d20120b50812001ca0441d241aa906603490b21107042c12001404a80c1c4000c0c0305000701c030040070b8114940c00310b9600f940e00071990f60b06035980c1c9107c20b507101081e0748210400341c2c000807445500c1c031b40c4020140c02003401c1800721615258076400003a400368808100c0903101c2242d4000b402d00d650b400340a07200500025944001441900000242d0300d0b0310051145100e600c0c0b0340c6621106e51829008414a0164842200c0d00d80c4176050300c0803020010a000e6441074003145000040350038050140044420007503000d4030742c00c1c8184a1000e900c0301c1c0b8010960301e143d001c1100300e0944c58103224040000d07000d41001601d9000040900150344000d80040ea0321000c440c0a02140e9520003c072420101022626a582d442143d000300e0f06600450b8007140c4c0c00b900d03000700081c043c2c41d210010310040101da0b80801410ba5400030654032a520703c425200002c00052043d1022120007007051092400b545101340c0d0b40007482132400c50b128030800710780300495 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 876192886 1250 876191636 876191639
    0xf0d020318010801050f090a09020402191b03050306240304030914101215083c070b03040201020f0715030e070506030402060306120303010323010c020c0603100b03040606 75
    0x2690440e40607040200b4a03061056500d000300145030b8102601ca9a0711404c83d50000c00c8007251950f02008080f603026200355203502044004000707134411032204902080340200d00700f400d8844003c2c070400340340c1d03d40c1381d00741151581002d00071005103104100f602503441c90640b0b48043c07882c0c0007940c4a9442035445084103030516005042800c109540309024201d509141c401d802d8006140814242030760030001131501d00c108403282c0b100155402031003603011f00c40084a41c0d003814000000c0220030b107100280020106041d214980b80b44c0240006250030001c414481012500f000b1504203005104480b080b44403101c032181800c1d2181d018500aa04002544d14001d400d4051010007240d0304003d1b00a051402e4003040e042e01c40200000e210704000000a0031566600400000b901009011280c44e5a120714141d8922201c60160a0300c0b21440301c08201c2004050040402c03d070701e07a902034094401c11138184296038001500d0324404140d100c2000c02c414008201861003240a205c0116031107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 876194136 1250 876192886 876192907
    0x151812081606090c150210020a0302090a080a110612040b0a020708181f090b03180a05071a0c0a12110f07090f020921070f06050306030d03021602060c0f0d0203 70
    0x1803025900090403520174217542c8041c10b40205888400407031445000d03a9800449000310028480d100c00380f5440101000c0104045800090700301c17896105d881d40100003107000b03041152a010341e20840300690102d90004000032903024009400c000306640250410701a943c8443e0160002801d00903a4915440c0c10149403421400e60078002c070815000d06400a00200000d0800d5220301075035140400000100354030780f44014003542d114160304241d074204101072411903226101403081943c800303002d000c000d070300c08521011103680441483c0201381c0d1103407076a186000740356500084c0e4148141c182581c8050780c42400284503030b00c5108003402074541080f440c40d086a070400304d1543d1043c810720038025192100589a6030980d1503204883c51910241c08003898100d03590003144191700201d0000585680120180d4002c0c0800c0f41074030792903007290000310102e0007030f00003603041002c00d040500003500307104000740798408400054800507003002c240286407043c0c0d841500e0050b400001d5200d01e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 876195386 1250 876194136 876194153
    0x705030717030705070f020a0f0305160503030a0e130b150405041503020d0f080408010f051515040501030209030f0f0a0308070c0b0f0a0b130615181208160609 70
    0x310100352a400d815030038154070051a5000301c0788010900905200d00b80207543c1c0702c045000003007500c5d501c3d0301c8005807a490020380350514103d14104001c40cc0d440401c191802000707490018030281c1d00c00484c0080441000000000e40d048068110382d0b45010240341c1c0c8400d4048075104682c1240991303074500c0c103003c0c001200c1e0b0300c002c50300c4541200c0d0000d10040e541d130080000410b800c68400ca2490800c2d0800365054443e44c0d000584e0341d8038009422010400b903402591040721190104203a8010400904c404d44a031320312403440c030b42d41c00c010a001c80e60080e40981070800010b4200d600c0e59811840440c82e0805d190002c100541c4040854400c00d035000003200e0b030090785440d180101c03a00a946d014041e9002420041c0c1e4125a940084c0103812190701091100350020241c22a01134101400001030035a4060014a1a00200300b03940440c02100d459485843e4061800011403418038801025030105c18211504901008440e042004c0b50246001c0c00d1b000d0f800000d503a410318640b4098 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 876196636 1250 876195386 876195413
    0x501030905060601080402011806030501150807021509030d060927030816112d16120501060f1410080c0706050a0b131b03050c0a050c1207050307 64
    0x425051640c0a40040c002144481d0000c80038205480341d6100d51005072202120ba5049d10b8040e0003040b00012859030540181e0704030381500d40d80e114059007107402200c040e00d0488112002d42c1c400420340590780c043c00d01050b0b000b501d82c415a070130000c01c2c0030204c058840343c0d03101865440d2a0102100029078a100286201c0304040c90440450360940e0003a000c440010054940d0880106424050038015801c1500101c0b000060755480c420078503c2c4062172141482c0e0402c44981c00700c2103d92142c000511010100604483c1034906107000510076181608803c100d4840d500c590000030b2400303107103443c10301500d400350f42c0101c1030401170244221a480002d581003000410030078000303014410310483e081503400c00d00208203a5a200d064002038110207000c290807605008920b100e403105540005802e4070711188100070180c3c1c405007241515400d036600500d2420402c960308040740104c0042003020141c000780d800000f0f9045005005410181c070a6980b90400500c3c8d43c2000710f001d6a011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 876197886 1250 876196636 876196639
    0x25140a1115072402070b09011b02010e0703080706020403050304080a03030c0509011704050a0c0b1309060321090f0611061e0a0f0f1a031b010c0605071e051305 70
    0x20b080400c1e0741c03200002140160f4030004425070307801d84161045407a8040703501242d00040700b04414140204c56034002c201d0101254020030f410304802510b1071040c00f905010050300802048920f00315120701c032059001010840f100d640c200000000071300280041c4c0002d10511001d008140b4050034050103948400380480200241009004020b81e0803008200e00641060f251640603655482c0c1107140c14803c0384041d1201c014143c001032101c2e01540103011100042403140a00d660b6034104000b6141c16020051400b00e501035500c09001e850030320401d02880c14a0041062a52515803804602a5420800c000b03510120a0455440304108181c0c211035030950a001c4052584001e100480c009850304030f00940302c03400303801c5482c0301da0000d034900100945c04119101c03540f560071203207088414040740640210401900008049034000a00c0901070310303101324140c0b450350343d0700c000e090042051080c8203200d040010725404000683d09513008548540303542d0080c41c210103808280a0303126a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 876199136 1250 876197886 876197929
    0x15020c04060e100e09060f190908030703060909152a0c030914090105100201020408010617060609091203071b06051b090a05120732040225140a11 64
    0x82185c07140081e4080e40a8000708510409484080a103408141c1e8000c2a45440f82404813000a02540c0c200460150311a610100030142c1e907401d001c001c0d208a4100030f0200b011030a40d40100e0841900900603000141e003600880c1881520101003040e4810300c1000000c200c14031240c10140c000190b070001d0200440c0700c8100d165a0300c0080c00614050207240d01680e045010a8001c0b03000b501074502600482009102e0141c940010303502d1405a0341c040c5000c0e12800c00424880d040842c41d05026400e240040d008111240400c508180e1024203d4010030407240e841014545007001400d5500e8800d12020441d03083c03a200341103d4441c07001840c0c100003030070071000f0401c0d1ba5401981c0112a0140c803c4d0307020303c041464050038110b856105d49550542c0407034400d07080c1c1610b00328992001c80c0301141889880c1010611003240603801101d03509002c005e620070030280c00d40c0d10300f034040c80c441e0ba00e001f081c10764006414207181c0340d090120356100c0043c2c900c038128913020613407280380c8010703410a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 876200386 1250 876199136 876199141
    0x2060a09050f0607260421050111040e071404150c060516050724050108330a0e1f2f1b030708120402090a110415020c04060e100e 57
    0xc101091914a4502001024a40c0500200c1d503a0b401079400400307c2c1e400c403074240d40c1040210904c040030b480b002c903040d529044032119440b040009a40941d003c0b04c0030305440c0c2e500d00d07000790341003004610140720181c42440300003407170324211207440f945800c0e51351500f8500c0f00318904941540c1000d0100111214207004503400b995018098543c0c203a00400490403010030080318100c01c40500300e031101514204000807468040c0003c4840202505900c101d107820341d50681801501544d10040c0c0503080312001213200440550896400030300140c1c255418054103900c00d17920004000b050f00c00741615040e020703403000185c100004040030440400c0d110881521a42e00c500c1c420040b501040d104802c030f40d42404201002a6241c1e283d0100c050f903980c8001d01d00c80c0204480441c0c5c203d00c6a070600d40002c140c0c1d0224000c0c44944071034a14240c1c100350070540322a5060001100440c118800c040724403500350b485001d494010b1442e520682e40c542044039000141c1a801d41100b403211005006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 876201636 1250 876200386 876200393
    0x109091e03020330090322050604050f040b0409030e0a050111030a030c091205011d210c031c0b04140903090d0c0b030708010501030506030d0c02060a0c02060a09050f0607 75
    0x11203000014040c0b8000404c43e2020956488003600c9500b6a000d03500b400410100d804000001e000312020005030f8807a802d00b07041e25200745000c134045d01c0e820400501040001c0d0805016034204907000520102d280b51810000c40c00301c4285420540024004182c0401682400070131800940001c1c0b03000c0d180011011035065592103201e0303614081603503641040702020320510b6008080d1010078444e04003031003a13080030340c06881e10000d40c00e100a01050740c0600d024001a040e58082034250140e042601c1e040611410740d04620b00c0e82003035010411008086848008502c0c50940440e40d000403030307032414000c0c0700c100c400f82503a80a410040100303006680c0d40000c151418800115003007207501956240042003285641c1c89140c0c13511020090000703654010380613905940080c2e034100007613030720f460806070303501540d800a8000c136800c950786034007600b8464000c0420b09424127002031014020ba02281c21030340301688100028204402c280300c2c503d004421042040c10445100707082910710b44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 876202886 1250 876201636 876201643
    0x10050609011d0f031e2416020f010c0327020a1503020706020a020a060e0c150d1107080408060a0204150f020f060a0b091f060c060b06030109091e0302 66
    0x10000b8a103400e5640c52010320b98a00304401d00383c000181c1901c0d2003e9a0b82881c80b00041c0d0900301303074064054403002140419200d004d94007240e070100c0a1100c5601c0c1e1b5611020441d040048074411070041803481c9561b22424007889514455907a40010341c00c12805845281607011112500000c1081000401590701ea09500e0187e99450a03659203000d040c000a400a10460100624040c008503004655640101e2110000c03405680c0511881244200c155210402c9490340d641c40300c440303094003509640b120064030390380c025840f0000d400d10144003030400c0358225020072900701500080600c08000140101900300b031100c00b055003498140403980301d2580e1016190780400001c00d8048001504c01c01c4650292a1142c090383d04600340361562101620b07d9050b82c1e800381c054a00821070068841d005080001071280244010030300f81041220340c055208025607980e5100c6443d545156100c40080d4020800e888000408441c40d240c418203a48054480c500c081904034042070103c1e4010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 876204136 1250 876202886 876202907
    0x5130525051003020702031005040519080f07020a0503030c010203100f0b0a0305090a02130506151207031e0c051201050628110f010c1e021c03020c010c081005060901 73
    0x480342010400d403440301c03c400034000d5001c0a58144900000c1c451412280d6110a005a0044098880d104102010802e40e1035807041b008019903402c000700d121840745640642021745c40140f40c0003055a499000a00e140c0101080345034503503000080c0501d80034065a0103005113042c0e040346c1e0001e89402c08400e018081c428011f07007455100c000140c0360b180706000811203654001c100da180888041c40d040010101200d08a00581281c1d0390404869145000c0e201e030094459206c10311580d81b43c0c400c8005d484403841401410414441da02500360360360103200c08500e401d581d8151114004c1e55294009841a0311060080d1810030154a500c41074410a032540d0440c2c512200c9400d400500072250381d40d441c0d1045003103009046c18001da80744103401928521840381d031a0400600c05010410000c4502d120080244c3e008440c510095900414014684c8203907050042c00d000ca8020300340e003912085603054000905110400401140c01c00311100a804162801400d0012a00001c0d0000d00741 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 876205386 1250 876204136 876204139
    0x10f02030307140d020307020709050106050f0304060c02010b060f09040b06040320030c0303040602151b070f061107050a030f050307050a08151c1e021806030106090513052505 77
    0x4985950f0b001d01c0c4201200c0c0c4000c00031008554900e013000000f5101d4000e4043c290300d250078400005940c0c3d210b8400d42c2d4204400200043c03868840b0b030383c2c0b00014000c0d01c0c001d1003955281c44280c000b070f03651640034200302d4a440c400d655032070260301c08000840d1100f10740306200300020301040c00070820034803d081141740f01940f000703850320380600000e1420b1801001d440d13140c40000307008a17400758085036101c0c600041810811712a110054503018a86894286040c080e03c1801f655011548210b041840ca900598001030710040c0c07190100526481004182d8055100880450406a01040200c2e0f418901d2030014154200403034014418811038000304100400c020203d010b01802130080f82900c42d00400c448480c1c0d0350640c1c4400b400c0c050f0301069404611024000c0360f40d0b280343e044494523541c01000500c030b20440503500801001d01801c0d80c2e40540d80d50304086009005032060340d00540c6070560035990b400040c03502502d800701c64044400ca0800c0c15444582c804100c0b401c0d41d098510 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 876206636 1250 876205386 876205397
    0x19091104020d0e0f012003130b0411150a1709071e0806151c080d09031101060308030a0b043612090609061b0b0a0906050103051506010f02030307 64
    0x3802d55907180a8054118010183c0c09201c40c0b0614180055108018020025614120102c202440c01181e400b0403905914510004181e03a4006401d051016900502c5402501c026079160400b1a142240c1024101c00206002a0740b8141c40d4000c40340b400e0122404406001c2803a0903507103651154030510581d00840522542c150340480d289001e4400341c0940c00445019240c041d180382442c440b9404000d000340000c2c1c0044104034850844800500d0b0000e0309249080503e841800082440075003d5007000f564911840c9a03d10a02039000112b00400c980345d12824030702401c90403200315074103043c41549041c211100c0c0d5020494100d0000760b8034140266010755442c2c19000d2034640280050440002100b51200ca603001065030003543c01c030b907a602100070384842081e60306450a41614008000040e0043d000440502c02a80d000001e0000424250300076038031501501c1d420303001211250840518805620a07403056990b010a003403902010581a44201a44070300c40138000c0d44c00c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 876207886 1250 876206636 876206647
    0xc0a1406040503030d02030423122a01050402010909091509020402070f0b0709060822031b0303051b040f0b0c031e07020a090c1d0d050303010e1909110402 68
    0x6a030a01590001c1c040602a6552080d03c281580000d6000f120210f420100c5414000700c116082c1318030518142c00c54004104610395089140e0300e5070004a612849a010111a8226004400e10000404135101d0010840b420548005001100544c01003901d43d49840011030218500e144140780c00030016400003100909400800c000e480b031040d0162807407040e459070320f013081100260184030705615580c520764148c427039108407004001540c0b120180c902e2000580d0001c002041d024620611904003640802401d005044c0c20800405003680400c1c3e130f43c410066003000a0745003044410034181e1075494982071424044003e0054001c9156048001c200c0c6035081c24100220b07268440c04110b0302943c0c60081424403c1e651006004078090814010001107402d024059503004426989549012030740a02e0901003079462a008503500c018403007040804101d09000450107403656824411080c0340415078203080501c0c8500342400d25240c40070b6000490740b052511520584200c9002d60b417003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 876209136 1250 876207886 876207889
    0x1506070512030c0310080615040e07030501050c0421020d12090302090a0c0e010810141f090515091005030a1401141311071212020a090e090c0a14 64
    0x70358242803000c80c0d07403000001e00221924841c041c2d4803a05c80f03406000307156030325420126140c070015620b50b50041555041c84102d031038250004d09662011008468182d581c0381c13a12402d60304240c94014450000180501c45000c000b011184540085104500d6050307032540418045402c44201400078070381440541c010521a411680c0250f4000341208890306102882d10020311900b060040828a00119441d503540200d4000d88514243c0150129852a000f5a214480220b0324001e6101c02000f9802880c030750122084030880303000d5503503262686c0c14402440900703407500ca03280c070003d00203001070704203969900f0600310000e000303251141c4c80ea11441c2080c0060b08000103401d144103000000450041c0c1c6c518650b4190fa0340450307000000007914640c080c221000030b241d00c00c0c4030908000d01004079a81f0740ca940c0c007011a03403401c24100c0752102d00550403a008100040001051003100300646c021440303070103811240100182408010100c0040d0741410188181501c0400320388480009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 876210386 1250 876209136 876209143
    0x1050a0b131a07060207080a080121080c0a020a090b1518150c01090b0703061203090509061206130b070807020a020409170406030b1f12090f02150703030609020315060705 75
    0x31513a003c002951500b50703e16040c5110381103002e801c400140c00b0800003841c03101e8800c405030944808005281003d00507140d00031aa0f010750b03c0440584120101180141c5075503101030014042e0410000303105146074104510309501900340704256005000074601183c100003400c8808608a450148803010086801c030280140100c80e4001c0d40b9180c00002404100400c49104031705a036010050191205502419800640d00c0500040e44d4580144885c0c1015101241c02240c0142065045d2007050281e40c9025000c0b503071200300c003d402c007900341008038510410350044118240031203286000c00f8004c3da075410801c8080e1045440b076100d8010f02c2511082c003c40307440101c2c4410366580c0c48150207000351410354901c6019442d250f940d1060641000c2c0c481810301199030b0303070080d1401c0c2500f0070300290031510b500350707843c012a4005a00503514120740e14002c2401c0508103488405030f04001d02203a88c1a4401c000d0705004104210040300080910804401c0840b0150380310a03170707407c105d071a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 876211636 1250 876210386 876210397
    0x12010915110d1e09110f100207050637030b090f04080a031e0b0a2309090106083415051312030c20011202090f04050a0501050a0b131a 59
    0x2003042c42c042c2100c0a101080700300740c0905c00142c0b00f030074920103400b0521242d0341c419011880140c0000350180b20074a003480080c401c164200b051000410741e12024a54000b0b280a4034103403d0036041e06031341e007440e0107015441c5d07082c00c100da01d2981c80c906034040c005002001440100302013000103401043c17a009521111407000000d02c80301000c0e554403a2813004020210445202e01e200410001301c2590380380c10300041444000c090701068004d0814440c0d280c0d80902081c035155201d1030007141c2d07c4810040030300040100c1102c0aca8132289040d40000920740004040041d0701703030745002d00200a44d0031807044a001941343c840d83c1d9040820341100741040c1d41d080600011501d080d1002459401101d0342d851074000c00000c510a5001f5640c0c0b031484000860b118045034500c2c1195007201120f0b80075207040c03070000d403180d0400001030001400725482142c400c01081d94a20061000742002020b100107080c00c6004589401d110640300c02e004d212a01c200c4019400b81d07c0c0c180c0c40300e070300a4269030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 876212886 1250 876211636 876211691
    0x712080903030a0939050901140108090a14070501080906070906052109030d05090615010e0103020c0303070c05010e0109051e010e0d051909050d030c0302010b12010915110d 76
    0x150341000040190b40501c0360715010b0f11324106400100d00c511f400b4800703034100c80181e903001403003040386401584c1d107400051658045001d503011840114080b1034010640040c3c0c034018241c200e0800002624000d00503185a5107640030000300441160000481e800b690502c0c1000da8841c17601c0001d952071602c0c1c4451008000301075400380103032850000702805094150540501440e950715451564554048641e15600903c8803100c1d42da07035005141035203800d4410701d800b500c2c0c058403000b6a8956802a2050000a201521440b044c481e0a00c203826107011604024040ca081d2a11107650714687d041c0002c0918007007000107a0407240941c00284071168080544006d00c42e061fa0140c1560440c5107040e42135080c541e0502074041c418a03480041d200300422203031407829a510110f483d003481c20021000e540d44c4482c509419901c01d900c14111240000001ca64906645171410b807280c0312074040c90803035081249050703049443c2002d40742031a41d07000340040d00c00c40307040fa45240341e017035440100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 876214136 1250 876212886 876212933
    0x604080a0807110d4e230604090c0b0918070e06032a13060905010f080a0b03011d07140607120c0b2707060918200712080903030a09 58
    0x2499507a12111904503005107200b400c00700c801d809170781c420035503c00c02840011283c1c4003110b0081000e007400c1c0550031071000307080040d14110917a148841150310790020221000d001c43e0000151522000c201034444801e0125021030901c41c001a041130000107105105080100002e6101034140c0c5d01c8110520643c0768507080d4403201c6218102c40d0740b00801c6401c2c2c0006610b000302c2e180340a40540b40484206030744020010f14035a400700c2e449803029182c600c0c01ca0300c0d40d60803556a5024060342400c0b17407408010007443c40115010302d140c141507a10140c0729001d642c4d400d50b4075a0f03070342054510282c2c0144041c008072000704000c440b0040c5000c002846080d4040c240500060042e4081d0b01c0381484040340e0201d200c603601c00340c0d40c4807000c0c4103040004000d86001e000309001450807004250506c900410350b980c04141200c4412107884c80071402c000c011481109001790011000d8061010381051030f1681443c8041584070300c00100840086900c4603580000c205030201d14500d0b010b041283d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 876215386 1250 876214136 876214217
    0x8030a12150e040c09020307081303050904090309180506030a0f050708070b030a0b2e0c080c01020a1404150e010905041a031c02100b120604080a0807110d 68
    0x71000c0000583d0103543c540040304001c80d0702c00e468801c0342d00881a54443c018190380302141d1042d00c481b00c88044040040034494141c558031b03503008950b0034034031079100c446601d42030141184401d400315800b040281d0415080c002c0d03580300490007203200c54018001020301c51003400c0083ca410034a601041880c4241080020140440301c09540071b034610700000d00031042040e04100c5082900c03c001c82180c2490341c00c00300c0d480e642e00d141c0380700d0556508105004803d2a160010a41c105a8140040d41d40019801003402c0d4040d52a0f10300030700c40900c0d50300b000e0411059041522903e0501800c0c44000521300c42030ba80a00e4112000341002002840070072000ba002c03da840360401c06c060301910030146140c803885034000c1e05a11020482d401045811440325046018003402880c80c2c0d00401c01d44e43e080c1c41500e0a028207480303940100c00d125904c85a910006013040f00042005040045801c441480c1410100f1034102d010301c186840311a070182942e01c0160001812058a44000d004a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 876216636 1250 876215386 876215399
    0x6151e0f150f07021f08130c15020606040507020619051905090c01080c040b181519020c0108100e0907181e0501050603010e09190f05100608030a1215 66
    0x103103c0c1c58402d6500c2c1804129003140b01c45402010714981003c03a80500c0080d00300041d802c618668240180400d24285650713061128801201c540c0310360040e00302508100345410301c0e01030039822000a1006220500e85a0380d188901804000c0040d28581c4401c04034182842429120282e801469020802404d021121554400035121158040f0304d580d00056a044441ca0a4408440042c40610310b0002946982c402452500382540da01c07004441d6050310b0743c401400a05401c0c01c802c0e80111142100b240060b103400342c000c4045042064460401c40b22070301d40c085044c100c82d064241c60200380c40c2d0312025402d24081d038100d07003280c4400356a0105140000d0b00011201880040404485d85043c401c550a0311000d010b000d070000030404c0104410122600101d600c08011003d661500c0b80603c050f02c030468806905079860f800c3e01c8442014032070140f04d241c2015448920421420740b502c0c01164a0340510b40d1118140420b405014466071000c1d040801c41e10310400d9102c90a036250314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 876217886 1250 876216636 876216667
    0x7030b15040f0b0f2215051201060605071e2a140d02010c0302190b160513030605180304150201060b25020109090c0206151e0f15 57
    0x60070310550504410070381e40c1c01d0501c1030000600010b011516184982c00900507009482c014052041d81500d602100ba40114811307036540c51070204001c2405460241006078861a81c0410107050745012020001c043d0408112400550700c0303140800c41ca0814429a4070075140200081c041c2050311007050400c00c080b6851414a201c0c0c902c41e048451384400c0c140d4800b040103000d8a8004c03041007026000b640c040c01591050b2072280c41110601c412190031120441c8040c0001c0b038421900c2c1051151072100b400341c1c08182506403a1541c1001076401040e42d00b03500710303c00904166652000300308007010316424242100c481d201260341d9560b41e000e1150303403010301d505210019403030504049880d100c081d003100c0000f25600303411511100c1800c01035080650f100320032414060783e00e03400518440307280140c044034503042c0c0150501d071400480700701c0c009180b4051070b40b088244036142d6058034443c0d00c1d5141100800d0b520a12805030f110b000c0b0741c0006e00600324412011010030041101c801e1130 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 876219136 1250 876217886 876217921
    0x60411090301242903090c0a09090b060d0b0f060f040c0908010e0309031011090d0302030a0f2a021816090e04230a0606090b0114070503120907030b 65
    0x1c404504482e602e98011404001c0c0d0010041c015401004913003c5940b624040e58014008109503448110300d000001d074103520f6036001c0245d55480d030f0400018041a60a400e900400907944820005541d0350340f103846000041c4501e01c103003000000b2410356241d00180c104c00b500007030700400801503042805403010318a4840c40309a982006410f04440c0e03400b00654465090140042487c07004901e0240c010b400081c1ba0303440301da02d091040c0d0340995282e004500801d13001e03030081c41d5907000f120802403010585807442c13002d000b694201c00310300c0960b603521009000c2d4400188440c1600c01c3c4009038040d04d40342207290003400d04005210468028040d045043c008949424011955500d4840e841c0081114050030040702c0042c03403001c401c2d10030b018411014000041c1c0314034019035620070045500c0d9800c07401c8039a594250b9607074156000015103220b00e08540303e05007000300d10b542d45580d0340b04400707404400088120203c0ea00103010010302c0080c44c6d000b210a20907280c82d0103100010080c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 876220386 1250 876219136 876219191
    0x606030b13020405060f010c15090b0103290610050a0504050603010b040f060f1d12010509070f050f06042105010c080a0b04020703020d0e13150602010c110303060411090301 76
    0x102004100e01b8944031940312005401a180c100b41d012054503056603c0d00b0784002052015141d00c529400102500c10541c041c6104500141c00b200101404201602c0d4080355224440d101500f4440705075110203502407020311b9441c02d01d40e2440c1a03001140c0e0f6004d181c0c03201d42c2000c804000898001c4542c1c000d0004d94003890341c450300041d51800100d90703841003d055180800c0c40445204214044d41c03040b848059809000064030410003581c450840e071086841c2c10310b903000b6150070f0090040151204d00103240440303248400124420001e03905204030f203c2c902c9480700b044200d1910f5455503c0c004131954012008028820b0b260001420300c1001711070030383c1e50030300e0a61007000310316041c4240c3d90140c2d0980e0040c941260004802d45214041d05130203070740f02c514010721132808030312802000081c41004400313440f16403401001a00303488400b40c42c3c0c070a0042d0205002851b40001080d00c1d84400c007100c1c00b00300b030000407614440c584181d14601b034255003402d440302c1d00e54000581004c5111071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 876221636 1250 876220386 876220391
    0x1080a050a060f080102041a1206090c0403051006080c031501180912030519093507050703110103060312050a20061f06170603100606170c03130206070606030b130204 73
    0x192350f0481000d218009204a0245400000c40c100b800c080145c258005030904902d07260036140d0b252545081041c0307000c4500070752221014007803003400340140140c4100540051480340c485500024580405015480400c41c6840d41040d01002540010030f5160b000040440329280015005003e080111030034008070315480c0301079403c0c3c00b86100b09060aa0000081d030140490820021040c2070300c405174841c81100328181c81e0704100c0c3c0000622501b80b1600050020718610716007000c4140551400d0340c14546001010004500f42511910301c0781c1c0185011176889080d00307000d4906803458894000000890410105491000a881d50003148507200c0b01042c940c095a9000810155000c0c03940001c042c0c81a82121035039080070075030060402820744021846012100007180c3d00703548080e0002c1e04d0080c9245d001030b08200f003150442880351a65155181005003104400545807009004440014004043c44540d5002d03030065603010400c0400350400b014449440404c045080c1d126a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 876222886 1250 876221636 876221669
    0x12030f020601060509150a021f0e0708283e0301110d11040e040b1b09150c101a030106270504020d0506270a0201080a050a060f08010204 60
    0xd0064040d01d0820034010505070344007003901d009400070703004420f110081d03104424800c40c1d150503480350602c013004044070000e010b4800c40384113450300d01e0300d41c0b0040d3350343c03c1604c0c006807150107600d54007001c4a40d1080c5003840492481c0c0200703124040318038840c900c010003145055541d4404800805d048940503284511411001090b003207920b80090b802c45a80204008001e81b0300b80d4000306c1000b00024009414039544d04800c4c001004111800c0350300424610800c4140401c0d19034445610040000490030000c451b40406e083c0107220031000c80600002c00c01200701c2508201f80035004a046c0d00c10702041c1480407610740070803843c03101140309500302040401c28109050030607a55072546a2104500c450798000e0000800c030250050b0303084840c00c02000c0c00305000b048254000d0340307040036441280340010442004941038516400498000c5440800543c0e84880e481c1e81040c0f1111001030039444006d43d01340280703800e5201e9160b0500344e4900003000d95065020300215440b0200d448110f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 876224136 1250 876222886 876222899
    0x3040c091e0e2119080a111216080112020f04090501020a0c02030705240c0705060a0801061b05030a080a06080a050601031505060625060f0f06061b03030e0712030f020601 75
    0xc0c0134032014003804000c0075101030780340c038426188150468020300700001c070710b08056540b43e4550300c44000c211441359408180030422118030381540e18464245030501c842d504100884590000c1c0800103482003c0061500f181c0e46d032658862b041032a4400b008540d200c0c21030201411480245406034401c2c081c480f0002141c0c1001d00c4011001e882d025461251903824210b04170880d004102034020318401d150002c5201c0d12040700400281d99192180b00c0550b1400d20001c000c824005240f000385160304100e80001079001082d580380303075913070b06008a00d40e41f1007040400400316540044200d200f1981d026003400001306130076040c3d0f40a25400111400a103494100b5034805481c60f90304071104210015400000c17452005005043c00b07080c242c10b500d40e03211502611850040e0070f60712980c0f004410b01030041c0780305200c01820300341030201c90400c0121b0441c1e0544022200a800e041d200d041e01a1082000c4c01100040d0400b9000406503118a003801000146000c1804c03025114400021400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 876225386 1250 876224136 876224203
    0x3140c120a0b06030d090512030c0d08100801180204020315030d03060509130f0305030408070b330310020c0a060c0c021c0803010b0a050d091506050603040c091e0e 72
    0x594000b600c80c508190707e040144841d2080301010814580010f0181c0440341d0000d002800341c205d000c1d0b40c0c4941c00d040664080f0841e004983c08440168580200c03640c401140051000340c943c0c041350010703240e56601c410703100a030740e0b03000205a040c0101e0101c06121a0147d1046065a4060ba8410310725600ca0410000b0980a0791025288500843d40440000d10400045a210344500c46103400c000b415039420080704400e83d06100000c8014400142d80c138600050303401213038820400807005100d11408a43c942c081004005505a00001c0d910010703541007052072603991784010200b00e403210314100108001c0350a4403c9105071400703404400f61020a0102d000f8682e00004e01c1c0b03295920b0010503031a56800800d52a041c0107003480020b8000c181e91040b80e0302e6a000760f2501800500511403002254000d0b0003141c840c1805101b400081b0740382c0c5150f00f041e181036440000300710b08401e0700d56004040d4005802403583c2041441c0c40c1200e804604446107036825604802c80d42403800b0100380 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 876226636 1250 876225386 876225403
    0x721090906260325031704150f0b030303150a0e16050304020a210507080f0601050d1109190b0108130201030902120f01150b070c03140c120a0b0603 65
    0x16058849065186180e0036041c000121010b102200d2424109007600f140d071420307410816824251056040303051581046004555500e00031054426107801d1343c800007960000e503034070401c0503078a600c101310041c01a405405c1e9180000c04598407450b05003d06100c0001103a5103e00030400403000017001302211110901030f0003409100d40381403400d07000494003900001c0c002d0768440d541d040c00091503800c1c001c0c4491801154032420b235450245040042c078140b260b42c031480e40e41c0e1000041c040c446001180031415103804542d26005821982420000c241c0b0043d100b640c004409003e2040c03c0385401c0c002e0340c00201a180c28441400c0010054403001012110309001c0e810882c0c01c07800561003640454010382c0f0052407203090400c0a10381c3c1d403900f281c0c01000d81c960303036507000c3c25100e5070391078a81a0001d08411240c54500901070342d65585041d01c17844020894010410f941190b48d4090044461404000e00542c48000034640400d650f0154143c2c00e8034103400c40b40219920b030134042907404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 876227886 1250 876226636 876226649
    0x10110f03070302090a17030903150615090d0b190f02120105060d06090507020a03031d0c0d080d1112061e190909060203010303092103050a02030721090906 68
    0x505540d01c1c40c030107030042d601c114490b59008a0003040403802d65180c2c1c10791500801843c000710780324190340003410300c0c0c1801c0c070b0714001602001c01d08020441c0d99002100104004020000c0e8441c000700c00820f2420307190013001002400d4402c20407a02d5407260704890040c00810606020b1000e0400c1c10504922400030b0040031030007414014400c500b80349004141d44030350150005841540c40c1c02c2c1c40110344040c0c3c0c001005030002000c0000b0b055160080410720400298050240030180c0e003003581d10700b14940b0b0b090088136980104030500c10000280d42c480410301e80180010f840c0c07000c0740d02c1c45601403d42412861005004204d450800c2048011420360b0702c1d4501d8000c060010070011440a40d500362032454000c100f01060800b0940121004603105410158903941545805081c1101c03d0700301d0340d18200040340350001030304445403100c003a64150400e5541c80410240032070035886180ca01820355402806a074140e860800700d4100c3c1405140d4038980c6131504c1e1608201030b2030161044e032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 876229136 1250 876227886 876227917
    0x80a0b010b0414091305060a051902310306110403020a0603050f041704030c0e0f0603060c12131a01090b01030b2206030c03050607080a05060d1205090607051011 71
    0x1c041800c0c4813141d190000c604170f0303a19169400d50758905d4a1b04a00311040d505a80c1c0b0f400501148001d680c5d00452000b44030784007135007080b0412a40c140c02c01c01544e02d20302c00031009210b61400300d980c064104091a003241091100c98420303007070740200e64050320017280240744042c80024028031034400d0300d014000f8965480000d8440752070755030700b4444900800040c0031b403c000010004080080c07440042ca400c0070401c0251810040031204004014542e078001c1d003000d030802a9203803d010840b011507961014140c0d40d520b032071811124a0141c000c004080760594040c651205000c0c00045040f1201c4010501c806024200110103450009028503080100c014041d00702616000c08400c1003c6504000511740e9074948409190210325401501d0310f070001024450b0071075029165550001280000740428100390303011583d01c00000030054001c03000641c1005035103100d00120380c032400000348040c1d1200c0e401e04007641c07201c2030741c001180040d20b49104285921301200030f441042c10b49007082c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 876230386 1250 876229136 876229169
    0x1b0f0324052503021908010f060504051c06090209190f11120a0e1906060603050c0f0c012901022103070522030f030f0809100e0c0604080a0b010b04 65
    0x6410641c50000c0b0509068083c04000840801400c20040e802415903c10000c1c4d4034103001c1c0c0100c07844a03003004040080c104414003030758a0f116020b85600e184181030180200d02800d002e0010140001c0c002d50111300d01d01800b90465140c10503c40c60403103000208224020620403600712481c4030404000c21fa41405a0a071420021841d1035111490601c086403080312142d0312803c10120b21a101c00481e510303c00042071118500c240005041ca070f05081055040000000005000b001603000128400045040303014100390001c01c090b2034450560b12a410000b4a01602125001d0180740140300b241c40084405042c3c0c03124486078014402d160b40385072102402141c00c0c0d84420b0b10780d001d140c44101c40300307403641d40700003804000c44c080e0300d160302401c900f03160043c15441e020035072000b0091520184000f500000c90140703252001d00c0300019000401801880c240b01e0b02c036190300d0744000e021800003101c035008a45008914801da24440c2d00d0781e01d4008102650243d40600411810010032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 876231636 1250 876230386 876230431
    0x1060e040b0d02030607021c050a02060a0906090f0c090e01020708090d051204180b04020a020c0f150301150e030a080406030c11060411010815010c1b0f032405 70
    0x100d2000d100300542020000b000e0b0f41c000c28038020003504e003400141d0102e41c400e0070740c0d044a020501340c03181c2c2d4504a0300e4500d17000d0000390b5402000c1c0903034070303080d99030016681040300588c45201c0403a40200088c106403c81d0404048000c0f4510070711161504049980f03001c0328040c030850302904e502c10b12039030400182c10184540711a0741c0004a480740f040c130700440b50128448006e80002c0115280426200341c0c80c0c10954256000d40403031b24003460051041a40b12500400c40300c1c16000240c2d29005041244030004110303540e8861426803041c40040007103560207502ca00c2001e402020740b10716071000240d80a155640700c0840000e86000e50a000600280b8800c0e00300c2c0c0d101c29074918103c0d00c051030b06030304c46042070002c0d64215490000d5004044240d600706003000d902c50032900541801d0008500003825060700f50400400d0101c804102800c00d00720a40e0500c05400010700d440700c0e254591400c0c03516450584000c0345400904c1544416019180c0a035070b101c0c1c580003605185655a160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 876232886 1250 876231636 876231641
    0xa060f0501110718020c0f0c03010606080405060a0905030f04030501020705060c0f1c02042d060f0903060b3111160f1104020d200a0e06030a1e020a120501060e04 71
    0xc0440d085e02000b070302400c00c508002c110b0311600210301420703400d07800b0802c042c2111006ea20810501c420602000b001c1540030a540d5849031810300d0109548404d8900f1320706512403010949030080c000300b00802845015805801c0c8940b00c1c0c42194226207030114800d540f405200785540000710108000c7c00d08a40b1583c4108a11011407400350030291100710440308041010880011203903170190401182e03000541501c005c00c41818000310b42c1d460408020704906141c0405000b550300c1c0d140e200e00039190340c040f407070020b011800c0c40c0444000001e11100c1004801182404282c200011505952001c01c12a401d00560811441511401e07548021201c00c59013000e807254000c40406046d56241c0f80024a025001010300041c240b000411240030040340e20242004020140442c0041607007104400b003207100704a0340c0e603840c1d540ba11071050140c0054440d2140543c000c2d000c1e8008050260081c05203d01c0340d03116007202c05050440c0c80201d070424490007001501c0c07220204454240755 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 876234136 1250 876232886 876232919
    0x8160b0a12061a030f0a090506180f0d0201090b0a0c0504051201140c040501091a03040f050f0304090f051f030308130b15101107030201080711060a060f05011107 71
    0x50101e034443da02c04007203481501c030340391042059800004026083c1c0302c5508403640324180e00410440c2a00646403913582d007500402c840340715880694802590502005091070101d090350450303005403403040c4024041c1c03078030705c00407112940c00707802281d501006800b5102456500341e80786410a440e010400c089804a05a000742c595a126030401003600c0c80d020380340c032a03601a468140c1d00c500d082e00041031442c00741e01200b140f07420030400721000300d10f080c109c84c0c11a030007030390501b81504a401e20504001000404e21140c2c8800a000103144000e5040491128052903040005c1c0c1d5070101c02c03020085080d00b035815a1803a8010a06c0001e01411400341c002c3e44980c520300301c42004c0da4510210500503180c11121100100000090b8501020501c6c01c10100f4900a22900b101041c000e5881302c1c0c07408004d050054100028007400d1181c080f501480d1400e00c110b82440c1080007070000109a03034090024031702e0100101151650103203142e4460b070a13002c0018080030f0718040d5407c8980400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 876235386 1250 876234136 876234167
    0x1508060403030c030e1c022802060702010e03100b031506180c0d060b0d0c1103030408070201021501061110052e0e0c1b16090203072708160b0a 63
    0x15039001d4a00f00704100006c0c40286103102c8451001901190080d00d0503140c3d28013107210700c1032690002000000d2452900c10a581a03a450b9110600352005940317070301e0b61a4106030036200d9800d400c4c200800580004030441001e6003510b299848901c480980058102d56554100e5200003a00991010a114203607101c08041d40032418071111806560a40f40142e0003420148030220b0485004180c0c2e210b541e61501041c1459030041c10116002a01c9000040000e403500101050127010340e4000e1002c019802e00f0000314a1280d17854150142c001441e0507072000c458480c6100b07004101100d44511030086803541c40c00c6460480d00090800380c0c207003113010740b44095400400001e040260300a03007405040031000382c81c0c403041e544450000c2480000e00440c2c0c681e00500c1001c480e81c03d04400c090607182c04a00141c2e80b580d802e00c043d00d42041865034134078402450348c80f00600b600c00171403100c00c3d90207a40940303958000440c0a41616840c2c0d000e5481c40500420804000758021502c82000e41d18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876236636 1250 876235386 876235391
    0x50a09030c060918021e071e080d05091f0c020a06051005031b10270e091e0601150918050a0e010513080c0c21011508060403030c03 58
    0x8403503039900901d641e00e078040008030348002014448130499100c000002e140305a411400c250303807030801269080c224a0b01034101c000c000f90190502401c4000904001403040c01000e0038400c81c90300c1c0308554403100000c0788061a1a004c10f05103075000c0b801e20300d40180d90001212020810b81600010416901c14000750b108688411000400c40d000d0644501c0010042c0031085203000c3c1813504001c1d4120b03685c3c801811195019440380e4038440c5070f240803895460140300c400c41c2c5891040d0a003100c042691203141c050400010300322000c4020600c519218800c0d07070b0404541c84050252134a000091031800d030440310040c0580d40d2001041d440480251414144d00b650710844c00301e00c40d01907442e030380c4c03d1038466003007040a44040c01660861b02600707008000030715040364103034000b500b8404020401040011403103811507040000a6580b000241082407003541031504848a0301c10f1a10261194200303000d2402000348600c809088070088030151211f5170300d56900f02c00521200d40601e05065 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 876237886 1250 876236636 876236639
    0x50a09050a11010f080f0a1d0313031205090f060d1b350f090309061c0f20031f030503120c031006051b06070c15180201050a09 56
    0xa1040000160050142c2d095803503900c024400100b010303101d10071a5050141020500c4040c4440091042c0e00000420002502d070552140820035101c1900b00a4542d1101048501800c1e01051710601100e1240c0b40c8850440040070060340d03c0c2c000d005200d41e0044130040f00c0511750405200400c0d04a070401400228840c0401c0c0015000c07420f400818000342a03404e80c0e0101c1854090319107502071031910540b80d600280840c0d00159140140301d035034940052400304440f5142002901c442c1c5c8002000b40b13403200d00c0781c044c4000c1e9040000601085c0d905100d210041c201241c850b21198010304000b204800150b41a010043d600c064440a0048100e80300030b201d5175103c103000400785216030090360344c900b0401c07404640040007a0812203d0381040050000300440340e0010804c85109080541c9c071180c0100400c800724400e8050f044c410701403041080100d561080c80d40100700e200e00045180b91800c903e0305c00440303804103c1d608a40c010b0481d40c0e0003540c06203000e024a00381a20f070048a09 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 876239136 1250 876237886 876237893
    0x1205040507030f050f01050916060e240927070c140d0503150405070e0f120d031b030c0801030201050d1503060e07080c06120c0d06080c01030b060715050a09 69
    0x1804101c144e403c4d81103442c01245050003070207000d401104c000000c084080001c2d084806a600030721402c000e00403804000034458a881d85001000901c05030310350040c1e0404550500d031603100003203452080090040702c20141da00040082c007221090220130100d42e4034405d054550202d0002c050360030181940108520550812540340100303503540c4c481d503d070704250140381c03c0c0c18900381e4464421400c0000300030043e41e0080e0504007904046408003c40794180700411a02681586105400d0084d400e800c0a41c64154002103e08400d80c4416102041040d00c201d0455010792121000910007078010805581b1074800392510540350b4100243d690340c01d400004c11401564012214642c0b6548030b03100e80302050154400425a243c050040d6905410000707419220704410200b0451a002c0882c0800891805841003541e00384e80400205480d90703e0a603540301041d00c40e5000901700300100c034150908106503a4110362111a40700071000c01c50084000d08001000288210703501c100e5903012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 876240386 1250 876239136 876239153
    0x1407081006050f0405150112020903033c16020402040504091a0606071a0a09020a0f030507150c030c03020c0d060f0501050d15051f06080702100b01120504050703 71
    0x9152400c8000100c0c14036101c1400b14510b0400501803095140c070080089400d890200070149450174a03240c800040c611007160000e0180e4101c6580600c40820412140c10495180211004142900d071102e410103e4410b0400d018520401e180d20b001400a081d0b4061a4400000d009100500141c10151100046004ca40410308140d80201d04514500400085040790540084042e101140360a010340c4030014003a10307240c0c3e4240101100f6001a081e800b4a0b0b00c4088861350060101800715030b203a0b8002c112108074042560319025208000540705841c0d4120011031140d42c6803860303c0d4280c1e860a4038402c408182c15020f5000f185059001540e031a0440d00030180705540004948041816001c11504141c01640c01652074000c24030100380c0500c964104030496020200e80c0390345004180201c0241e20058060f494426a4045280b98102610f14400c0c0300381c1e401c40340410001d8103150b00303a62240c040980071403001c40030345009070348507040150f000740588100d0310a41c0d07507651506603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 876241636 1250 876240386 876240403
    0x405250903080d0b01091502150a1506050a120b1e131b031a0604050607050c0a06080f06030a08030115030219020a0516051c1109040c090c02030c0307140708 69
    0x12913680d40381403d03c90360b002403024001d00416888a40490003d16011b99203919000008012946000c00a11520080e80103200041410410301c4041c40da1181c02a0041c0c10070190480400c40c21101418100c202e0b00c59040c814500500320f804544408000d1010b00b000541c12071b4011080384985200f81055000f0400d6041810615070107034103c01c400102141e11014501401d804144646011662402e0983e8243c810448103a80d0f00c1c07500d0314102d45040700070102c10380c01c2000c0b95000038000380c125400c2071041c030020841d02c800f9520401015140c604094008082c10401d100600c901d031200341c83c8450001c00c9013001840e044d4003030712202c4c0c03001032003907148010b07404008038404000052050b8510700042011041c0d03800d04040004001107044848441034965030300d5010305104032980046c104400150001c81c042c00c1c20704214012480e5070240242445c1800c00c0809810301c00401c441e90704000c030f00a182080301c0e03592041003011280c4507c8640b481815008688044113024404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 876242886 1250 876241636 876241657
    0x90901030b15010306030b010b0913050a020304020406050d4805120d02030901032a11010614090606030a11030f09010c09060512091f0e01050105040525090308 70
    0x240c891a01d9010b00d2090080c0d158860f0405052040420004843c02d40320707415107120129294a405032000841c09003d00c0c1c4001d810000d007400d09102039090f071a030085010702d0080d40d0500582c4d482c3d0080c0401030200b0000100720007600d00f200c405012041c0900c400f0403c2070740090b90540108903d8a481174088500040880412801008075250014040c520441d420f03001d00f54412000328080d40341d00032030b4107640c18184c49080340e56009002d039580ba00342081e4070180f50003000c5c81e00c40060030400280c3c0d030040c60350300e0584003048803205080b294000150080c11041c480d501c020070711040c0d400103421407c03c0c41d01c800d00ca9541140e484040c503c150302c1580b52841ca80b61195945007521203000844062000c07107801408007550020413200b541510602202040c0c955031a241d180814100151801000e102808180d104080e001729400c840003100900c103698070b50042101300c604c19662100254803c401444480e000840b090400c80750505004251b02e640e9156201680c0c1b20b1840758 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 876244136 1250 876242886 876242903
    0x30e010f0b030c18070c0320010e0706050309071806050d080a0207050913060c110d02030c01111821060c09040e0a020603011a0c0a110901090e0c01030b0609090103 72
    0x74000c0d0408104041c41d102045405110b01c0a4451014034400005050003040048040341c07075060601500c10400a0003d00c500604c41c2e5030441c0c1128000c000020000c40680524100000c1d80c5101e1000c0c0c070300604c075540c06401c0081c0f4203107603084041e40320b502c080309450701c03500000fa4a6845070700000d1030701d018514096846064440003414112187c01c101d00c640c00c03c109105400400d2102854140c1e0301c0800010554441c28043c1e60f2031803004483c815900c074842148a1081d8080090640305035808024050b14040f0148081607003e502c501150700703210304004034110b103000b4590402c41c681c2224902074096406c2d6406060460440c1c4014030803500081c0703032150b81028412500c2191055011740310740001680020440d00c010320440c0600c481802119400c2c0700d1a4007102c401d1039650741252581030301032500713035109100f400445124203490000041c0e085414050300464150300c0020b81140c070610320040d0000c110502503180c0125003400b0b00d04d80380c2c07118142c440c0a1801062403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 876245386 1250 876244136 876244151
    0x250b0711011205090604151410060f09080d0f050c2a01020c090402040b0102120301090f0e0a1e0f0803310c12081c1506031e0b01030e010f 61
    0x54025240403401c00d02c09480c0c1002c000100350081001a08950720901d05841900442080d078007402c4800e43d605443d6103000144003030390011500c4074048800d1602c51003214409480f041d07444105a1103408540c0d080044e400f01564803603503940c1e18000003030902c1d42c2000b1949010a13700308009034506003104001e000c5da240e400c200319007050340003c01d20052580c0001e94002c105001c0d0702400082c002c60300c640128080768000d0140c00310306010400c0382501c1e581d580f058030703025140c00d200429441d8a4641c1d13200310349101081481c8c5543c0c20444c1000c03031038003604581608503569402540c00c4c2150b514008001424a0011401a811480c09600c1c039280502107107508040720704503401030024890841c0000340c1c1400740d941100c100c8040410103e0709401d00c3c0410707104000320745c2c0d4014101c080001580b503242c1d210352815108841c1c4010f00319104c030000c1e011140e5020000d90800d201c2440100e080e1101d070806440800103250100d65840d0442d10389003074543e01d402104544d03071141032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 876246636 1250 876245386 876245389
    0x120d0813210c02040b0d201309050307021f0203030c07060b060406020a0c1e0b0c01020408030304050d0807140f0c070f0603091e08073801150f02250b0711 68
    0x190302c05141e0103c40080f206c0a00780c0da0305070038110300107440c03031007200c00d4000300c10390760f120020080501d840380c009008454003840c000342c5030346c030585d01248185005081c0c4000e06061b01c01d40d0b45445000e8004500d075480702c1d920410307150441d4000322440b940303507880c0c1c8603217031940e0001c5c0c4004e1400b60000c169480305403030429485e009680215555810001c5280c080c00040700c01c1e0002c58290209844c0c0c0d80e61007142c0540a4426030304101410301c0000305100401c600080e16a2603400140c0e912040340d21406d608850a10840ea82803c0c50364080c0a0304855101000c010070440756042c085a1006e50780e600482c002c0c1c50300d13612820201e5600e03103d41d070511120321164409900e0283c40c01c0c604002d96601d0603014010780c24060546204407200b0b0300411140c1c84429550086c114814407400620068044480800d000e6010200744500e03580c0d04441c0241c1002d0140c0050b5005420281e040c00900791101101140c0d4201d280d0386c80c0d10001d40c0c0002d41d4020100705008005824a40c0c02000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 876247886 1250 876246636 876246641
    0xf08040602010e0f190c0504051015302a020709020915090a0306061e090b010e040b031204031101080108030c0a1e06051005120d0813210c0204 63
    0xd0071081c6400010524000e0302010030600170b5081d100500c41c8000c013990800403140805070708a0780d0000c0ca000c090000d50421960194210313400d45002020342205e00c00e0458a84542d030b120180c00703502072156038030310038600003140d01800307103145001401010359000402d81c0d04503030310400003000c028807038903850b1030f41403001202512103104150300d0810b040c0302007003003c0d400c25006665802d010a01032801e80d5407a03400002140c1110003485400e0f202c1041c80304103610085042c0e104001500001211a9a0300500c5120141610f8500716030300b62138241307c041c1c2500d80119500d40103140382d6000300164400900040c6004005041ca00c1d0110b01c0090944101a003042703d0716801840b1419072009e000602d80c90039039200041100500008401542841100000525240c04d2000304003054008c07980341412100100c132720442003604110070035110100e01800741d0000b8003400000300500345c08500440014407038250200c910144850440700c0750780840c072907000683d00d410580b041d442d150 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 876249136 1250 876247886 876247901
    0x703030b0405150303030c0a030e0703030230030a1109040e0a0c1d0c0c0a120809010c09080d0c050f01140103120f050a0f090302031023010308160c030f0804060201 72
    0x50070b8032200100f0b82d030029580e404004c0140350610b0380011060782451013071f0000280300d1161811203441070344901d0065200d510800002e14003022104d000c60105200d0310128416000030550b4500d1a11480c01c0c00001e4030040182e03203060042085086050f490318480c0081009561340039092a050310b2400da9040310300340d4010020980754030074941103150b551400a0304400060212507031420500d400030f00b44924450054128001d1041c4e4070300d030745e82094420703100301c240b1b4008100c0c0301c0c0000429502c0455030300481c1d0203a4403d0124603940390060102e54542030081c4120781e441c456031400e02d825141c520350340c1d80c00140c01c600100100301c5030f680e54000300d002c41d00b0146207001402d4001800c900034620103004001c500c01c00f030b000403800388446102a5030044c040d901940790450b0580040c144400000ca20407695500300c0c01a80111340034075040c1c81c1e000c5141c1c1d00d40480f903c407004505040e818141d07001e06e07441c00c000001416400040313000a22888101e41c03143e15110010b804c54411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 876250386 1250 876249136 876249151
    0xf0f210f030f030718050303071203050a1109100917010b030d0c02090a180c0306020a02120405090105040203100b040905190509060c0c0a050102130f0f0e0402090a0b03030703030b0405 81
    0x2c0c82000e9116442c030040c0ca078002085c0c5020065245c03031290b41065641194462500340c040050001c051003580f51260088581546092000762594022001150700c0640311402c0c82c80c0a020140b40e500e801c1c183c10417222100d01d4103d41e000c1c0c880d0b5007120310000801c0221100da66494400005007000d102100014a041c20151141c4090350042168001c00800e0701001c25030f80e1206031700403070003186040069904154200d856644902d407440096000c1c5e4040805486044641180280c0e40c01c01c035015510301414070021a4a0101400f0180d000a40340c00c07540342d403289020928801c00e2020f48020701c000034022403142003480050341c000390680700007803025042c641040802c150000f5003503040326001144070b07030390007501d10f085003000151100140300d9400015014620300c145502007040d128500c5128200654540704861040b500f849011110b002640000c4c0c0903203022002580d02c802011000f250090054001070308540c880310040700800c3d0303180b4040f41c2505140c030a15500101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 876251636 1250 876250386 876250393
    0x6060f0f0509190504030c03030b060702220e030c030a03060f080a0b0702030f07242309191214040f260f0f060f10050f0f210f 56
    0x100382902294a80c14011580120000300102e0b441400c2e45001c0f112000c0c00140411041c1003034500280016182c40701a00080c4c18140c0341c0e904d40c9403090840e0540c03607004080030541504a0000c03407980550200c0b00200b40e41da43c45c0e400d0a52801d00041c9408064100138545d02c2070b010202404070341d0f45030055400741800c00350a0143c41d10001d000919190041c050340c1c40d40d529a07800700d10354451255540600c09d40800c4000810019989880c510710554000415070094400c1c180c0c200c6422040d014000e550b484200d0241054040000e900001214140c640c03003209116203002d44600b100d400c842814081e200404100c2c1e100e00d00c0c00180e1110b03004130349004c0c6030110300c11041a1a008050401584041d401020800c8000482d8010342c050140c0f0502c210f010f41c150b840380c0c185901c00000b4000c81d40054100c5804903c601c1c451910001d01d203010720308003c1484450303c1c80c00031140d000200d0082c107082c140d40c2c0c2c03a4451070b400310307000709d004a4a150924807410f0600b060a802003a03070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 876252886 1250 876251636 876251639
    0x114060703110106090f0212090604050c01260103030f020c03010908040b0a1803030203220f06052a100e0109050d081b040308032203080109200f040306060f 69
    0x68400046415141d05807404034030305a4002c4141d40141440d5020089440c9400317120101d004041d0064003440c0c114601c11348995461840360b03034803103108645c000c1040c0c0081d50400d20701e60060080003000c10720358140380d8104103030301c06581008000380c00035004039002e0030444040701c1e4100000310312a0702c240c000b40400e00036640c0b901e4060040b0f018842c3c10340800308000742d286109080b10240040800409802590749050280d00c039408400721040c2c1d00103810045040f40074104680040b501e50801900000d45000021100b035080001d50204030903009403d00c8042090701d128440840c2e0560281958650311200b41d8211401d200040c0741503410100341d0000303c0e101080782e03521090142840304944da113104081c206d450848106408400010902009015101000d58802d1008848003044500400340060045d4545d00d001170001e201c40300103010b8481300c0d07007040101a8980c07030712100c945025040b100c80d030340080e0b11070b22185034041000c10900c045801a00024020f06034a403208a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 876254136 1250 876252886 876252889
    0x9060a1a01080f06012a0201090f0e0601030207150f0e06090a15021617030720060601140910020f010c030c081612020d0b0907080c1606060e0c120114 66
    0xd000c0100303c084030040c1c4500090050b4002c4800c000c03503810b941c0410540142d01d101c4a110001800b005030300180c01c049001c55070701d0300b03d20b07001c050741c0001c05d01625517a12000110003942c4a044102c03141051141c0f034940e0304d0954000c2e402200400c26000c50304e03500388000640341030001041c89840d68401451b00300469002513640300fa4520740e08015a880392040240300340114022402803082c1c024034180d00440160001a50040c175140c0d0380d80c80c40ca01000210001d2260100301c0070565040507010400640c0141c410003d44125010f43e80d003000303900d10000310916491401100903030400e001c9141d2910003841800310f2401c039800c007000900c03030a140040c103000009080503245904e1a600031100d50042a42800b0340f558000155502d0040185050180024140c1a400342c94140d012850080c003072a02039101c0c51860300010b0030204080d032254490400e490013510308650f24140419640c600c4c5442c140b0812070881030f00c0da104030309002500b080d0170590185070702c0c0003410202901e9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 876255386 1250 876254136 876254147
    0x90a0504060c0f0c030c05031902030a02060a020702220905010f06050312030f010b0f0c0d110c04061809081306030c02060a0c020309010c1e0c1a0717030c0c010509060a1a01 76
    0x240e01032500c2c1a64a20a15020b4070354455409c0720544201140c0d52182d135a6400002040c0703101e80ba43c04e585941e2124130010741a400790800c002d40c4145c01a80041e54002024540c011107070880c40003080d5030316152501d50071030300d01524840348030707890310300a022600701001042c1d505c061428126241d49846e010701c092800044c010094440e500103101c52640c8000400d40b024071102e80e0a513000d0301c044d00c030060440809140b00902c01c2c0140d8084403128580352050b0400c0325080c0d441c0100401c9076042c0c1c07000401203200100c509060a20031280c4030b441029040003d001291000218030b05100b4000c1d180440051032401401d05285083d4002c95020059801c00c98023801c103603d40701f4003440c001130400300034a4810203064052211205000b82000028110f4140f0200440c841380000d1500440307120f15070000d4103143d010300100b09118160ba00450744001c602040c64104400c0040050958030107443c60905c990110082c815000c409100d50301501c603642c0d408000381107540d80041c15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 876256636 1250 876255386 876255407
    0x1090e0601050c151510110d081902220b07050c0603060a05030109260f090f0409080f0c1e060a0c090b07080c0d050c030d0b010e090a0504060c0f 64
    0x400c040801c49082c40305082184007540b62031405074400f13602d01606007031480c44420100e03d1040d0b020300324a4460034014a00f1182c48101e80f0302900c400c00d400705068034410006024442401e001d0701c1c00c0040c4001c2440a4040c1f40d40c2000344200d6194088810310420f074050b00141e159103400c204200008200084014071001d041c4d410380d07141d81c0c0d4000080c00b9034050751b102d16015428404039100700040440c11040350107038900302d04071180903078528400f90301601c202c10401840030001c0c00b025150081c250150303d0070003003002c11886280e0f0740340c4129811010844c03507030101c045200900500c040c0310040f40f6484881c454100301c0915105c041d503078507000d8400c031012030303581540204262245440f800a095201e1405568510702d03e843e140660003480014114041e0f500039001503131140b41141c011081ca10015418280c82042c10401012150010340c10b0044451240780b00c0d8561007456442020b2030080011b2034502400c0683c00d841040303843c0020031598288a000c0d454004c1140003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 876257886 1250 876256636 876256639
    0x1020a1d0a050a080319230306030f010c0c0c050405151905030d0215060d1112210a0e0406030b1b0f0f03011e080a060f09060609020c0c01090e06 64
    0x9003114a000c010a1003518690841a0840e1036020302084101002000b00b680b924110364801002103490b0b401c030703442401ca07600010490f11081d6078860700c041c00c070007560b008000282030b11540032050903014219802c1c0d2030045c2c0428950541c0d94180402034101e2001801e042e141401189003d040d90180003012160301c074800c6041c48207002c48090301c00c0c242c81c003611002e4102c81c3d14103c4240041e64a10841c0000c155108140000a00c036040c9452002003490b403028a609103403c0340b0081010312100d4410f084611f101d84401e100d0048801c14510090391022609a95035600601c4018001d02451243c00e008905041c42000000c40c04100c050344940718002a800700781040301100058454200d0100048030701213088141720311050300950407900b10b85400c1c02803815602422800410030300c25900e140c0c00c048140d43c0401c0158215940902e540b543c001000c0c03c3c07030b1341c4240c21503c40350000d25010740d000c80d8000400004000b20751001d18242800812140ba0030701e09489840c0080615 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 876258992 1106 876257886 876257927
    0x90a2013090216020103020708070605070804150b01090312170c1803060408070206130806130605090118151529091e0111010f0f060801020a 62
    0x2107103c12080454294080340c5600150000d4125000654a03010200a207100040191007a14480c403200c0c2c90742401030426050006500c244a044004807614100045115030b810449d000c04599100b02e01e4854084440021a51032880c059510443c442481c103003e03039080b600025003080a1070501203400c0030644030406545000690b005811007000f080007070003600b0464001d120300c004409120181680d41c081c02407800000302c0300c5c01074120002c0d03940020410301e401403540218081c0028484000c0c2e101100d408011503000003420b450444410015244007500304080e02041c0c01c1c40501c1c0240c0d9807100c1e1200075515064542c031380c01d06280030819034880030252806500c01a03d20104055840804201c6150f4100000e06015149400741c41c980700c240a044c0c1d202c00c0002d408140415042114802c3c0c03065070300642c035164014001d10b0f40946c3e000100030b04c1c0002c0400300 = true := by decide +kernel

theorem cover : BRFrame.Cov 876079136 876258992 := by
  have h0 := BRFrame.cov_init 876079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 876079136 ≤ n) (h2 : n < 876258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
