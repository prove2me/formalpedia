-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:37:48.704407+00:00
-- url     : https://prove2.me/submissions/2c31963d-4344-415c-9c5f-b1b28e371dcb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 555395683 ≤ n < 555575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 555396933 1250 555395683 555395693
    0xc030b0604140f012a170a092d12050a0f0f0b0a0606090519150c05152e0506040807030311030426010609020711102a020a03 55
    0x90300007000b02c450007010000390341010510545005401d00c2c0001c01c4040c083d001c8000b00e0550704c00c6401d00c000b0028180148003070500c80c00200071098440a50341d22440030300904c1e80d0a54001c9001801c1c55640511403d6204905030783c0496844141e800924600b050202051100307540440b0940580c48821000c41c0000b0b228810701801070081d982c400030140b03012190f06070010500c40c0d0709441c00d4401e0000a51201c5c82714107a490944000f40546040451301c100031410750320400130103100505e801c0c1401d41c000380e07440e000780c803c0303080b00c002d000d000202c02c4c60101c0494020242c43c0340c3d5120201d182090502d1100071040016920580540750004610f8541c80740e044507150b41e028490800070154031444d010407000100010f141000d0408460080344848145956000c604000509034004400c1d0b01550051641103c1150f407000c403442c221506403d58101c4912075122030549403ca81d014107061315201d0351080d550540d440310711303000d59920070840c0c900740c0c0c20032182000030000407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 555398183 1250 555396933 555396937
    0x70c0b040b09090709150507020102031228090f0b04111003020a02070503071a07080c0709140a021606110903160302040b121c300b040204080a060c030b06 68
    0x4250348500942e01c015000510000c000064502e80c20000c10f0f510400102040000400745104280303000c1d555409103000403895809980302080c4400302c054240802c14107082490403891744141c0d100c00880040703040d40012100c07081006405503a80c0820200050705440b0019405413280510003882400301c00401d0940c0280013106002c00e23400154a18400d0701000080b0040030201c00400c2d90504000703501c0c2d20aa1009503600c51110b02258100801007034030f084e00c0102140c02c08540d203050362001020040c04441140e609a410030501050241c0524000c881c01c140c2034595100000c201c41da51000200030425202070b1190060002580c15a0207100040038450510048030304c00d03083d07004104c1105c0d044061648241380d045500c15640c40c0204a10440741500380005140d40b841d0760b0141d60f502000c1e0b0740500442d28513284240110208c042c0c1d4491554860401c1006101074070070322040b40b00c0c034000c00d8119030281d004a000079030345411046021032a03160110b060100c0201140580d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 555399433 1250 555398183 555398189
    0x11206080102161e03020c0d0302030712080105190e16090914011e030b040b0601020a081606050c0310032009090f0f01090827060408161203050f070c0b04 68
    0x2c0400c2c0400c031001e0120220020484c00050108948880ca040c1e8010f55105400369400740a0a001191030051600070700c10358a070a6002940d1a0300085000d8000301300380e10034000e4511030700b14401080b03d54401d24640c8011380300180023403a07240d11041300342001d482c054405607082103c0104085941d464500507076103412035250030840345504200d1041050241c00c0f40b407400c4e006070f0743d40810118090300095604150402c400380100d4440c080106d0420a40c01f101174612640090700d003e11505840000298a0003441c040160fa241d8003410089440705aa800dc0c03800e14a91040c0042041e032040c5482440c01d2403070b55901102c09001040070040c0848084400340c11a02c07080b02800414020034859241c0c4500811101801c3e5640c403101e0b0140d41c00162020348410240c5050151000c80b040c3e00610061609485aa4410009a13030340102100d0080021180741c0014416420b10079000361254191500360400c801c80d05070103034580040c0c4080d41e01d041b10540000d1203044120060001e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 555400683 1250 555399433 555399457
    0xd0c030e0d0c090c1211040e15040c05030f060d030906030e1006060306050319030c060f0207050a08041e080a14030d0c0203040303031d0a030305091e0106060206010b0a020309011206080102 83
    0xc003a1399404060f1600e109034250201203400c03c02e4045800c42440115803d1f0b8401000c1c2c001e00c0d07101c0000c58180da0030701b280b6aa81007890080d2000000b80c20002a601c254809021050306a43c0e080500106944413480207011851b5660148034250103900b00a0810701d44404454008028000c60016150a50300c11000b1a41d20f074400d001c00d0409108000e070001d000c80000e0600740241da001400000500d10107022141c0d42c008686c0c401019070101e4007030729000000c49014050b01e0038900302c240e10034490401100281500f03c0e062007100c460701821101c000c0c01400d00500d283d00e0b07000078940d00c0d4035250f201c0d00003041999110904c5c0c2c486c0c402602016401580c880e03040d450081c0481d00361080c0008251401c1d8038101882c1030000b155a5082c1d41458040740303e41300d0310704503440c0c44052000c00a440b2400d1628004003001540f016007104c80c981d08a5480ea40d0320308410300d0a10404a41400507007003009181980d5000352410b24480d903044070300051035a030301c0340c2e02404c80e00300c58260f2003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 555401933 1250 555400683 555400691
    0x21501030b101d04080703030609140f07020a03020c0d1106031003030905090405030d0905030d09060f0b040e0712080702060c010b0301051b0a0804140607120c020d0c030e0d0c09 78
    0x4012030b4002a0802504280f140076440020b02e41e6146072500009200505c03200c800035050003054031907040403004280b0f40000380490b81030310164a000741801c58070010f00d0035000000442d02840010644135036a0190003030680f114003402031009540e08400c098900300391101d480c5070070f910b0301c0009522500e00026100704940c2103180c018003440043d48190311802180050202140011084410260500030001013103800362400704d00394020000c8c5c3c1c001c02490003e103403003444100d4000c01000861440c0400c07030241e10404210860b03901800301401c95000510a10589899603c0f464500e0700469410f0f00703002950f800910079034010462100750741d4460840703520600742402010f0300101940e546107825000030b00d514003e8002d6581c43c004024809003c0381c14840c0c0003030400004405903081d181d0741d291000c4003512000600c1c0a056040d40b43c203003040c80452020642401c40c9500c1c2d6070310364401c1481d031800c0713880c2840e8905060b13010401540d0a0300044684880c0030040c280710001207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 555403183 1250 555401933 555401941
    0x405040f330b1f03140117060a0c090e0403090503011d0c0901051e0a12060606020d0809060c0a17040b06150c060604050c040b041221020c01030c021501030b 69
    0x81506a007055100781c80c00c1c86200110b075940c8405082c01c0800003690f034102e11002c1107007140a032800545003009080c5220000c99400440307400e000049001c1001c0f9000d64031110444421160300603904030000d0b0300a10f051011540403180340780c11074000c2c6000c0000c0c94031a00001d0869454000c80000c19124002c40104d0f5502440000c0c004081143c04082942c509800f1405000401d1740307600040701c0112403100e03107980700c1c601d02c4054840c0d008034182034802e616001004121902407180542314840c003409000c0d01c562002031160244034003511050b1260258040c0540041507040c081c480c00d10602c1c400c4109402160744214007412240400781421002d02c5041440400042d1010b442000b014401d14400112190400b4041d20f00140665802502203080c4c042d64000700c45007031000034000341c81001c00045403002801500800a0701c01018225160650001c403c100940c003d20700100d82513000703900085024405d401500c902c00401580c0b00c82c0064242c0044440310760000600c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 555404433 1250 555403183 555403253
    0x80103020405150d15060803040e15030a15020310050d050114070527030a21090f05090601120f180506130b011e030c14040e0705060403020405040f 65
    0x2243c220035441c00741e19880c1d41c3c50b03000c11100541148043e1681c1c0885580c0b010b11003160b07112100401601080c0ca8540d074440f05078010105040e40c03503102d003044441d00c0000624000c02c1c0c49007400d50090039140b1044c80060200045d40005004e4698042620342c0000c440d12000701c0403504a00c0b400c000600d20049840c91018071501178651b60400906104680095001015030014400340c3e049840f22100d0110000b0700d4407580100c010660280c825003200d001d01100303c1c1e04100385054603800384840c1c4500d038031454650749104031030b0b220346139801080003940999002e450803824000c01007060f0b841c809a14068844c081c1c03002011790080c8014105200e028401d6542040e00c03030003444c421070740d02d845400b0003034130600030754400118081c0a0440f2083d0103a800d0001c0d2b5010f2204641c080c0c0e61111001010300a44409020310b0a107070045c0d11200c0d0228071201550401840e040c10b140c15602800020a00140102c900301c400340642402301d414242184c103031041b01c0c0000c49102a01c40e1174 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 555405683 1250 555404433 555404441
    0xa1404030507030f080114120a051e190b0a0c030e01150303140c0304230a0f14031501090e030702030609030304020a1403030d0c0e0a0305030a020106060206430801030204 75
    0x10344d90401c02e00e0030060251481003154241d11540480c6c0c240311111115040a080c100000c2c0002c00360b11031441080c403454141c03c11940d00401c0d200542e1400d2903008030802441c01942d00090074200c181002074500f0086500004131908a0301c1c00080c410f0300b0110040c02c40e840000040c5018100e01c07010810940d0006101320301d00c004101d010700780300036180655542c2c0180d008005910040030000b2084034030680502070540d038010300022400b603071912100180c1107035000340074000411440c40002400c00054a0a03d400341858086e4203a10b00a01c010083c034006c451605140000c00c200d0001d60790401030140a0134070000031f140d4900342031041041242c0141e024402c01c0e42c6104204419903408400c1c3c500c00d0342c040354013042980944500b1104800701c0888a0307400300c60344a002c414440000301409080c403841e002080440c2c0c031920282e81d01e050440d5002c40c4034036642da10711441d07281d041c9602c42503480041301c0ea2544082c2c1881c0b1851401c0107002c44009003ca138010001e61a05020b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 555406933 1250 555405683 555405707
    0x2191a010605431e060b0f061303022202070c05030613030504180605030d17070e0a050f0d17030603160303022509090f0209070f080406050a140403050703 68
    0x920700380604502159800c8410300310180f50702e640d52503280f0005101018016400340c40d01c0008055034840d661802c07000818000c02c1e881c2c0500002c0c02070250b20f09040080b503048603451070760000301602d160308101c6000c51095500b04000030b01044c42c0d0841c907003400035007130300ca1154000d802d10b24203040605181c450024182c082d1500410040800311350080201c400740c4800c48000040255a070808d40044d2509038095505032140d90b402c000b440384e202ca400003190004001d2001c1b240c0b07940204554041c032220101e80e05c4450752008100700d00d0030040301c80145601418010034600d1075115040546012801044848400420401e20345000d010940f00d0300340c1010300d80c0b9030500b1500c4c000c0d41ca030750205542e55200d465800050751030b403802c0c900700024110782d00184450307882440c0c104800601001c04900a1000c1004240000e01548246101004694442d0600e950b5500c451000d4400a004800b005a40300800402402c00c45462031059000380c845a50b100c0c4586401800341103045c2e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 555408183 1250 555406933 555406987
    0xf0b03010c030e1b1e01032d1a030304090207050c0a030c060212190302071a160806090114060307050d0c080712060f14040605040f060e130302191a010605 68
    0x104120704640e0301c503814800945e241e01c0b4081003460749800140e0045c44c000401448201010040101010040082413410900740205028030760081c40a0b0b44000050081203515400600052020690a5002d0107465014100300c62007140d5103008034140d082140c206442151022000740021501048407100500000710000e140030000303440c0c0b05911000d0b00c1490109900080c480050002c2c0101810302000120502110b40c1440c1c0c10b0210100c00299041e030110345594002030045c03420900880c1280c1400016002d0052810304003c0b09610041c410b0b418890180010062800c5a00c1202c01019954131000300c2400c1040d809020501c1c640c1280c01ca031402c05809110601614101e00101c880c507602c0101c076262188006409000960441600a842e01c84400380741c03001900640f046455003c948030540d10707042c11000000500b4800900960f0000c0c11051401c40b4100644e07821500510220b104c00039119604c800c10701003a481319000480124940201502000e201440043c0c42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 555409433 1250 555408183 555408223
    0xa08031314180402010c02030706030b0111070302150a05040b12061c0f03050c0f0102030910060501111f0f140a0b1e131103090114070e0609040f0b03010c030e 70
    0x7030700000700e04200c030418446480c03000001003011640500820701c1c107190f00600382c0d058144c690b6401401040301c0302e00da40c000b5000c4070800300d40e480c1c0841c2d150305407034024107900041c903850700d160200e99105100100c1009400c002c0000c458043c0030240034079079002000b500c0181000010400b00084209130345400032421180a80003a01800042072883d80c581402c2d600c0b445144a01401c0c81c17203104035284e45500000400080c06408200390000c044c0e122401c02003070f51500011134150110100d040010b41c8200d800e2402401d0354003e0401030000008045240011040880103441c085042c80892a14000174014140418050741c0200d038000e80d11070301d0410010305251214991051031500500c03007140707803103201c4000c4c1d0402145605483c0040e5a80c0c01c00c00199802411041d004415001108002c90400c0c0d228110510b40e0000041c0280c0c24500020308010041080003403880c0000c0d511421720307049440038018000e05004a0b14009041c80c001840e1a0801c010481400710030056 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 555410683 1250 555409433 555409469
    0x7030c0f0e090607110c040c02010e1509070e19021c200f0c01090c0b0c0d02011407050c01060503010c05090a050a030803070c1106030c0c0f0105090d0c060b0a080313 73
    0x205594010243c4c5017500e00340201c546094140b07010741181ea81c2003401d0448011b160f5805400c03e591040c080300486880508a034000151709600303581c08582c58102640811030f1030345c0304d14201d070007502070040d543c0741d00008851281280d11031103403c00491a400040000c0c90401c1c41240300c4508246507181c0740f5141305481144034070071003070110824100441c000901ca00250321080c420b950103031103e4844e42c0c460184070225003040b40001224420400000101841801001031440850084400503114080c040d2429013054680d80c401d5941e40c03d000942d5030b403d00030301100020984640341d8440c2d245040c882c1c050a04e0704a0f60080c0c0a0744010000541410122075100c111840e10b10f00c00c41c41450b203000b18060203020103901a00100c18405880301a600405400b40e0740b0b421202001c24039040310b800d844c0200c4402050b50080042160450300850071626254490070700007030801b408000158002800340c220110b1a403005c2400c0100d0080c3e4810380000c0c01010200c0041558 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555411933 1250 555410683 555410701
    0x6031e030831140c1203040603112208160509010b2808060319050606041e060b0a120e0a0b07050f04080c03070506040f09020a110a0605090105011d042307030c0f0e 72
    0x403a034408c060415903500501340920203014141c43c2d002c880c500c1111040100d00c92151140b02190050310854000c000c44094070071003402200f012183c0251841a04ea880c015042e03403903401054400240300e10500d41c100c4818102d1074000c92000c2a42c0703819000741010b405051a00800c00442c107080402d1800207004540300140c5158068003c60b40454800e8203054505110140600d07081c0c2540d0804e0800b189800066010f000e108249076a83e40c640403030b03040090141d0365004445021a0000940d02022a1841640302d03488034980c10114030702406100951001d40c40340c0d001d101c543d080a103414001c0d2a0a102120040c0011034045003058204142c680120310b680c85414412903001400080d61400f520240300084990419100003803954204103000c2c0c0000c407900d06140d4a485c0001c90b09107581010030982d50b500800d5400150740c0c980d80c801100c3c0303025505180c0c1c001e01c01c82d19100c40d1002c000c2d14024600c02e081c55a255450000660825509a001480044646000c1044c080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 555413183 1250 555411933 555411937
    0x180c0e090115120f020a030b040213111206061902060a06080606010f121407081009020a14090a0e09150108010b010507080901170a06031e030831140c1203 68
    0x8035002c1c3c0000c030611540c80e003800d80c180f078804000c0d08814051800414800030302301d91803180e03000740c0d400130300c2e00040c4501c0e404654600740b0310440b090007481004015086800a00d80c403035400fa0401d468150503510707424540100c026090011b0b0b00400402a400e84140108402806154000c200c0360a004001030948821101d6100400c441e003070b200f95070080c4581090065103090000c0f0301040c14610402042104121288280260800000a007200147c401c4901d59000340d0f0340c503070a9011003402c8040982c440c0020640c003000c22100410a0303c44d10300000d0054200c0c000802a002d80003214000e60601644491000c1c0d260294540042c1d8211080f200b000d98006c410780d030703151301c080010394943c0391842000386800301c80000c0000c03c0c0c03402d9000c441968041c1d5900c042c0605410400c090300f0341183c0c4010300140164010a004880302c020b642c60a8a0b00ca8100c0c4064040c1d5070902c1d0151070b282c5055500300f110381000c0020110600c10040101000e42c0c0c2c0030111044030618560364 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 555414433 1250 555413183 555413189
    0x5040b0c030712021306020f0d0801061803020909010c02160b03060919050106020d020c0a0b300c04031e020114090316030501090506010e10030303090204180c0e090115 74
    0x10240010000b00c41c035204030715441c41d4005141d011912542ca00701c03088280c269178051000903218116040400960000e2003842900c080e0b42c5984ca20fa08001c0121112481440a61802902d85038040700507030b1603030080d0740704a02d0340000248840c03581340003d00c0c10083c000051003c0c10703014405e10100c5140012a540010701740c0b03901450ba160607050561201d0000c0704252420b00c0c040010500c194085400d541c8039040341e0840b00c034607440300100712111803144a4600003d20800003070f00e8001d40707820003180500b0055a40040c1c44546070030386c0110441161000e429003000a03082c402c00460000c2681c541340c0002580561501680c0041c1c603090b4140800c107905040420301c13980c1540c04200c1c0010341d45a20381440d80040e561300c8d007503018082c20582281c2602450001050358401000b4640c8140080011410600d2454400350010328046000781e820a03182d501031194401307a40c80ca585468403840f41d001c00245031043c07440c51007801502c1208244d04200b000d000401c0e90410300019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 555415683 1250 555414433 555414451
    0x8012f191b110a1a0d0c0c200405180a0f0c0f090e06060303091305040f1e0c09050c2710020d080c0702010c030e130515040b0405040b 59
    0x121610810301030380c4106404685501540050001030100122056004803100d019100d64010300e0315000303011038002d203200030036000d18014003003181155016009010071022a04000b05102c0107500c86500d8841c201c900b07031600f103940104021681c106846150b034000e00e1070042124131114108000e40ba20038400002d41000344496114052207082044c003001020100c1541040503541c00810000d002041404481c40c05110b0010368141004401c941191000400444111400b41c610344010007025109841c0611442c1c603800004140c02e03551107040100c82c45d04010101185806050b07007070036800142c2d0b40c0b070508051106111703101d42666041c04040030b9401110540d9088200c10000c500481540020844401c0c1e0313006801007011370344010603690380030242c0c6e51103034800743d20b08c0317071400080c00aa100d51a01d00440d10403007040f045120000c042c0c030b021001e60007548054901c1038492040228103280b09022070f1405204002c200b18003990f0500143c5820b44030800b0743c680003071150207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 555416933 1250 555415683 555415717
    0xf050901030b04060b060d0e06250c03230702040f060308160f08072105040503031902010b121b0103110a051c060905010311060711061606020408012f 66
    0x10810a11760407040c64504041c0c540740e02c4024401051010300305151100c1c147d801980c002c01e40e0400e05848603001c5882240b05100d40e124150301c21581181c91603000d90400490400c10100c8040240c18000c174911a0890b041d203460031801040700300e03000103050142c5245400d100300002500c510981b030081074009420b40303221140d42084200e124032208020011100000c034a4200104080c016000246e24894070225007001c14059a041c8a2400f9840d03040e882441035400030182c101c4035081000c070610000c2005030048000c80c12040c1400248401ca42100680880d60381c4d8048000503a10000d18050185803403d00c0313100b00324407a004240701000000648002c02c0148040002c4507940d07040030801c6200c0d940c1925500501d400c2c08100da040203400504095860448141d0350f1171508114090b6061240e041004401d030b0080303070760000c07000c10f6810b403001094152000d00020080e440002c03591000d60f081c03107003408030102004a002d08620541d1689611408150707482c1080303041d0b101d6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 555418183 1250 555416933 555416941
    0x140c03120c0c06130e0610050d0c09080a060509010b030106030f140a0c0806040201020d0305041101080603100903021006120308191808090909010545070f0f050901030b 74
    0x5050103020b45246800600005030b411080b255200c0400c00c50300e14842500450301c078001002081600740700d801002423001e000d2202400080d0740700810004040c1000000706035185500d504000d5124000e5070ba546c1d952080000341c03071342805070303090400d011030081004038210383e901c0090700700d0240040c07e0382902000100300e1520801140680030b4100c6840101c07195600101991900c040b201280140541c050750a005c50090082c0d60150f90b1220b0506102040d420044400f0440201202c2d0f0506ca484800c0c80404040d124240b2803d00a42c05040078000c0d4904040581d200baa2007d84900580c1200324046039002c031540d90044a00380c2c83e070320008210a444400f4107622018510016100000c0d50708026040004009500c07041da82c5030700983d038000100d4222b800c111001c980001c0040340151114884021a0415004030880050b0310946100c041c00b144080c40d96400007540b1000c820303c8003000181490000b0403901c001d8250309030608001c503a810806100040c40012560045 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 555419433 1250 555418183 555418207
    0x306091b180902040b04150e1f020c10050406020114042424150908030429030103050a031b08040504020901030209090f1b0304080f0a050c0a0807140c0312 68
    0x81c8004250104040d925107469110450590340b19204900c0320091324400c0171500350103080c2c8991141c200800c12002c80b001c00c3e110401039900001000c0440c0144007070103005940711040000e0074030f615500c7c1da8a9a040c45030190131150420404044000e5940400001440011810b118603001e02950070003001d035030044a0242c0816900e41412500700c0140a21120100070214111031100e1141c056031220140b007a0760840795801070f0035007a0010002444080c1c00d0014690000310011ba13820300460041c1c0c0054890f40082e0003ca40a8005441c100241a0f02440c881600020703118100717401003890b43c84002074411807103403500035a00420445001c1c4e0180d41904c0106802034824000c80c90008690180d800d01101ca001000000047c6d40c07004540c050f0640340b2a652004d007652030f0529000b12024650070421440040082c10031801c00001414490600024815884039440d15441c9c6014600e0721414815003c0c2c59014140c00e80e810359002406600740c0d0b9070003040d1740e50f070024120742d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 555420683 1250 555419433 555419477
    0xf070e07110a0b0106030911061306080c121e0106020313050f0109030f05010e100c090308070c03080d0515060304020906090c0c120d1b0c1b09050405030a0306091b 72
    0x1510f20005040009071164058101072555881828047c000003500000c2000314080c0300343c0f400405a03820424410b06001c0c6c0f1500c0e400c003004100281c203020242100e83d00941d0210303044107a41d082d0013420f0034445103807a2510f01400b014000b45013006280ca41000e5011424800c00d4070a00c20740c050060a40d002c1c2c450100556046912038000f1003050810358040d1040e500d081d002c0b40f160500000ea8101203104002c2980d5260b40c1780d0304500e01d541c03120906900400b2050700c01180e4908000005910b881c014560102c640380b000c1040c2c50050200382054584035111400340c0d000300204801030396000c01c0d0aa00030422504443d498071388000c004668080e001501070544100107040340807400c003401814000c8541c070014042014482c818840180785880000d0204080e5032540c80082c2d181200c08041001c4010f003015000e40c0c03546400140d0380162010380d425000021502190707641401281c000e005201030174801c00514201460745482d12441c0142000310005030901c00c10300000d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 555421933 1250 555420683 555420703
    0x150901031407030b0306090c0a0b030901230907090207080409200d0603050613080a11161815050a0506070614100f06140301170f06010603050105030f070e0711 70
    0x40c107060640340103903000d002003500700300c1c1e140310b80b003550005000d1035400198032901036005803d290040d803510300c1201c100d400182c04802030355220410008118168030001d0003841c035070b41a03824142030040d442030900d603e6030445131103180100020740c0845c0e0058110f8080f1740c105000007901c3d61085981003040070707002e007800302e80110008000700c100c10150401800c0d01c5c007560903038249480d81400201a074045c0b5600500450b414056814002c0c090380005010811104c2a60040561032000110b4101241c102036100b0b01407014a030900a070b14416403a03502c0b88070b80704410850525002608c445014480c0d64410800041d510040140c603400091004e02040300102d110300340b040d800d10942450380079400c45c003d151700002801a125241c6921442d0300f07070140303d1842e400d258106000441c2103a00e80701d24882c0108901424004200083c0204050350300002d45504142c1010700b000000310100c082030748010018800082807081080d0003800d00e0030116851104407030790500b0008802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 555423183 1250 555421933 555421961
    0xc150e1219060203180a020306010501030b0a0b0d1e02090a1509050301020c010c020f2b0306150c0210020d0503130f080d0b10030c08040605090309150702030106060e15090103 77
    0x54814200300103074001d58081d0a800d14200c0c03200e2103e0480b81d1b0b840c200b40c1c0010b50b1689c03094004000700d50180e03001c03641803000544410103c40d01e810304030059070300c0801c9081ca82a52107004c2507103040001030070b44083d00c1ea8181503107402205400101003000324055419452165071400054500500c982002054050000e6440d01c03244400c4174024901c14545101502681085e0444008081b60040003040550b410304108040000c1c00100c0002c1f242da1442419515100801e060503107100c1800c00801507a1024049800b600c140b00c10380350300d4400e02c0d00755070001009200c156004004d42c0c2e840409a541407041880c03505203220080f80c030150207003000b480020600c641002c9034104140594050350b0800e01c0d511691011001c458052482c040020b80b00700100d000120107400c0550010b440d88100d9040000f00b00010f8a244110f203014011040700040e00700440c00c0078060340c0c00034096401c000384444e000b0400726801d55030500343c83c0390a0b240000c2035a50703a1b0095001700c0c2900001c4c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 555424433 1250 555423183 555423223
    0xc031b031b0c0a0f051f14180f040204060e060702030106170d080907030b010b090d14030705070f0812071511030103060f1a2b0309030c150e12 63
    0x2664903160290021110301500035220f02148822801c80142d0450303402400008900318582c81c003d16903002d42400404000c0c45c0150716a00c00302c00c0300038060000c0385107040d408503240e0404000280300e101220b140614014441001200c1d04034003000c0e4480fa0a60b1030543c1e4898600c0000e0060489811820705219500c242d240840e00000d011800c0418a84589003030780c03501e0440729034485403031100a1004020200501c0300110810150502010180091901100c180d030748002c0350b00c900b00500f660790310104030103040c0082089503070f0080800840c0c60004a0a0050103616070140c0c0c043c000004100194040030070043d907010703c55845c0c0b410401c1004244c40e0b2048800740c0e00038801903641a0614100c24954411031050f9034501842202c409120310600061008ea004054603651500c0443c42115515400f0304d072900c603880f8420f80d20344820505500e02416042543d8001000c0044000c080511080c5c020141010f4188110381c803003681721150081d14545071095016022003560703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 555425683 1250 555424433 555424477
    0x151103120603060a02090a061d090a24140904030c0c060504090605180711010b03030c0604020108010e040507050402070c080f07030209070c02010e130209060c030307020c060c031b03 80
    0x5003044403800740c00200e0607200551a41071000c070a900461940d154002e0390010100a100d010301034000500e14801c400303010303010f99000003030b503001001c03140b08001c69101c0d5000c0808401c2d442d0900020105502c0c2b01103d40d0401070100b4410303030b1707000c00e40b8010740010010070306150041d998402080d6001c0096048152a0b0314010302c0d603006840394808003400c3c5100803540c0c0c5850350034060300c551440d01401460307403400c6080320300145041c0407450035541e0710610710072914180000c000c0612100020b18490030680300044c800f507016030100440d501100103020001d84007107002002c03030b00308480c0036071180ea07075082042010b40581e01800072482008bc607050054408144402201e000b2108041f281e90b442100740c3e01081c0c1c0d020000d0014070400e414082c20320f40b0765a1520007025003d030042c2800c241c68017107490340d8804180a034041d8004820040a02c2e41002810304160f42030f40c0150034140c0d05d00c1400c3c8d80340541c101c5500044041d0b12802000d010400c00d5a24107600725641e209500300d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 555426933 1250 555425683 555425707
    0x60f0c0b060607141e10090b0f1f0902040e0c070c03120306210302060a05090c0d0f060c0c050f01060e060105070f051c0e03010c09170c0d0b090105060f0a151103 71
    0xf81e420750406010386c840f00f034103500c118481c84000030f40000e403207036040d66045100b82004800030030741e00e0b0992940380c1d03d5400041000f18880500b00d96000181e8a038103000200041c0c0348000c0c080d101e458010840318002401442d541c100b240c0e40701032103013001c40000305d003076000e04801c1d0801804481f8400c2c0c407136019505102c0c00d40d40f02d4041c0e0282d499588038018005c00307458084072002483d0b40301880451583c20411480c064050180c10040c07503d01035655030005a030b81034010800081c03002d010301d900380310040c02040d086c1c00b8110300030001c4501d00070940311402401000181404000714900382070040d060244000158400203640031030700b890000016580b420100340c400145d10b00c179408154201403051001c0d80010f03032074800a91307252000507290300000116480322402003841a00d266240c900748045264031403c0ca48a280c030700000d40c00d085520041c0402d20600d009002d4480548034202142c06443c40070000c14007418580109407800c6160030300001032031000241c0020904 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 555428183 1250 555426933 555426973
    0x3040515043c030c0b22091d0c0306010605071a0106080a06170a0210090b0d0f050a0b0a0308030907081506011103070317100519060f0c0b06060714 65
    0x20008548218a10703001600c0d80d000c4242d400010102511190103200c03e0448101419040c0c10840c40201e0050010b03444400c01d0816502a00d01a41c44880300710071114404104890350100000402d11482d0b4800000e45c0c0d681e041c40382d18203001c0e00280e14020311502c210080c42c1103540350a030802a5951305002002c0318402c0740d415030914039000005c0740181d014285d0402000448005108001c20b940801c0f0011036140707410824090400800a048111500039084002c0e940c039002684c0c0c070b5040d40c2c0005444008080700c0b240c600c0e280d9200034035071380c000e4207905882c1c0089803140c50b42d45010100f840d10840341c00500e00e40c0f1405a44000e134203550711926115403001c1e43d8820442c0401c1c88801d560b8082e400d4010042422000d61040b00c000240d4155070102e5260307402e000c2030303a40b00082045a9240c01840303c400380020402c0c4861a0003c4104501404e1803506a8503203126890380e04c1c25110207081d15110f144001040e505000c050039862138145840010340f51840d820401c1d181d885 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 555429433 1250 555428183 555428249
    0xf141e0109050612370c090e030903060c070308070801060c03030914030403080304020f0609130207020d0210020109050106290c0a08040806010f050117040f0f150e06060a06020304051504 82
    0x640034600400100007000c89013058810b900a1ba0742590500707046e46400980101084d200e52071005002c4010a41d500b0000d0398000c11204800a584d11881d040051404c0c000401c0502400340b044010055281c0c048040e5003c00c0c5c061070f0019125100f4238005541010004080c0c450b80b00204002c000d105c0c0b50001035004074400c4400300e01070ba080c2c0090151074014903c425034010726400c20070b2240c007841e800500011b8801412074841c0e0201d07600207a10091043c5409c40140e40d070720300e10030400c80244102009001c0344640341c1580c4a1004011140c0d419442c400c0034a0200403441d030000000030401288016445034945896036221852540c0d00d410911031a0031000e0320b80c0000503a940900d100040301c0318080d02a203601d80d075507101e952441a140350211203021504011201041d0704481410484194940c0802c519869070000d91030424040e04c0c0502c10856040c080014580010444086520a03200d008004019082c0c905075406250309c40580b400441c03c0200e0308020382e881594031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 555430683 1250 555429433 555429493
    0x6120304080106170c0f010c060f0603211110020a050c01020f091306030201050f070807060f02180102030c03030a15030f0f0b1e040303050a02070203010f141e0109050612 75
    0x1c181e184c0c915585107200d407040b54011819001e84413103075105108070842c0c0c41c001d01c030106031010030340300c1c140444a01d07030b00554050040601280720142603040c1c0b0f111419082c90011101c5a5031000d03691101000710b410000700c2d81c001035040d5864002c0f01a10640c00541e0000c648400d40300d80e83da601c07640402005d91091424500780804421580700310000d4a4042e51614101030700f10304806484d40c041e1700150fa84150501c0319900198817400b0340402030300f1191000d41c4520f40f0101d080c2111101d034100e5030542d0414030640000c003000000f585d9002915483c040384070b40d050b02035040e080d503050f00040c08100c64846084140806100441b000307521070340d0000304070b9480808580c003441008620210050001002c4ac02003482504515049036401e4001481d0011a0b400a400c44030900c0441711195207c101100752201e10800060384514840100d40a4a41000340c1c01c22a04050251016441d07071000030940c140c403058080820780d800da100721441d0412684003402e1030b00e0044018a0307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 555431933 1250 555430683 555430709
    0x1903080708010803030406091e2001050c0309060310080609010c02060703051608040c1205061608070203040e070207050604030503090a09020c070e04060e06010e0708070203030402150306120304080106 88
    0x4509846807007424101c6030800d01541c00c60312540e0710940074145a03d816600101909142d0656955803032034050070500c101d40211007450007180e6800c2080400f07006905000c828000301807207400c0403040303402c0d132070b8102c2d0455600e0f981c000b00e50502024641207400d0134030903c401c20903aa981580203420080403034085611541c1c901d0011802d81d08100e8041c01c04842c480c120301c0c0c0c031a00611400e500948103101d040c0001c0e4640441c2030324014130030750944a542c402802d000031a0300c001e080341e00100080c0707464001ca19060001965905c281e20410301460a644001b0302114403c1c4000405000000c01095a990340c03070400f00d540c0d07004105224810911428001000d80307451080385d0090502d04041d2882074a42442818fd02000a00640e80c5a442c1c24007140103000074071409001e40221488072115040020005001d1200100290f06540c410420b020143c0d9400b58903414144280204554a507109804540342104c40d00744108544000705020541d4541074000b1000ea40e00d12038244 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 555433183 1250 555431933 555431941
    0x503100519020f1b060c0a050d380303121f090f06031e170d0605190806010f0807120201110a140f03040f062a0b180114060918190308 59
    0x1600d945e400d84c0c1c0030300d80b10802c0101070321241c018000344c504544c1014000071052031102c100c0e00424404180d1404840404044503042c26413000081075601d01a40250705080c0281c45400c40200d0280c460040d06c40a400d0005c00c6162080f41100540819441444499000300e24480582158002140c400740740406034600002c1c2c8650f094455504642159601e03185409507611541c4150503150406403940000b05290701d0701600c810380001d008060b03074421864240128280325040c2c101c06945048080c0400020f400020100300352182d21000040d0410b4610050364110111003c411180c0511007a07407091041510400540600e200b09941c3c0b40120710707001a45900c514081c100d0700c00080301d401d20034036120700b52240c0b181c0c5450030405032a180f94107003981e102e510601d0885e1200e20075005c10000c410f0300301c1054081d07982d800082c040700702e000081da00d02e820001c14a6001c2c00c04e02c400190400200d200e00003d01c903111050381c503490030010b070311380c2007001c032607010f40c080fa24442c041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 555434433 1250 555433183 555433237
    0x1a090f01110a06020306011808030d0c0c08040b0a0c0b15040e030703020318010207050d150612030c17090406060305011a030906011703190203091005040503100519020f 74
    0x418500000e01c0c0a8500d61103240d4a041c000d40004c4c03d12810401240e03005d40c2c2e00340b00100e03007401500380a030065445824404001701542c0c11342c0c40320b40400c501c0002503000203c240c020348003902c0e07080d14490345840c040780c4200c03924440c0b210007424403036010052010000c0d0200da0b540c20080265028014240504c060302e82d40c4c450540c2c0103005910030030003281025501e4400040401c4148103440074599540001041c46102c07800a6500803440701c200015010180b041c0c0d17000b8086407035204001001d0380c4015048002c0301c480030f0104002034460314011600312084030086034004108120301912400000d004250902403070002c00010104040c2d02140e02050307a05c01c01c009001010a030382892003030054105044c00e00e40c0144001e01200c1240b41c02a80b04204164103540156107645072032082103d44180d00d92024107000d0304100910032900e011500c455621a40b40021407251254844144401024414072115070701c0850350079640001e1800500b0710140c0b415038802c00c1034440e102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 555435683 1250 555434433 555434447
    0x60605041104030f0c030203010c05040816030206070b1f0b121012080c011e0e0c0904030219030e0604030f2907030b0102250801140f0103020105070c1a090f01 70
    0x300d0580c40d900380410000141302d5201290780511403c01d0141d00790380d950119013900c005d800d03800007003040420709029520080100d5042101130b00c034034080191441e000314902e44149070f00a05549005400a08280491441c005501e80071250643c001035a9403000001a04141901d83c250070741500824940000c80007180140c403041403030024882804d5803441d0181d4450311001805d55200c40a140c00a0a5000144507070b182071400420300c070132000310843c00c2c0055900c029200345514030900020aa00003480144035018001446080f2414181919124001d252082e4800000a804010041d0441c0d104c03d4251054109040000082485900e8003500d0344506c1580040000002c8003284a504054070b14441801074449003101215454404480c0b05241c229000b4401c1040207001d034244200d0309040c01c0c3c904d1500c00d40c1002d060132004030314184000790400c000030541005210351100c02c04028175100d1007160203031601d200055429009058024491100b003d0650103035401501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 555436933 1250 555435683 555435701
    0x90f020708091c14010903090501020f2107020604080f0127081c02032e03050c0909071e060e0a030f230d020a061a01050f0307121806060504 62
    0x1425402c0c00c0360b803020702c1030042644424003060704101003c5008189110313143c1402e405550004170380007015081c060845426070740240d046500a403104d240e49100410040500b19420315280e880032901800b4200600a080d8007a5118400140000702070000003030003840301e20010020300510392440c0c2e9070945075482d07022400d04c141d4424103400c000751404000b0300750425400c4140e070055010140301c804a80040b14401403044085d00e000113408072141c00318004600110401003980d086580309910750300f051580c0760003510355402059212409010038000707041800040d20340f040c03188801e89500079491003100701042003e101d001e20703402d0161000301965002074908992030b0341980c5a10b0115082c1101c0400c0801c3c01c11000c000345804d0142800358802d960051800c1c01a40c20f2450880318000019045401c104002c0c000603600103043e00c0c1c003001e00303107161522941da100c01540c09600103604c15031882c1c44c144000c8090082d40c02e43c000035030301800d010800261100309100071203110503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 555438183 1250 555436933 555436943
    0x1051212041509030c0e240f150d1811030303010f0b0706060302060c0328170a020904060f0618260f030a050403120801030f0605040525090f0207 64
    0x103015018001d0038a030480810303450b01d40269503a90311100c004c001140c026039011007001c42070001c0c69440e41f052040140c00108400b600784480c0000411010500b0102c1e8064010780b01080403000d0b9810603220f46c2c1501500c10300013881d00010740318005907401000c561078121010100b040307050000503a41610018001e003000c00d8140020f50246410050042305c040d6103d007000b20040e12000c01070105220588021616600b00d00035500b0440c41030018203000c03e10441882c20355640c8003416120181e001c6070004216121040804081d206103004203800c0790401c000040d40946407041101100c8980d640c03000041e04072100509207280911580101090043d5450140300c000070045a070044090120f0702c1e4404051416030954100009400106a000c1001c005000f000e0805011118261508042c658110360707484050035058035000c0c01081c5d81c2c80000b03082000030440c10401c840090080428407050300c0704840c5450480c050003208904010102131001020f0003a42c02c096442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 555439433 1250 555438183 555438187
    0x9031009020f01140d0c0816020a050601050907271701020a0807080a060911030105030c1f2a061a040c020303010b0c0309060a0e09220b10080d020601051212 69
    0x300004444014104d9002ca03420001000b810349040007500c1600c0c501030071030321158050b145c80b22508043c042040b144c034055410001801000039004204641558000c0b94801669203c444040b40d0400d800048c2d20390340300129617003241203c038582e040422a1a2003c0d80e070200324626242074280d01400c007046021035580700104441ea0b02400354103600c01003141780000d550b9650b0444a0a07110095081c3d0310121b000401448241401d003c0c3c00b000c140e0641d41d411241061004000b000c42c610b12800040016aa0030f140305c6156a003e04c43c04800045550ba282003081d0170418000e0850b002c03420b5000642e1503100b0300341e041c5070040b02c0900a1907005541140c5c41c0c01e50034201680b00c143c800c10180810003000b1041e6170380744050001c20b140d41d80e030190b0f840100c0d4180407008401030810039010005100c441c2e0b515044810301c10314203a114a00541c0c1d600c564000b1701c25032010f80c01402d920f00581c0c8034a2101075000400e14102c9000b140d251076602510303801651150241da044259055003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 555440683 1250 555439433 555439459
    0x10912060c1b0c17062202060915120105030f1b0d0b040f0524010b0d060e1305070e060d1b08061924090b040915020903100902 56
    0x3035014806020890601c06000e030002ca480da0440d002e851011108000004024007406920742801403052440b0401020b80b4205402549045080e50000c0d0440070f045030910021920342400b6036246850240000d61162001602c410303241d04100101c680c14003e05000240c98070700043d00c0b10300c1d0760340d2801904c5d0040486e20307408c540540102100c0c2c0c100b8000040440010400025a44154028404034084411525025040c40ca0f02c003210100648804056403000150207142411111140d80c16039070740082c084800c010f4409503014115400301c41d03040000141e24036007180000c44c81036054a169548440b14003529440a4803000d4001002c0040d1030001444c60f031890705540440c6404084080e41d80c4400c0340784c20301c112410400e590348448170740d0404d20980180d60215898400c00750132500440f642c650418601c0c814003260310b486404090316a19950302136289603400030b14404040e0306580c0c100d0041d52143c98014001e114034402840b4040700741c4103d0603107d034010030341170407004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 555441933 1250 555440683 555440693
    0x40918080a0c0219060509010f0806010f0804020d050d0305160201021809040c090e0a0312140a0515091e100605030c030406290a0807080a060f0e03120114010912 71
    0x2c0841e00498004004481036540b9207490501c2c44004e1070349a0300c855030342d2503044c00140000c00c40c1e86c1a03010710400d0f4041c400c0c1c9a1300400c0401c0600c903145008a0340f50341d2400041c0b44101801d40240c41401507004614a4a42c0750b0403851241544140d80b02184502550072404c0380304141004c0c03488845008a1851032400021694026004540d06130742c1c00e40782e0f030040341190210181503e490344011118000c043d009500d100344c140c0c440900b0040c10410066406c00c249005010700500742e62080060310101d5030540d2200c43c424041c1038101c1500e80503032540500840d003071101c4104c290359400035424203840711200054902613a952810b41c1c4500d40c00c031405420240c4101c0384240c940525125200710100d1005070a004100806804210038040c462041c015030000825600704039400c0c4041000066401100303030f44100006002240c0c2a00000102501c170811400c2d400002400508100d03500f03d01c034182c4200f800111100c0d000700005507085003052040707441d102900010000851 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 555443183 1250 555441933 555441947
    0x4060e09042108070e0607210302130b0705010509030a02120c031c090b0c09101112041e0902090d03030c090e010b04031a0603060f09120708040918080a 67
    0x1d88100d20b21014440302e0707407a80d002d088444503081c00050f980d500300000158441c0c600000c01c441a50300764540480d03a100c40294007080b0000c43c0700c0c580d078000c481d0201340c8294115102e59104901c0c1055140c0c48883e03030302d107940c0290016140d030340c01c0ca40812034160000c070031a80810341c1d9800400030150802129062074100700740320b440382d010030303c0a440b082081400c0c848122406500000c0c0440141c40c12110906010f0080e03007400344144100c000585a4000c5c1b0070b50714810f820160090080301d01c07058500007801c102e258262a001c43c00260001404051180d00b12000d50b2074821551560307610000ca01034644d41c075900c000e45040324404680281c5c402c100f100c440b443c2a100340340c3c40c2d1103142c589003001e0340110803900000404005024003207140c0845e00600d10039007440c0d0b061010000c0d40e201c1001d400c200700c0140040110b8021402048041e0400c0e00070a82c039501c4004500303002103150010701c034510095042500311020200d201420002c9c40354403000301800c3c1960300d10211500c0e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 555444433 1250 555443183 555443191
    0x120207030c0f090c02060c180d0221060702060c0405090702010e0610090c081b030c07050a0308151c030f1407150b0a080a020f0402250b060604060e09 66
    0x1502910901001152501e800c03400a0020b40e00e800c0b0344140f5282440044807501510b040031508100c0602501e5540786044408900b5104500c400c48948030002400d000e0f040c6000a6020300744d800c1000300201004100011240c004d41a140c00783d0350070340140c0c1c840000700c4030403056820403c4103120350301c1d020040a404c10003510001940b50714400c0f02614080040e10381244121207600c0812000c001801a030b943e5680d00e2510710780c0c40c03c001355442230b040b0441c40003051880d000300000718049500401d9581c5207410004403041ca819030708028003002c0041d1100318000100305400002800c0074414140c646001d051990019000b54400707c2d24003201c4d10042080000d026420003280c1ca0302000b0b031400c00d0160031000713803141158500cfd1040f940142c0351140070b1a0a614104404400482d55003011501075644000a00200700014001e105000c807580500300400b540e02d40780301140200c01c00c058420301003100c054494404008a80c065031140d000094183c1003c0000c80c00d00c88110340d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 555445683 1250 555444433 555444437
    0x60c03050a09030609321906110a032405010f0e04110d1d010606320309030703090b2a0c1002060a050709120206030402012a020f03010e0a12 62
    0x1002c0d880c0d0341e9990aa401000307003035890100350454810404401141101042100400d0001902c81482501e40718150650340a9415020070848821302005030842030f44107501e03130b1119548400c000000340040494119580e4108800a41c2580420b00165030009407601611810348000c00408200c07680341c0784c601529081511006881d0034440450b01800c0c004d00b4101c404140c60a941c00c0d106052001c03552095196030500504104030b030b8000c0440503494140c044955004c4140e11701110748c00201d604040c15502c0f00000300070345803002001801000b403203595440001c40d9164105252801800740800c3e03182da04640c10002400706000718407800c1260020b44e89415290f10000b9843c1840868440160b002041040409031061242036442005820483d42190074113080400c0e10400c0c2800a004410010200c4d0039a8081d43d681c848010b580001c01c038002c115010b4269404a0003001213009400d606000072a80c5018041d600018540f0310082c000c0c0201030301d4440042c2e204c0142402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 555446933 1250 555445683 555445697
    0x120f031602030306010c1b09020307030e0f0a0308010303110c0a0303051804111621030606170915071206060201060504500109090309060c0b0105060906040905090a110307060c03050a 80
    0x1c8e00106400038504c5060725842c0011118280c4a00508003a60f900188000c2d401c0305030a0400690490195410b4a03010300e041001c075400c101b0180c0c84e00c00d1f02c4a0095002d10810800810164000000c5c011071008480c1a0004030410b0144070a5506400050711002000c2c0494071443c070b00c03040c00e82482401100d00d052311001441548407408421091480000c0e21a0341c148511a041040711920280d811f00a841a00c0c2920041d51642d0504070b01e212124120804a002a44145582641103c00321010410279070341c1c40d4064001c00151050750b00650420807010721020504031a1000c10924181005407107484075440901100560004031000e0f5041c10035804c550501d20445018152044000855a150b800c018108040c0b650200c02008040211200010030300103885044031000c0d2080c5494440f070070300207034043c0100d40000e4440c5241ca030400bc1c02c0e00700001d00d0111107015100d03402850580801b41500c41342d150280300003103107005400f500040e200d400100304144c0180341010f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 555448183 1250 555446933 555446939
    0x191e03020a020a150515060301060203030705130302090907091a01020c0d051207050c0f040b10081b0c01140109060b03010e100e0114010e01020303091b03120f031602030306010c1b 79
    0x4d0042c41440001c042460b40d80040000702c019580d03051030441d000701d034528155850030170002c0d500e1200500340d20402901040080c4c000307106011103800746a00520440035860008841681d80403580300b0200d1003820614081c094048118045031513902c1a400360035006051800e001401240c070100311864483c25820928480190300a0610140b00c2d0001c4e000240280b420049007110102090707124524080300e4980d80d54800103400549015400d040d0042d070780301d40c4244011030b00030801007421035001500c0c90f2102c20642c020f0702c80d0015070070010f141e80d817100d0f0741c0d03800c0341e099006004204800704014084050300e0002190302c80040c107102c80c0e486498149002c907594080c0d226001c00905000086801d6800c141d41c030540710b0080c0700640c00d501d01444940d942e001c02140400000c2000083d840241e01d084c8030200c4c031000d110080310b2f030368921080e420031180d01c2260001c0e1030110140c10780c00507601c00300c11280150016074400004084e191210106070900400303250503848544000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 555449433 1250 555448183 555448193
    0x815061218030a05070b0f070504180b0405070e04060b030603030a08090109050a060b0102190b18010905061e01060201050f0a05150a0303050a03060504062615010b191e03020a020a 79
    0x2010300c1c14143d0307585500c0f030881b0720300b80140d1003020b840d070303d05264480100068294441d09980844110482802e84a0a02100b000c010302c5184040c6400034107007020840a950850042d85030000c05a9003041000c0d650042d0401c0d5002c04c2d00c201c1d5064104100031490984284082c03900111498000100068190f9406145c000310740007c0f5a01074071001400309540e01400b6071421340800e036125031207808941d611662800c40080502034402c1c9405e0b445910001c00754480740040d03521030202e5110b42402d16108052908584501e400c00c01810008540d440c4107015450045204684009040c0c46078032610010340030007001d41600c081c80205080155450049047c01107000c0e4460640da0601040300030b06031016500540c0c015400c1130070800100708900c15141d142220000b00031019062070380150f0611500c9101c0000c0b0010020004c109021800d004244a00580c0b0038017210620798a410b60f43c00048070920724038149070520580e280d0f4025002020450703180d1054030090300190b0f0324 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 555450683 1250 555449433 555449437
    0x10e030a0305032d0a110a020a030f030b04050a090c2106230a0e071202090114120703080d0b0117061504080f010515040605060a051309050406020a081506121803 71
    0x301005004440c41400702d100c00c1031003843c6080100001041c6000349051f0f0103580d59000900c01000c010b084030540300b24130310a511041140c400148180801c1c100030350020064441c03100c094614041d41c00c0b00040900f0780d4403070420544029240b034454034800c4c0c0c036030500420b1002d221400071100c450340f008801420660480c803c49581000144521100c4070161610065800c07003211401d9007041c9501580d00e450420341150001d0511121f840f900748003203900c899004c04140918807816001004101c00340d009010f200c494000100402c0f100240111800c400160040b83e440030700c000402c80509280101481c107002c403030f10070780c940f50381c8440309131905280c400380262030f942d108103120200340480000000c900003290140b0140741410002502031150340020020302c0030024007007000b03101d8405480000c2174422000c00ad581742909207040070b54000400d14002400c12400200003a40c0030440012003e00030f4003007420720b220900b06280c40c1101034004c3c4c208940a80f070313143e890001040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 555451933 1250 555450683 555450751
    0x109050c1204080a090509070203180d0813140103020414040b01020a21020709020406051c0603050303070c02010e03070305031602010e1017090319050708130320010e030a030503 78
    0x104044e41c3d22a4248020090b243d541c00c258030801184003403000065000043d2000742c2000507010282c00c85a40000c2d00c03906d92400010103802022400e07100240e0940041e00454117885100d8006400341c4004408030300c524058594107003052a00b0b40001d0034980d01c044841030041c01180d24032641c54445000c16001c0d044d10900554081d03450380311460b07051081d4001131059110650030107082c44000b900502401608a24005d4101d408464907081600104000d5400c1070130369503a401c00240080c4820081c007000d0380401c029000508003410000b5172002183d402030069801c00101c11120b8114401c8804113904100380c54403c128a81c0e103200701c460b01d00403982c03609060b000701001150300e000801040100f03190000c1c000c80342d88500041c1103a0003600245403441c0d0f01c03a0b09150071103090168136150f803904c512160010013088078074010b102c0001901007000d81c1a2070300000449695030a9251136804d50801b0301642c00290140c000385400400c0080d41c5012128901c1e14181600032140c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 555453183 1250 555451933 555451943
    0x618180f020d0f0c06031d151e0f060a060c02031002031008120d05060117061c12020601170102040303050403080304061107031206050a2909040606020a170901080109050c1204 77
    0x104040207000d80500c036086200f01180320588085130514000740c0c48224403000b80101c0140c02300020780d004000410395400c8086da43c0030540c1c2e402d00c1d18980b543e59004503030303150007030703407420404100b00380205488079030681c0c010018070706000c031821003001131b40018212901d050040240850035000070301400e070261040da8041605c82900c5d8040c24103441c4d000d0f141a05002d414500061482d0011040c07a40c0038401740d4810301e2072080c0140600001d43e40b0000034041554001c24030141a40c040340c0a03040301d10a800c115030700941c0c8400c41d403c0f84541d11004010404c01c2200704001280000038561050003480700042c0c00300700c5880380816a00c20b890840004a007a8600ca50300240340c0f103504c010b4001940c40118041c10000204403005404485066143c2640900c500603a404000c6400300c600103842408107a681d000701075625224a40100e480c2d0a4160b20f051040252200303907440030724140d4820002c0d91805424100600010300820307600c881c10022112024100400240254030030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 555454433 1250 555453183 555453203
    0x343080f0f060105040519110d060306090209010e07350f24010906080402040e070815011d0705161a010518040b061207180618180f020d0f 61
    0x1480c030850030b0410507009107106500c1c08003800804070044000da00842c05100340050310019045641070325000c2c4e07030440e00d299400c010010040080c60380140310068030031b403104440e50362180100902d4030b0007181c01600089a80d85070488544211500c40d00031072100b1a5000000420000c0e08801031046804c40e41d00b51080044c03102541207101010841402140511145003c10300020101c0101e882001e0803c8050404074043d9912039024240300c3c040d200403076003919902d980064842c2c1c4003d01d00b0003000c2c840000003468412030029541c074080e2080d81c140441c0c0e14214180c1d041d400c58458441400d48001d44a00054045200d00c1024801205149803c0d0303d1302080040300140f1801d002042c6000d441030200081d0403c100c42e4100d01d04594540c00507640510003031410706aa48014141c0d01401c5400944201e00d070301800903074029202c074030500c421482c40309003a074022081c40d403a68120031aa090200e078406005c400014401800c2c2c201da441951070303030000708699241c1620000f5030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 555455683 1250 555454433 555454453
    0x30203090307061403010501030207030e1806010315151b1a04020f0402270f041b0206010602061306090c0504020a1706010216290f04050343080f 64
    0x304000368001840f00380740a4070050b40d580001141c1e8081842124141a004146401010b001da9511001c190000c0d02c00010361540030840c0c00411001d551032408a45414144c018503041c0c040c0803029264500324803030f4441c441030001c94550100d00c000400860100c091800040c180032040d100145552a0a05460030a030041084421480c0640340c46540704224203184207c0c1900148403120b1400c905441e12459440404c0c3c1c140c002000d034076845450110071540b08a0782e92807904801070300f40c4c22940c0c1c9a0b21103405981e10201a03c1c0c055040706d902d45a80c0000b45540c011103205c0c0c0c03241781d1110051b0380d698080b5050340c0020914034085030040c0b05110700350450341c4d080740d40012300748014410809a442c81c00b04d19a00350140440a0030710344044e08040b82c1c8480501e51004100398025070700c980c4018604a603800a010b918481c2c051481d03441001d0110341c4d00c0c0040c441c0b9184161030310784107040d00041d0543c80c40300c1040c0c8007000e4a20000d070700c0c40240071030709000c0540c44c05003000d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 555456933 1250 555455683 555455689
    0x1030f0302060708150f0f180a05010503010902090a0509031306110d140405060c0a021c050c01030b010e091b0a1110110a3905010c111b010509090403020309 69
    0x1000a00d03610400c40c92400300544403070328540c820382c5c100c0705943c0708025944840104540c10380e0ba400341d68116860101483e00850840812403083e00c5070030b020032407640c0354000c05081ea8602d0b4000b940c891081400b00c5c00c00c80b841d81c08190880e1522007160714103104c940d001c0e0900c0e00103511100120340c15044003c5800400e10280724000c02a1074170740188180d90ba00031085020b103014090182c140031030742420076403080008464050300180111060544100010081d030300c030a81c00c03070f4203000e84450310281d940a07014080101c034058542600d0900d044083c0440303544001e081c036000c207072050f40100d010182c01d0020700c0c030340c0d089684035050030b00b1600700f45182c140c07400100a9236500e40401c1c031041b041c4803000d890b40e918161501106580a0030f80074940400e00001400c800044480b08040501c1183d41c2080c20b01d110344000e02920341031110558004a8100c8a200c150b04040910f0824900c000c4000024a1050400d00d09014200000c44da68240403501207001da48006203441c294030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 555458183 1250 555456933 555456943
    0xe0a27050607090510050d060e0f06120d0210020f090d03120b01020a33050901151e290d0b19032411070b07030b041103011a1201030f0302 61
    0x10060900343c1c00f6624000119651110f044100310420902060a95031818180c004000420031040a1800fa060080440c081d2a005a9505102c1e0044100100d00c6040c013040340d03c803c164540150000400c0d40203a240030390b100468185081904100c4003d15a03900010b96605038040e0340d070400d4112030501382000303c1d20320707a400303505540c404a0303000001407a02d040c81c0901401c900d007100444454810701980c6407000c4d181d0310303400750400d41048400b0034158400328010600308065a146903031050751403c00d000814840300c8000c030995050006030a042400d00b100c0200103910010211514521203080c0c02c01d240b0112995204c030341804041c42d00310400a1031080c440c508944c0c40c0e2640d0303107901c4012034079a40070b141d0340d0341d138074001824203090b80c000e955200120010340e90b15500381ca0800705070754080320b605001c6454101d00c100340c1e061038401c0458000808003140e266900f01461405030620340103406084013800c2008001203d02c4e158a21700079032140079500c41c031030f0705440e01900301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 555459433 1250 555458183 555458191
    0x11030a05101a030a02070c0f030503280206060424030308180601060c060504171218030a0504120c09020c030304050f0303130f110918120705070e0a270506 68
    0x2800c4048110300b1500b080070102c83c4c100e50380000042c2c0d265030351710f001d01041810380e02484035014011400014802c0100c01445003148038514480c120b400602c42406c1c4044900c3c0da4001640b0000010342141080c1c0e115407480240d050304204d02c0c02011101050700101504110700103411801800000700d00b02d070022000040c808050005907041c420020440160b428011b07060b1601e51001c1010700c508a540303032440025092003c1ea8442c00c1400e110101c080940380c00340704400c101c603d900742c0000030090354003d404554070585441d00e42010000d00714802041510b4107502c0250010b0b4080b11440101107494020028640300c2c9400c1c10400d00703022180d90700e6440e54104008000341001030a000c07a003407070b500c070080700101e1a050030003000000c0b0f214285c540044d44039060040e44070680c1201005009520101d40d1102c00c5102c104265018451000700203601c80c403000d10a00c82c1d482c840310f0b8000811000003601c08421444010300901d41541c0002003181a09081c041c020300703001180e84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 555460683 1250 555459433 555459449
    0x10306052d0a0f020a0e131a28030b0906130803010b1309060914090109020d1502070b04050c1207081b011806030204031e0b01062304080c1801060801061211030a0510 73
    0x42c014a085142504c2004680040c4211108038003075944c004c4d4009d214106d507004600382c0c05004d1710707440d00901c50602910300315003602c0f801c40040c291210001d40900b81c2c42e8000741581c2564a400d8002000307401a444140c0c01c101e01c43c00110303043c40d440c4500c1700204414540482c811701e40d01804011148081c0c90a4040e9041500c0440580c840410220344554040c42d0902300c14208c001000083c05400c20007051100208280030a1000005a49906800441750007042400c016901c40d650b0500303200314111604070004071a40a1348078260001540300604001040c01c5045007900c1c0d20655030b821440100754085424030030f02c00c40c5550400980c0340100c8220380b45625486108407814144585020450915507000ca8610031800b1003a10300c0c081c0321035079111522000482e071030740340c0c4400c2607004032401e40140400805610042c2c0c101c8540d91120986c0380d0a1840c100c0d84440800840600d00e900c4440700ca0320184514000d6108400c03511300040c0e6810400030b14801901c00307a001c180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 555461933 1250 555460683 555460691
    0x9060e06160203040f050609060705100b0406061704060507090816150309081b030906072102241e010816050102281e050303010306052d0a0f020a0e13 66
    0xf020300c9881401c1a2801141c040762121000000581c1e40d11812800400600585088403440000c940001c0104c150444050fc482916214110b13400c404500303800e00c0d00c3c550304000c140820b40c40e500407900801d4a1400490303035034a40084c1d030b01e0964840001200e04401a40821078000d01446040c50002c0c1460240302074101500d8005090281d00345c40140000d07044c4000601c86010812204e55501c0130301800d0300c500c49403c044a0011551a009038107511551691a1aa202249401d2508a40e41c08403142c0c49550301e0300e0780c1d0580c0c002d041110001c80b1802d1005207200b6400d106000b0680768000307000d03985241031b07059405202c9a01c2503065503c00360080c2510448500d0000310b07a001401411002c2c482820310000c3d4406c0b0f00e80710300e01c150200c5240d40034410044015416a03000341400d204e56202c03050b1200c0d29640805c4640305030800c0840b04d01c901340d0050b01a940003940302c90045103242c241840762040b41e001e1182c58000c03c8070b80a030700b4000d00307040035107071140611094200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 555463183 1250 555461933 555461939
    0xe0f0f060a0b0a020c040c230406080c03072303090c0d210504030f03180b0702150705150a050711031e2a0109030306080613110409060e0616020304 65
    0xe40003625030050422802c0085001150240300308030250640c00c0c024028008020000d00242c022048000502c80b081c460348509107050041c0300c120703811110740360b585003e01e0351411200c030307801d80018000c681008407a81080d913071038001040c1e8824021419920179503070f0400c81800c61400717201078021409040454410750100342d4000a031031800346080c0200039102c00e80380044800b0310a64000420024903211040145035020100a04640000301c1e500c0003141c4600c1b002140d4001e020b002580540b401c210303150031034502006030807664440c90444580300d004401c030100704034049034044d03041c2d07540c0d504010030943e004650395440003003480914034110480803890704004045880d0b015403540061401c111113108114904406080c581c29560451000c8205000c0c1c110703d001039000038103240c8081403114002c503070750b8083d02c100c0e00110308140f101d582d4a400600d0440b803690384995100d04060120b001c6019002d9900842005010640341c502d41c2d0001e0b00c61318400400455106001c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 555464433 1250 555463183 555463189
    0x120e04061d04081602120102190801030f20040509010e1002121f05190e0709470405030f010c090e1003060f050901060603020306010203220e010e0f0f06 67
    0x5411603000102c2d00d40d14403208061350401c984541009404c604102d001a262030f1040d401341030052000485507001d010f440b81e0882e5100c0c400e0100bd80a0103020080030006445030007091030245418003d90320040414000070112842114a40e40e2651a4210007004100500c10721154403919a011030404601b4121500c054100401c40095281d8201c40c1d41441078039084102c00500300208500e414005604180541505a104500e104a510804581018040ca4251056900c070044038100c1c0c060700750891001000e04001c0340d88a0003811249110340c810b060207407010040c508041ca079140d291806051404500c2c01d07640501d41d14203940b40241540c020b5016044488103044e004d250303250070b4814500b802c001e80c0020038240c0b81844158880302c00380c200b640705101c184020084c0740d584100982c03e9200890340750340160001c02039040e040c00c041d4a0031216540d42c081c5d048200d0348840f250101f003070302a00305140c1c4d20305410070000b0304200c0640c060340c090068990000141000408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 555465683 1250 555464433 555464489
    0x1060516020409020f10021606020307120e0a080708151b12041406070905180c0a0c061509060e010b07110105090126012c180a120e0406 60
    0x2441540c841e09140b09642c0c5e100031070131245d04005c00d030000020316a90065900c0c3c1c0017001c56944c900d20b1040008030103002005584590750007044040100c07660030803c44600009401e0664400e0b030015020900c40f10810024019140b42c0006206000941401140b6000010000d50b56440b840303280c0b02d618032010050300c0768000c003250018030a445521f804040788015a50001c01c51048c04108424545c1c070520003070841d081a5580fa43e40c0c242300340302c030f42e004408031a074256041040014400309841043c0ca015424040d1000241c094001031031800e010503560b1018811580300c140c241304000031007250a0060800384e0a982c50000960f540301549410341d56030506014001c19840381c2c3c3d90050303003811200c1440d40314000f800181010180360704023080c059220320354030750445419940c0d000404000344081c0300101c55100d59070541980005019500101014007614000c0320019209602c0d450030001207455103a4505404800d0000b00c0d00d60b640305e80c425070f05910300c094410b181c1c0b101d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 555466933 1250 555465683 555465727
    0x50f0d1d071a0c15072d080106030c08011509050301090b0901063212010e07080c04020c0c15070b010803031e01030308060108090c060c1b0109150f2114010605 70
    0x8160303480d645001040d0b425a6120a100205c0306c50420401d1040031056441842003042c0d031241001c990300c54004508503054a8610800729140c0b10040c00709001d90440903c80b50743c03a00d03101c0d25081e10352003ca42520044101158503000000900c0b403180401c0c0203100161150b41070700b800030008102c0241c54072541e81410201c18101c000c01c489907031640f00e030030013110420030001e0201e404241180c50b500c0c9044c0c031507011140501c20580f1002d03d080d00072100042c600364000c00009001ca420440075070361200910003013040400821000500220000d0300030701d03561019549a10700100920701d480c03660541c0f41400d80100005100007908582c04580150081c078111509586080c0304924100049210075030041d404508042807000c0012030500c1503540c2080804002c0b803000054885000b00c1c000d600424145040300d080380c5105d600300d0700759110706140003040103010301e89004001c0582c031060b0180c5a1992100c0420b025802c1810703004125614143c1d11b405410422a402110202c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 555468183 1250 555466933 555466963
    0xf060912030718030f050c0a1203080c0702040c18080a12030b0a1a040315200d09020d1101032a030e01150b09120a03050f0d1d071a0c 59
    0x7001080010b403180105210b48600c0c08920307100307580c682c00d2180c110751485100321000e104807450741440d810610301d0302c4222088002c4d180700c3d0703c020760740c1902e44180081c94215550018440d01000d41d48600039040e40c1d100c07517160507040700c01d90172080c442004903800000e40c5500c221500400103141c2003806a90404618000540740f189400040103049680d0186c2682220700940c1c400d03110705c540062040342e116012078040f0b40203041c80300d020b545084803500030411140d406a015680c080300200b1b00d4801c04580014a8482a40090006400c040054402081ea25801007095030103100340301d24010030014001e00700c4441c000e500200385034240c00a04040d140c3c9910141503109401607916205580249070740651155101c501c00d4221442240c0301d102c08400c000a00740c070108010841130380580d6170707916110349007810091540c85030310b14038103940d03031341c144148002a40940000821092000b030540c2c20302e88501000c0c0c40da03203d28054159181000800c0d5412030002d09003002e81045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 555469433 1250 555468183 555468187
    0x130b01080601211e0606180e0414030c0a030e030604050604021002010e030301090207050115120602030c09030f0c01081501080f0705040509070c0201081323010e010c0309050f060912 80
    0x2090b510401c804040302c2c880610f50803d003589003001d510b10480d0f140c040000104100c02a91120116102580c008051129018100081c41a403989003095030b4068080e401d0342e880d10b86104005031a540c4960550710003070300b00c0c50001c0c08040e070000b80b0b4104820114010019400c0907122980ca501c40580f0082c0700d16035103c129001d0758000e4220f40760300c4440c0c03410741381c80c1d60755802810302950101030704480c2540307040c2e400c0802602142500c0d003600d02202c075008200616944440081d4006801ca4000344002c1c000c20380c0c1c0c3d940800c140701c92010034201400b0070200200001d8062a4040c140714a460f07807031840303407500e039038002c0c91036030b020035441e5070382e6440d442d688000d07a201c0c880c0e500056088400f6508100e0000d8025480b00041407003a61190801d540340d00030003070b043d5008500200042c80c050951021004180c10040c9100380f80c2c000013811007584100c06086407444403010011030b407110842d60038000b05020440c912004040504043d103000400c194884000e40881a01a440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 555470683 1250 555469433 555469457
    0x50907030905161e0e0903031302220c1106060616020a0905010b120f0105010503010b180415051c0b070807110a0b090f07031104091109040b0402130b01080601 70
    0x402000c429401c001c8950710905481d1020180442142441300d61110b80d1a4400594800340201561040407003102550460316084031319049400799070000e0380d0140d00000d030410200398400c1c0610001c0c0d008100025401c40a090203020007900f009189856000241042036070348808003282c081254044010715054050b100240300c8a0f81500002c4640e440c00300082151500f140080c10031003c000c0e91101c19a0740e030b400c4480088001d0141600050003840104000f610040c0501310b6601010141920b2001c3e410115007103441c0750000d6808159400d0341000079041c085046010710000720441000144a42c03941c400e00e03c40542030404000031200000c9102d4825048108816503e0301941e03c032000c24240b02d0f14800081c4d920040501400020720010200050003400b01d0713038400780411011900c0d008000c01002c81240c10758810148903510084d60b5100708031503201358030407a1502d401e800c0600501560000217042c5442c00380ca09103072003200d685c0082d04250302c000c0910344609200c2c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 555471933 1250 555470683 555470693
    0xa05040801020f040e09030c12071a070f1106060616050703150c0801050913080a02191406130c1802071a22173007090509010509070309 60
    0x20855004159651012440c0100200034400801c221881111042e0311500d4010a02c0c2d10b03445032034400461580005250f81141c0c40d05e00160810b64090103c0c071030018002e092503c0e81000072114180080c2820105280c4184c01c12030385251654448014420b9180c1040410b050388512980215500090444c0070200142001182c000e5a44100f0403007000c00d04681c500c02809a440c81c80000c01e80e40000030400c0c4c18060100c43c03044012003059802c100f103c3e2994049507012183d85070440c0218040320300c400d089034110980e100e10909501100c070603110740c2300e0f017440d5001d4410b0800c40d290005101c04985000c2d0305000340c90700030700c00c3d9000c02d8001c107000000b8401c0d49002858021407036035400724010185030300742c414403102030b9008a4041d40324903030309c408010300d10060956454481c8041c4000c0004003801d40ca0705180303042110203c10f015040452140000840c1c0c42d03120403c20410079581c8003000b03800901056421000300e5043c54002040030600814a80c109955407443c0c009201c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 555473183 1250 555471933 555471937
    0x101112181201022104230607030c02010e12031006210e011418010f0b0607030e04061e0303120501151101060b0c16170a021207051e03160303050d020a05 67
    0x680448214803000c00c044d03c5a0780a03601102c0070b54900d4880701503085a4026500d0301d9005c039111401402641c2c0c2d0f210000d0700103100482d20101150350342ca403002207010081011103110b0407071701c01403078031f038540340f24605924080c0d0340100e002c000c0c1041c0200840c403085401d02003010207044000c240120b01c148031a004100d100c0400d07000b00b2a0a00703004030144001290304443d545071000b800310f1074130480a901a66008981503401410070404034000c01c0c441c1c504071080b0f01c0c0c000c00c00326290b907450b07504c042d0350300d0f281c0d4400904210081c000c00c00c054001ca5076030240c0074004e0040c045580b40400442041038810584824413030350722038100c040345c0c0c00e506c04c9000c4c040341d14003c0d03241e107190b0f645260344d03400c941824102325500d803102040c64038405e943c83c41c0200b90b21004140060300c5d0340c00d22a000354150030602c8a0b02c280c01020482e991980c00b1f0001081024401940f655504010145000710142900748000038404080c404640d11004559648421450141c0d17194001d481c119214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 555474433 1250 555473183 555473197
    0x151203041a0a020f0106060309120806010203040902090a0314061905010602100527010b130605090c0a09030b090109060605061309020310030807060902030c0603090c09041110111218120102 83
    0x217940303000800700c0c42d1a01a0310150340d01e80503005210040c2c4a4490554200005444ca5405030340144020080d09410381c00400010401801500d84c0075900d55400031200480d03aa40142601304d202000103a056018842a00d044841c8052085501d40703040030b5103801c1440c10503001ea5480700c000818800041c042c21071802300014001e0f2405040c81b180c10700074018801514418180d01c40001640c403ca03000c0c807015110028400d080c7d0392204000c010f0282d10112419084c01341280c4004040ba21940006200e817451100100e58000540340c403000715a50f44e00a20310a01080c840c085880d0949102e800036211030b04001642c07602d5004441000d807030703264402881c01e03000061200400c0619042000120710990840d0000c040715000c005140c0022901e012860780000b100b8072407840d03e1642c0640042c020301c2c458180001042c00b181105d240248041c002c20395a000b10032030b00104200b851440c802e921100c03824031041c0e1214400445c01031030207034881e1450040140c071140c801e6040b121030f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 555475683 1250 555474433 555474463
    0xf04030512100305010c020f1b01090b031f06110d0804061d030c060a06030f0605060a030602040b0a022a0904020303090307061707020703080a1b060203151203041a0a02 74
    0x109152600244682c08201c0c0000c0300c42c4d5091a4800b60b1403800001c1c1c0700081c0584101528941040c0c2c10301d061003031000322010381080240c0c107001800c407066070010b500500e0043c0b20b80d0b00b0b610030300429003240e0030180e02c903604001d2207000f502c018001c0420300321560000b0307283c2000b00e42c550342030402c0904102c00507101101c01480f8a8500243c00100802c2c020f65400300380c4203103546481035142207601c284000390041c080684643e0002e1016480103a1045d802041c0802c2a51240c9518040703800a4020201311480014000d443c0c94041011591420309140801034403295800e4405200e05000b240d54085c002c500080b80c110743d001d106032041c943c0017400f11820140d841c0c500902d4020a00b45103011386c40e1030707008503542c0751000c2102001d40e50010300d468031b0a0200c0b1400c039503100c4110311060864280c8100040000d81500041d40640203140041041c14682070400c800842c440300e0500303840d03108110411030011041b1200122030310005c1d02c0c50b10369901040980c200611100d01d020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 555476933 1250 555475683 555475717
    0x302130302030304060e130501050d15020d02180f03070302060d0c03020702090c0406180b180103090212010e07120507030b07020f0f010c1e0206010e0705160606060e0d08030f040305 80
    0x168603600c030014218841c42107c224a0442c038021610707040311400c1c0074030340e00802e00040310306c046905c020b812081c05294040051034084042004400c0343c00c415044218040c443d02c0d0720b122413409031070701003200800314041c186007482c2d030f80000e0542c4298800d0010180c0c07506000202580a54150340140e038001c0c00100c9a8500b094080385c8980c01313801000080354450704001c403440040f40072441917481e040225498403008412603005c07000540615030425486400810044c6c440c01c00448200340c001e40042024481c9031401400c1c88001c0c0c221030802e401c0d2401d01c81c0402c00c0024440101c0340c0040c4030840e00d440c0d2500803420905112142e1115101c0d02c10480186c010550000c82d01c5030351981c8600c19440d0101c400c0d851070040003048070050340120014032660804514441d081030113400d05502e0120003690400941103460025920642e81d2182005130300d421158403800000300310384c41201c01c0030540d04c28845000203004040e40355141c200003020180a0412641281ea40002400e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 555478183 1250 555476933 555476939
    0x310306020f040509090318131d15150102070b0d1d060a050c0f09010f09120819020a0302070b03040f061b0e0105041415070c060207030c0f0b0a0302130302030304 71
    0x44507580b091281501030301010700051403401c804400d58078110000344040805d514035204020307202c1000c0d50105d840382c2c1d507441452081070320070500e0813116030400091304038251250303500c03210200b0040c00c1d0341c866250100501d880e13a80c0801c02c803007075a002c807003401e8480c140340c0c8155000300031a400d03064003902003000d075407180b500c0083c0e89403040722460018010365a541e901d40700d881c000d1884c039280c0381000740018491903008040c0161341c09600e20704000c1c0c1c6035072a80002c4000d5440030b010341c5e040b980012300e08424100c0d01da1954000354540020036a040031560001d40e2502c0b50b10ce00310141e0700200100e020001c1a48003512420340104080c0100307040c82e200b1203501e40702a141500400e80c2c002c005c0300c0303a5001300d050b241101d440c400c1c07d2440c0c3d5010000e00c60103c0d1418002c0c1d50884080140c0c000054104141d200501170715402440024210b240030000e94400c0d82205005005d0030008210010018046580361070007850050307100c0b5080c1c0f6003000501c2c3c41350802541400040740c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 555479433 1250 555478183 555478207
    0x803070c080601091104050607060e060c0904140601021515030a1505062e020312100303090902030f16020f0a081c0614041d060705030a0507030231030602 68
    0x5491844081e103007030341d903a0190002145c04a90305009000000c0c0000c12107480d01c41d02811500e4007401022980c038924510760f41c20120100c0707024080c05800319000714182081c0c4690603281444e04001e40550428030000703591550001100c400e804801c10004601e94410140f510460001600300c40500c0c07450b141025090015904005c1040e1514001410f10302d070030000c100048040d030404c580e4400d100d028106c58a040c41e0854006d42c40100109441045900741842c4643c41c2343c007410340c4441c11850010805056540604c038440e0060091103044039070044a0381d00004081040c02c07420131600c00030b070304007166592821258001c96440000f405000d0004116075900d9004880b40c03403170030000b20421200540201880c01c7c05c9032140c1d0701141001d40c400c0d071141c82c2040360894480c5074407178103c0c07402c1400c13201d81c00011408000d00041040c1d501035290002d810741010b50801d2490800400d181c3e110040e1b0350b5505130807400750300c440444402d151000e10340100b410343d075030800340000b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 555480683 1250 555479433 555479453
    0x50606072910090b030606010e1201020f0301030f02030106060809030901081003060905012406020a120e1c0b070c110f040e1510050603090a0312110304050d1e091e080307 75
    0x150f05100c0341803900c0380b800752a01084c43d921644d0161110382400410500b4000003840100742105259400c10480c0364640c483c4001e1750080d813084213103e43c9141c0b075105260940789a41d010b40305011115051000b5841c01205551001c1401c2c6010100d9a50b0780220041c284650b500180c451880c2510030414460190409030040001030208030001100c0c807003940d00800f42c2e102d0140145c002c80c000301e00081d0f8000d68100030385214501848140c15290015200302150700400c0380300080000e13844104400385404d154444e15504080c4102304650b11040c19514419a1003440b40c0880e106104840d40c030340c2d1005010200100403150420807a402c1c1e400c0a48003078900b41183c9522441c0062107242c41c0c0304403031103400402d01034804000c5a0791305440f1000922291103149488140640090450710b0241d4070441c010002489001e02c0b4800c090075041c0c80d0500305e02e02541c18400383d04001d8010002400b00c0d5201105003044940340c03c0e50f0511400150001e40550100068503814000c1d5440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 555481933 1250 555480683 555480689
    0x5041208030a0b01020705060a050c01020712020d020709060e0609130b07170f040809011803080a210b0918100e0309120705090103030c14061801060504050606072910 73
    0x400440341194010780e07442c0c0007032103408e902000800581690307a1281000d00140e0903168000742c24100036658502007241010301e0391005910950340303a00141c0d410400c86004003001001080514103191204120240082459001700903903008911001c42e0810342514160700610800958100504010720b05012054401812202c02020039060050740074564065503001100a14180300d1000643d203240b001440c4441280910400001203951180104003005c015600c3d0081e06114040c8102c60121000c0e000f0303a09442c2914406103507c0e4204565000203150190600b09030b21100752a00c0c29000581c205400390038001700103035288000000d003030303000720031034400c04d2002c8a500368030b549115503c51a0f030301010000041011900031503901c0c54040c064410b01580004c0d0902c02d518020050702e0001030100d2210040304074100a01c43d4402901c4d0441e0140200d0510800041c400d004058000e080c0000d164204a503801008001100c210307050300c0141082e01d4105d030342542640c0984 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 555483183 1250 555481933 555481951
    0x1508010605090c1228050f010b09010206150d02031b010806010c031704031205091006080d0804020f06090909010906060e07171009060b04090c050f0301150504120803 73
    0x148040740a14002d82c0b0244102c0f42c9900460416542540790080354001600d542c4110404050102e1080354011601545000c04440030903c0e04140300c81c004007260590002c403a0703110902c055070003a039002c83e542c4e80049540d12100c0003001000c0003e800041000d000940c5440744984c45400c0c041140003d05a2800c01d8842c0c50a5941d600c0041d1810036540c1e1004000888480841000c0e007440840320b900300380285420742d00c5441403501001210740940e4178210681c4003084c00814002140105809401e0041c007401c000c0d40c07400300203442c104010b07000030700c641c8914001034255141e4000761008501d00500300e1200e400c0c04068540205600740f401c0c1ca055050010100b4081d946500740c80c02820705981d00040c03490380c40c5c400410f045024150a042c0320350120700065118090040f5009030082e50038050703880745010004021121008010b8040c0b203030502000640712100c0003074078111102d060408104c00c01120003200c481c815900500c01520302c0b400301005011408026520459000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 555484433 1250 555483183 555483191
    0x40b1012060b131802120103051e030414040e010b040501030b0f0a050c0711031e0d0801080601080a080a110106090e0d080c0316030b18041209050d0201031e150801 72
    0xa40e0300ba025500c101d40c0001019034002e0300c10005414031482611444080d440b0050600c0414028101030300e00c2a80191441e80c411150b9151000c40902200d0700d00d0000801186450314200c1060410003030b01d800c141c8150780c0e030801200f90300403c2d00100c1c0c8400700104208859a1030340b8101d48041c05c1591949030035854880019002d0032684220f5001e5000808514101b02080d40d40c100294400d80c00075400d030090440c220600300150b10a4010000f185000e41807045d1101401032040c0c10580c4099901c0e408113004100381040899141203482d000358a860b0307a0254400d040d51103090fa03440c03d020390361910b800007500c201c656100380513456105094440074805460b08681032482921078403450401000881d400382003100c2654682c009070308012500c05400030008007040c2d000c02c84042021460004c1004105407548003441d1b81c6001d0070840d0035070707040801148924082107802410305680b50020b0341b010312502910041060202c400344401034074002e90b0480075034507200703800c003640c24 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 555485683 1250 555484433 555484439
    0x309080714030c0d1d06091906081b03100b0c0a080c01020a0906020a0203150a0e0609160f060203040302040203040819020a151103060402030a0207020909151b18040b101206 76
    0x1c1450801c0c08007056070400000400c41c0d50410035070394450901140d04c40040e02c0349803504400d0044850049c400d584400344a494000d40c0550072980c4040d02e4000c0301c40410030420b1610600d4101070a88044d51503143c0c440f00e0044c0d40a02e032a001ca100541406000304142d24a03034415001031a280a941d902e842c180307903403503c003641c0c0c2d8040c110f0025499080500b007544402c481c100c0a40e882583d94401083c04007040030014100350054601c888543c00058981644000c10040c0c9002031428004090080d07150860003907e0b80528003000784500c0d000404141404120419907460310401c10341d46240300d00b1181d000e5034814080c2c4084494003c1e903c5001d82d2510140700ea00040f00c07040080c149560780d241c08100080d4801440150416070030b001c500c1c05601d540650b103100c1c80d46c40008003503100f9400c4082c03120000041203516900e802d1002120803003614030a880e15248414100700360302c3c99040001d0701511099580c1608105010034802c00c8c117a02c2030000001440d40c402c00c01806032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 555486933 1250 555485683 555485687
    0x70b0702070f2303030409020f04090e03040501020601090207020a0e27010506010507080c1006030b0f0c0a122a0504090e0d020703030807050f03040b072d0309080714030c0d 76
    0x811842079800703c0784010440540303081010442500460020144d0340f0303040e142c803183d50072a04035511910203483c1c042414080001548110525000003034019810a850940000e564410500074160513035004504d01d0215203030500c03d4405000b00c001040540e2410710380c80d00e0407400381d002c01000141500d072030070305d00601823252502500c03040e915507291141e5030701c940c1401ea1208001e0802d81c8030300c02100701c800304944550b038041c1d4400c80b6209801d0034003160b04032072010040c2000ca1600703c00c0002d1303802c880c1c2010012801c0181130201048032644042400c4207401c221307814207511a0403400c50011a98440010019208070340f00400940510713088003503940612506040150f40004402c0c0003182c0140d0743d4692040c1c2c0d41c43d00d1841c0900c142c0110280341c100381c80032a40070400e01c0a001040750040c0805c061b42d5a002c101d401c3c1a402c0510810480f21501500b005041e513910040c000c1c0402d6104443c8216000031042000c288900341c0f99a5a074480480c07284103028000013600d8181c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 555488183 1250 555486933 555486959
    0x12150603240b030c210f010903120605030606040f0e060f07020d09050612040c090e07050f180a0c02070b0708040306060501090f060f0302040924050a0302090a0c0212070b070207 78
    0x10140040020b04140700510099801460800321440783d81460080300c5e820811001904103d030000209400c00185000303022070a54200440d629418110103000c0f94800040003039100364210703000300365801c0b1203101c80014250300380282a42e004a1040126070030b082e107130345070150323800d9401c0390520a6444e00c2144c450400d0302505522410401482452071581c60250790030038040d011300110b03a40d90705504001ca40b00858000d4658110b9041080300d40f40c1804e11408000301a5000c0c81a4046284c2a50120000030030250400d41d071140c0a08005200b00413600c0a003180c00f4083e0341e64062801c0601558000f031204640c0d8504111011842d94810150102100d000450850465051090555020b250906801c2c1019030070702c000a4442e4450281c595601550b10050122150040503007400701c003190002c0e40980b500180400058403400c0150741d00444000000030303110b604400881c14002e240d000d0141981003c00c848050280440300603004c1c0046800312054250380702340148643e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 555489433 1250 555488183 555488201
    0x41a100302091b12040c051207050a060518040e031908040b090a0530210c0903030904020d14310f031b150b0a0f08071215060324 57
    0x10f000700384014540e500c81180c90b00d0708944030b10003041c1d24075214000701d040c0410303c5000c2500b980c802c800800c4242010714444c0701400c0b003490501c1c84c08500e81c1d00d0719003002107200070501860351400740440400042c402e94904841903800b204603100080c5c8000c00544080d80c081c4d80c06e4908001007400900b00181124429500078090b1401e074021a44600190500c09402244503c40106042c968405c3c1001000b070544100980c1c0e0101c0d04c00c00c00ca90903c01e00401400c032519040100c18103594000041d10150101294096a264450000140070348034002c00010401d0007041804070032070711600301070206060305010b55901000c0600d4903240022160020300104070200c0400003283c0304030306040e945009410105140c10030b1759100e8611214811002c0c080759681c0802c45914034081444000819046400c0c4c0c10050078426180d03200c840621480044403007160040040040410b030a0160014000c1c00308622079581c10982c0580132440406200c0310120b03000141c4001c001d100c0d020b21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 555490683 1250 555489433 555489481
    0xa02071205061f0510110f0703050c041a0901080703150b150304140609060601030c180b0a02070914060f010315170f1e060709060e09041a10030209 65
    0x360f1100c8048085240711031074903010081c600c182c042081c1e00c940b01080c02c0880320b030359400c400d00d02440c00c03a818032581c01201e11660b041800204086000000c460f4102c85080b2000a032070411502e04000c0030120224454200c0c807a00000100300d0b8012420740100c2c1d0140030031010341340300c0200782030441d00c440c19815400b00d41c19130310a0381c0608000103075510034810060585401001c080c05481d1500c1124105280e5000004020b05d070759150040d407007600a6821724070a480f040c800c1d070700885a064012500301c00d1020541500f150300c200402ca0040881d43c0013000502d40d0ba0901c00d12a1400b290360500841c1c400d0300303045440d4802d200d034082c40c80c0c801c10404070450600083e50a900403000d1001090f1148099210750726a05000c02034503070b07010501e0907a074074480c01c400d18200000145000d0502032822010085950014001307030b1483c1341240c0c204420703a110b14012107100007000c0c00d07503400c0300318101300650f01000b001d95801360780c000c42d4100d01d155a51013086489982c006d40b1420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 555491933 1250 555490683 555490693
    0x4140106050d021804051f080c061206030a080d0e070b2812110d0f23040312020a020c0102070f05033f180f010f0528050a02071205 58
    0xb408200700d0b806450301815085220304454100c40029050b40d6007900e4520141d00995070f40480002810504002403180001601000b00030300d0008029028009000030080a0140003403079654052002c0e243d1268051201e68982e6500c40c4e00c040180140308120302c5612952001185400398101581c2d0b14801113807942e041c20203402c208107078141c1000c40b000d09100344004c218040c8a00c0e802105500f500c00030040c3d840b034040240c408240d54541d140354075510b10344904d403841c81c61105000e041c0070305640403a28280e2160710302211102000c2100124491002c0b400206496000c11010b904290036800c4661407601e454041c0070007440f0b8414242d01d40d112000760507890a1507504103086004070f03c0a49003040e021201d140c80a1203945510407103210008407081e0006101400e42056201902c050304010401c00000c1d152a07241d000b040c0c240000410748158a406044081c8124000d1a4050f0894910160058195000310081c0000f60054240209207130400041ca00c80382504040204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 555493183 1250 555491933 555491947
    0x30201150f180b06270a060c02060c0a02220e070b030a0e03041707030210090503150c090a080105070e03010207050c010513090e0c1c05121602030a0c050414010605 72
    0x40c1200d42c08a88102899115100d030364882e80d40b071015210022840007000d000c4c40c10400045101000d03040324911800e4810780c00d01143d41d125a5601640e6815140a907462403a0032045140c90f400c9000254400658680901d1b403808440c0c102c0140700c0c02d0072080c8582864080c021343c964009004444800009200092081c020b83d000b00410340201e000b40d0349420307103034402c181d82100b101c03c2c03501b810342c8025410070450800c07001803101d003201441c0c00380c3d2030307810480040d45813109403050b01d820844040200d100644050101c0da05841c00402010f200c590b50400c2c0c41c00b0700340846030b0102040715503c0700c0d140c03400c040c02122143c0707074040090411248178a00540c1c40d90811400d607000003541e145c3c0032034255564404da81c84080000024544140b0180401101d4992039800391100c01b100411400060000a98000e0fa480110702640d122030988062a100500b407000107035051246110300024000d1554000d41910003d54040c0100359500d6840c101c412028411180082e50070003000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 555494433 1250 555493183 555493199
    0x1c0b041b0302130506041e1a0a08040c0938130c0e062217031e090a03060902030d020a0b0c03070302040b0325020106050604030201030905031b0a030201150f 69
    0x3c0a080881d900103040c02a124004107000c2d4005030441f810507141c10000000704540049400020801003030140c8100007107030386440050040d01400402e110415012904019440c000840982026a0b00300b18920034807a080e41c0a9184d00c1641c0240c21b17000550b440c68241055002c8030326800a00740e0b02288080191005c014801d04034908200b005800c0c06480a030b42d22401000b402004040d01c400d0450f4881c28643c1782c00b003580c442058030140f603004880c0000e011003a01e41d0000400d2052004034142c1040d15641d120351100c041d07000301c010710040208003066010280ca00d0007541100c0e80005044001c1e40d0b500c00003a806000d040d5044002030880480300021a40a045441c000d401c0030740e20b4000702442d41041e5681249615007864481844503900b201c11080e140b140700130300503a454600480c0d00f0b4820703800302074101901e4186c3c000600004208483c112062074607a088405200c40c040740c0c50704503040c001c6005500303150300d49520102150b0910155204034852402a80ca000c0701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 555495683 1250 555494433 555494437
    0x5010905220b040509071e06090303080a0b040f2f0405060304030309050312090c090f0a0b1903121403010303020d030504030c020904080a020708011103042301021c0b041b0302 77
    0x101e418581d031114072480b0552140c0c05024041c614503030080c10310740d040c90120550008140380301e85c6210100c0c41c04004542d807100356501120340600304101c840d1100b035030b801c01a00c41c8040403a04182820403582c920300007580300c200b2070b400f0092004401c42d03012544019a00210308ac0b05018103042c0024411032600c4801150003500ca0305001445091a94a803030558104070b0302200c0bc010b000301004a00c4400340100c05400c0780c201d801c00c0300d03482c0c405049a005040170b042141c5042d40c0e01d0100341980c444800c00a2007030413140005d04800e035030b03280c220016070b40390040c5030004640c6a85050304010042c15a03060302c0d030540180505402000c0100e008000c0204103804100d484140400580c460810035800340d80071351070322541c0c1c2c0b01302c10010746007441d9944580d460780c0c980850907112061060549421a40c400c00d01c00140548104080301c00507442447c44180d440003d16451800038510f06201013034101ea0180b012076203d2080100301c070030884980041440c0c004070f10300c0c40b84c42f0b0342c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 555496933 1250 555495683 555495739
    0xb102303090c04230a0b1e100e060904061716030f0201030c20010e06220807050a170d0f0b0102030d11040b07151503020102211603020a0b0105010905 66
    0x4202c4240e513124a8255002c1070742520381c02c180f507641e490684500c0c01c0c0305482c00d40342da00042154440c4000d41b404141411130310300d810002c21034412001100c60740c03014105d5080b544006c0040c001d160f212261007103406ca40700e20b189071501c50040c075a85107810030b1074103400f2a900b1126506802410b90010340182451180c10410410b400e80d00e00170022880c4040b40f801110f0300000241c241c0f040000c4c03407501002510038500c1180c21510400500c49018240708041d40c0895a15250700b031703d1500515200c0c00b810010030381c500301070840384802da000b00500184007060b07000380a10031001210740e08460264070000e0068000f0082201601c01c00e4001e030701c0410881d84114a099074400c802410b6400800044460b4902400440c80d409498069014003101c447c008030880380c69036002035510000c000e141c02d015490a075151140c0f00c1400c0989040c195201ca485c050340d2051302c0c009440d5404030030100c49031200c0400110f003651207070102c20203448014000b8a220712031800d003030308060441e007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 555498183 1250 555496933 555496961
    0xc03020607080c130e0604050c18060d020708211308040e13020909150f060a061b0c0f0e0f0106021207020402192c0102060f09010b102303090c04 64
    0x100c4414141000200c13480107120100800c88582081002c21090300e10140c0300980c4a0010301c21030350755941e4a2407100c041d00c804c544180e40e0340ca8072103008010b401070840c044d10250000c10103c3e0360f091450f4075000d0103904102540e080c1d80d100000ba54182100c0d031409130090b0800d0001380030000401680ba038014201425103e00c040032070b800940c80010448208219406c6501680e041e2010f860901e50018021001d03550707140f8003a004200001c2c035a00c1340c00100070305074a00b255051101404444074582107540404a69103516042c60200ca9901c01e0321031580749030000170000b003003040156040c2d603815409070416444d20544d0002030342101c1e40030382e8002ea08114250302c14a185c0c0e403a40030a0a1f81d100c0308041050680b11411a400014903000307000720802912029a0307010a545a21107480074006005881d040700040c0146000e01c01c0780c4e0849481044144590780224a0890000035202c81c0802c80009680c1c08040b800705541c50a80c40e44449511f59061802c2c1c0c110101e140255 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 555499433 1250 555498183 555498187
    0xf02152205011a0a050409050309010f050403050a030503010518040201090e09032106100801140904060e0316050607031103010308070812040c05180402060919260606010c03020607080c 81
    0x103032900e5003141e420310143e454005a541c500881030410400e0400148000c650400901c15186c5403a07882c0c1c4550906c841c10001300301041e0710664050710503038000d0368024007150460303581032401504a5000307024442c03140202040020754881111000b511455041e5141d9561601d0310050400301d001c090000d50031404240205100e140010f010001403d4406040b801c0d54240403050000e0720a0b503c11450400446078014440c2155041d050520084259028601c5555070b05214000b80540b00c0099aa400001802c0e42007040e4040e03030b40c000c0d902a509407101d945410382e056003281e5000c0f81000407603009000400214250740d02400b4064000d26980b890003c1c04110b21000c440d040b20121501c001a1b00140034509120101c40c45a0030480e010740182c0c10141c0000d80c4502039401020300ca00815107100f05010003814141d001488007072201c100380030f00d10400701c45a03e04da03044e0031403901c240b0002a0140d84070b039404980440d0142c01500f51500c0e03210041704d03c2c410040810b0020042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 555500683 1250 555499433 555499501
    0x230f0f190503120a0f1404020a050301110a0f0909020c242a0c1207060e030a050f090409060623030127050705090c03010303030518030912100f0504030f0215 69
    0x628058030840c101211b003000400d00d402e104001c42d00f05d081d04268020381c90510110b488843d89000c5488920305820401d090100b50701013102c0210241d00301c2920180040342d00018a00b00250091101c008001c039103056101c00c003140501d40300102c03482c2e40d40303440394521212074607100e089030381d07005403401c1600d4a465007905403a882e0161085000c48801c8001038148207100c42e6204280c546446840514640000c10400034210300030000c5058500100003103030340c0d09940340d038850704940740c0c042424000326a56007524202d11803018909126441650308011091806100d1303004119046043c030141c80001080304085414800c404403080d100b140800302d1190380b0404440d114507a2080500c2d074039815454000c00343c40f4080d00c00c0e1401001020341c209040e4002c410748100d014265040d05903074100006080c5800500c141400b00350b4944040703040e00040d543c000a05c164040e8440b40a02445c0303840480c0d4038490250051080481100401d00040e0710300500c00c099010700c0304206818003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 555501933 1250 555500683 555500711
    0x20a0603022a070302010f05040302150a110f2515050c070b0301120c081605040f1d0102040302030607170f04021f020a020a080d050304230f0f190503120a 68
    0x44001801c0650f50b100351010411503070300503c174248014051804a00303140c60343e4041031140121040d092007409010039613344041c4900c1c000c4c016280e015040390308010031540c0160b102c41d042d5288041900316000070344107078480480f40104507002000c07501d200000600b4210351940044900b08554051514000760048100f4050b501030180c040000400011a10703207a01c1d410b69075030081e0303001c1d0441d0061740c02c058441090301c4201c0f0801e841c04542e2494031301421000700030007401500c1c83c29515807448000318055001d071054a10039400c442c01501e403200160342401101c188200303d02c0004002a80c0e4078a0706100d035030454805460034510320303c000c40e40c41d8501500c1460b0001a88070380030050039032034005602c900a04e0060b01400e5580d40e540001407207484002d00250040005d05500940d031511810f03040300c08101da0301981c401e049584001e41d15038450424041191103101e103001c69500d05c843c286448180c1c031500540c40c0c0880c40c00c80c0c2616000c01454801c070140d8503a00904010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 555503183 1250 555501933 555501997
    0x20d0b04031d10021b040f061d09010608060c0c01020d0204030b0a06090b0310090f0807080a0216050d02100201060b0f0d06090506030601030f1b0f05030118020a060302 74
    0x98800c0d02c0316031440075aa0300440c40d020b080015103105010040e840160b41c0c0d00800e44c00d000b4101140303041d032400750b6100070401600b80000c0705103031145131800020b00d01303440300b035070250a203842403154440391107100354513080c0d42c021301a400c540d400c030802240d02c00b1191401001100004400941032032405884031040360000e0340140c4002d1540e000308104c1c0e00c1e143c030507000680300408007001000e8424010070398501212400780710a640c1d5800200c28480001641c901c07665005122550301d00080c90410055008456034401502c641105c0c0d48005c00c2c009881001e0f02d50240060360075041640030010f01204c0343c0300c00340555503580c0c0082140c2980e8070041100d04064060165214003000340d480482d00ca6500c0100000d1605c42030101564003c0380c10360469810a412810705940ca0601101190741050721a5604030341040014852040202e8001220380440c020400604001e4054907106125440290b0186a40d00c06129441c003a5010742034140c22440c807550714082d490700e250001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 555504433 1250 555503183 555503191
    0x18040c0b0d0603021311030712150b19140d1a041a030c030a1106070201021c03050f06030d0c030f03060f0902030105030d05120103060b2d010f0c1a04020d0b 69
    0x2610742c1800d1056080034030400f1001c5645000c10803d00c0c850303020f80005400301030099030400c825544403c400c44120f0308804200240c0c0c00410900958a0300700f43c080ba4400141c0e2807942080e15208190781d4065074807804612102c0074081d04e4032040380140c1c0020207a02d8084003481c0700261900c0d04941b00d510440140411500c805269008032004041ca0002c1d0100c0f014400c2d031100b00450005103039a8141200d0403804c1d1810b640300c1c2031074801030f401c2c490358003900402e00c20400b0300322190035850342040e400b443c080c0078400043e4480100340360705d8120314128000420541419440045d1003100e08030603095803441c0014809443c0c40d032204400c1040e40c00200444c0d000710040c440703490240240c040340d45250901d50314003000f420306c0c4058007034144005441c081d50344c00054019141e00082881d420f4141748070b07900560302203800310303086c0b8040c07041c3d5400109510200d0180c035003e40408210f13103802140324030140c00b0002417100e060bc0c000308100c0c0c00221500d00040041c411016076801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 555505683 1250 555504433 555504457
    0x6090f0f020301060f060e0411120c07020907030204030506070e0411071a010501030b0d0f051513030e01141b030f07080a02010b060f040e0a09020303031302040506040b18040c0b 78
    0x314005004140c2510f03503a4004442d19044580e04100084e0414080400d6183c16180840d00e11107020074200e40c0d020380c2124508441c001000c000888000c440200540c0e4030032a02d401c0d40f0f0301c0d10101102240a80c0c04000c1030390b40080c000c150140d005007905050003c00800114826020f052a460f180e0003404040b2405584182066a2240059400c0d03024200070303c0c04008103881e450015502d07040198000c6c000b83e649400b12030a01805001c4403148910300a410038103410300104161092128800035400180302228803c0158801c2040e51102e1008000d05401c00180d8004007940c01051440c10401d4401000824007080740340c009020074900810761151103a0390104042d0030f4a50742000248194010030410fa0030098400030b84007034500c0d007c0e0040150340e5190003c0700070902450302a52500c0048100585001851000d40d041407080e1424030954035400e00748000d90300d81d4034060740d0141c1e400e03a681442e49011200e1907405130140b00f41520841d50360300001500e44c082541c8440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 555506933 1250 555505683 555505703
    0x12030b010215041e06021603050d15051e030304090c02060106080f010b0f0d0e0f07090b0d02090105090c1c0c090b0711010807020c04140709050a080304090906090f 72
    0x2907070148044a60031401c1450b81c40c2c240703000c0e600c154805034603000070640c825010b0000750511400b581a6000d41c107030501c03c50040c03c01810040c01c10380000400c00805400c00e04115460100070f0540d2048400140c41002203a551055031000e031802038071415014401800001000000c50003030030342d1107201d41c0140000d035041038002002543c00416048440d08024010002e10905004031400c490140e10740f0307a1200302c2400203401418001c040d0890b0341c4242410039042c9500860800200c56030b000c81000281c440700140a890584050083c1d4401d0840b001006603003402c200d2a98001c03490910703649801d02581c9072805140151541c006842d6071400b80c000d24a410035408405040380e03020184c20100340f5a00c000303d2108004c100c504008030000420306240c0200030105003088003e00034009003034a00d130b030450080b000b100c02d1030000302542e4001130300d420f00c1c00c81e0b0b81c16100d070000030758901402c1ca40c400300a08444001121801d998030303000d401080254420340942071049500c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 555508183 1250 555506933 555506951
    0x4050a1406101107170d02030f0703030c09180522031403071b1518050a0215090307090506031e1b010e060a03020706050f06010914060d020a020703050f0607080a020304020307031203 80
    0xd146c084000c8000c015075004020f404080410700050794401079240c0307804109402125021602c3c1c000a0f8031014000110b462040862909500014880c01a20010801c0c4540311068030280101c15180500440d540090300711140c602c0300d005503030100380c0703013060f1149058600c02400c14842d078400a8807203140044600303207444254051000d040c501082c1722030709601c8607154036407203184d4948002e05c02c221408414020b500d4500950300701003001000d0743d5100d96200724440c082c01003103548a10a0003013542c060031400b500078192a01008560050101825010151803070a2001c1501414002c400700424071550750100140501c04065602580b0340c4158540203041d0b0344085d2610220791180300130000d040e6445003420341215070951202000c1840702c004100b0714818002d0800d4101d000043c828401900040c4c42400c4a2052007100c00f00d03100d001c03159440308802d40b610b80001e141000412310100d40764028540150006090355030b5155644e0312205e40c03505002e0b101000c2901c07034040c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 555509433 1250 555508183 555508229
    0x60717340f050a12091a0702030a0e1203030106120902040204030c0521060601030f0b12070303080a05040c17013305041802090408161104050a1406101107 68
    0xc0c0c8a0390501c0e0511508110305502c02038a510440c80c1d2003040c00e651240798109010401d20200312210400342c4040207030800e881d000707449502c80010203010689403d1081614100070482c0ca50400094010798150703400c101e41280c1d603900340c980010003203840781c07181c1e4050ba41700d00c0188000c42c403d0005c441c0003882c3c07100f401940e502007603480b61454218219490510300100e51036600c4202440c0c0040d1000c14445080020030611503180c1e08025030a8484100810014044064a0094855010640c1d640c02288203454080710300500540f0081030820083c40403980c0241e104c2482c000214040e10500c1c0b519040014030003480701182e00c00554012018503110004000d81010b560600005070040c113424a051100b40d030090007294038500103420f01442009540350f000507043c094001c0c0515081200a440410702d130b4501c070303078038110205403d00c881d4407880c2c03120341c0900702090301540d44800f0410204501c0b2000400c0c041c2e9503901003146a01806400d02800480366503086883d040e07401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 555510683 1250 555509433 555509447
    0xb0a1a120a05090a06110d0e01091e11010e1c03080703060501030c021b061e03010302030d0c1e240203190b0114070c050d110103050906071734 63
    0x501610145010140021001d010544e00d44c9290020804602134403040d100f4604c3e803081e5000d6140040c03425001001e070b21019040030035054005c1c08000110441c1001c50000480800e6004102c5004287c0810f21540900b504440c2600000c0c1562044c90f130092241c0c1c880d08030740c42c04230000389100c81081180360f01885050301601c0c1c00c1c60108680074030040c001c1c7d501c0000000040f0300381781144c101001691400304540e2610102002d114110103e4075200380c03103400a0000700c0c82801380b1013010b00c0c902e11032080307111155000721103510445d000310400d5990000300ca5040e1260403a045d00040c481954008003480410340710070041e52483d1080021640c0104c0c820080596030600103484101c0c2c3c1c1c0040001c525045000c9130564030b600d5440e0405500002c1d61000c0d40007090410b01206010440d801c0100c000400e88060019581e030b440e4043d02c42c234044409002140d81840c0c000070700e2083c0e411a50b0310810f24403154981c840008101c0e014000c2249140e144200c551200359400d50b84030030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 555511933 1250 555510683 555510691
    0x1021603080f0c0f0406030f0b03070b040614090a152d020705030d02071502011e0218040b03030d090203030408010603210e0d2a0f05030723040b0a1a12 67
    0x41040c204600c04c220a9000d1046108510416484421801100105900041e11088000c04980040f80d540e000402143c11501c142004500400480c00e40ca01e01c0744103c1d00300c000001d1900603180d00f0a81c08034100010700c1011020052026034107112070715103510011714154140040d050b420f0100d03100a140407441e4105902940000d05201076068000039400d00380d51b801501101144510f11007240148400c500d844590905100e00060548155004210441005004024004080d1300384410340d070381c20b00080c1e010340c81085848a207610960001d4690741c401026281f0b0940e45044150a40da0715030000d0360b000c0055000c241c0180c002c0e440310f038040442400d0001d22054130b4000120300c450a4503001c1c0440800c0c03440303c0c02120f24408401414520b189021854589818015410090b640a4076000388204a00880d080c20158990b01c4541030300d4030321005510092040c0800340403500400d642001c00c0400c00325004001c0c140644003c07103a180c0311500c80f06040303800015480003070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 555513183 1250 555511933 555511951
    0x70b030c1b100f11090f1c20010e010c060f14090106090e06100e07200d020f0c030a140a0b130309120308070c050f0f01060801050705032701021603080f 67
    0x3051400c410f60310a401e890000f14100c44011b18018440d000c505c512440f442c01038501e104034400402081500b070001101d0309190103920104000c903400544025450b10b1160740460f02c1e080b881c000180b11600070000c6000020303808101e005c0c1c0d58080e040461404e0741c440c7d0850f5101c81041c440c440e854802d42484220000092405040000c15801c0d00c058600480310686500d80000f20600d0060308a2480340c8041290100c8aa20f081426526079a52000c1c2c0f00c01030180401500c51040d0004202e40d1624009002e042141210380e60750441b001500d200d40c03194041c03c128440800c00b51504603114580c0c1480790b80e030241892500a00f81c02140e00b162401600745003041d404a40e0040010b540701c412800d01c0010400c003800c00740d107071080d40b000d244800d1059440780081da03407044d0031481c101d940184c0280940e403109001a1168001250014034a0440344070b815041e501c400b540c012980071280c0014a0000c4401841c003114408400035000300b100002408895051132525640c880001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 555514433 1250 555513183 555513191
    0x1211010f090516030807060c0509120f0f0f0d0503040c03120f0311310302040e030c160b0319091a06090a0501030816020f09090123010305070b030c1b100f 68
    0xb558600d6070500034180080c04250b42d07031400300152806002101c140410052002f4140d40743c4500d461b54500404800034124040c00d550018201070000303d4280c408000c001408030107c07540d4084550f81c0004100f92040340003102c1c008045001c94002c101d10364816074682c00d00301901c91024090b558040160300c81442c2c10000e140105d5807811350380c1c0c450200c1c40c2d4840c042d0a10400c070952822880d82000e58400d142c0300108d6910395001005000d001c48407029640c41c00100340120706000a24842d031502c8100810001e00300c08000400c404580c000c00c500055041c0558865601080361a010035000084403018801d9500e40780301515880b014824082c0b0096040d569025918068101d280801122001c0307084115941e9009110b120031001c0c0c0344a201e4548054070078040d258030342d0248110464140c1804600c1860109581a2034004008059035483c05801d80c100d584010221140001d05028590311120341d4111316085c02c491500030442545041041400c5400c4031384200c100a2030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 555515683 1250 555514433 555514439
    0x10e09030a0c06050403200d0f0302120610020a0b07361403010603080c06070f020d02030f030a02090415090b0102010b0f040c09050612040507120f1211010f090516 72
    0x10180308100e96030340c001c2c07010600780c4446ca029281c1000c0101c10b401000300c00902042100d1000881003036007407a99550700c011000500f41a4203c0c8103809416524401d04000640303213080050381d002000800380f04880d081d400548909440f40c03c19640d240010b003402c1e03030400c508081031220601001007070409a519180368503498200300d205100d44d40d0100c290441400be00e0350294490002180c0100c042130f503500110141d9501c4140456011010800303241401070020700c0018070585d408400d8008520b8142584040d800a80000700520000382d004c1056040c03a40311401100c0d0000c0d108001c1000c0310f800c020448094980c220b190904583c50400603500c079980d1600010407850054400041c50b9805034001c607080c10300c80e00b005400040000d01078803007456540c3d00611940c000d0090383c40c0151202621000c80c500c80d08042e004198480d500c2021940c2901106003200d010f08182c060000c1183c500c509540c00170500811140e80c42e090401031000a00451140c0385803811040c403440c3c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 555516933 1250 555515683 555515687
    0xa1406090705120403020c060d02120903070807152003062d040f0204122301020a0e090a0608071e05030105061f0e063405030d0e07030605070503010e09030a 69
    0x1240307480103c0300c2c00f081c0464140750091046034211340000d0030859039125101c2c0414081d6110b80d10300540750407070703100260301200d004c8150344120350f01c1009945020929182c8100012800c001c001400f503441c0071003038130045c039071141f0b0310703401110501e554403854800104079148262070000c141e184540aa8054840340c000c2562110803c11140000c1c00c40700750190340001d00481c0c20203421112000031510600c410700342d85034400d80c0500382c514160420381940307d0a034003c01c0c0f4110046000b96011019514000c9031460b07025010880010b029542c0f1761010349000e141f940501054841d04504220742001c64895001408055000748524100a0081621880d400b00c1c0c81450000101c81c3d010403030310072800f00010250040c41d0903103618142c5a60b04079144c2c0741704030460781c1c00180d04400c059082001ba100c00244c03c05c02171030424001001c144094030808805001902030a140840066040d11540d80121602c2d69103a490390704100d035100303206c000645982002c1c0d1061041d98443d075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 555518183 1250 555516933 555516937
    0x1406030606010f140c01020306031002071a040602070213020a09051806060c030408010603062a120e01020d020304051506120a060b0a03082209090c090b010203070b0a1406090705 78
    0x25000303207004140d0648014003203c8441680c01d09013055480061000d5040005401440c01440128261942d142c2c07040c005504078400c0d60320080140b05043e01140d0107131040e110280d802401607502600c0c0940d1503000424003140e120204112550105600003015031020801d00548019150540c900503841c000386c0d14003c000b8222882044006152142c8907000e2041d50000d1406074001c0c071249490385040b001030070310040c07940c0d6000e01c1007c0400f185400031001d41001c008646a10400c01a052182405841c4540c64113883d9902004031250550240c4015407044c1d00840c05000d01e8160072028020405024014900c2004060b1142003440f00104041041c6076000500082050020022a0004100e5407000d405c0100100b01c2e5582c1f100c240092400c20130117032542e2114252211782e14011941c171004046d003007503580320040c03044040c07661040c201d04105004880c101400e43d982c1c03064000d4100d500301c5503541c4440031030305058000600507811840840b031152203458540c0b0f00418038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 555519433 1250 555518183 555518191
    0x31b0504090b040b1002030a080a2703031b0905030c010e1827100b101b060605190905060402070816020a090f02040816210611030a09030314060306 65
    0x89503100360b5100301d81e50f160322100020f50003030200e4051104035900652207030425199000403e00500029030400750600c540c0072074415100d0176408140060042c03243d0395041610890505a80307007803500342c81c072190000c0038403044e0303958641c0300d100d00b864145810300d4000c200107418421906150714040d5641103a407250f03807802d070030039500d03da44680c144080c07015034910300c4010386c0c9194203240a0840c0030a08440c0403031034550501a1080c4201485013080c098103078880020300c140c00180c00c158142e0780010015000740c0e00840e501c4c3c0c03904001082c04594060014a604c0481c41c01c0100a02d1405043c3d80483c088500310308003050358a4103c100e210f4281c140440e0008108050210f5480f414241c0150075103c008000280040650380c00950007402039100c0b5105a206048103420109000000d480191800041e030481c4041c4440b54011000b008481c0180c0302c3c480e01c1e076003e560101075032050b84020800314481000381030107002c680481a0300c0643c40c242100300400d079100001d20a801c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 555520683 1250 555519433 555519449
    0x150c04060e240724050610110619110d0e070e012402100c030509010b1c06020a0903050f07031e120f020c060c0f070b0703020d1b0b0a05010303031b0504 67
    0x703101454506040b075020a0b00e14021600c3c120360350f540c40c44010f51701c050300c504801d0f5902e03c0403452814080c3e80c10007402428001c0755102000282c11141d0500360f44800c3e2210300400708140d0b0b500044214280c02250502400a039240401440510108a041d006240050040c51a5414500301c48000c41140046046c1c0380c00740d030070b5421034600c00c0090080902500701c041144240c1c481004002e00783c00d50303003900c0310760a04020641c1890400c100c0e9510701d040211211814210341d49410180d00460f201070f003440360311800013003c200e00b4080c002040103060050907140b411403030320701c0940d120000780e400441c10840d15640001d00c01050080708042a08050300b5400000740202e2402e00940d181a420001c08209030804400008080160040c0b000c19502d1042c0c840004482c540a85070340940161701c2481c10522840c02451025080203910910f40d084c603806885031120410b040e03da0062250341e0340010001d0550500c0f4044e0f40000007194650f03c000d1f800401040c0307010310300070005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 555521933 1250 555520683 555520687
    0x11030a050702120615040e3c0d0f030f0605130b040b040207230105040804230d03050a0206100b09090a020d050403091a040323150c04060e24 62
    0x429503503000b10303094002c903520080b0b4400c2d15126007000000761210010900031407d1044c109426040800ea1041c003c420140c5202003140360b00c00c1070751540c1103049001c080310b02203c840c01256003d008400c00d8a8150f15820308034900444010201da078441d20859085107850424049580c0340074141c242d5083c81c4401048104007140000d00074032a604d03040742e204e44001508800c1190b0088400701c207404c4c4021294480040428203070030303550100c60041031054204405e114905441e1804041301303103140c43d030b02d007101b2580c0301040403000031203015030100d07c003c5a0510328590401401d94070020215880c10401c0c5000318001d06401103011070b520900384180011b145c410383c1e138140c90548400388010b01240c1081d0030003810780985030140c0e1a010040d000b80041d03004400c130895048035400703d54002c80c0001540116006941a01d0166850003120041c080c1e00d0380280c1d4440c01a5140700c0116901c40ca0084050007400400f1015806500b82d46241062844124142c10100e0002c0b894a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 555523183 1250 555521933 555521947
    0x30b010e061b06091f06050913050102070203010c03021207020a051e010b06070b0103120804020907030c021603241e020c120a02070e010b03062215030f0303060611030a05 75
    0x94506118400790a958401c003010071003c4d14000030f0000da402100f4a0000c0503c03603800111040d03030002e008150700a82e0700c402107501b80e5000589119800d009500042c20400d1607400079003900c401030a907000103500452038001c2445024030007a0403542d240002e000c132102c0365940b00e440d002c5984400e56039000913481c0440d1000290013101440c02d000b045107503180d03101d10b045c100d8581c0a000c1a201d4020401d80e0f10b012a000b9403491303001c0c580040094400350b88003a030440240811440354000c5004000d4003c1101000c08520b401843c400d20720001c2810000184c00000e800e41c400a45580742815113040d03000c10400c007104414000c42d400580d548444104035450a0141c140094100d500080c492011503400705401c1e041d510380c4130700b00e81540d13641c00100050f8041520000e92015112865080c805150896910030031031191000c038410544101d000505504c651007603c8507804540c0540030164144201c5000c0c0a050501c000c410390070a490565034020400d062061020004142d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 555524433 1250 555523183 555523207
    0xa03080718030c030309050904170901030906090609020906060f040918080406090504230f0601030b10080a05071b0f0f211404050f0603040f050604140d030b010e06 72
    0x41d21014001070381001c42641d9140035000c0321030620040d4006061800e0101d03013450112a628010364200640e40b89052a011400102c0e034020fa44181c1815999405040010018001c440140f0700505000952034818014000d9000d00188218400e00041240240140d00442990705803152071500150809196943c094801e4070340e007024102c03040c0400d001480315486004201a9201a1000d00c05089030161203460000b84010007200000700030300191181ca6140b404d558481710501d4003190f140b60503000300c0c0808440809071000105403c00b004990b5032980105504035281785810110703030f548502c0d0310341045400a00100300c0303040a00c0390001d008819541c43c8942d1380141504445000917000719004151451842010030a903100040b1400714030700c1901c040715000303040c0b5001c000d00791042100b10360000b0f1040310000300074500c2c640031034010400300d031045118001c00a0341c0c040204c903203460615100c118034101400c100102c6200e903885151085040c50658425840c0d200340108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 555525683 1250 555524433 555524447
    0xd02031009180302070501090f09020c0c0a08010903090e060d021c02030607090608090604030801120615030506100e04030912140a030e130204050d020105070804181d0f0a030807 78
    0x8408840d074107102140c07621184a8604a0b080d5210342c080b500d000b907851006403000320291054150000342d5400421129140e50001d10314422900b060312501580c0314005441100c180d0040101c0381e540714804800c240d00003055a001d8004856289403d00c0c00c0d40016004111000d80280210b41d486401c481e85850301d880240020750040c00c0c0c1c1d049203401c690060841010307100300c500281c0034001040c013030400030448900070b84c2c01d0742e070308265a805c0440504903507944d0b540c2190841c3d0307200440f48244e40c4c2480803e02540c400c8014144d98100140c41212210307041d0007840d0b0034600d6006000c006a0420014000c07289584005410300c10507044c05c41d0600c20f00c0f035240100c0d01800b44908101a4800e960584400b0200c0304000b408850340210304c200d01031401004d030800c0d0349d0280103000d58080c8014201581c0726084861800751110304a100c038400110b4514010354407000c11541c0f030010350340e40c040b0a40742c6800600b0b5030640c801101e552440303081005818010b1203030101390002e1040314 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 555526933 1250 555525683 555525689
    0x2b0801030203032d0c03030601090b07120807090305060109020d1104120303150e0a091e03080103110604080313080c010806090a0506040b040e030712180306050c040f031a0105060f0d020310 83
    0xc0085d100c080203084503480e035004445aa000507202d14010501d4884031007543c84090300a4540c900d80d0041800a9400c0311014012505000e1260230010002c0c0003048603c1c06020040009a04c441403006080183c420040705158000c1040c0310034407101c440102039024440e09480d02150780007018005180d0701c0e0303040e046144100002010826a00e0080d00000282803085041c0c4404076540720300c44641d0307042e01c5001800949102d0041010690907238112529100c001c0503640f40c5995080300c185560300003400c828240019450802511009100a88040c50700f0b007003c0e007191818500282c0d42c00001088010001e545002040e100e07203555100803291040a0020422303140d9224076141d0303980015a0490307400440146103964070f0f02c81c000d41c411158100c6c2c41e41d0000b074210799030700b8041c00006110752100141400006100c0c102610441c00950050042001c144200500404109416003001e801451300b0024560118400c000b21003403231154000c0141c83c0e0310350b03034078009100c14654 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 555528183 1250 555526933 555527017
    0x5071e08280e1e03040324090b01030b070f1b03030908220506040503030a081e0f011d0c090613080a06050f0f01030201050f1b2b080103020303 63
    0x50510709070000c01d82d10441104207a641280c0e5001c119401ca02c0d588103400e80480c15075041030008000186d900308842c0303000d030180400b04005100b6501090110707442c22605079100c00d83c40340100144010540400c0d085003407481d003410090050040906850f4480d4500c041404101c44a0740a0511980c0b21540050340800070036540d901d0000101c40c00d10300f1422500143c10403010024851a2490445080702c2c00540594180f540d44641958100c07402072403d806100342c40c0c00041d070b0714405c0000c1071140000801040503541003548108505850000c040142c40903034091045040c014016a401c280301205d034550b40e45000c0100407090303c8035130300200e41442602c514900308881d580005d40318525284040341642d40310414524503a40070f100180c04100c1c100842c411075410440145101c0300c0c0b442c6009104008911140e24180304280400e0080194004850310f0072803802600d40c0e85c600c0c0303141c8072500394115000241c4030703c184000d03410720741c144c07030001280010030011110580ca058 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 555529433 1250 555528183 555528241
    0x1606080606070f1a01141e090103060b060d0603120e030316020f040e07080a030f020303070905091803030a14090c060d020d290406050406030816021c0809030105071e08 74
    0x44030011609141070000b07e10442c943c549484001d41100c02010048030010303e800e00907440d40d11810f00500c1c1400e8250b8001104000203168081070780039020040d88160300446105258000c01060f1114415080e4400d40040201050a1800890b1090381e0360301180d0264940c90103d00080040c07038658900202806050700000300c521001c5401c01e01d1a0180e1103c0850300f4821008913107034802200e40c131012403000c8805000c00d00740300110640c848007507103c24101c049000d05c580d00d1500301311400074a031500c0b44070301000c690100004503048400040100000350000b40041d6460240c0c0e00c10305529640480c04e2589601c5030342004140d42c2034103103907440c4072400c080c0c42d040d003601103110385002e0f60814500040e80d040500c60300f4102ca4100706620304042c04240040d10881942c0410781c2d0181440c4041a044841182d80d080418400d03401d180d500c441040a144c00e50703038010300900c1480b84515614081c9103449840c0c50204100c1d1502707d2590f60741000c61044640d8800352040c0720f10340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 555530683 1250 555529433 555529439
    0x507050315101b0605061014030109051308161b0605070f021c050601060f021209100c020a17010e010501050102030a0c1a0406050a0b0f060409020a02030909091606080606070f1a01 79
    0x410762086006035415510087c225400c14030950382102801154011000c0410042001e01d086038443c0d900010784540c0e401000b4029221035540384c0054569564101420f80c113401007285481940340246024802d00480340d15004000d0300c0340c0140c1c4005004502d0f4203000c0d070215a51380000d0054940031441001ca0107031642052607840400340501004a200010b5403812180006200151009203001713591800c4e455005001c02c0a1344081c1130424406103403400001a607400764a00d028141080462900000350301c5000d00b5110347c07100307114140e49801c00501c403999000c011a85000c0407130821040c4180140340085824620503034007854049428188010402c443e08200d01034443c404051162820020421941480404034564032060800c009c00c0144540d40241c582d002140c01581c0c01c012005020070f00721041190300c42d400b44c0044401084400304400714101400280c542100300d8505000800c060313100d040303805000c0c1031816150500b040f001603440b1200e90014a240002969 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 555531933 1250 555530683 555530693
    0xa03030207080f0f0a020f03011b02010e010c090503060406020306120d030c09080d0905011d0409050a0605070f051c0626070b091516080a050d0507050315101b 70
    0xc428040e6100602071290701c504031400024a1309802c02460018028030b15159003040014402180301e0b54155485084a04c2200140c20744420303242c10715000483c0e0f1142600c012421100c0d00e075000d000744484a2014841520f00060056200303034030440040c2e40341c540000042903410b02d5641d00c00c0324414820904101da0749500419041495034403011216922240c08685030003003002503c0006040841c08c01c41d45d807086516007102200b80b0298288445000041030941c0c442000507103043d4003500b0450f080100d140710b020b84c0300ba0039203481040310540100007400c1d442000c1c60700400d10002d00d404500b00565074866001071101c000b10040a03a500e0b071304c8101c400b40e065112540c2d8020007000140141c0d02008880d0320303030340082030b241c4110160351422000d80c211203003501e0030301e01c0407059100240340040200044400c9484a90300c54940081c0710040e110018044000c0000500a211103144145849584450100d13060702c00000c003032108841400d1161203401002d121080d030b060500c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 555533183 1250 555531933 555531943
    0xc060a0609060b0306010c0303053c090d0801060c1704170d021212090106080304081b01020c011218060f0204090e0102030f0609072c3c0f0a030302 65
    0x380003071014014a0364078041c0c8040c502040351020302081c150582c806c0041d11035030107203500c6003280b80d03d03021541807152401034000c15038030310300b503036020f6803880090031060718081d658490034890080c0903408000c00f0003850030806202d13000500015a001c00d080020308088600386400350b050301501c0d142e85841d2100040607040301520036004050440032200e10100d0003540c1608002c012030310b083d0103030340c5085d03480c04e0040403c041550383d80d07404101a0801d00041c4010000f043c0142007102d400d80102c0080204000400d05640c02900c0780d00d20f81e6085020712040c2c5c0210540020020003030307410034001c4010100028502c901e802c6081d0700a0485501038400d03214002c90030000349045028903400c0b0703c400d47d801ea18440c050780010300c40d49014150a9403102c12840e0030082499000420b544455580f4680c08400004041c02103950901c810650001100b0019810070b0024240540b60500c000076101c5550b0890140340e01c4407078468480380078036442c0140410650355940d060080d114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 555534433 1250 555533183 555533189
    0x2e110702010e0a080304050d0c050306090132161e1e0e1c260a03230a110408120307030501120b060108060f060a02010b0a1a0d0e030c060a06 62
    0x309524002d52141420000c05240c15110030340c004519180c10401045820390345d0ba0000c0f0b810000d4024049030546060141c1400b44002d00008280c8500e4001c0702c0b4101c107900308003050503803075881e100502c0c0741e0281d0384181c110b003085100c02c40d0300240700402c5400940c4011078041c50b405001c112404503502c14444401d200c01e201d40b180c0e5180b4000c0080792506c000400c0301c1c0d88000c200d0403070014291034940101a0500c00c0301c02800c020503d050000341040f64928100c55410049240750702c094050080c1b4020b0000c62446520042032044000010200031740403038078059840300c0900114040710201c5014250f21411550600748400d0003a1040c0e20448480700080c1c140000050107081c0700c281d8041740c0b54428480001780d62103200449002500801442c2d110340045648401501c0d95001060405101d0f4008a100c0c9044000d100c01a14613034058011065080b5007a911000b60f04162042c000c09900701040c202e907510740c4c2e14598010301000d4a058000e4109119051025074401821 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 555535683 1250 555534433 555534437
    0xc08090d050c1b030a0c030809040c0e030a0f020a120803100f05010215100e090307031709151b0a1206060c0314032a09011b052e11070201 61
    0x80034440c4042161140504101c0c2e69581c1d004454a403c18192800c0307154204001070704580403a0382030344034100c01c0e102950061314201c0b030000b00407009042500820303507000c1d01c03410456041c0311442c0100759207009510010301040f10203115401103640f00b03041100204800ca005881c880601d0900800546c015500c049140f010134000191289400c2d2202c1c04465050b0080d011100d8164410000b1240041042c0d0000204402c00300d040400882c86a0083c4d88840041d5101c142625003e01000e6035a01f940788849107a2007003002c1e4900001e000f0245040c503000000583e124800c0f81e8100b403e400c0880502c0c04004183c15070701c5584100800340041d0410010300c08644d4a0317000b075404032004070b809000141110900f219002c1413400440d0050b01019040060002c59501850101d0030f0300c1c50f0400e507040001e0740035110f60b880400c0140c04070854500001038a100d03609c42b540c13411085800c00623040e0496034003041e048820b241040e0704110810501c420b2890014048066205503400c0380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 555536933 1250 555535683 555535693
    0x7020c0a0812041509150f0f0311030112020103060b0a02010509211209160609061701080c01140c01180210050309120309011503050d110a030504030809060d0c0809 72
    0x242003000248112101070721060b1285014105a221811210b0910308581400880d44000803207202d5044010104140c640e10000502c001c088018410001c1c010804101400c00c05602c2e4505800001c590465004e0130403080030f00305034401a80909041c1e4425025132501142807440950190041380c42440c41030161031030f00a01a6543c0840f403003910340a69249c1f0306010b00e0000b017440c00010380d0000000c20460706461000c00d40409440c800e50880c00000718807032420080640c0144989281901740030071803c940d810035610340d546408105240b410000c0c0d5142c0283e9400d1484200c580281c0c10100910501040c4a02c0110240b0141800c80c014003280d08100b5416118400362802400000003500c4900c00c0d40b0410005504064220310440d544d80030801007401610009100440c0b00f4800742580111030741e40905400b034400000b03035094120ba5140c0001950100482d0305880d40301001d103496940e0140400c1080c01000c44074010603140891001855400c0700e8082d108034004801c8039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 555538183 1250 555536933 555536939
    0x60b0306160507020609150703030e01060b07031407110a0b090a06030207030519050c010606020c09070309020d15060e090a110103020a021f0f0204060903210f0e120607020c0a 77
    0x80c940d4201e440d200c000100244850360040c03174440020420154003c0002c3e514010103440400c0c00e91140c441100032980c2d881c41a42081d07401c0c020440241401d417841e500301985600e002e0004100ca068040215400280d07010801c480140c81064821021340401720454031003602c0a82c0d64003a1200600c03903a200c11001070524868000c44604941c940d50741c904000040d24803030540809200a4828842d0500c8034028040003442444001c2c00c1903401460040d401d2800c3c0010a54003800c90001c060624044e0000f58455044402a842d0301441000c2d01c0140203500000502c4160000d030452941702c0f061003808036000508507005802000c0c1107040b1466000190104d00c160001e45015800040010301c0031080021000c4c0703032000105004c42c18104440300a42282d21075005070f404580840d6050082c803c402d42c482a050720044038088000400c00c90280840fa101c00c0c81e070301000491807000c903840d2510201450b0290f88a400c0f14001c0c2040c081c0030751074064081415010f051600000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 555539433 1250 555538183 555538201
    0x60f21010c1110180f0201030b031606090b19180f030f0b060f1509060f131e06020705040b03010227132703110703052a130209010318060b0306 63
    0x2000314140c04503a96244c0030b007183e855590021131204207a060541d02c2c0c02e106803e4506204d1600c101d2030304090000240d0811b00d000c2c0180c02182c009044042c024002a41000200340c0c01c40100440c6081075088900f04030544800420740750021402c0d10031903100042000215001007549504c0760322081220b81c0d8040c01e106040c501d082506601289001e01440c500e07034004000c10005001a00c0301d450902a0110a001ca620118061040401c0b00004004048240b1188400903450001c3c1c55481840c01d10000c0d0385001e40c1c00b40511a039924030000304a9074095044400341e06140ba000101c0d0303180d4041e660051100003030400d004200044411340184d1403449010000214159105c00103041c00d0205c01c08000203d404400303220800e0060b10841c4420818500154815002000300440080d40d07c0741c00c002a01460307101021141e000e441e01e94a0310042102c40100d4a80140c40b0980003004074041e00704140860700c0d10403a03030720300b00501400ea04940d04911042c0d0498031aa04c401b000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 555540683 1250 555539433 555539441
    0x5010e39041805060a050f030a170a020609150f1005041a0102060c0c060c130b030109050402040f05091c090f06080105041109010906050903030d1d0705010206060f21010c1110 77
    0x130a68014540d680c00d103c0b5241001103400c1c000320180440c0c4030010300769181c841d119105a1240740091020400ba003803540d041000550180ca00b00203800461820b00580035801c5016280f606800881e0000882c10859000401d0050400500500c00c1c2a803101800c078514280e9290326005001c0e00c000902c1d10005d032003c0b100c8510300300d030092a80d075a42c440e6203500c6403c642d1500b01e0440b09014001036480f045000f941c01707084c0c020300026440c01d043c8100401c5400300c13603d104880c0e040c0010400c100c60b022031a95120300c542e02c545040d46421807000c56841259402c0348101d14605000032a40a0344584040d043c4d4a05560800030303110300714249061405851070983c0007850100782800301510540207400c0e1160007900f1a4148664503092005407201c0e000200407606050305c030018800010000100180300031b00280015041c5000400c5000a4480049028441e0b04000c440070b040b00f40b40504071000da0000070007001c25458402441c140942065100d18490542d0803103162116100d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 555541933 1250 555540683 555540691
    0x203161503051003021503160e090c0318010516110601031115120c07020f04060e01050415150f1e02030717070203120d0f05010e39041805 61
    0x1034811414844250031009880700400c9884100c024150010050303d0360703100d020400c4080200581c4924000c030040784a6414040044c0420558607401141c3d42c561040240d00850008004e0780e03640d85000c1000e9002d0400c40c00c1c14882e40c41c140401a000d2003c2d0368100005010b555227400044135100f0203a541c00003030102410031307425008402c0f044c1c901103021100038100b40380c1507400c02e42c1c0070521805041c0222403004103510001100f100b180340201c20761028101c11034013080308a0400b002d10000b280d05000e5980150b076203510461202e00e44d042c51000810442803082201c6a403104001c04501d0456404804540100d910650320458003198000a01240d0f0040d800c050f05501d901c00c100d6205942034090080400810000d61006d2001c900510000301c0303499a01d40250030f010f021030300c2d81d40d41481060316260041c4015400c0310312554000f42d100209441100c6950040655404040c2000c00c85182000070000c034425085c000e042240c1c28039202a072040740d41c58000c001d40340125 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 555543183 1250 555541933 555541949
    0xf0b0702031005090a12090603050c1309181401020912030a0e0906060409140405100b060414030c10020d0909091112030408030c010e0d020c010c24020f07020316 71
    0x600c0c0640c04010395000740d602c00011012603402031100d403102400d10901e46c98040c0040c1e0050001d1040b00d826028143d0020718030300d80f940c0f4000e1b00400f0203620740c0003030041c5090079072264240041d0300c620420a003281500f04d64120540e02d800002a0300130750010a115014200c8080d1446050030044207440740744032607031516501d0030101003c100c200c550007000c55920400130710012482c96090300c21007001038010000700d0521f040500b02070303152040380e00740032610a09107522540309490b000c3c103580403902c501c0001450100401e0000381020480030215800ca08142ca0401c000c0e81e001a101944440075122202502d80301c0248500baa456400040c06145240035142e030750382049511140c0c0c0691031b1040d2030400d07403608295411a403043e40011030b10781d181d075420361401034240301c1700c600e00d40140001c4c45200e08581c0064201f880c0010050302000461481c3c02400310751100c515540d070150802107560f4140850303603040c01c0d002844180c0c00381c4074004914406a492083d4282554103503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 555544433 1250 555543183 555543193
    0xe0f1609080f25120303021c050a090507050a15081b130f090203041a0604090b070e0103050a0b1c061e0e011d1209010908060403030204150503070c151808040f0b070203 74
    0x91744003a00694450700a443d80c010640c06500e12010640c400e840c02240c03128404605181c80742403c900e40201604458482c04100d4000c0022901c0c501090131840c1141c24a10440d07a1141a05010140d1201c0202100007001030300880e000b0300384d2518000e40381e00da66112034442c0c41ea0710407022800700300e070014042e203613400004200c0c41d002c02e2020b900840082000c0303010101a40d40c0a0010400d0728684080766070041002515070b0180a410b520000b0f1110400042000350002041d5511900c1d4100104038280c948109004490300404400c84c0b40c003214005501404440c0f8000709200d03c01c0912552801050841c40d09800040e030441d02081002006181c0e082210040a031f44075400c080d050210102000030048001d0060303e20503801f98500588a03468159400200310b50214228100301d4108204a50a074100392241c0c0c00941211402c0c5a0342e10b107080900041541000c0358403104019260202080305201c010803d40d85007102c20050030350b6a4003460094055000025856002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 555545683 1250 555544433 555544469
    0x108100911090606070501090803061827030d020f1309090f03110a060501091505100c0b191a150901091206021b060108070e0f1609080f25 61
    0x120309a003e4101c03000804582c42c00c4103c1d80c6140c21180009412514400c0c04010041c00d85090a140d82450090003104445481d1270780114050803885e0220141145004c840c0390304503001041500c070b035052000350841d038840c0c2072070042c1c0c1203800c10303010600440d615010200300f80c640c501541703440d207a003e01c012900035443d6800351811075103441514800c0c0318039500300300450024003036180201a031441c005100694078403514140c114542000303009413100d91012071469803107001680c106801c2108002c080d110140d007000320540b4001080032640c100700c007007140c6441106040c65017003c21188c21200003c4201c0c1d0700b600780150880a4041050520b08002213102c420707140300d80b18444c2500624184182c18008009040c0d69002e811581c000e4005004020041000c41c0192050041d25401c514110900080560004007aa218511450f0138281514001c902c4000074000c071900350745214070088162590341c0f04101814a07001d815001c14001135020039441c00907610f880c3c10a00762554 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 555546933 1250 555545683 555545689
    0xe030304032f031c1b03050a1b21090b150316050105041a0c0706050706053102210f0c040902010c1b0506120105030d030e0303060111031b03030108100911 68
    0x151030201300d40c840d2a8280c21410304405207240b440340301651000038190420306400011500004150b00f40c0602901d076500a0580040407110340921089900b40b4000c3c404801d07002514901a0040c511500c21042c0f0003e10401c0c104580701903000c0c0c0458581502d61854000a2844c03407260b6808218104428441610b4110401642d00344805c0c0b0f02d49007101c3d64203207510b040c101e07a00000001b58082007910400c0498001d5580001c0b142c00201014031841400030300031940110074021503440b854000b400c40d12010540051041c2691035510810031340350260340c4170300d000d00c000e525074000e080b0158000e10b007609c41c1e8281c1540613511051599050381e1104584134409440039280c0d07803000000141a03986800078182c0311440c081c0e481d56549090149450300ba060100350007810700f04070800050900010036290f125000340307003005e448002ca03000b10b4150310448408043d426084203088415800000095040307271f410b0000c41c0c1215000d805c0d80c500f29101094020610942005241c010785 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 555548183 1250 555546933 555546967
    0x8060906041e06330b070203072d0806180a11040914010f02070308060f1e011b11010905090108031801030b120f010507051602040e010e030304032f03 66
    0x1c1d00c591000520807040e05100046650f8100449200c6440e003050403c100209812200082c00013011160410f05994002526249c440c02007805100d00c01c0d011240d42041c1c0c0b44112010b40040074011011615407000503100c600413584403007241d031924100122410000341c0c1840f840d8101a0418003036007801c041002a01680800707490060050104503e450020300c502c0450306441940140c2d00c10031407070041c00205004104601c40c2040031425070140c4c03540742d402d5280c041d821020100300d00d03103100140c0300c89002d80303400c050a251658804c000c10000003200b440301e4074240c0f500c0d030b1155510000c0007400c003c24007405001d608280403061101e0040314418240520506001c9480801070001c6981d100380b80c900005190710a2261401c0f0000030b20500387c0228441c0b8100e4a0200384655149031139150b940001e00690340d4561402a40e0829408600c8a5140e08280d0f680c17070501c1d041c000c0031051152024602441c40314404000c0c40b480101a140101981020f0341c24882c8441c40a000d070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 555549433 1250 555548183 555548243
    0x5060a05030a03171806090708070e0601020a030e06040f031b0b03010617090a02090702010f0f0b0604032a080d080609040c03020913060c20070302090c070f0c0b03010806090604 78
    0x1159045c00c001e905c00c0c07080c072555210b03c2c0480b008041051810b4415458224603902480c0415600c0c0144441ca0740d003c01c0d117041440d05414001458100304010542920071b03940051030b00796030000003004006180626040b40c001b400140c02c00c45848002c06d0403984800e11030500071030002101081da0740c2c41038001d250300010040640b0800d00304e0f0380110304110b1045402c0030060759178090030003882c1c080d4420080000d6882500308210691000451158400c50002030803041d0041200b00c1d1203800c080c64429001448000c8010480c0c0d5203000603680c3c40a01001b0011031a14000105d1302c0c21314640c071f54402c9030042c07017040c0301526540038000b5101015100200598215844c040419450700a120f44081650740300410348112a0b0700424552115070b070300c2c0c040d0300480c07001c002603510229416040040642441d40d100881c1c9480048485040e00080400c048140300203000d40c0c00001441c1220190b48c00d880c4241c0d900c05a10307488050488000b0400b08200b41082c0300c02d510750b0410508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 555550683 1250 555549433 555549451
    0x42c090a0b0c0c010c0503060306090a05071e2c0f0402091302060c0607080604060b070c0308160507060806040c03180308060607350408150a09060f05060a05030a0317 73
    0x6049200c0f6011030030f4a81d9070b02c520700461070000501050307050800820750310602e61009040d80040682d00d4648580041c460b858003010b900044540180c5000c2441d8014604400704113007003044803864240001030005031580700c4c103101c00040c0c0c00d00542e900f141c2c440c986c0104000c0f1141c1d20403440d40700c00000030a0507600541c080c05036448414080007014000e0380306856070324241c9022801c001c240e03005a00217290134941070085000003855609000213581e8890b001d940c0b190300f03c2c901b1000014500364040c06521034014002404c0e038100000c0d900802064a080c09690004c8000780e042d601d1394908003030004400340c011008207104804e40e41d080b650042c640c1e460b00c3c80301c0d100c4010303403168011240c01c07442c3d03150890280c00e014020000c20751894001c603242040d1030807402d251250f0841007860350404010380041da00021581c440304002c2d034044010041d07505200e50040080504803034003402102d00140103d0603103030020b4810fa24550554500400c1c406e804640c0081060180c440e1071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 555551933 1250 555550683 555550687
    0xf06050f07060504150e0c090a02030601180b04030309051c030c0203070504020408100e1203010909050c0d1a0a18080d1103040f031215140a0b042c090a0b0c 69
    0x340050040500480c0a501485c80c0d80c040300c0121005c40b018007840c4025a8401c1c7c8030b0441d1500c50440650748a41c0c0b00c40011b8480c3d0b11040181c0700d688240c0d2140c840360481400c0412041e0b800005030060ba80255100c0001d6611303035007803010300c09986d0b0700c1000c000740ba584110002031040c0510303501248054140e4105958440c04103040c0c1e0440d8110403806e03008060203800c8000c1d54440c000750b40404000400000d841448406070620040c02220a90b9844070110030600c1030400c41c1441e0404007501c102d02000315800c00740000d09a00075106100300c0103502003102c41c540c41c001c04036030701a914606e46ca2036885c2d650f1340c05180e05c0780700c4002c600f644a4048030282010100a944154014001070410314102d11703005113614405c414001c1402c3c58903811095501e032000704507055542ea40c4401c81030401c000700044d41e00700c0d40c0d808020410303400540807603c000613014010714440f040c0b10a0240c241f00c045080980b0310119404040ba600c82c5200c1404505603060080d04001c204070124 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 555553183 1250 555551933 555551947
    0x20d0504290c010207020301050603010b0108180f030d0504030e012f0c06040f030b0a1a041107050106080d0f020105040803070e0117040b071403071e030e06101a040f06050f 76
    0x19166080442e16141036540072460700190704081c00340c258402c4045000f040388a031003400103464072201503c40070a4024130420b03441031640c1046a03804070501c500031203032a418060915030240604072021800141034071064100c41d400f07610043c400c562801c03403030380c14501c1e1100b0300d021856903400400124402c02d20340c0070300343d29803100400240101c0344c1604951405c5080000c2c405002904c80000b00d49004100b24080344a04001980c544040f1000304210100049010b07041c0a410400307070181d440c104000846480c0024940000c0001e03803100d400d0032034400b44c144e003212421a4040c01c1c03140204001154a440341d00303044140841410044603c1c0c2d482d491144807514106c0302202c80c0003068081c0110f460b00310b01c031202006000e490840c42d51604541c0105801590b0180320b82d4000c480c00355448a5000ea0409417a05207400119800c91a25140300305d640c0d42288204401ea034a28507940800e16070100c100c80c00e0710120f4410304a284c0c6024021605c5070b00180d06032000f90810300c5a5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 555554433 1250 555553183 555553259
    0x20705060304060501080c03030c0a060b0f04140601031a010c0611190e011e0f08060609041e0506060909180304180b03010b0916050f09040e0607020d020d0504 70
    0x1560240b4040c00300018950b051890380b03442d11100347c468920070f50040c0a003594120700052402045e542c400004928040d5001c0032404422191000b940d0103820403010b07400000312108003500c1018240da00380b00b00c5a804640f503107141c000c4050640095400e9501c41c3c0402c110340c11520a15400507161481c2c035000a10300700c007080310751004c1c400040c1c00204488056074800410307050080310029040840300d41210140000d0051000e030020f00c251240001e980c1d5032640305840701c140c0c02510034050000d1259800c41a500381c0340380460301c02d26041c00714009041010640304011405058041c0c42c1d00c07440c11808620b103a48529001c0e034803081001081022880c0e078000416a030007540880c00e01d200d041058250f602216146014120081c20001070320a802c40740580f4124074240300c1d940d01c070742c0540480c140c0b00d10f1810700d03005814007041290035403000981602c15100c1d40d00b5201c1000320b070030080762544030507a042c1c00041c80601050202003541c40c0b0b0200401d00144104090340543c1c4a0307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 555555683 1250 555554433 555554437
    0x21f0c23220911070516061707030603020a0b0d1a0919090f06060e06010c03120209031002120117060603060a0c030902040c090510050301050904080c030d022a1507030c02070506 78
    0x70380b0703c00001c92014208001000403800c2104102c111640890170504014004c4810321500114003a040b8046040720340690300c00d0004c1c1d9000f901c001039087e1a1021101c0562003110000c0d000d910f003c3d0b41281400606c24101c0f480d140c02400d02c0d409440300b140c058814040c0562404903140d441581c0c1d000a00c1403001111070070300c42c0201007101881c4c5014a4200d0800410340c030f040c00b020722001c400182d07005d6080c101c44a0002001a180c1c40d000c40428605115803243e01c1b9868800140b500a48034190171841c1222200079014200444076803000d6114041038940e5501a48101c0106204035002e40140c00644240d150005141c0860b40000381590360041100010810b00c4d68240990308102481c180d1031440307810400c1c507551600d00802e02084009001030076991002c2410303060108207000311000702005101c2991201c008810b104640e101c81c140c090148081107101617a400360204050074488181f80242d034042d81c406005030003030f05001e00303c0d000314082c1500104107941d070080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 555556933 1250 555555683 555555701
    0x30509100908220501030506060c0c1c140c03010e1203040201052113020916080c03040f0b010803041503090f1b1d18061b0a021f0c232209 61
    0x4000525184c00000740031600058603d9004880412251540200020384049a41401e0701d540004403000f038118107040144c180c00a1800707108441c045100318001801c10099a4110020003118201411482c2d03254111311188101403802d0002402545c05107002d41440c0d00a13205400401c0d2103550380d41d1030404200c3c0c080401c44a0254040d00b58107028042a038098140380c0200e20030a10b01501500540700101f903804919800030015042010500460001c150301031003100365940c403400a1512034003e4002c07008120302c1075203251801e034801e0140c0c440c650340114200048100d261a41511380c1c2c1544850a020303440c48000280191081c5250000d50107044000411410201d541c00d48895070100c00040a81c84401070080034a42c805000003045820f4050b43c4d41c41c1c001d01030a80c24614250400d0010082d4586101c400c089203401081c1007401581c0c90314030081e0192844030707140f1102e841070b01079000141300301c0304429052030b04410568007000c0c000c001180d9602c20901a110105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 555558183 1250 555556933 555556987
    0x1e090204080d020c0f0d0f110a0e19020f091014030a0204240e01050705010f0507050304031806080a0908160f0203120301050d020607020418080a0f030509100908 71
    0x4a0401c0c2e040d5414042071643d61070485801c140d942e40100020318441e240400580705588102c940b408104205c803c1502d100f001a00304410a5500c401c8241d0b1140202ca120340308010100b20b072504888a8800c5501148043c0380d9a414240c198060210540960000e00140301c11224159001b509800156124000c244000740e980c504040d000c0c500906006510a0044424401801c020782c01c100f2480451a013841c140d40c64001e541456405000302e2041030341c1180c6807509004400e903001d40110f208134000d40300c032001203041c580d082d03005401510540d80041c006a01248885540d500300640103402089024100180c2000702e8900c980c03c0c441c12509031420702c81f01c03011402c0620018094442045180303007558940800f040003a041e490000780710764400165807045564682c80786e521040d01c9074800c00a000a803a2854080e8041900031000c505001080e01c0149e12900525100306040400792184c0d525a2070050050141e291045500c15814003c000b0140c1d04c141c08a03d19031546 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 555559433 1250 555558183 555558193
    0x406081f080d0f090506072904030905181e1e0c040f06081905280c120614060703030b101e03020a1e020f010c020606120609071e09020408 61
    0x2c0015041505000d0440280a507040e020002e690300c2005440030f86030000910480c0c40b20350704810701003d0a502c1402d486480210a0105141d8060540700980341e080d601c45001504484039202070720003c55268550090726246003880c90f40020749281c101c030000101c1c0c6000c009108403142d152104551248a8042c00b0034208407140b100c4045900601b054213207031810382010b803142803640c2c841011100101c0d8686011900c541e020342d08070060300111652908284010200d01000380000014240016540c0c01d18031900c080580710b0103089031450000c842178100841d00740300b0b1503009250280d05150b548c01020142e0348855491002c3e26031103580f102c10b4207008240d00d5000c0d90490341c9910815105100d40f6100316040841d400c080c1042450034a05115005012403521a00612039940c42d400e140b203c054054001416a014000c00c8071403c00d005404050700c1c1d51054103e90918050307210150800c044817140000c6141082c007860b40307000d60b5031120503031820f9030700541c01001580c2c08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 555560683 1250 555559433 555559453
    0xd1220011a01050c0d080c070b07020a0303150b0d0e10060b030a060803040b030601052206050c0f42011205060708060310020c0106030b0a020c0d0807050406081f08 72
    0x880c1c060560415000d080c010300304510003001a980d080c5048851042c8101070000c01d14402c203d1090310a0740707900c10511615480d00000c025100d1005d89001c0b00801c1c00c108003110010b2294034003806982c00200700350304124107662680060f02050b0200b600074040d2100454944003680035840242841030340083d560304001611000703c1d882a031040c40c607a00140010f01c14241d41c0411242c21401c01d291058813202c00920002c0041c1c0c6a01200d4801400b0541c00912075400a000e04001071003801512441507007000c070030707458168031200384401c2e1591154035051200c0b0641c01e05200b0030340340e4101c050303c04003107a000b00d404000e8200517a400940303481c800810508002a5038058007500d00864030f82820808265147c030724100d1400001d03000f04103421b15940960003c1c00071034028442000c1da050010412000354081e05100791203002e800180d4800c6c3e80102d9450303005050960700c2e01d140c580341010403280c0320780c040c0199001c030010030003d41440b5403e82c404c50150446402521501d0702c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 555561933 1250 555560683 555560711
    0x1407050304150903050604020f010201020d05100906090b0901210c09090b06040c08040b0c0d02032406031b0d110c011512020d060e010b12060a051003020d122001 71
    0x54103a094410400d41c3d001c00e100103440412902c0c0c000b80e06441107800c944100d00140d01a0046400041c06503185c2000c124008610700101000c542e980d22013040480c0c4c6038078110017030300e0320803c2d11508070040800401c054020741400c040a18900f81e080300031a21140da401840b00c2a642c01401c130585c8801010041c408016017a68001c2c0c4e0842e800c0082c810200d030043c284000042025204003c84c0d030018020542c00c104441d01402c0514045541b450040e540c503100d00c07542c181a1200d680824118140c80c204101140d004400030103007030340040310315030351101560300002940081036110410000407554101c0074240072815180045040c0c2e400103001031407404954004210145180a05c2c409a1101c8600f42501c035001400420943c3c1d16100c6140034000c040a02900000c44044407508070760081a82e602800b46034030b080c03115403511822a00311f15190b020107540101002080400189850304a103003101c050b0034043c05500f40400003032403601c41c10304640390303594407002c030040016 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 555563183 1250 555561933 555561959
    0x3010905010b04150806031c05030405060901020301060203030103060903030b0d0311010b031c110c180403020c01023d02030901090b0a0c020a030f050405040501090c020f0c0618011407050304 84
    0x490452200b508040c80d010000303084084002c011002c4c800304501055651720148000301201200c102450b00ca04801c500c01052903104480c1030782c9900a050100e04208418021681207a03d15401107086909540701e80000304100802282850365548a0b11099240d1042030a0f84501907128150b5207940d0507445030a45507071030840c5100740c00441c0c2c88501100c0c00051048180100e1400041da04680e000b424070f04000166405c1e4001d02d100400c0c8071444010001c24481c0e03105e80c2c25200c03c0c1010707070010390b03030742e00b62041304c01c6401035080301c04241035a08c00031585c8072080084081d824641c1a2016030880e40255002110784c0d4545200c1000c1c04203042c001c0340c100780010020050010703e01002903e0350303401000202004590844150743c20700c6141550041c00c4020300030804e650b95019150000c0402c00d03034800140c001c1c40480c03107003084041109240b100c4054205803070a50803644940300d9001e805080381c180103d08041201c90790104000e8420107104c0c0004560f510308201c0421809 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 555564433 1250 555563183 555563189
    0xf010518100b011416060207110307090c020a020d080d06090608010e03130302040203060a090e1c050a021e030408070f060806150a0804060b060307031e11031621020301090501 77
    0x7007400c040618030282d07401070000050303a192490076515681644038400d00300d800e81c1c3d4040c00490010031003105018614242c40c420380c004404541d0002d85d58120340d400d070380d51043d801740541c020b6681e0001500f40020507441d032510036203005140036104072180044030150b0b00400c0816950740340502841d8800d00c03440400c2e00c0c03560021400c002d000b924802d10b0b86414080240a10b40100100b00d0644a80c24a1000b50406500501039400c460744000da41d02880b401e480304280c0c0c2041d4410b51240074100f04c42604220340c2c09006040800f0a20748405801410b03d401c451208000001e4501014041403000c1c22801001001080c9000d400518920340945941d10901202c0102c0910052003000c4403001c150314180042c6a076620700700f40700200342d6088515003042c000010030a20036455440340201e00510711004140401c0c00c1880c004451800d8564443c0c0a410404100e0001c19180d280c80c40d000b151412124002003207c10990a00401da00300c1e802a0700403006010b03a00c0d25002d12809 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 555565683 1250 555564433 555564463
    0x1270e0f121206040b030703020312030603010c031e0b150d1a040e03180a030b090c0103050a180b04050c060f0a090801091a152706030604120f020f010518 68
    0x2c0801104041100c40340203000c4a1041c0e944180010607034600b80000e00045030001c094801d9111b02004030602903000f01c69807403181d403078480c51101642c000e11591101d407250021365a0780c0000040350038028080a5032969200c0c8a0030105080724500c4c070000d0042e0848450086000251580000c0031000401103042c4201d0510f182c800d0340c03850000641c0c0303800ba40c40c1450711200c0303100004500004100d1b00003500440b51041040f071041e00c0013446411542080c1d9007040b00e079a1b6210140102e4407101001f0621f910504c001002141244480940050003101610101020180043e5151b4000a810034100d100031031f004d030b21603410060000c0248503090003440036917040d9442c6441c00e5404405520803c410f00041004074407820700da1121180064102c05601e041c01290b160005201402000241440c0740001c00314200419860300440e0302200d040380c070710200701d0709031900e1111040300400c52080041d05030342c0c0301090103018021441c002c8020503000240b00200d0030840c0c84500d03800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 555566933 1250 555565683 555565687
    0x6090a05061501080c130b0d0e10050f0105210109061b0804020a03170702040c18050a180e19030f0806040212070509060c03190318030801270e0f12 65
    0x80c0b0381d030001d640c954805084104a641d0f01d24110008201e0f607580c1d0003036408042d01145110041c0c501c1c0e40118864121070b03084545540140c143c103070544000311044540721128400400060600e0383d444a56501d9940c01c404000700300034240340c2164a0010103030350a684a6885200d0303c48000d104e06840c1d4960f20304400c00b460a42c0118034841c20601c8000d1403551990f0f11421440c0d100720581d0301301c039070080c001e0020b50300300e040c000d001b00c4a59141143c0203524a000043c0351a007160602d003203802c03441040140d400d000c070360f441c0102038105150409000f10011881c0013080740c0190b069491080d1a00c000d240000d00c4000c10003200105454080e6104004a540a0307810181c00d40d44111103152095a540580022804034060080c2e40ca0b140c0c40f0100702902c0714094404060a095900d5404200c8803440d08040701c00d000c43c200b0f0180114128100502041d44102101c0b40040c0003300d082400e2005955404205c42f071038210050960402c03000100014010300c01d2903c42c410041000e8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 555568183 1250 555566933 555566971
    0x1305041a041106090d0f030c060b060403020f0f060412061406090403050d0911030a050105091207020607030507020a32040b01090501180e07052503080403120e06090a0506 75
    0x403980044200b948190000305880e01140c0d00c11164031011940400304070211841072a0241c10a0100f0300100c4d883c50800c914020641005000d40d405c480c0c008110401c1c1014410500c58440488900550010b00401021811012001e03c01c50203600c03d29001076103034250050068a41405414148a0940d034021300001ca43d1210035100b4101d240603000480348110714040800720704003043c01c0e0b0980502a00c080134030006500441c461001c0c034061314003601140d445d2868038071030b012000398050390038403034800400d11440241000c01d02c060b10040302583c581d2000001e8124801401b03c462103203544ca460358411400f1002c159440035503007403007126502000a4120000e42c051701d4100807450340480194000e00e2076040050030081d01080c42410080c5000341650f1000c018201018140c1b080c0313224856280c801c9241f5503805544000842e240c0b55402c5461a01034078080602903154040011002414040341e40101e61000080842d0400d80c5042410980b0052075402800351512400b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 555569433 1250 555568183 555568193
    0x120702010504020904082a07170303040302030a080c0f0d06090c0305240d1b0510090f0b03130c09060f0b091f0203120705040314010e100e0c1305041a04 67
    0x866002035104050756103c40c08840a02c0145504110980c0c503207260122003021f059021484d00184c1e090800300032300d001c1040c03400959070311050720001e0040e0300402c010341426110b417184a401200c0b14420508d03111940c100641c550b00b09003801901c10740e80d00c204001d03400c0e0324410f80b421380700182002e01191509411062100c0380044104011518804018020350b444400c86500240c0c04040c811084015801c1480c2800d194040c1d2401415003414402c880760080c00300008aa9036094100561420600082226040503081c4a04440c1c1c81601900080d140100701000d040d0302e1400181c41843c0c0207021500b103950768881070103040208a403078455254401e640c0c0d440d07074001d192000c2580c84180304900c2c42c070890503a014451b0024090010460b4802c00034004c9038040d40407000303015240380045081f207e000451401d5648580070ba4500c868554000c0141010980160394a500001c80846c0c0b115040c401c0c90841c0322703500e5040000b0010038442038128941441603444507442e241c1d1f14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 555570683 1250 555569433 555569449
    0x1c0216080d33140f041404050c18010306090807050105041209120203060c09010e0a060c0b340908031b070603020f16110607080702040e010b0333010b12070201050402 73
    0x180181803c1c4150b100030190311514201e40316001c0c00340c020010899842c0380107980c400103542c1104c59011300d2168540c03910b05040030251801c880c40f4400b41c26440c5955440081516480c200e482d0041849204007140c428800ca80c820383c04be40c0300c4201301c60700e504004c281400300e8014201c1040341074403110241c0c07400114290700c8000307034015a40d1000d04a0044e10101415010180d2005c295040400e41c2d03a4801d40e03501d100e51250311402c42603283c0011840d02c40a18014614001c080c1528044d50883d40103007a020036900c0703040103c011622909202c0c1036922089008070181d5401941c040703082001c101410080050341340071411301d41c0c4070143c411280710b030b04444c00d65940070103000c00c107102c0f0a02d2002d400e114012300e0700750303031b100c040c42c02c0740030ba8122801c180c0c801d03031034a401958540d0040c000c212092200034041d0040000101410071100490500078002c1e150700451501c10101100001d0302900c040000191070350600030202000305e01c02005001164144070a00005844141c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 555571933 1250 555570683 555570689
    0x101a120d09030b09070f06020d1404180513022116150f020c040606080402010e090c0307050a090e071725051612051305061c0216080d33 60
    0x1405610344400304c8441c600300c0503402071092010a140300150650300054400c02c8101603480346100c1c03090703c0811060701d01031071088001010340c0c2800c3d04502100c540c08103a000250f0401e2841880b1290082242c2030740414074580340b440340d10201c078906c40c82000314031041c5055a082200c00ea08040ca041c084501809098042c0444d40041000f010300900c1000158100a401000380b10303642d100c01081580c1c10340742030b13000c03940212150f800f038205681031a100d125220205403030764a03038580071900da503c055443c00030002c0310400410f000b403200c20032500940c516651548400d804812076000080c01801c2d4140310741c0c804500840e0140c0b400526182d002c032034180741761a4224603a00c00c20745145040c3c0101201c886102040b00540c000010304800382c505030204051a40b20403c1c0032440c407031804001d004400002090107506156001089170402d141c842d00064103241c4e48019880d000b281080c0f00302503c88245400984400c03400c005100600c1d81e4002122040517002c03d01400680 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 555573183 1250 555571933 555571943
    0xd3b0109080d05040206040e040606050901060f0207050f190803180a0f15030e0316050c060c060109090203011508031c060b03040609080f070c0806070f0504120302101a120d0903 78
    0x41c3c0042c040d507481308142d40003441d1090310fa1038a0320306860580300a01080c056030344a00c4000c4001b040b4584503400d501042c08403600148043d0b400c1408000301c40d07084054581c1d1100d00d9000d02041100c1c0300004000408095004546503030981c070082a1940d90313110900c0c0652140081004240b207003e50000440307902c01031050385800c8904040707010f07002450800c03200e840b00042e840d0201500e08181030001e4001d00a807081e030200380041002d94845c500c8002855842480103002e0000940e0001d1220b0f880200001170515101106049405043d400291190004614410350b05000750314101e003048552410091a424012481c0580c040a4009040c569840044408120340c0100f102e586c415034030740280e03c4030117602e8080b0502e1018020030380203000749400300b1040c074020010008550101d443d0070342424209001d500700341e40240c1060b811445400c460850074010f82c841c441c40e0313082c0c10501038140182182480703080c40c9100909980c684c40600202801c80d400f0414106495100f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 555574433 1250 555573183 555573191
    0x20c070b03130606060e010e03010e0d03020c0102090405100306060504181209080708030d0f0606090501050a0e0a0905043507020a03050709021c0912050d3b0109080d 73
    0x42c42e200403042075201401401c1c03502e40311002c100140c10001074140108266916106c42c41c04074107050982c1c55120745c15000f54461513103c1038050003500034203c0051400001414203400c0c000240036950180d62440c4030003180d2505100b80034007406118082d240c00e403814050b03040b9414000c41854040c0304098401341d50045207843d40b500c14080c2e50020454081155050354607003e8458680e8040021441300b640b400c1c85a521811044c010381e0b00701d484984585440602d0000190350607030201256101f04910521622201d80c1da406aa9000d08003044000a09240614010181c85c10151310340c4003402184460350340d0003500005c00f10268210380318568564945201044183d41c0301e1304002c08a0081030000f10f007a000a0b40600419176035080060701c1d9580351140c080480e8614070001e00080d0040da91550418000c400a103042512100b0000b41010801080707030761500e8014542c40c42180f80035882c0400c808032070030041082e4601000b00301141d080d603601c00c640c1c890101e880e0001030b21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 555575539 1106 555574433 555574441
    0x1090f0906050f090c190302090702032506060803031323060a14011d1314010c02070303030c03020f0706050907030f060501050405070c032102040b04031103010f020c070b03 76
    0x48840106d2841d04580a00406002c0200b481007984010003030b05000010003441c0303a100822500348846540b9080c40c08600340e84041e4040049075106100b4004851342442c844800700364001c481507000750b15004014400628001006014005e15042007541c40540c2c0100340305941245800301d90f13030703260b0800740c10410444050030020b200c070304005282c001c1003104540c00240560010810344914505171400e641c0300d4209100181c0100d0001c008041d058010811070303600f40c0c101541440880d42900c4060b009184010b0207064039100843c0200009004104c0079580040641440c82198100180549402e00c251401540390000103403542d44181e1200003455815a120800402c003a00903102101d40c00c040180300f15801c01c4001400100c000c01440154400c0885242c411050410942102c0c214802c10a00d20300400c000482c0e800041040015a0040c105403512522 = true := by decide +kernel

theorem cover : BRFrame.Cov 555395683 555575539 := by
  have h0 := BRFrame.cov_init 555395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 555395683 ≤ n) (h2 : n < 555575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
