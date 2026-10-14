-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3756
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:29.612707+00:00
-- url     : https://prove2.me/submissions/9f9282d2-dbc9-4579-966e-892184256c81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 675359712 ≤ n < 675539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 675360962 1250 675359712 675359723
    0x617040b07030e01060509040c0303170907050d060f050106120b0406050303070f0309150512061e060d0b0405090a0c150c03032d0e071208120a020903160305060c04030f 74
    0x60311106014113000d440c00d5885260081c0d0404180002d101110007407005883c02606c46295a602c00101c0c082180320454451015030000c00050050b031800030760820a0601500000c5842c4903004e41d000225082a8040d001084403184c06030b160804070300400d4503a000c02c4608101d01894900403039140d114858000f0514400350101c10205070223600d804001d4001001000c1ea154030302240508254001700c203643c03074841c8060014260349050b0f80305840c2038541d030086180e852610030600c00143c019a82001c18107031100b00700d801c0303511244102031242e000e600040c000c075041401d01c024010a0b5800c50000850404c141010745500001380003405545841c00003601310002d844100a001d04c00300e6800300b03040410092503005003581062041620400a0715100c0b40d5035100c500d180d5900e100002c0059409000c81c00d407100c1301014250b807022441c2c0000d480d00c250500003a0401b5200031618014082049041c0107100042221551101b0306d50025440d250864403604054070290000a20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 675362212 1250 675360962 675360971
    0x102120f07051005040b060f060a2d091404090f0f11041a0306250e0a0506041e290d09061a010e03030301060f0c080f040605040617040b0703 62
    0x48480060341128260794101083e03440070008450824080c1905550a070b4440125402040c083d242500303440e17030200c00081a5030300d06103905109a4004151140003a80680784005e040100340c440c0410450300010b81d030743c0030002c0741000441c030380e01e1175001152400b0794507160784100010000301060b508103410203c1d50203107100d00e242070324030380c1898411150054202550a41501c4c07030820706a003002011026655155180e0100c910352403107214807917442d0700826101c160818010a03008000341e40c090031182c1801d13140c10125000f0703031041c0d2041203510b4203804038031b2100007000045000b50030a0b6400c041441482404008244140307051680d01c6d680025502c61214140d41c00280c1c400d40c002410b00001200075509294152030249181c00305003032034140b61107442c010049034140c92094844045511566204451154042d601144e15180401000c1c1c00642c00c407003d04001c140c10303500c65540381d0410034010000340350040a01d00700ca10742d409200c0003400e008000c66020040746030004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 675363462 1250 675362212 675362227
    0x1902012a080f1306031d0a0201020d052d0a1403010f090f0906140105041a0a030308040206130b0d0b0102011401032d050106090e0f0727050a05010807060c02010212 72
    0x1031489040048590b103da585000224150035400540302414103c44140001c2505a0426112546101c00900603040301c217184450038083e030003500c0c1001c00402d80c01884c1100b6540b5000340c0c805900b24074010240486c102c244954028100390789200141c2a460955143c172030000303111007440c0074100c4980c1c0c541c03004205100340c50f07004510306500014148003041c000c058581e001002030103031500540c206100c02c0c286400c004401e40e002d0101400c3c1040240ca1524115440c080c00f1f0f1040382d21060030400b011520300d18018403400307040403e440303d680e40301e440303a00c00494403840e000c41e0669040409110043c55980d80c0c440c1140e401c80b1094000c01c480e00884014124808810b81444400708a200d080c000150300880c2038860805081142d2050704007400d40c0c98841480c0310840d64040701040c0400b070b00740c9039081000c045401c169000200b0211180d026038600305e541c01500d541d281300420400d04104001e0b07009269509190b401c8a11030b8000035102c001c082d1256808020000307108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 675364712 1250 675363462 675363487
    0xe011a1215150301021804050106020d120903110609100b01080f070e0303090316030605070c050a120e06031602150c0f090303070501020307091403191209081902012a08 74
    0x81c401c0c030b00700800865903044120b40c1d01180d03050b4405070600032480d050000c05c99500006006c03000000c030784c90301c141e603107284103076240a4241040210704020031a0756641201c41d04010322802546081d016119048480c0030910454103030443c080e0402120406100c1e40200d24440360350004c0d01440c180b14034a1214006c02d20350300c0f40d003001c19018440ca115141d5124113000e03046043c0d0f4442c880500094541c01c41c200c4152489000181c0507400019903000000c2d240141e201003216542440c84500c42a0000109a60000ca4200e00d0030719485800d09025a070610004268106954100040e804c0074294503016002e403c452003051480000c4245041d5000c005a405007030380040290740e44d04d01144002c11103030043c42090340d00c4406444240c06da2030041b61150000200345a641c14040d0651039250541881d0080301080c018803e101007a2000144821010803604100341c44000d5180e04c00140040d07030451502020120035429182c00c0000189420b04694121904507201e0a115000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 675365962 1250 675364712 675364741
    0x60405060a032021090c0105040510090f0306092a12050c030f010222150e060d0906290d030e1f031a060315060310090e011a1215 57
    0x28908500301c04142031103448120000c0d00050413110281396060b84614480d9a076450800691502284003888140035a0074a40e2046511000d180360060b040c43d81e503070180c10054195082501c02d20b464100400611488045003141598840710041580b051004030401407142c0380a890307001c80c90160508240141000760034904a0010140e0320300100e0311140e41d000358040254203d05030f00240c520b032000081304800b00111040309403c6610302038114422989461b003580142c0d4000003d020003801115284204104540304610028082c05c06002c042c0c0d003000740c003c0b1044080380c403894030000d58960074040fa10b440d40c14180203030b4030303100b0000281624003441510159400b481b40010072007581901f16107800e171040a41e00a9800401d020f02c41b0740e00c811030790140c10092260b007000181c01e00400840e40301c038480d04000380032922100d04006869800d240c0c400181e45401002c410005041428184481c1c1101c6103184014121070b89a25101248c0101d040c03030501c000018145034402e0503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 675367212 1250 675365962 675366011
    0x71d01050417060421020706030b0135060402090a050402030403050c0f06010509070903111201021b10050a0b01090603111612031d0307140304030501060f090b060405060a03 76
    0x1582029064054180e850104440554240b60a4449084400645c06218201d81c01c940c0c06480e04a040c40701c290050700307440e0b4410381080003100c000c862600070450702c00540e860002229414040c0301195a03080240a0b0101d8441c2d0300c100042c02441c0e4948910b40110b4a040e1070146c0c03a0f17a035605040d50540a40040b003000d034015885c00100c100310100340f26043c2c1d513003140c52291f01d4845c08070803103280f5420702004102e107004204380089031411003491a90f40031441c00140c6450301500e102c04030840380f009007038030941c010b40681c3c04011711402195030008008000300011486100002d250700d500344142000e060b91541c40d001051300d00390031200c50403108600f2030401030349480c3c109180c0e0100712064000910b810700800e2503591202540c2d100c64001001103092085640720082d40c0841300f6140c01061100300300c0040010400e00600000f003590901c020302551820800b08203a07500c0b020202c1c0300f4402088240070b0399581000b07565200c4040c0c40d00142c0340600d080707560040da4000d030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 675368462 1250 675367212 675367229
    0x10090e07090917130306062304051b04081605030111030412030b0604231021140f041203050601022d1506011106130b04051005130c0509071d010504 65
    0x10340a4107000110708124201c1e4400c1c0d104204282da00d140200b02820202c00300000d00040b200422380784d150075041143c009808107440e41d140000c14030035004541c030a61202c08281c001c0c900707440b00c1040400700c107030042034180d000f03001d610079484101c400e910008200801500011111154551007039211101c150406820350759607a4490000c10071114500d01451051105200c8040e07042c00c2c04100617400e070006403120342c1d203030b03034800382021045101c0d07240901125070350030a2500039070203c0d1606014403600256203105003081e05041c14448182c1008205160910302480038990380001c1416108000503076681d1034400b84413203240104600c5600e0b82c0c492041c00c2c4032021440803110303000d002e200300f6280e49030400c480c80354540e00d90100300c0c0e04e40400f590721041c0e0070208071100d030200d80c031900c50801c0d070701861a800000d8003110402d03a940e5283e42c00c0c48000008110940c3d03140303805460201c824008600e48120010f14110340c100c0e0b0500f000b290070462520310b90241c41664003070840c52 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 675369712 1250 675368462 675368467
    0x604080307031518270b0103031209060227061908070c0f03031406040b13090c12050303040b070e062703031803070f03020306072304090510090e07090917 68
    0xb60301ca00c05400c104501800e02e1100c0c100450840c1e02c142900f420f06030744451302d2410b50703207161815620600000400c041e0301d52900c204200042c214402822201840d92000c0c0c0d41c140e103031a1494640c0314033b0340c1c240e0150303404119100d52512102e0048030182181d04c0c0a400681e1140c40c2211000314841009020b04040852442019055000000191410b4060b51400e81e02d030010001075444910b407407604182e01d0060145442e80d65001107040a00036034240510503500da500c0c14421000e60340954903500044180020008110803007030b00056a840e1143d0300e49c6095000031340780d1040c02550020030043d16902c0d100100e071103c5000000d880241965101c09045103040d40480c0c071007070307200d100c0c1c0a03410700455410410304404080e0ba4015006141d159180182a5040d840323000c1410400c540306002104600d440800800c098900c110010540d818185901d0f1584109500710040d801d083c4038000f9524000001c0c40d0084a882c42d001203524520380c1050144520005624070744c80c00c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 675370962 1250 675369712 675369749
    0x310b040f080304150b0109060c06090627051c0e090402040f0c0917010509070b07050312270c240c030a0c02150901080412030e010e060703060806040803070315 70
    0x2c00013001c0d280c46058800b484010311020045900c80042e00840012944065a0310003144480d44810f0071240700303101c0020000707882c010741060407101d08500c4161b41110368050003000000c0c1300002c50000742c2100302d480600b9103280501031640044800e4040c560600001d03055554542082d80380c52000b20040151a20b660342c01030108140780035002200e09107917042410404140300c1e2500c910204130192111901f007a80b04104c0d60300840f000d50301403000748202c40c56071440d0030880e4040c0d05440001c0000480903809580d8405800180c1d1903d50013400158020341c131040d401c2d4480c80d00d20112a1446460800a500c49006180300005948804205903000c1764000650810078ad000312451200c2c0c40502a041c030592050005039800a4141004500051010340c4490300000f810700f07011514040c524141801c440c007000995980b030b0711101c00e12100c00e416105480c00f40c500c04018140354600780d00c55428520020702440201030740c924045240400d8200c203d8007503c804460444040745 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 675372212 1250 675370962 675370973
    0x11701080c030d1706190b0406020337110106030b0f01081204080309060d020f071109090109083a060f27050405190803310b040f080304 60
    0x32a92103640c002e110b00c00605200b0f0b4001c0c4140b0a07440243d210940d8980c0e1802c0c02c0c440d100c070309000360b00c0c4c2003c410000810082440b43c054009000960b000b10380741e040d44c449007214055a1010094101c1b0008060514204070008000d94070506007021121003018a14050040c00640c0c40504024140c0042c090315614040e0294122402c150890303c04c40b60400d44402c803840741c1d100704030250b40100302c001858103016003d850402e500440060600d49002c1e0485500c1c0d1000b001120b10700f220705017084040c0340c030720180c541100c402c7d4000c0040c1ca009684a44240c4641da8484d41740c0c641c00c12411403084401000c0f48030408140351080c161032a1098100040c21050242d4455000101c1020602114514540c516240c6902c962800600c101041d20010b00d40988141c0e181e014104407007106c03440903c01440b00d1449801100c0d07681c58007540c1211f40000d50740c0300340000b03201d800e140c44c0c004890300c0340480c10603041800300409031214071700101d5004003400c1c000c0c031801c0080104402d101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 675373462 1250 675372212 675372223
    0x504020714010b3a120305091c0e010e031c02150603010c09031b0e280902220207021008150a08100c11030d0b0315040b1501170108 58
    0x240690090003440784950810518048030001c83e800550401d42c20222080c0b0041404c9007500c500b0240880c2c1000c0b911303103290100882c805540070a49034018400c01487c1042801004201856000a220954800200300000c0d0b101140d041019209244c540e9540511a80f04002804808001c03c400c21000c00380d21580c49580c1c60140c200e05600040d501d05041c0140c01c0200c0b003941d82d04071194215030310071900842081805d810303032800c01c601182c028400b50901d40500b0111280002040c60300003c580144c010b042c400031818100f080060060b01c40307040e550307a60411000010058070018800000a015651b400707580300340100e2209420a0300a640d083c02a19050aa501d0341c034000800d0254902c1c05200b60041030f4000040c000b01c421031940301220680d0a49032012403602411001407079038111101c242090303950b0703080d1081d55283c00c100314a080c81103107094900c2c40c80d0680300c41360140c0009110103060300c946002e801c102e80c8542c01c00c405813111880018984d50b159000c0c26a2503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 675374712 1250 675373462 675373493
    0x5220515090903091c320f071212050c0d080a0c110d030b0a0515031e191e020c010c020d0c0c03170702060406020c190e0406050c0405040207 62
    0x1081c04001107440d0440c0407040f00d0514801500002c4011014420131168001001c07050301c1042514403600341c61084448100d80f0350301c854440e440080030400c0300f82d00380403699204910fa0303404101e04102c4994440d17941500d8580090700302c2000d480880090320140300d000d0106640e80101d01e40003030080c0d001740c2da41d03025034103203c410851404110015540707040b0b40c030b6146400341e010303410742d4206030310a422141200c1000380c5603103010f560316404103069260300d41507803d0000c008400c10619200d9400c1c1c10b070152a44125000450400041c0e005001e4003500b045c03d80750742c45404522103903107543e19008140c040c5000840d500c0511105241c0280100d61404005024210034403900c18460316200c00e0240e040b10000c050940f8555544021080624030030f503114606001e6a8096911480908000d00d070035000f50603178241d0f0108210a5001c000c0020341030075071104e420700118055a6015030f0007940582c000820b40c60b81c400018090085a014980c0300b400003a4101c00c0149003000c8a024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 675375962 1250 675374712 675374719
    0x6030c06030618020a05070f020a080a111206060d17040b03041101031a15031b1216020304030b0a1d0106080106050f09090d1b0203030a170a0c050405220515 69
    0x1100028070750404d80c0300748800e00b00082c405008000c04110702c8000103800a100410318443c2581e50f81040342041c10a2509031110440715400c21551300f130a03031003101d28001510240000c1e20300000083c18894841002510b44041d52004082e84101075040f10060992602d400e40c482c1307010b16002d030041d00e5800140d40000d040c8045055180303801da47c0d00d03040000080968464480b40d42c44082c840d00014290003c0204040d44d440100c0e40c000010000381c41c400c0b81c1e4071810b1904002403058403104462280855204000400105900d0300c25143c0000d52180301041c451040d54200162103001c1c1d01c100c03565442e02c3c4000a05000540c814001c481d81500c0320f606004481c001c01c0040030040710400059042420141d1049102e404d524041c000342c01e6400180e034240c0d0b00420302d1038014050000102d052820035050440c120760b0b40a501010040041c000a4290400140180101c1c45a54060b02040c2540303101d25011008148680d4007045007009145040811100c9800b0800d41e00d502 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 675377212 1250 675375962 675375989
    0x1603140c010912061532090115020106051c05060c07030e010509180108010e0c0102010203040c032a0b07060b100c020108100e09070509061f080601030209061b010f0e15040606030c060306 82
    0x80d04200c24120546c484000e280401c01d0f86408090307034110240316591000c41d542c545c0c001c62503680c0c4140082a040c0090030442e840308003890300031b240c200003600b070845000041c0b14260029500c40c812404409081c601140c443c0000b1010139420807454110b60a052261400800c0021381544503c0d403003a06681201c48248500006908078401580c0150084139010410b00c0820a04907013806003032014001d0050000368420f07425003030003ca401400311840d0010384030082c0101405a1201e11400b1541e40b07455101400c0040d1a40b0140701b4024140b000c62400280c81e0420f00c400c03000200030780d2003400d9281c5026500103460f1042c1d4043c0034072070380440020590900784094503048050300d2803040e4240b003140820588200da001450141056002c003c081c030151140405003800044140140d0f524081490101d0700707403190f0703080200e10140743c815010200140041d4110340b03404558440d03815a1294140100130300200c0d00042c0051a4000300018810352540c0110f048135542c010f1142c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 675378462 1250 675377212 675377279
    0x9041e1407030b010c0609030207050607030e09010605040e13052104031b06050d11040b070b0601031d030a03020d0e0105010e16081006201603140c0109120615 70
    0x20210380107419420300040951280e500080e809902042087e0302900407254a2942c0e0342c002131140d881982c00301c00180a40044040504062604501420040c1801b81c02c0ca41032443c1001024402401001030400341d034018010f0100038044260030800c01101202000b007078003141025640248001c40740d04251410030301d4622080c402005c10f480c0e19a581d6403400d0100c3c04150302401103242d070011216010000050700301840300013020624410000c00c200351812500140880d00c0c240305000ba60003403450760004408011080740c66000141c01c0060b04c1e080160140340c01080210740021042d0318010001c218948011b040c10309c01c1440c030449445061500c5000c880c072100030349a2040b4a004407800f40411800750a44c001c4051601900b0080c1d09100780b8004d14010b880c071601581036052503402d00601c0010300e00000c0482c51800100f41c0041c40301c00007400b40c0320034829546802e0311108007200b00a02a003040b480409000841e584003a00c80300501041e59406440340c0c0045080700403503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 675379712 1250 675378462 675378467
    0x71b2a120b1302010507290106091502070602120d0f061d010b09030c27010b0307030c030605030c0d140f071401030902030c090c040f0e041b080a060209041e1407 71
    0x4038442c0354103a44240c10040c030f90b0380d080081d0021144519955102820b600280010070400c01e00070f20f12561103460480c64480c4a08075000640c8403107003103421000b0140b0100341c00044103000b00244d0301c60a81d440c903c890f01c01009050f00421000000d00303040000455038030011030b55075802e803208003640346a40c0c2c2c3c0304200c95901c80c411130640c0541141e10400301c2131a01d4441c400c00030050040c404c805c8911007c101d1300c114003d81040e1110200402401203079a41031050309000c001a08041200c2400c1000281e660f800120030241704071101d01500040262641070283c0b0392001c03004507030198440d0000a07407070f0384403401190400900d060310342c145507110b80100c0d004c568000c1d01030984604820f0900030404c3c001052010480c1d000c200000d08a80a4002000202100079813604141498900340403000b101c3c45c500b907d0300c40450828068200080ba80d080c94590260300181d440181c840401c003d420900411202844014450701550701c5035000002056407219080d203090b907641c0e905 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 675380962 1250 675379712 675379741
    0x41a060a0609090207080f1908010f0e0f2503091a04081e0c0d0905030d0503010f06080a1b030b0420070209101703040e071b2a120b 58
    0xa010000c2d1040104001c42c4000340c0c020101c1c203004a459a2402e5014000281e180d4407404c610300c1c00507000000c808030703254003045003805490100107241380245000c0440304141c402604200d148564400441e0840d0303481c0002000345105520f0034000395006c50809401007a00b210151042030b0064144890301c07228140c0240b0456103d080c981c04c1c02d0f0065071003980840c444145c095a22000c10840c142c0d15800c100c28107103030b034160756881c80c41800d000034581885000414102889401d0006001e0003c0b00d03840c07002a2145441d056074244d82c0e0b080d6981c042c118400801183c3c0851751081820a03a158001c205a54001d07038051000081c02c400e01d5243e100c0c441c91100d500081804a00010b142020056400400f222060702206480300540d00f5110480e00c3c0404d099840042c0c20408102c80140566000140d800c2c070b00000940b28140c0300c5c008900b880001d00048510405580711226442d10405854070b5400700589291101e0001d00340e984030400545106415078001024514010300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 675382212 1250 675380962 675380969
    0x501050301020405061b100f0c030f0e0a0f08090612060321031b04030c120b090c03060c09010c1b05031b0a271103060f0319020108090c0306041a060a 66
    0x18451030006e103c100c11403000040b290b413084600901ca007036101d2801d80d01840108280035440000c09841c10760000d0119240c800c0e814010504180b0b904011030008100101d01c181c1040004143c58250701e44034005200f07000c120790340960040780100c60741c040c0303c03800d520681040c1c0c12a50f0340c0d10030010340c3d0803881c0c1c284060850004100001110110140705451701581301b0a80d850602c1e4407944c03205000d24040c0c2103180c990002c3d00f10941401150300685810815510152642071140c00c00701e516140c0082c81110381e110009001111740e442035003082480c0741c002080b0861a6900c00b040010307850381c2e1042ca07100303100d10364000542e4904540310400b8484010311080c1103c1ca404040e0f2842480d046513188a041e01210400f100e07402406050400040481600e076286042820450030100030410140a98400150150b040380072105417000d02c1d0302403d00124598030380b50700c2c5203840c945058032901802a1818801045200c2d0f0f020402418000388900c041d90300c2c8024404a403244c2e10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 675383462 1250 675382212 675382219
    0xf020c031209010c02040915290d0f050a03090807080d0207140301090218040c0e091f0e0706020f070e07091e1a0d0606020106060f050d0e06040b0106030501050301020405 75
    0x42580740114000e1181074018103000050820903000142281e1030b03050f0a40d50040c1c40804200c6035001c0b886400002010040003209182210059102c0000240c00381d83c050074a0b0020b080030b01c122a070030141d4840e401002c5801100c10361a00070403882c164400d01c4101d03c151031001c100743c0000b281078450964107034024055207103060511a00d070034000c40c1c10760301075603649102c13800b503220080301084941c640c8075407a030b2070300300b600c1e1170301e00d480c82a403010301449007000521691203030200d111542081c007101c9428031007403805501c000170804580490f10310304c2880350006983e0b80101301040b0703003044c00c02075a050a541c0e221425150808941c1800040c500045c1070042810300800d80d0001009a00c4a103070158540e60f0306481c5680d204000011400c0102d52134605521b5401580c0291415100174006107150420141c036850209103010b007840008588594005000d0784004006a070200807100c43c0e003001c4c01c199018031404e004101c0001c0c10000045601d050500031281140d01c0078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 675384712 1250 675383462 675383473
    0x19030609050f032134080601050a08060d0611041502060c030103020a0302091306020412141b0f0303090a09050402030609190b190501090204170c06120601020307051902010f020c03 79
    0x1407040300c2070680c0043c00d083d40c5443c3c90709480301c0c940c140713001d03500c0d404171105004441068142001c3d00c40c0000801c00c03410042c0400c60703044910340c05100107401010540d0684008441440c051010302558280440040401f01d800103d03000344c1d000e01d4004280d69000c0e22169181c120b80034910344001d00019404c03826a81d001c00040c01c040044603800284650605a058203642d12a4181da000b944200ca05a244c1c5401c9418000315420060106960300020078800482007022444141c1c02c0701d5161283c41c04c103190348150f49051003200d5070740b1401404400041e4880400740020b04050300d0590180c410750000074079194001801001d40e0710100219106200b950359000c0074003c00800180ea058560421850408140d000d650701900301890003503103030313402d004c0404808010390118140a03440060421442d880f0790044800754a41c50b407a908450380d03481c0041c1e00e0740c450700b84002d24600c10311184620302028041c000c1d00300c074402d90701c82e8001401240f040b6983c140c1c0c0682c459254110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 675385962 1250 675384712 675384757
    0x181303050f0c250806040507061d03120703030e0607021c0525060c141e0903060c070606062d030e0703051b060a050d090219030609050f03 61
    0x181000c0c1c102600280d2109140085101c501c034140b40903540d032400500c86100801c030040081c8204031001d003540000602c49840c01d03071101595041544a090300780705102d10003141d282d2483c125016030140c00390455414070301e00380480c56950b10140c016400207150080c46158204082407090181810340c2c0100051403007460366041c5000c4014815091107070800414030100c102424100015022008010f1070580c0c60500d81c0544281e00074035020422811221000058508255071252409204c0d40306164010b41c042c0354181f240d50a0035515215500401c4541c250030700c01008154850b00048c0b20655a40c5020703100b00c82e130300300d419100718003245900000306201c0355040104101c0d8a40821000009142a410003007240c00598040d040700c6a54030354001008000c803d103610035980289400d083d030400500a0007140045031181da16005c02c1025955040102501003190310044000e02d0340d203140c202c00038410100304541030300400104503202403010003030703e2414101c105283c0d01300c5003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 675387212 1250 675385962 675385967
    0x3030a05060402120c0a0e040e1f0603060203131e080301060c15050c1216080408030a06090c0e1002060708131514041406010303020d030c05190905181303 68
    0x100140110b4126501380f085401e410400400e541c0150b000c509010380d15180e52034028818410141c2080c000d47c1440c90028000c2750000d6009041c41a1050020061241e800b4040103071541d41e002038480e038004414094500d10004881c08054481c80b0114420801c00e0603c004140c00c409002c1d095603000e02c01000f1440c001d5144002462240c040c6500e282901004482150001c0ea82000d200c1030100b0b03040700b140c9101402e907410101428201d082c2d0403880c100240400c4004000400103940800421241440d941011001e40980c010501c00c41000d42c030010461091031541d00d20400040303a041c2c1d50700340003081c03e5005000326541c1d1640e566803a01d0040c440314a07601308031904111041c04031424065403007801600442e044010030141028103000c804000c20424003003650300003400400020381c0016064210742040c0c24085081190343d08245c070726024100900340540b480d45d170b20204403684460321174180d40b421a011480c041031680c080740740400031500f1141d08004612032802190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 675388462 1250 675387212 675387221
    0x40501291908101d2d04061505122d070803030a0c0e030c01032313261204020411070302011401090e070509090703210e010309050604031d0622050609010203030a 71
    0x30ba195443c5e000948540303082c00c00b004440a03140c2c560b50729050f80c0b0501a01120100500c0304807014002c15074480d80e025181c001042d40340e01169a0f12f800d02e40ca41051140320144034a8a100380c852030790b59104d4158580d0b0044a8020344249440107900c09940150207029442002030001c1c21122005001980180110084d141104201c00c40b40c03603c4903001852907105800e00c0410224101440c909a14042c03044040114080c1a82c0c817000c6010704071720103840c0441400c0352882c3c210346690020070003c0540c00340081800c6800100f0406050301504076118444040095501c0c1d030780e0b035480c0c040032034144084805054000c0c4000b00810b00e40760001300d4000d00c0b440c055400107540c0e584e03003627000003030307034242d00c680e4840b065079000f030103800810b0b000c4c44101c282400d21000300c03196605601c0c1c5030b00900080620680ca035480304400f00c2240c04005180e0301400d00b658410040035241a40c034003480c00000280070305030010404d0701303102c0b0075180800c0042c2c0007035046031030711000d500291 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 675389712 1250 675388462 675388501
    0x305160f03020f1b0f060f070324120228090207141e100207030e0d06060305030a0315050312070816080f04090506040501291908101d 59
    0x142c0a00c2503010250b205402010210341c0000305000000c04000503604100d000485440c0d50b4201600704140919100c0c0030585c000c1d02450005501c0c0341c08000e0308180b00b45011a2403410b084a01d0110b52500868480425240201c82801001580034084528200031142c052444003015204101250854015101c0c0c01d01c41d00d800f01c9000020f1a079a8030703040d050307400040080c00f0161061900d18041c803c42003440e0218500303500d40003050310080c0080741c0c0e0307109150048100e201107400f407003180d034802c0d000380d644403040d60340e02c800b1034800402901c8000c0c2803420f5101c902d880010f99150014900540004010b002420002180c8070642550001c510740860b0481c0009580001600540106175008143d2880da4840303041c850003004440c00100454040c40ca00300c010b0100b96007444402d402c506518154001c0c888001490b40e10324003c2008401100d08a44e1003010080d80060f07000f0b01c60704c1000c0c5402074066642860f602c00000502803001d000c2040004141d0b00b19a00c0c020700e501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 675390962 1250 675389712 675389717
    0xf0b0a0f0b01051605070512060f1024022a0a0f080c0907092c06010507050a060b0d0812060907020a0804060806010c24060f1a0d0b03030f0315010305160f 68
    0xc0300da98101046845010788e4050350345d6000340c1c0400400300c1445080a0f0042e00749403200301d41070309007004132011518070040c4986c2070003007002c8440500c4c07081003c80c50068402e024010507842c03180b022007190360400c0016204164101000c00c07081c200541c410704407440bc4000b054002803020500c2012080500500d04000040d900841c41080745810700c2400d00001c0395403190f904084102c0b07400014007512050410004110220219030001000d10306250407960000c2c058008400081140c421000000e0452a010880c00001e442c0e200c002440307050295220032003a034070000101e807154851517004002200034030041c00340610421016a0144060412240e07800c12500c441c00d030b5500c950321a4910585802640340b0704015070049500810004d0000c840080c100100505903010018800c0605000412203403803040c1c1c07035044140c240c1e80180699940d94a420041c0e0001d500443d0040e107000b440e05078240b2036500c2445001d2188800079540424000d0289088514810701003070a0708 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 675392212 1250 675390962 675390973
    0x2040b220e0a20030c0f01020309040c051c1508070b1b030d0f091b26010b041b0e06090609011b5a0f0f0b0a0f0b01051605 54
    0xb942c5034800b0080800400c070030f242c0300d4010400301860800f40003021809030070380040d503152a0341c00005560003588222030100f000b000100741140d083c051031440c0003a103460444082400342596110b0803004006c000c2010382c4c2601d1b03402c41d507510000340c4110112140100142e40c841c6c4007a00100d21040040402c0d80d01c1c040c86c030401281601c0a10f41d0000109907644200420001c1010310720022119008a40c480c9a00d40560109155008000c001c6580825a401d16000000f984099011395004004104003686180800d19410049841c64041845040c9509841c940301c8140e4042003801400140307012460401122074040100400c01070108000801c070000d8041450fa031008501520540041c0807503880030343d600c00214001d20046511005102100501c8100a031006544105803001507900c0386096020625100c401410161000608404000c0340e03160040c000c07040c0c080184619041103585404807000c942c44203011030001c02292401154940c0621034650180c07090310b4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 675393462 1250 675392212 675392233
    0x30909050f060d060f1104180605091f050d120206010b190507050109020d050c010906080f0402120a1209090b060901090302130e0604050303040b07020f150a02220302040b220e 77
    0x1010b8031b07890710030004c000c540072509001c0045402400d001c1c103c400f103414020280360001080c2c136000044c0500c180010200f460b40c5110025141120003040c014003d50420080c0303041401216204c5641c3d41d0050041200006101002405492031034000560050b001c0f1800e4809640b1a40a24001c075519500d98010401594545e04a40a60342c09900038000307203180c810004202d00c040d50000303402d00c07907100305000f800309001c0740c03c5501a6064850648640a4280107480c26144c114010141e21008920031000b90707010100108403107403141c081c05000f80f000c04001150042050640c00603c21110030000340c58864441d5034454030201d800210000000c480c1c50070042c0895050b600c1c0d9000000b84801c000000944a80c046030a10141c00c00c1640c01021584a01d00c4d5018030704580340490204192a6441d4112088018030011004520154000c2001015401c0c4001da204034500010031000307040408030013100c468200600c41a5200c1a40418000c0600203151442c0344180c4040c1c2c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 675394712 1250 675393462 675393491
    0x10f09090513020103050a02120a05060d0f0c26100b13110c06012709110405150a05060c1011040b0c150a090b0103020603070e1c030909050f060d06 65
    0x40e01404030300c07000d890b00e40c0340307400090190b83c3e010b84018040740c410061801c001c01020f1100b078102c440b00002280c41c0d02d50500250a400d4607400107400a01c4510308802004004d001c0c103c1114800c00e2214101c101564020381c40c40d010034440c5903140c0115031002c2c0c0c03669040d40301c0c104000005194a1a0039100007028044070f00d174045160701c48100003000b03240d00408111403801010b005445201ca4508003850b4210643c0c9842d24030007850721119880c080124101c48502064805441001369240402e02c040800c030345440054060310b00e1000106071410f0120440c1d41e00391400d4010400b9040441032140200840c5000410950f000c0c000803550050f44002403182c401004000c01100b84034050003040d014000d80511580c0345007040600c00501030345040ca04403901214850303102d43c5c17484401d6440c24100403041354048004032003084002c00c0c205036504403a009540b0300e082c240d1901040d0341100c030141e07414104150002c000805d1440e00c00308000c003251054030003050403140034103107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 675395962 1250 675394712 675394721
    0x804061b0207030501061e0b131d18010b0604051c050706030b0127030809120a0302010e0f030310030f03120501080a0201032d050a0914030702011704030e010f0909 72
    0x80c0060b0004103040091000034001d04000d00071040040c00200c807004d00340088404184929100d00001050140307030440c18107d100010305603480c1622880d804508a0a00c802c01254a00051442c2460b050740700c000c14440c078601e80b800035040341d162130701301410840e4001e142c8111400003070b100344416001450a2290f400108503a07107000c260114140000751074800794803018010180307941480550300000611031003ca039000908299a4800c140100355540c80d42005440d180c0300b0700c00e2050405505503c40c0495444d140709071040410700c54070f03c1d601c0b0b100940345000c182841440a0002c10400c945420b001c0d403003800c10081d11a04245004240e03a0300340d002804a400c520000300c15940c150246140540141441000070484074294200f120051011112100e503a000007800e25003c503401401d800f5000300680305003c40900400782d070f0746e000d407070201d00041c5891650200e080c08420014021a49034440301c1800030702a00440745066600103000401c0449180002c0c90356540c880c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 675397212 1250 675395962 675396011
    0xf1c050f0a06050606070305040e0a090203340503060105093c0601260c0f040801021c0603050d03090c0e010611150129071e0b0912030601080406 64
    0x3801e21000c0740e09006040340c0c00103016500a107420031510000a600c801168180c1d01864a1160310f602d4540180d03000304a1410300035014850b85116002ca44100d2918000d800342d02c0021301240a03503c0d40038003903c01280b0440ba0980d0100005201c1d524040c10401c1e0311545005c8540e0698219940d500c5540446820b601040540c075400c009200030b011699030381c010340c282821440c101e400c074500804564005100910444080045002008107400300c40b480c02488121546950711484510b001398069012520402d030b141542802d0050b80c0d000f000102c98000000d0003805a8910042e801760001c0c21013110b41c40744a001c08141328420340c1e00240a03200c03a40d902034200d49881c003d2898806d407a0f41e80d021108402004000c0c0310381c1c2c00216103c0c859541d00015036500c8000c02075500c0d0142d4840104143d1000268205102e03034a0184030b100340c05158002d1003602c54000460b2601d03c00d69062002407410030000e42c895000d07012494105106441c0052034100c05940c0c140d664141c3e44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 675398462 1250 675397212 675397243
    0x605250819081f0608060f090a1d010606092c010303050d150e190e0d020a02030d0c030509010c081306081905090303012702070501020a0813020f1c05 66
    0x3500e550105a00c66415075000344180007042c403180d480e8210001c851401e01c644130820503400c2c001029030315420115502610040e000300d899040100305000031341007502e250380001c8500b904164500c030381405a007040381d4403074641c0491070b42414031455001126040c40b141e10340000e20801669504810301900840c000c0d901c01d51034000042d0740d40150303141490083e0640c414114140103603068020a140c100719040002030415480d06010005000c2c800403201c81c901800d056030040540119800c03440b28800c9081e12401d2508400a6402400b0320001a00042d0103200031100342d401a03a0303c03803545001e0b55071181421902070100980083c550413840c0004d04040c1030100845149902d100300451201c002d10441c0f40490400e40c0c0c0340014407400303810710765410002001c841c880c40400c3c10b82624002c03d42d511200350034400d01030350042c003500c0001604080003c46640980b00500a02c560041440d65504000c1d000c021000e1000114103110303000d00c243d0380d80010010480084141d1028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 675399712 1250 675398462 675398497
    0x140a320c1615050a0504020a05040c020f0f010c0f1e0507030e03030d1d0307050c0603060103020403050a030503160503160c0c090c0801050a0611063108030f09010606052508 76
    0x3201d51005960b806132940c0c1c10941820188001a51542564000e0715020b80700019100300c6c200302240740050341e031800d800c2c500915900103511041900703e0070380c00605480c0c4003120001d12000b21200500f050300f1001c0501c40c1c190404d141c4c1d1042e030003841018020314008008000200c002410356002201c1018070581e541d8010006540b40b80c0d07046042080900550b081c040f0b161101e64498140e4020103100304c3d00000040da2582c000d506071005035400004848109a491a003e0050f51059a1088800c1c2160a44086092003a81203903c0388180c415840c400400401c1d05580e0a80b60f203c0031aa06950b4040214400c24203104a20010302181e0b42e204942d45070000740210561203421090401924101c81c400395200052065002a000c01c2c203c0d08009850882d100c40c1802c1c6c5034031458201454185c2d000b48500ca9001e5805910b03420026945611800d10150803240e041c802c2e01c010078000c0c0b0900c00d01050508010140270645c001e004502400b598805120707512141a2140d650101e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 675400962 1250 675399712 675399743
    0x206072a0b1e0706060905042607030c0f170a020c130b010206010605160b041a0906012601020f03090718090b0a09050c04140a320c16 59
    0x400340000c01815407400d003070314048840d204040310340014902d281c2160000190b10080059542c0103800521001d00100404e00f0b00c2e10b06032000c00b500040301c841200b8541c000344000e0503000200c3c0c520517031503180c5440380d945d2540d41140400c506082035a1158030065480d2000d00072400034040e14007036501425002220200f0080020003140c4d4203043c0302c0c5030440d03e22070303a43c001072102e054840c1410165100c002e010b0891004200089001b007950401500344010404c107102008132a0f50404401d0306150f50301180503584010034410791020880c40080100f2100c50b0007800450354008500142c582030900b01c080c440d80d4800c1d11040c1556111081c00c00c150780305100180d48007401868140303c003540d01d49940c10a40c3c4c0280602e155641d17106820710421100b0030900c1850310303000c3d01c107100000c603015051030b019508452800b92641442a08240d011031240018560384800960806540d80044840201d480050080d46801d00c10030250114950340040642503501c81c500d180c0c4001403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 675402212 1250 675400962 675401033
    0x7030e06150111070e0c0705120f0301030c090216060e03040f080d030e061302040b0a0509150901080c0306040b130812191109010e01021014090c060f0a0309020607 72
    0xc0301000f20010b6000401309028074035444511a801c842c1444443d0703154002801c01600306500d080d4440c940e01800640c001a0305650000b0f1412070f8043d041360b81903375907141c080071300f81d11a54000c5900311004101400c0080c00c15880f544010840004a078240f60f1a2101d01d520b001044d00582c02c194040400c0c402090b5143c010041e6000450300a881241000100c15250b1240d190000b4404c07a1100c076411940c0e241c03003401f500185070040c000c0525050500300c1c2c80f038031045100758a000325043c1c0004038414900091030401c040d0050014542d940c0d41d926040c000850107407820306806040c845a50105940d4405030400d100100c600c40035908054504e8905c3c074110384c4182a01c00d00b8008001c4500d0410800c0c2c40e410b074820f0034160700007002540100c2c101035001d404200040e107000ca9035006030b2a40f010585c0300d80350070012580c0a01401003040300034010494100c0c0c5001003041400d021510a0700300140c86072001d0040d6040c641960b54501c010000030303601c0c10030301a5058807682c5a10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 675403462 1250 675402212 675402227
    0x310090b060f0d1509060524011d0402090406080703050d02010c0f050a0302130e07020a1104050f06060f040911090405060904030207150203160c06021213060807030e061501 76
    0x1004032501e11044814074042900000014005008824490980c04048401d03402840f14203038070131400c2086160580080c2000700e050036104000c9230007a5503240555014210212503200c904400d141413880c16410400694044000c0c950065120080003504810401032000618030800242103e0244080020f0849501e07000e400c00f0000147d02d001c20054001c0c0403189c005a10b07240140e5110345920ba400c641901603030040094818000c1080310b140d0340442e4a0000d98403528541c0c2046010008100599100b5030b01600b1814031000458450714001000b401814000c140e050308150743c0300da490044450f030152034405260700060302c1d0b641d440d142c03040590000007202c20356110300b82910003e503941458010a80c001c0503860000720858020070545400c10045800802c14078075900c4c0c1801c5004083c841c0000bd0304c0744a1840311803c00c020b041e01c850740991a880c00c04c3e6450014200e40c803e02c040c000a0905565404801190501340042c0e4814440c01040745001c149000004100310b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 675404712 1250 675403462 675403471
    0xa030b1e10120b180f030307031109062d12040c080f280c080319080c0a0315170c03071508060907140304060b10050a020a02100e0310090b 61
    0x50800707041403040c40e02180c599440390740c0281607030030240c3d140024044460b19002c080f1075a4031600d607510b80c5010000000318410400750360b05011920161185c0c003418020910442d50000040c00002d4040c0780d1a034000150700c07018451604079282d95a14030607181d00c291003401c1001040c0d401c2109200c01941001d006200c0e540090a01498050303050f62284201e040c2e042c001d80a80c2551140d000e041c414000003250440020482c0c6a501c1207030a50f6940803071164003072001c54803442c450035805101503500c90748141c1101c80c17801648000071401418002c25885e80b0a4003858045080b80d640c0744042001e601510080090b098081f04040c0b0341501544451520544004546680c540c8480700d60b812000c141c65a00d160b03150310b40d05403140290203604085010b004030070041804040d401090250340f080d982d01c40002080306080703803640300b0102c1445c00369104103541c20040c10316880425912042c0d2500c10700f01d690304000241454140190315520549600302041401003a00d04513401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 675405962 1250 675404712 675404731
    0x312010602071a070b0612100c0806040b030a0c0603020304031206120501060b0f0d0908040503120703030b06040302012109170a02010b1f0807170a0501030b060409030e040b0a030b1e 80
    0x134030050781d481c54885900106001d0254203928a0805141c604000700d004071507202000340212901024001c000303260460701148920b090980301130180c2404101c264991b40c102a400d1900303414408240c000c0d600141c0114108a5510902074461116210f1400549100b500f400006a00340c02c20f1801d50b1201d41112840540c100030102880c0c44500c1260010700f8030302808181d042c01400c0101711800345600c4a6018002e00c004004843c441c4002440b00c540309403020000d90f40c0c1e44060151038021800021702080d5054030080890700d0b42035100781100b14054001c01d6404c880d41d01e02003000581c55186091500205403400055028040c6441502043d590201c000200400c008034490b02c1c005540c00740304015006c03d0a1030f12410001280010300e04000c015400c0c030109510090200344810381d50540c210010800503e414050000d21075050ba44108885e52040e08000c01024448950b99004100d008004000b4450600c000d100b8044405510b008500c212000b5985c0600105251038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 675407212 1250 675405962 675405967
    0x1f080708090c01121e021c0506030316050a021504090b040504050c060901090b030103050c1201180b09070f090c0801060c0308010b0315030102120105040f06060915020312010602071a 80
    0x10322220000311107180b0082440c20650a403058240d039402400c01540060f410840c070741a07042c1c400710a4009200c1007001100e803c0d60f440c0c10340c0030300b001c4070419106594942c104216101d12044485404220240100b003520407511450b40003c200c000c2c4090b4000950f800414100101d40c3d5074401c2601069040d40c01b40a0307498182c1d1559290b1854128051003000003090300c103400d905c0703501068042c041e17136402030382c0d2940c41c2d0402a90306d00d00540114450306011600705040c0c88113001c0d6015104c4240309007408001c032962006480700c0001d011030103902ca03034840090031002d689000001007080803000203071030403072130002422904141c10040910a00c0001c001c0001d502c12400343c11141c03441646516510350082c0380c1d184400e8502c203950315600204e144690364081034401c50490b10112001c2182c102c568105000340c42c0288540300c04150048c0c020062140006a150070f211418410340749004106040800b05400a82000340181c2c0030160a0240080380d105404c40034010711101070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 675408462 1250 675407212 675407221
    0x201080a0915050405010b09090c03060a020702060306041a060a2007030221070324140108030f1c02120907050a140402130302090114040b1f0f09051f080708 69
    0x144010b06807a407a0541507940380043c040c01001c1d4811600801e0081109546040040541e41e0705c48100da4041e00c603011708000f0454084041c0f0031505038680c058002030659459808200088c4001c00100010780d2800c051000030b56540780041c00912400c0c0c5802e42c0074400c13880c5a05c8806404e00d4402c0d083e600a0f107050002d07958140c0c0341100021601500c0c003222401d014074a0a003a0305d940024045d00003000559041550107052150011a68200304244d00c0c0203140f98404007020b00c503191294000300300341c1c88031000c00c0c07008086242851500d03500c915204040386089a01c005086180ea214010901018140a2102c24010403045030003d1a01e0b040041515402c01c00a0b443c0c0d11859000400e280c0b00510702003450001c6030010f1842d1507e603901c00540c03203812030340c6040750711940c5003443c01ea0141c0f818030151107807113003100e03050682482d4604098400003802c90811052000040c00022259102051907030010001c0483d008140e03460040500001c2d40a49600309100400c0e0421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 675409712 1250 675408462 675408473
    0x30a03060e310303060b040e1602070f1206150b03190207020f0409031803080309160b0403080f281103030601210906110a0924141b0a0201080a09 64
    0x7250700021074580142d000d089450198000c1000341c1c04002e10910106000a48101050005114502100070b010702c1c40340d541400ca8481c41c0c42d00904100045101007806000340c812041c42285105501c00a005035000c1802d0040c1d04c0c4039482200c41050003c10045036000505401e847c00e01c02120075402d0054550001e10031a1709070384087c2c0a44d5445a1202c2407521034404212500030b142500c41ca419124101051582d104a03280c4d101481001900740202e01803803111411240714420841c10207040d035848880700c1d407280c80075400c9c1d8401401124002208180b0a8400604c000440c00400462a0300900040c00d08006003607035400c140104030300e590b0003d00707484210030301c1c452444202c45030b40c0002d001003081c0c480240440e4605040328252810250003094905100e03160101150f95aa08001c1c4080581040c80c201d030104a06c0160480d0084e0049454801c00203003150411002c51101090266000c0f207001c0c6030b9110050580a55070030035442c0d5007024125500340f2901070a5100c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 675410962 1250 675409712 675409771
    0x150f082109010311030420010f0504170307050304150206060d080d0b12010f050f01080f0712030c1e0204050c031e0903070209010e18010b1c0c0503030a03060e 70
    0x8018021800240740038036070f110303912040302074005104c01922401d0034100302c0f0941f040103228100450310040c19040b203601501d03800348910380b00e9a85902e090305040d50150201d0410003244d80070b1206004400c0050010310241000e010540241100b01200c228020b10b000c0d0f010788401c0c0901002014880450140e008807950b40640308008101e1000c00c001050200d0310480f4028455441c020a4400d1518241c05c0540101e444200103171060740c0742e405480d100c0e0321400708003019601000c0c080103c01110020945002e02904101c21081110340b01c642c1047c020300c0055208100410f010801c62805120703498101901d590854203528003e00746d8a680c2c103c02201600c80002140083c2c0070500410481e11001c4e4064070b501ca155039602d614070520501038461030400513a03594000c509110510038061459001400388241180c148a0000807141c0f41d0015561555440350104044d00e0400041004400f250b80000300a0b15014900d0346142000e400d880008010982600d0400c3c0b0321201d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 675412212 1250 675410962 675411013
    0xc0302070809040203090a1b081b01020c1519050c06071106011e050a0f0e0702030304020a05060c0114090c0f0307141c060c030504060606022b020c04150f08 69
    0x80050b517075110114420300e400340c694001880c6e84404810304201003c50030301c90301202d20034400c03141c2080e0701e207407d038000075172007419a801a8880080c801c101d00e002c2510700240c09101156900d000d0010b80c1c080300c14500740c0b00c2d04d0702040000405d0441341c602004601e51022851500740e200810b2564460784901043c1b140b00b80c0808041415188200d80f9003102006003c01418800000c0da04c0c100700c001c11845104403000c1040315030014100300c2c000b0048070700c956401030041c2116070a01c0208142900b0580a1032010740d6941200721030044140e04071401507000200400b4401300180800c10a08903025185020f604082020081440c0c020006105040700b12001d02251030404082d4840c07155106001d0181410905046071190305540128001d034000d00b003c0c820103880e804140d070345025004a00080e40c0783c3d07502e4900404006440a101c0010318030555012111060015080e00d040811f41070b017038440b02c1d804001042540298030020000c0300e01615202d10b91500141c0c01c10138160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 675413462 1250 675412212 675412219
    0x3070f0e040209190906051e01080439060f1b0501020903060a0c0e06090904110f040e160801050c03040611090a06120515030316060b06070b0a0c0302070809 69
    0xc0300d10907588030340554815000c0904400300c10b0110f8004201d911440c0c0c0314070154a481d014002c070b042e0918203403142207119440e03441ca4841c0148801100c4081e0000e00c243e0311304558072014805007001d40c0c90b00d0b02110140300200398010042201210424031a4026018414440a03241041c1e810504007284482c40212101000c000c5040c030502911031440201e6050083c80304008444134103600440103184a81e46600d5600f1444c0e0500285110708808140c3c41b9141d2000207002074000c038007501d44d85101410056494032894049029252058454107060300b16094080c819000c80241c0360050503480024400d90038100303240c440038403002c1c2002d81030545440da22010900300401725030b2054030203031005110036912040185640318109102e150320b801c140c08200004c0365003401d65000680140614580003010307808445811401104482c11070b00d07514541001d0740c0703881c0900a034601440103250289003c4400c0b9084500002c2d44600381441400444007186008054038807942c000d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 675414712 1250 675413462 675413477
    0x81902011b0f081347150a03050708010c03110a0e06070507080d050c0f06070504090b03070305012c06040807062a0509030d140d05040f08030a14010b03070f 69
    0x1d04c07a803503100403002e8020f0604441e817072070701c400b060715042c0007009440203080d4242c9500042c0c6041041c2d940c00d0441400d42c10460011841e4944485040703550080e004146807201356481d0f441c107051034505d03800062240d646040038070317415816001d8003080c1502c0c0d4034203c0c540800044081c200c2c0c0314905499010b18000320b06030b410854100305200c090b0440004a500754070f00c40c10024010383c40348001200b240500720300b480d040b00001440c24016501d0741c41d418101410100380200034032018180a50600c60010b000011540a11401c20f089280e03400b0311003240c0c0510007025200d02e0245c11122564000c0040001003060002600c503a580c2c041c1000c20040d001204101d601e41000d0035800f54007080c1550100040d0b0000c000302081c400c1981542d40300c0620410a1711070303800400c0b624406c0d21042100341c08900b180e40c401ca40c454880c10685211180c241c07514901070b00201c1d0008403483d40c44504401d0320125042c00741c014000240c8640c65494444402480c1c1107411101005100d0f60 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 675415962 1250 675414712 675414721
    0x506040f090825153207050f210609060901030c05090a060305011817092202070c0303050c070e040809242b0605031216081902011b0f08 60
    0x2d010340300e80c0d0290000b200d48008004c0b608004020b2240000348003851400304501da0302c2c1807400840100080001003403080e00e0fa100b0700142c501e603101014010f8411002c01a85091401c41002d10514211001100000e490a04240008410702174480e40c0b05584500c010030014011040328415584251044107c0380c0b9201160f60142105802c010540d50900317000e5685141c4015403814000d00030390040400b44540c04892003a80310f440c50042d045689140c121111030301c881150b13562004030740300c0149052069100c07144038a440c0c0d00f04400003213000a0000c0300300410080800a48203000350f005d210304041d80d81800b1885500e415030302561150541240740818036016482840d0f2608031143d54143e103928250880c5200c16a1048034054088144000f900501c508010703030b40080c0041c40600c0340340d0110f00040d00309041464020008000b010001400007002d030040e0000180f140c04000800c007006400d41b030700c0c0020000e05040c403000402c81640d1242c40b00910150381d0801018070340740d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 675417212 1250 675415962 675416017
    0x603250510031509112b1406011d060f040b0a02070806060607020d0501141e131212020c0304030804050906030a020f060c07120302030417030705100203090f100506040f0908 76
    0xb03491541c0b01580c0306062615500b646e00710001e488114800e000c000544040e00d803050078000650b060350004070034034424076469140c5500e501a50304002c203420705203a95031591036070703076401500b01c0e500c6100c0c04201c0c40d6403180c0403c01d2501802d1404007038192840e16101042242c01054030291143c0c0600c0350413014030400307502a03000080356594031402d61a009078100c40560701c141c02c0a80d0300004200250302c2d1320a41e0351481c3d0b4260f005029070b02011042800b00c0c1c50b800c410590740701165081010000030001080108011480b03040e04070340b82c0b8949000c00000c0c50005040e24042d401400e1000010307a503c58035860100000c403504e903160f824041b4440e203840d0a40d000503210341c10158400c000d05030000042c1c0200d0701c4594402c1d203400e510054294990140c80d01c0180711b039200b01c00313200090806401a503881150034048540d1500e83d803580034a0111984040ca60680d0388106225840c2050300890030a4482c0c8034081c4007211081d5140006449690503281448400d014040e11442 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 675418462 1250 675417212 675417217
    0x8030a0819091202030a0e0906132301060e0114031b0f0d02030406050105090c04080c040c110d0903050601080a02030312100b0304060f06060309050307030305060325051003150911 79
    0x341c12980d0783d1003081c142c2070007950700d502c1072601d000413031166900a202458000c0323003548551005400d1030700030420f8512160140c480c01d00820707261150845031040c2c40c01c2d1445114000c084607661a05211400c40001d1b00d4060b0030090b002e000101041044007070209000e0406c0c0c812414100241d850302040003603001d50040c0604a8000c44c00001480144241504868181e0f5412a01c8000b1512400844105841540306515558000c0000880c061030b05034064505088203003000ba0701500c20b41c1c0440e0a002001040f6008070360032031f10600c24440d04004c81030260020b04020160b11030301d40c001035030324050798500380e001400c14000600c031004c001c441c0c20001c00e142c0c20420b4490400e8540381c005000c4543c41c000c00e551805000050281c8280203241c841074001d8051442e044150701c084020b04002807105405110b49200350401254038113482e0460541c0011040d28241042e0070402008040084401054240440c00398480651059a8111040c448000500c460100340800050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 675419712 1250 675418462 675418481
    0xc10110f010515010c050a030302090f1002010e06100b0913020c160806070f050403020d0c1a0403020a1403030f03070c150b130e1e0115170708030a0819 67
    0x203000d48200340c9224541504401d004028030310708844008040801103400b1540441d02500503840b9008040200b80240e0040c8480400035094001c012008004510031102d00004840141c0d941c1442e515074250230b001254100711088013003501149030841d2601c0034000c00070036a104d074450b504841c0d506003541e41224004009031040d180d5808120041d100d8034005407003015407602968000a0655110b80d02da044d0b494030f00d807161030a15085400340002e203c01307448111136225004001048850251400901c20031002081e556100d0070b502c180204011550700000c41d805000c000c0c64890b9601005581d00c1c00c0c508002542c480d920ba1404580c03070121850041c10b652880340142a02e01c60325000001c504a055a102800001c060960021160354007003c03000b81d04003c2c03003200ac5001054848034001070707080001c5082c850002904000c98147c0e40021420791941031843d05210050010900425110303010710f00308444031100fd0b0819400900050004064075100c6012404582c8100c814 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 675420962 1250 675419712 675419747
    0x160605010308130905010b07060f090533060d020f01020a0803010b0d14060a031b05121501060203031003030c141b04150b0904180212010603020405070f020c10 70
    0xd5a40e82440080e039031010b54405691400608081420282401650304840c44c1892851518201791583c500031b00740d40e0245911a030f200d40c1c004000c54070402c62502c5800004080e00d40b1509594603101c407201c550481c1401385144101000507540d1180300e5900c10351340583c4c0e40030045400b080100d08141101d0380c01000a9400300010440100382c1026292552408034204603a4000403045240700c08101d85095202c3c195200500008802440e10010800c2c0c01d85401c205585641c0040c40c03030340c100f034440521a44495a200480813801c914180105110b0024600c1c5041840c290807017640940000f805009c500f07043c040400c01009501c0b14000101011340e5081d4904010204d910100d02009501c1141800c0b16150100e039184003807021101d141c00d016290110900c24007000c1d110007a00c0d2107a0305445503c41e0050b80754844010200c8098000024070a130035803040100b100c40c040d02510801c4441d0701c0703109076079400068040c04117101300c41713204154100381021105000300303044410b407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 675422212 1250 675420962 675420971
    0x30c0607060209041821110703051f0213090c0203270a060e0123130b070615030b0a0e0c130c02070b0a091502030904090807060f0618021606 62
    0x140103496000c3d24030240211070a0000d0504050211100b80b8044c4c4085c00302900c0349510f44d002070100841c44070241042c00d01c4000c0d44041001c050624100d0341c002e86668015004a441c031403468000094000543c84045003883d2000f04030f915038003070360f0080d051174076a10b040703034907800b4000c1058074190000c8c07085500d41003110724882041d07803034100402806481d010070007140c02c9010700380792500c100e4180d648014030781008502ca580303003d441000c1840403600700300c6101e41088803001d502c0904441102169124118503002c000c0f10b003222500c1026090210003403000603000c00c80140c000b07501380d001280d18411404903d080c52100b140e00c07540041541d006420024007078002c070701c0400031602500d40301c5550f40325061041c861030b5101400201081e10a1004954a10031401060031601c104c03401c0590010100c0c046640120041d41c2c8258082485000c12110780282040e13014502000c0c000c0c9482d02003e403803042d04620b12848165000702d2401c081d40b101507003004003160058024003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 675423462 1250 675422212 675422227
    0x90a0c09170703060614030610140120120403140a0203030706020c03280905060c0a0605090708060906013b060d06090c08011407090e040c03080a08011e030f0206030402030c06 77
    0x45541b50111300c6010b401070a0000d100510402401d40480d030086102c1c200741c5282ca00110b4240c0302c203002c000c452100103010514402030421800800c4810792031050394990450505580c0344007403048042480e440084c200307005850110988024561218025840d10f0305001040d0450040292141801000648210a0305507101c00d04c40344984544641c200aa1104140412440380602101d543d501002016001032069030042d40c0c016480425200c1642d1142d040505000041d120f070140d0780d01c4240148105281d92906001840550480e080c00018000f41006034042c9151804c405911b1000003d4040d01d400c0c111484040c0e00400030020f80c0a54504400303080c0c084e014504044d840d003085e01a462404001003401040a501c1e00088140b80841c080160080100b080341c242c80030713090010005250310060b00c3e0400b601d8490285941c105150b07800a485c0016030b00c038441502d17010800201d05c0045241d008180c0550300cc3d03030740b56154000f203417801c1d004003012a08454000b42a8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 675424712 1250 675423462 675423479
    0x70201060504050606071a040203010b09040303091a27190506090601060e1804030c0206120402090f160302071704081b03060106090b0903010e0714090a0c091707030606 74
    0x4a0039240c048408010f10b407140c00900070140500b40d40205002c1d0454101610450215006540203100800200d00b4a51400c045a8171800a4808070040ba484a07424000c02c50900021000c12542000c0b580040c039001100d02102ea01c4c00254449030420320b0800a681c0d4010b0240b64040704400040d40c081c0029850626074900c402c03149801a4041c240c0049081c07841035040003e4600c004204d88002031403c0842907022034040c00850900121181c0d00c001601d035240a4075101120104201c15403906005021001500070582c03640c1d500d0107000c10000a21400d03641c2810700b01460b006881d11801d15101540342008880c2d04aa29000300b0001140360000031564050304207044e008030301c480d55200303044d503401e002c0c090840442c20900042c03020043c9480a4a800e10703000b800440c103402400c2d0281c0c1001c10f55041280d0440b001090380041d8108242c1481e002111f035070042115901d0f10314002d101d55907e0103406281c100540c24049120707000c00c55140a140c01400c00c008255446900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 675425962 1250 675424712 675424721
    0x3040312180209011701060b04030807140705040f0e01051f231207060f1e12021204050304060212120606070c0e010810060509100b09040f111b070f090f0b0306070201 73
    0x81750442d801c102c008940e6043d81d00680c2c0459030302445250a0102d5592028207800c2d40202e0070031203101e42c8100180e1a500c0b40200004a900d5440018074054880321060035100010030b42080304100f14081d8041082d5480f44500703e80501c08180031920b0318001c01514042c0c4184001d52050700603039003610050011641104840090300d446048540703510301910440341202c0f40d2401d464212803078a64150080c02d03d490500300c518001440c00648030781c445480784040d141074445500204040c08026010000318080e0b54071030f4082070418480694008880d074000b03040038010640803078504100140700701610050000c260498002c0d6866612050b6101c01207160920010b05040f000070f07003800c3c00c00c3c1240c091402100c07040740d00e0703040c500d07101c5065025a20180d00f0955411030300c0070a0425200e45003002c01309251899441c180043c0c2543c542200410400c116005004100000308d07142c80344030704030b441040c40400c48a081c02407010040101c4d401454050145d401049100390f4190f11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 675427212 1250 675425962 675425999
    0x804110402090904060509010e340503030a090303140f03061c1e03021507050313022803020411040f170106091b0f1b031112040f08010b01050304031218020901 70
    0x700440d0f13912701849a03580401d40c05402c1c164610480e0101c0c00a05d18162151501c80c11010f41e900341c2e580e401007480c0d540702e0150080051600c141c18002c01d94041015802e440c5000d1207241099045089a000c512001c0c200390b22415440549440180110100490980d0070024032006050300c400d00c2050715511b110100c0c0140110b840382081c1112107e0881d0194440da900c0f0f6003180e4404100201070401e0030016a4045240c200d4050070340150501c00c642d2000c1101c410f00d0b114618030501094aa0719540100306070000c0c8024080110200c03c1e00048a662003080052030b141c00c0c43c40ea005108030b0b0030141c091400d101c40b1030b40c040031850070000a9000366403641d206008105007110703c0400680484000c0d10324080001c0440e205681503a50750500805403440c09110000030b9502e5441540840d1003004142000c0041180c2849101c151035002e00300f552941c94030fa41c008001c8101c2d4480c84444543e40e042511415603220b40314031400c0d0340500169500e58503001e00341c0c041e03201c00302c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 675428462 1250 675427212 675427231
    0x31a070206220620030a271e05030c0c040501090e121303020a0f03050c1f05090415080c010207060c030801050d2108060301060f18020f0f030a061508040308041104020909040605 78
    0x4007581e1980c7c03d0301200221940e02c04c4800a55071600c1c0d1303103101130b08680f0130b65490b11030181c1c100200815010300042c040c072016840102070044d0010140000c0e1101640080380382840c00c401d003a58840041515003020380c481549070f9456200c080210042e00c0f00d9003010f904100d4400b00490444200c007800f4050b01d01a00844c2c1e02402c2460411501d4940c42e01c1098603c840f031031141680354000c4001d402074840042010a03092164203240c1c10b08229a8401c10056101c1501001c05580510559001e003c01c2d02e40300301140445e40300540703000703418410b890207080d108902c0410300c106459100b0030720a202e070100e009290f40d6480206130140988040703121b9480d1000004148207407100795030407980344800403400f0300c0c1218051350007034000410460503000b0030041d0800c541610001181700341101c1000080300360408110400c02e030071031142c0c4814843d0190038080400c0d000300c00240d00a42c030100d00c4000264100110700a40151440745d6001119030080c081000034a1300114440d00811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 675429712 1250 675428462 675428471
    0x10020d0f060909050c0405070c08030a1407080f060105090d02270a0b09150109121202011401050906040c02010e0d050417010b060708130b0301031a070206220620030a 73
    0x2404501c00310340c0f00c004001e000e0360202c1d140c034049080a4021540c013562900b05403003408038648070030708180e204482c1c40320310715a191079669441c01170202958002143c0c2c60300480300d181c500381201078a01e001d40312505001000c038458107141da480c11101c0e400b82d03028191480c000c046400340d0880a2019620203103464450000901e421070360301c1b030304070421401071041000ea11000da2190720461380f001414100300600f0008a81c80c50b904920302c1519100e40302d040c5424035441c1c40207007150001c01074081c0740c10340c00c00108402d0740c914400c50381000b401c0b50300040060050b0780903401001800b07554a40c0740503a51098a00b0703500240034000b19108550417050303020716040c24508a80003c1c00c0c060b0300c02414030101021070702540181ca03103000842c815079807643c0c1368400c110241d0000d0f801100c4200c01190b0103e01c0303081c046007294125032030780024190342c1008510140b8440b0038101040b07a03941c1c040c1d19003003840069005110300c9082c4260003404814820342c10000e40e8821180350348583e082 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 675430962 1250 675429712 675429719
    0xc150603062915160f0b07020615010c020f010207080115090b03120417030c010603060e0f060105220b04060b09091e0a1112070201020301050a0e0603030403060e10020d0f06 76
    0x1d0120304441c5100081680e61070742e01d04030701010f454000c5180084844428070302e03d800142d0709015444000c0c0141016183c91404030802071074060010072408082007074080014250341c0182180d141d5940c100d0300103400c0d40080380100d250a1983c1c0c01203101d507090055101000c0700b11661942500c0e0048030a03c9030b014504c090694544003080c1c1608540030401040140c0300c03a101800090342e1030201520b180249900d50107003500c0c0c1c10b4000303803251580d0302031000c1200d00801c02031240d0340011000e08950344c134200001f8450318003608404544041441084030158840e8415002e040d00108100b05154135034000300c406800c0800031500842c822030124400305035001d849048802000410301040e629245007001801c101c100410900c0c3d400d106200d0081e6540707000d02c0c41040d1503800162650701d003200f00700c2e013101c60754418064014990140136154801008880c20f4980180300440d00301c00d169a01860b240411900244c040d05c045601ea06040da00e070042080c10780040da00340241905c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 675432212 1250 675430962 675431021
    0x5100201060305030405061308100f0501080d200c1203030f010807080a030f0903121d010e010210051f2304020309030901030902040204121a070f0c030c15060306 71
    0x10240409401544180006c01c101c3ca0000000c010490005030f24807142c40d43c4504080c545815402c1701d070a0305440d82000440112944502d6004290060080c001001483c00141102c40c200c941004408510303020012055410071441c503c046019000074070500494000b140c403074109403055441c8208071400014010400280781c41511003d82c06031100b10101c0e81c0684880981c40802014006031440010205425107603540d4102d03405d449440d2900d203100b500c08150382010002c40d040c0607140c0b12811059a001440c41e44c51080007034005281d865011800403444030390002d51156424a1002085d81c00020900a10b444441c01d0358003203c00d00e80c002c000903800126106500c0e54014482d420701ca6100340c0106c0a0140054001890181c80380543c408110490009945410f080d1f010301e1140300f00b449078580c3c000028a069498130080060060003124800d00c041c2c2001080d1030bc000c00c1c09000d10610740800c440302d1040020325a80d142c29405040501d400149024800034140c3e00c012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 675433462 1250 675432212 675432221
    0xa05060102060f0601030920100915030e1005180105010f060503040210140c0d0e0307060e1e040515011b15110f0a0c020a144605100201 60
    0x240140c015007090380c1c0300c2c0c146101e4903d0003441d007070400d03407518562404580321100419400d03d8024501100e2002c0c1c0c0c00f13000340580c25100311010040d628000304900c03960000740e4407040d00c1d1440d01285001c0d003038a0a0b0301c2c0808c1c1c030f817130136556525040a1000d4404204c400c0303048040703007a000303002503a81c1d50018003400e0700130300c0f8800101e00704200141c0185047c240ba00f4510340035080113100b4040d91000400e0f184c100c486d031004164070044204800c10b40010b4081e620303050071001859480d040c200e0003081400320000071030007640948101c26a20b0303088020796246003800343c000c2020b868001809640c48804064190104060020a049c07404003140041c12207908001016159900c4204500c0100020349402e2581c54090100c4484041400d005240c900b55a0707842d005000007500401c083e200c0c0681c044440719441151a810369140c9100d00c81d80c4c0c04000b0320200c0064008621446401c000c0080c2250200036022100d0824581030b10b00019a002030302c1c3d02d455110007010507800c95 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 675434712 1250 675433462 675433471
    0x136020a0504020c012003010f0b1312050f0a060b04050f15091302030709050a05010602160303140d090b01062606040908090a23040c231b150a05 64
    0xc4021103051101e4101500100100c9401d40000030b03800281041075030603801c00b4a10413000d440000010098001a040c0c02000780185201461902e0807484401d12501d106100d1400800c003210130500c24407000784100c40c2e2544941058071040852854080000d000c0301c07142074421413510300440d40f103491805c241d038410b40580003645148030f5404200a03c2c0c40000b0150421030084403250700c0140c9040c000500101594840450a0300300240540d05480c816041101154080e4540f00d4000802c20704030002c894050074404601c50680203403507070341d10810068020003810300604030200318483e4090360407240310f9a905054980200710560320b0703280d440d802081160111380410202d250592241c03c03a103209500841c81e184140011907003440c204d900511040702605108208983c1048400500407012a0200948104a003010b00400c0050a000c44400010401400b801c001901160303041400400c01d0b0a402820401240c2e440700f844040406152681c00495018042805058043c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 675435962 1250 675434712 675434719
    0x3050411011107170604020406050d030c080f0d230606030c040e1003050105130b0907050607080306010306031e05120c07030b1e04060c0f080c0a05090111013602 71
    0x1800c111030011101030160800c40d07072050180480c000703183d490300003a1140c2c0464401c050025440c040c01003000b1a8110350085004894524100b00002c1d1300c016019081c2e030780b2911654231a0400a00e05e00b4038094615482d404d00d140040410f0f001500d1003191251900890704015a60780318804c4c84054002134443e031220000034003003402a60110000b080d48816100b000064181d03994a4031400c0da58290340c000d0f00c58949007040c10030f11807a0901d03140d0211000c8004c00040303240102080f00d81c0301ea81d002600280000c40070444c568440c0d00f041000316081403201c001800701e4030510b48042c00d5030004444030f2050004840c0c000713408209580004031118042c0044a1031521119200d402c0100746039809444d000060300794600b40e01c00340f80960300400740081d20040d0400043c1506610200707940c00d002c00041001a9180e43c501202d60400580c81e01c107441d40c030800c00680e88103a4084012101e03500b172440f5040e03202001d224194802159040003e035140d003066101c4240360351040045d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 675437212 1250 675435962 675435983
    0x120210030c02071a0c060a0212010e01050d0b0403200f0d1d010804023d05031005210a200a0b040b0f120a0606020111130e0403030e070b070302010606030504 69
    0x2c001c50041184da1050b04441c3d18000b10b24030100d00303000c001c07144d85000c00c2c5d0105100b241c0720f034258400c60140c19038015041c0d455060800103039500d1051000104184410800074007010300c00e01e40e000703081102c00d44034200503041c50071103a22165028011100707442064805400d8038451000c284504c80058191075003401c1f40d50044038900c50050042c0d070015800c000341100d5015040720050040c01c4150b205481c2c02d501401d4600e200781c0305084204001080c0b040c0301d6400004243d020813540101c50000c030f205ca0340240c21403904d5403c580101c0e64014055182e040c03006402600200f610390034059502281504c040011408050048110400e024081480380c04007803001081185688000f1034105600350188140c02e0a088503c000099201d034410803041ea0240030781c200031042424654201040a5123020058480e0704c0380c450320400d0540441d05050099201d6041d07680c0f0f0350166504192161610b5206034130400c0e08900643c60000c002451a2282c441d240c06254012009203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 675438462 1250 675437212 675437219
    0x40c080406110f0403060e0d080618100b070804030c0b030915130f051605060415032a021c030903120911030f100f0203040b071209020a120210030c0207 67
    0x60424000055078181c0403c8010400390300352000d000114410880840e169494030102410188920086030900035081c081c460300d592103d10310f149210140c2c43d81c80035a940c0100c56001c100c5581e0283ca00c00000151903030030701403058002c000303881c00b03401c1d4803550595801003d0868801102d603110241c0141c0c8018000c681050213241d0044584213003240c020302251641d0301e841c161648200d48030303130041c10150780000c130f00c0301d15900500085403518201072070240d29102d4003125814490805a40d420480f88041947e4540c038045800382c1040c00c010b045030344007e50707600303246810f1140500d169045412500d01c20f01402e05295895903900c00b1540c89440b4100240400a40894110741c0e1840d030a0b0894800300500d40182c00000010104040c11080c80c008581c4402e03c4000414010020040401c1008501c190000107a1800245076410140620010400c00c1c0c0c00a40c40f224900d000102d402101d2004024103000315100007624030b00c504182d08494010001101503004040b081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 675439712 1250 675438462 675438473
    0xc09011a03072304031b060f0509030106030602120f0a02030402130b0f131a060c060103030c170d1a04021201030b090f01020d0906150f03232406040c0804 68
    0x441c1c0290780340c20140c03d40c00440c0404608090ba100e00d103000381c1400314040042c424400d2071505600e010344210003000d81017000040c00319900081c400c0030720a001030a411952800d40c400b100654210804640750b1002d1911380240d14400e4900740101000500401d42110052080381c6c0110b5004103a000c4d80080014514060810700a040d5805000102810300071340780d110b00110014a0843d0000d461050302440c0c88442c601d0307002a50103148103110800d000748001030002c0c196030b05418140c02c190700314075018101d40c1c5c00c019070000c0340c480403450310303c1c0c14071039000a0090700303905081c0c41420b01c50f01d061000300d02800e18405848081c1200420101300044903582e003154490058032103406400010320709a134010f400c400b10b00c0d5600c030324031024000c451080c02c0d400d01c2400420b007011464441100000445400003402214024802d1403482201113848070480d810081074072440e4800b4421a84400c0304020f0001c0328041c1480010700c980b40510604445050a4030751509544598441c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 675440962 1250 675439712 675439717
    0x70609031b18050103120c1a1003080703031a0405090d120209060427020a08220b010801020a030509160b13091419061406090f0405010b09030c09011a 66
    0x41805001c1010030100b0203100958100315401105500450954914a0221151030000101104001c2c03a082c03d400080c40c440c00700031043c003a10002d550143c80300d5038000c03840700e105c1d480104080340004581f000c25415400c03006c01e254151241c400200318100c11322040c0c0d1412108080c058001e54007030340d00c0c1401200d00031a000f01c61540141010205004a806039110390010300c11014003100740c41c50200c00310121ba0f0070010f00c820560400c0030205025004490140c11f44800344144024042030a848042c100c1500e900039600c031180e5603448252500075444600c02e400064207020000e07402c0c60300010000c070301000c41201020b20700d1500c84080200d8201600b5101542a05040060640e080c3d010320400440e00c000003c1260814002030500d6103500d22514901c6800d00804205031039404a824002c0c2800741c88140c2d4600c3e6a80000300402c0346140c2d1aa40300d403409001184248100740908480541a022164110101010012144802d201d84090403800300d030500c4a40048401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 675442212 1250 675440962 675440993
    0x18060e0a0e09071e0302040f0207080a0c140a08031504060513020706060503030706060503061f05060306010c0b0f1902070c030f08040b0409151d0106082802091207060903 75
    0xa50300003e4513290341c1c0341d0360f4002240803013000740070b40c005106620b858400d0b010a01c1500004510700245070b510a480c60081520201c24401c94030468018403103510440c9900c2488142a0b91318660203240a0b98690400e4803408003000250310350305043c1c01c080c4501c41c180c8500401452031102120f03c07020107076205e0361086130015100c280c00030700d5440c200090b10159104401c081109030811091610700480100442c6010f4490041c0100b180f000118060581d001551b0241e50307030395484016a80031080b641d0013414400500e00300175140021103800d40c050002c00c5a0118040f00c2e50031103405074002c1c1503015044154080c4c0400004801c98114441184035841250409964824501c0d0782d030003982c400c5141c0b40c0c4400c070306169920b032030082a020704160760228000c0401d803113440200c40d41c14010300040c0100354010804050319508942c080d01c01041d61103495050703111804cc00b0750081403411703004000c441e81d00410841d01080c8101a907a00741d40d0195128603685900c2144180e614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 675443462 1250 675442212 675442231
    0x304021509010c140a1e11010c11060a081b070506151c05060714120a0e0106051c153303080a0e090c090319060b06070318060e0a0e 58
    0x30b40f0400083d0151000c50107040d155024000690050811207412814000c240743c60f1803945003254000380c1c0a1800c2c004680003813800100c0a100c80c0f41582c501c82541881d194041004190b600d07602d030f403001c18548280340c841c2c1c1d0001181308494084819001d000c4000309650450000500e01440130140451140c1009200b82d040c43d0081c9585660343d404860140c400c3d4000b8420816290f8019181050704901c0a599629204405134080c00c21900509010030403603c0302e5045003200000d41240010308002010740e212406201a5014617443d103510840b20908220381500380b113662841001c018850900840032082c402035201000011540e0500c82c480c900100c000c170115000d6000341030302288a4580c206c81c010040c0030400316aa00400c05110400f00700103090b0651008695001601c48004018451022030f144c400302a000d020040307500700101240642c1815030240c1407001e060442030030580019200c01c81200c49203140514550044e41d114000c100c00d01510f00c806a10803241c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 675444712 1250 675443462 675443477
    0x10050606130620070b030f060d12020d0806100f0f020106080d032403080d0e011b0c151a01110309042c0a0b0c1b0307080d05010b030402150901 63
    0x7440c061507840826005240012290b814039112050110b1689007081980c10040021070301c0c203080341245200c001d14504107429a080801c00c6030315211040c0c1026a03000d800040130040321200203681d0014100043c00150301c54001c0707405410142c05017045004259195480d102281505075508160100707080c045641c0d45000048a0000340004a0300d0302169401149070111070201c410400c08a40000c00500b04c0c0010400014480c0030880d081d440c124000411a5400a0181401009100b100580545000132107100842d8420044d854003440755842c0102c51038000701c202c04480490346c138050001c9148422158541c0180880702e84403d1701012a480c15001c500410140d0b02c5da4000718000403502014091407541400405031032100032070003003441541c5034132201d08100c0d014210080101d0009143d035500035010803261440e0b814001120350700c0c040c500d000000c541c0552090742ca024540400440d42c500c2d134004172400746800518550b80c40100348401c6000c0d034041d915081c144480c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 675445962 1250 675444712 675444727
    0x7050a050a1a071b0608010b0c07091a030a050109060608030f1c0906090b06011e0e0d031403040f05070b0910081807081e060c0a0509060d090b06010906080910050606 73
    0x802010541134005510b003005664908003000d005054180c0141c54030301010700110325810f00000711041202d500d800045040ae20303c2090b0a905116180e49a4050191400c1903080c00015000061841e215000801070705960340a00d41d140e000350030f001000040200311030070074040d2420340a8500040e41c000002c00018694034981119948103003211103d007106e0804c4010760b0441200311110381d038a0318180081024110040c40e0034a08000705203d0691030780700c42c050504c151040380360305481100d11907403404c06041c5405100d0b003a6000f102c16210300300010981c040d0003810f440f0030400c0944500079040c0a5a019910310100034030206a0741c0c0700c0111489184c1e0200181070013008400081c00204807007000300b098501100d08103688680c8190180070b01401c5420445d0895859458801c0e180ca18950001d00750388a0891000f4001d42408640d4040c82025913031a40240803d0b20b03045000303a80d805040d21503110071a00007a45400410107060140700c43c0c1c101c180e01213001014545030094 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 675447212 1250 675445962 675445973
    0x160203040f1401090f09141602070b0f0f22051509010c061b050711040507020607051308011e05060d030504050609010201020f0f04060219020d1103010f0c0305070207050a050a1a07 79
    0x8040d81b00210340c54a400d011704160f101d403034440b5000b52168481c2290101c002102954480461140b00440c8000041c080b40850061003940c6480301030340714030340e541d1010450349500803040e40d41407480302d41103234400141441d00c401412280c1c3c00c0d0020880c24200240010340b11200050401c0e18603a440b4240180e11418491030030100e000d0645516071920081d0a002d2230549480e0382480c001c030300d03002c24070100c1900003554035030100e405d141c000d941d45003610031040d1940e550780c040307c1c4640c2010b04460501003500106003c401903281c0401451342c4a600700300f03c100f119034005d80440c03420001841603081880c02000204018000945010b820308021041d95001204101240c10045414030900fa8180045142406501c58036180080240c0014414106103a00105444128181d085881c1c4080d000b11082955008080014064041020b005008200c0d9114014000c0540200b5240303009100c61040e11009050104003504110b40800d241d40c403d0740785448442c081c043c8000091 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 675448462 1250 675447212 675447239
    0x4031b03020a172109071221050301380d060e0a021810080a020a0903140a0308070903031b020105090a0b0702030d050c1c050d14160203040f140109 65
    0x803051843c80d543d203031040c1c1c1d0b003000180e030000079000524058060001c07007580040c030101075420407403c601d888501d83c17400642100201f107000c00c418880503860002a0b41242c0614101d4803001c201702416a80003400200c0411103c01d80000303454140c040140000000e00500300b02071003180001401034070b606c0aa0310886085030a00402600040c0c402300784c1c80e01400341800e8500540f04604011420240582048002015185200c1e400315000780e600b4400c05101004540040c58294000010000241c0741d440440702070300840c130710002040803103118042910450350140c0e1880114440b440951610307051400c000da0411000344001c0000c0c0d230310303000d1040041008406041da200d0840c4145418882d0f0a44a8400d0000500c1061701e05c9001040742941c00082d00403c6080d064540016103550040310b290301030081c500f82e1031030548610304c1011400b890441c0711580e1035444a4004996a1285024008000c81288030400411200c13000b24056400141031040c0802d880741403000028 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 675449712 1250 675448462 675448493
    0x121a01121211011107050c04200f0d050702012a090905102711090618180718050f01090b030a0609020a03020a0e010e0f0f040b09040615080604031b03020a 68
    0x11880050081c0801508100c041f241e182c00340ca05000d46026507000c1030189101601680c84000001400200246c4090850740600b0411400b00158142540001c0c020301c00465160b40ca54025030003c2014074590740d11103192401940ca040120307003452507442c00381001506140300032030705000203e5401c185c8030b83c01c025100c01d005500401c03000c0c25003080907600920110741d5000300c100002411a11041c3c1110008140e12008610f00074031040424114a958000e07040242d00000c140244940e00146842413000600303004c0c07003116103502c1004030720402d4140d5a8085070501408200c48205a00038652042c00c600303001515581d00c0f0405001d84c0c4c401001d482c0020703800601c4440346600100c5840184100f846c2c04c0c40710340311003c0804d101340e409803141d510641c80031840780e00c03d58170f541189107101780140689401d401c2c1460710101074049411512443c40304031002242990740090398a02c03c03a010396416aa00000b541602004c200e032507030030b07001c500400076040042070b082001203409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 675450962 1250 675449712 675449741
    0x80306011803050a081903020a0503042d030e03070608064c03061707171e0c03011b02100504020d02030115260a11010e0a121a0112121101 61
    0xc3e1445e507052901c06c002e543d0b851100341441407000c070811715400010750740d2050340400301404c2d50408100d110349291503070301c2601c3d0070700da101030400815a0040540301248819411624929204d40702510803134400c032045900303c400700285007000503d481c0c00d00a280b0140b5071000581503c08030b2010041c040820500b00c00a08011540d04164113214000042c07003084c02c406461160300101e02e8540c038803445400b0380f40c00e044007030644002e400d00003079440d6110401d5070308400240c8144141c4403070316500440d00c254a42102e400302030841079031041c00c9513656030203004031007180080100100000745c001d980040b0255001401605c00f4400c00440391020800310301c1e09441c0801c0e140c0606e01e942c401c05501000820701702e451040002d070f207803000c9901048602c000c1008000484130008041000f50340301544c101c00040140b40c40ca91452414090174180160426203803611031580d80a10034504410424603648000c2002143c2080b1000ca0a18041a10702c282d0303110b003400d541c0c455046608 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 675452212 1250 675450962 675450967
    0xd032309090117060609041505040507150c15060b1207020304050d05030d0507050a090e06041116050601050402090d03050c1006080c01080a0c050a1b0605040825080306011803050a08 80
    0x5440f001000300a9000404650100c0c107440c0a55401c3d80d0400d52030782008000351540081003c22200b404000c02a00100f02810900600b000f0010641c08a48409844100c0d14009898911007030340243c00c04e8a607201e000514141140400c034800d210300814000840c04181300110305540e96040890f410360040c0010360b21140b08100142c12240003405400c2400703010040310640c144c02602d003000300c420700b03d02d00300c8075920140480c01800d103544010070300400005a8500040d00880d09220342402402250030581c0c035a4240801ca01c124841c4903802291059400002803003080100310a9040006075170400c48410304040a071445500b11a9007500128410121541c0c00700d50960711140020083c07100b0f5201c9800640765100d500000d00c1003189240140d00c0ca0000240759090b10b0b58800020403072890f16041c51401d6030000e038a109d480300c00d03007011561142854030540310720031707040b0200d9451520380d040191102020100c141800c00b00e6a50000081403040c000340d10f40c94002c220b0247e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 675453462 1250 675452212 675452249
    0x5010909060e0c0f040902030109050a050307030f020102090a0e0a090c03082d03010e2e14100815040b0301110d0c0207080c010c020114270d0323090901 67
    0x301603402d2103031902250340c4050340d00640307030356600090030418205440000f1440903500200340540314140300580184a070513001001c1000000040c0b4002e400f9548020590068440880c2130380318410302c00e039100204213000e21400c002c0000343d580201503440d0003d50055240d0390050b003158030364010f40e401200855410034901030980c42d83c048418454012030300120a0490400900041c09290160301c0303088002000f0300c1140020f203c000540300c1500d00803030140c080a0905810314060301c080880c0c100400c280500703001035100c035420025100e6103040d550380c00d140c00172581c4843c0182d50294407450807901c1ca80342031240d03415002c044c7d10001ea95035032100500090f55443da4400045510000c000c01503030402241346482c8003001d00e00305000c3c8446d400102d5007000100120341c1882d20000c2c030040311140900c0f4000440307801c4003071001c00f19800010402490500007000c0c4c04140000303014044030701e407a0074501c9507605482d00c80d401c11220030082017081c00c0036000300b8503100d11610001e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 675454712 1250 675453462 675453473
    0x103050a0b03010f151202010c080c0106030b15040c0c08030f091e01051e22080d02030f16390515071d0f040c090527010e0702030f070602040905010909 67
    0x400244c01c0c2d40701b02c440c000741d003a030000b410b842d50080c0140880a010030020754540080d003025000f17540101400185041130030400e0116008415240c4c410752406420740749090103482c00948081d00006180d086030f56510090511000c0100131114602030808a03250034000c003003280c0e28203c0204c00008592070401c0c0100e190b0303060100c0564041c038a4008100400c85203020020b6200d140f0060324200c2002c40c44c00140b00e008107024407a0a6001104004400303004820b071602c5040c100d0900c2e407034848142c0007540c81070101c0c103d0711000400d65940340c1e200e10094015014900d00d0034040b03052000c00740c55107820650b184010300d006a0040c414005a0390f4403e99052822400c60050003050a110002030403544081040c140615112088010268040d040e04c900801c4058580c01c41070320950800b000c071200908000600255080c00401c54011142610f441010329400462902c030f041c3c0d00c2250180c004810465110350204008544082a4020580200341c1c0d01804507014445241a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 675455962 1250 675454712 675454751
    0xa060b130e0907080d12021312020f1801060f0c0f0503030613150311060c0a05061b3a0c02030406030605030c2b05060c0c07080f03090103050a0b03010f 67
    0x2e040c0a540501e90901c41e80c100440c6980508102e400e1041150100c41200000390113903541e900e500404204001946007141600140c50380c0c42120840503c100303070703c104148101c910312500800100440103004040c0a0314070189980d509080000000d0a16a41c810300740b584660202c0d120340002c400d1140c5814010708506212034540b100f0312014449070103800f003484c4984005030480e41c01244024064407804211400c1000c0383c0b054a4880034541401517a41c83c00b0307101c89030450307043c4a140c124610382400307680b00400040412080b406201005804c5002c8600c800c801183d003002c82007030044c01c60b10a811014030346401560300c41d4500340000e0111485070f40158040c0d003029002e1a190380c2c0e280e28004400031001010a004a071030000524452582c0000812038880c4509000b003503460749001d0100e2510b0101140c1c0010340701e01e000c0f034442e0414a000c0030107500a000039501c540c007980003142e10002030440080c010100200190944800d024100d02c0b4969410140c081e00004464 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 675457212 1250 675455962 675455971
    0x309091e0115050a0509010e030f0127020607200306041202061003081c0f060b070b0c04210204091a0a0c081b0d02091005030115081303080a060b130e 66
    0xd140c10b0394519264064214403038000e040042040c0090300d41d0460b80904564030010401900b00c031113651259001a00900d56109a1a5081101c01c842620501c8803c036088039107601410150904581c4e40d100108100b00706081c503851550b402e40706035a0f8904110041c80b440c042c848620031095101c0010b030610324041d16078508450540c5092021458200c101c4107003142503416050361410a4402034020700c505c9a40c162614100840020301c50b0301c1364083c1c0380f80c90013a00740307444c0c03911224031317094561140d48182c008044490906200d64030b100802921001c2c00608045892449a0394607958080416100c552001c607000500c410352145205440e403039901c1c0c1c00c100a2034200031030034111f400c0c9621604140c05500040144080032503030155500400082d00312a108226100b0150041c2c00900520795025000100c0944180c490f501356030180c181d5035200d1181c0100c13610225044d00b8005c21004403a901ca490004000d46501e000b450003c1080001c59400c9040c035000b42d9800318041c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 675458462 1250 675457212 675457229
    0x612020c1905060403170c16050703020316050306010b070c03020108070908120c0123130c03050102031314120904020d14010b13050906090a15080706020304090501091a120309091e01 80
    0x1f080780b84944401241d01d584212001c0030b424039002c0c03034614904161908000d4060080982120b400720704448038a00b1f0b00c1085040c2c03030031607880b42142280c5000d8110b01810a001e03030784080000d075001d5101c80b81c0084603407822018081c2c803a801d184c9402000011381c5065040003a07001602c1800388602d0205103005075a4134034101001038600c031071402c050445001124a519200d0401808868410003194400001d40d16844d082c0008a00c0c86400b1600741c46004030500c000c50f680101041100403004004000d07428103000ca410300009420690031a850705688008810040861148003802003d04041003980c40304190086000d50200d68409401080000c0510809654106e91994442100172000071030741110324204440011030342c8124440d010303c0901103482c0d07901000800c10b0301c900c64410700003640e07545640d000719243c00001d0070a81c8914a560740907441e003000054503041000e421a03050907900c0300050881e550030b4072041c280c1c04154484050f0341015403401401030810343d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 675459712 1250 675458462 675458507
    0x4120c0603051812032d01031b06021b0d21110703110607050a0f0b011508070509040c0e030d200708060403030e0118060213050402040612020c1905060403 68
    0x780b43d9a0b03801144820b803e040b040840003071003e40f003810162241c2941c0d2507600c4611614203213520001407081c042501c440d03050b80101201c2204805003581115690360003400c410074082000d03961001891091648504001560300224003982654a04071050320050314948580c3c00010b0f103911005800c0c5190342c0c004100c00c00100d01c0745810080d200405495890303880b8203a10b001410190314480040c20020399050000034090203060003410380d0354804980400c001d4a50065502000444050300020401c022505803401c01e904580200c44803030500d201002c2070140040d084c042d00710001e0001a029100344003020950101d0107110668001c054032219080166840d2500390051001d414151590102d1800020962182c8400340d104603407440b46a11602e840780181d480241d070019000d06a19001c1501e145c10f01c220b60480c1c100740c40320000d801101003030030003942042c0503201c0240182140c491a440e1350541d00841170b440780000e080700380782500d00a820f50519001c03842010800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 675460962 1250 675459712 675459751
    0x5010f0512041407151701030b060d020307090501080f010b190e09030708030a09030e010e090105010c032a12020c09040f022e110a021509030304120c060305 69
    0x104007110040d4910800011169949080c141c2d800381420544140c0c0b8410140005030705250840c00b6191026a03948945403030b0010759152070300050a0001820440501000c10414500307c0345207410a880030341500c0c203880d919100724088070000d074800c1d04260044082c0720000f4800380b0469404260849000041c41e0b141c0c044001c140b140d42c050400b03a101d0340c001040d40b1207010000d40702065031200800340d9a20f0107003d401c010b8071003000c0c100d01149400102545035030050285d511030480103000004030360b103020011148810181d03415018407015085010b411444074202000910710100b030703849007002900c1c024461a20080c0590115085003007100050b0340c032410001d03041904a000b403000940b040c0002600369855404081019201d05e031804441c117421170703400149400030745401c40720800c44107070241c0710440d07484000e510100301c0c101d180c0010310b00e4014010400b8054212402c26031524444004840c0b06002078071034036030b50f03801045103e615000e00d41d0b02070b0003100d0308800e0101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 675462212 1250 675460962 675460967
    0x20109051506031239152a2a0c0105070303020c01050f01050310200d0902060301060302030f0c09030a0b0703150906050f060f0d05070504170c030705010f 68
    0x912941079500410481c011503859a0100314a90002c845983c059540d0248204150b00f03206508240b00014400b41080005800c02c20482000c0c80d00c1d154050080040f08010b80c107244c2e40020705410380851003260302c01241051007c031101c0b240310034265541e262940e048110403103900c01c030801921403896454104000000c200c0c000b01030820700b052600d804143c84d094029004419602480c0d41c45c220030030552071801384041e8101c985c25400d60b001401ea17001c50344280c0c0c81b107400e007243d840c41d000845003c9100141c0146280d05d400f9100007a04010f5a001818962081c0c1c02000000d03004400c1c40308280a106019801c440811901c1f482d00700001d000c6525000c0b2028050400384500000074140d60207038208503560030403019404075580e11050010010005400340c540a1140c00101c4070040c10000100c40d0f40290880d1527504100c03030310492002900005003100f04003c001e0000081f000d000a030300d16400c41041e409010012039030001d02d4170b0030909a1042e4100a034140078409a01d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 675463462 1250 675462212 675462223
    0x80c03032107020a082a010606050f07080903010203011503061d040623190b03070e1609090f020307020d0c03080106030b01020f0d170c090906040203130213051602010905 75
    0xc450007400d5441440580c00d000b0802006040704000040481008201c119100e084003103084003180005a40300c401c501302e800a01079040450000c225041a192140c400f408025101d4041245001007040101342640c0081e4045030040309001610240d507030f05406081e014102d064450b4031516201e0007140403d52000c1e2010f0310b40d5582e80c41030841035444a00d9401c009590083c14220703030420700c100410700e000c1c007451090510300e00003400d01300303103030220344c002c111040d24201c09030340e0716440b8140000071505a02813003841030500c0000791600b41801008603070b03e0802d200503140c0c40c20f544080d0030301101569072400c1105240c1000002a0091030b0301d8103681c0c4078030b0006840d00c05d4800603460104042c1c400340c800c2c81032640303400d407684c0c0c000d000707414000850401401c2500c842d00302c80e44034002c10b40a903070f1008442c000a00f0505040d80074545c40103030f91040010f00c94068000ca5102c1c802406554403c07500c9404211021030701c0c0c81e8402d07509040c0e100030000e0b2042071329010f4030f40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 675464712 1250 675463462 675463507
    0x1503040b071d0a0311030d0509030307030e120a061401080102070b04030315030b010806010305070509011202090709050402030906040c0501020a0b0a0c02070f06050d06050103022712070906080c0303 87
    0x18009190a554042d214401e0b906900030340083c0d4019180d0400300300180d400c00349a07100b48079034124605078038400c405481004101800031418442940d40c29591104008030340c6400000500071080c0b03812040107800852805084001103804201c030b8480e44400050b0014a2280c1c0100241380000d00c1803400750390b009400d03282c0042c3e25000b00740c03148070210481c0e1000d40002140f000200e0b01e0040490868101c83c81841181ca0b002e0360350003800800c40c1e09102d5149000c044403013110140c00c00f921b01f2540420300b490801e0740c0344c0c1c40b4400241240c0040d206440b0590080f01003008105c0880d6000c8082c4c042400244080540341c1c0d522015030000402e640800d40d115007100751000c6c020801c0e403001d010365600c0e0f440c0c0a0b850b01c0c00107180c0d0700300c9000c05894070700f0b141e80000d01d0350081c4212030205081e0f203aa03000f0320071511424128070944181c0036401c041742000c030300f02032902442100041c117072000c40455554a020070840c609070100340d9080c03107900200904050802080340e0388004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 675465962 1250 675464712 675464717
    0xb032403060403030b061e0909060d0803012c0705211909060908030702150709050604031b090e072904181b17070c030509190906060804021503040b07 66
    0x100c4441d00828428001d070500c01c0e00800c87ea004403086014600060700682e03805849000040da00c000070402d04450041004d007a280f0104010304c540001d0f000c85442d01c01d410307444220326801d600707004611482d00302c070841d002400c0800d03850744440d403d800060780f117a01512042481e044c854081404000c0001c11f05c004642d41c4c540d1002045010341003080c4890b0840c40f030319100d2410120194071000700c140d88003584506140011521401192281c055580103400b49051500311360b100c0040318401c2800c081240701c19a0002100840d6026103030742145042702174401546031620340c140c920180d46592a244150642c07001c15103c54a060380c2c01c4444a951609100805500ba20005c0083d80d0040d02d214405408a15601e17030040311407800110340c01e1040100c0c1e640c91200b01c0d00c68410120060020300b0402c00c3d00007915000c0c103540d00c0000000f44401c071203696100c11104541c06507020030003140285080005501c4e080074540f81003204050060315605e41541c400b00b410070020810b00c00d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 675467212 1250 675465962 675465971
    0x31b2909070f06030c0c02093103020d0318051c02010606030b0607030c020a17010c0801060c0f03140f131a0f16062c010b03010614060a0512010b03240306040303 71
    0xb0380c8500d81c075440080d00500802d070303541802642c55009c085c144400310b00780308640c030b00a2004000118080800760301640544442c41040310f0132400b0301344030b4001d141000d80742e607003210201c1c10074804010100e2201590802c0148030003400307070a450407039110005141c0791804034429511000708845a0551515040002e0035052000580b00c00180d00320291a000103910305000350710540c41410202d50f281c40e1a0710aa99591044580f0403c2d00310040803170401075500340000b801181282c0c15071124001c0755040440d280c5401541d034010703c90401b0182c9140a04129604184c5000b01075015401141460500c01c078009207030512591140c07003580541c50300c42406100c010344c03140701c501d00712020045241c0b05000c07140307000744000b82940000354a051000d20491a0511503001160000f001c01020840f04100b0014581c02042c1d0b1a42800000c00000340e45803400701020340070f850100903440d224140b4811007a00c0b900e498010140d03814140404211381d81d0b0000d046540160306140105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 675468462 1250 675467212 675467231
    0x3020601150210110f030109020405130908192307170301052110020d1a0405060f0f04230403080105060a17040f05011503110d0f031b2909070f0603 65
    0x44c2c0303510400d4803250b00c1c44008000400c803406181c00420403560121080c0f1080a1b2944400e4103d4401c01001020321800f0400c01c0100340c07807001d030741445101d41c0c201110850644601c0b1400f41080200d0b58082690000e140c1040040701040b4a0b03200f942e18003c1e07411981414003094400e500a000d001180041c2280c54031014020448140d414956030390554580d0417801811010b40098008034010041d085080c0e001401c19100b0fa5210f210000c101504100b8040b042c0b2404e220205d086940140e11810072001050844071030b0800244000000c505900c0c0070b080c018030b504070680020380708003c1003000800a40c2d224860070031441504240d48616200c0b031038050031001e80014024150350038607241581d0003400c090201d04480c00342c015011100e42c01e0b8108580780800045c000c1200d410a000c0c4000700b4440c0204a5a502004540d901c1101d4140c4800303985800c8510a0340c031082c0010682c031a030040c65207030301e9005541040200b40150034625105240d04041c000e00041640d92510b0070b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 675469712 1250 675468462 675468491
    0x90a050702060c071e0b04060e1605040b06131401021002120121050f0607020f070b0d0b060c0f01020315011d01050c0304030c080d09060206070c0807020f10020a03020601150210 78
    0x40030440c0901d0000801400b10718014101c00c6c0226410382d00c039450410302d0009505c000c500744418800841c003900000d0306010800c40200401c1d440390381c01c0141448221461801106504081d1205050b6409440c140130002441c01f0b203810840d001f014010300008018031801d42099040d184206020681221008098402e50703814041c050014483d0181c10b040c1d02c4070210303040b8020001070b826501d04a0012449075a1810f00e40301e10854100100700040c5513102d0f9900c4204513410042c8400d2404000108051030030220825405e156540041400a000401c4940070540b14081c01c1404881020003c0148040d4180080d1818417400007034803c00074405004450181d94050401c6105a440d00702c00c0755500090103132080404c0d00040081045e0b0b000103000ca2180301203544a000354140d40c1c0e5406680e03085140100d030070107021581620940d13508460041c1000460b401084a9134280c10001d180130030680c041000d84081c80b800c1ca51076680850754074001c2e0351303c000200e041403d00085 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 675470962 1250 675469712 675469733
    0x90120120718090b1c060902120c010503010b1312110901170604030324240203030108100e07152304050d020405151c061109010801031e0507090605090a050702060c07 73
    0x120503179141e11020b401008021360241c1e155038000c2d03601c20003a0808982442e0780d40a01b060f0075000c200d0a2004002d00d4080300002d251a4400d0000d085561b552906110a2042031040072140c4465219a80c0c046080624400f40182031101d280090b403c4608406515600090409010180c440d52a000c1c14100d82510210b0440c40080034880c0c1c0b95121f200041820070034034131100c1c010b484076280308001d1000040d241070300c18100140041008504008008245c641c000000b075005c0e040b40001e503408002501d4080390a10f0f1031b0319072903000000c040c0034402c0d240b0410060b910400e000a101c13544643c481036144550507100003c1c6e80c2c503050b4040c0c40000e0480c061540c4401c2101c2c00c46800f2004c80906445c41f0f22584007070004c2c030720030380030800d45004440f6601d0000c4c1031480100f004c11005214101d48110006881d9145207154a54506288141d000405200d44075035042005040607820b0f140e0041c885c1200704918100f031039009440e4000a03001c01e0b9440c04c08181071081c000707120403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 675472212 1250 675470962 675470989
    0x30c030b0a09021f0201050c072f0910051f08130c090c0f110f0604150212010806060f010915110f0f010504061b0c0b090120120718090b 60
    0x81301408088002c00d101d0f08164140c00c0a00650030080855070300701020013a2100c2c15445030a041c0c020500d031860860002540c2c03c0d82c140340c22440f104680548407001a03d003c0d2058101e0540158285814460b4445280d19819401031864201600003035100c406039411101004032003607090301c141003080e40d44c0143d4000081651a24000c11601c581183c05061710b002e55866076021402410703c1c00f504c940c51461040095002040094005400e85000d00d40600312842d005085c400080740c01c50195500b40c2140c2c90f1544980144207181c5002618440506000d280c018056801c1c4040440d40380d00108060050100f042c0040000c003800380b003010480d200143c01c80d5085481002240e0180c6400d4500340d410f24605040082141d50007840c00e00d0511041d00c50100500413990755881543c0010b0101c2c1c03042d517030344030007003801118041440e1103036008000c0103480300c40710002000024409041c0b035040c081000700084075000503404050898485007800561240b010000c01d25501405e003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 675473462 1250 675472212 675472219
    0x10803030f040602090a0503100e010606050708030a0902120105090a050c040632090f071202040605031503160602030301180605090c22090227010203120406090f081c06030c030b0a0902 81
    0x12601c071280309d150761240b0940140c40000303101865682800341c3c0c8074491014080d145420800c00500b181d461034010003d0244040c14021900f4140440207003182e01c26550542d02d41c100d0000c40c428004104680039045504440400c038882c170700000c54106c3c1fa40f610a88845c1d088031001c00748903081c491880c1100c0c003006041e0b5801481c00d00101709540708100c0d2004003103100d050081c0c2c0310044ca48251029a500c98581e2882d540f11025501b0491040c0324907140d0521070700011180d10703081440c410000785042c4d002192070754180300806135030388a41154011041c0c0352540c01c00841d613501c0c010540009101701626901e0040c41f0603502c040001040c03540f56014040c0e00001d80590940c000c0c11600c81f443c419030202140100c40410020310541c100d40141d006100e81c007183c00d0300c84092034015114203400642010a5603420500103540f0009880340f00700410440e2600e100c00d601c20440c800f0040c4100309550541c0c0d16203511070924007000d45003103d004000781e82c000007a0301c00d442554006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 675474712 1250 675473462 675473473
    0x9030d1b050d050a1b02060a03020318030a0c05011d060f041416150f020709111218060906010b040303030207030e0a0b090a050a0e061012020a020c09010803030f040602090a0503 78
    0x2200190035a80a591600700017804500e641a0f00702c0c036000014402c039402010070b0300e0054500d0044019400c040e01120030005444c400c0d9010060400040603408501d88500e801c5543d40c1c2081030849000720700103842031002022003100e4441c0491981e6204a8101b220982c5071a141031506002036120204645071066488040d0380b500c12540c0c00701180d840c010001202d0080c403508032010b01002d440303c00075074042c980910192110307070000301d15060118070b0981001140301c6080100142561422580c203585506a02d00d09428003c1a03482001a002009035501d4007a074650a48103a203c0a020158046811000c0512400700115040802000c0300038039601c0e000c900401d5440890043d01c42c02032540006501c1c00e0000707804007120800000d60096540c0c0506000844040700454410440501c00768224178401c0c2c0301400c120310899000341118180303401840071040041e00502c034281d005008100884000406850f409640503030090384038080d0502291603406a60400355160043c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 675475962 1250 675474712 675474733
    0x303010312050f120610020a03020d0f021009082d0301050d0f0b0403021606030b01050912010e150402090c090d0f0201030b180a05010e16030c0509131b0509030d1b05 73
    0x613030206000d04400c03140003c2d85440d400d000d99454505080050141e080401c103102d5070340c0a04880c80b14400c0c603005540e605180b440407002200c0d9022806c0340c12880110352182d001e40c00e00040b11100800c5540c40d03005014540d00201a4041481524450502510701d0001c202c5c07641101e0055540c40340103641b50b402e20b40740c040d458040200050502c101d150000254a5100b401241020401a11590702d03200510003400020000e21050140079900c522001e012884108042459005103906120050400c2d204000c29180d014040702c0383d5203030031b20202916541d04a032481e03145900203149901d488603440181c000d44840c035603507980484d03c0f5503004901121569500d21800101c5420840c0d41e0b250300b80d00c119100151403529080301c2004c9460302150299005103100c0e550ba00f040c506080506001945100c0c0200c040d008190f119800c00c264101402840c4961407941c0c01c010b4200115500402d0b51041d90102c1e04080042c013105207000380c24a4500090000e80200640394460b04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 675477212 1250 675475962 675475987
    0x304060212040506190b0109050d1b0b1804090804121401050106050901170702120d0b060304120e03010b130b1c03050a1713120e190f06110303010312050f 68
    0x24200c0c0ca003118401180c0c81c1d240110b205e4419240480f105071120031400f4182030501c0000706007c0340c1240d030400d042002440e00082004040000d005010080b43e036240640b446000c0c1e1100e00c080d480c019170a026003240021070404c2902c0c1611040203070b0200500c1a81001c030720500604c1100c00d840d518140003c910b055022004107615030013a00c81c3c800309145031180c1e08d02c14800316200c0c001a0403c00d44c14034903a101100a101c0284065804641850b8100c00181d56a00c241d07421a40b001c608403155101940000c01c0d15031011046000308a000e01f000c001c900c420200740d054002076a41c0c0c86110900303645032607400c1411882c4e588600d03200c8a0901e0060700550000c401180480c0b2041204049904d02c1d449032841800c06648801c2c0c41c8429030390383c0c00f40c0240407080006009600f620105640c6a5800460846070307100400143c0c9450004080c070300c8820b40d04501c0400580d0045150003e40c0003040380d0441c1d9114209060300781040c2e5080f00c03a0301030910030002c040303000a42d001d0080c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 675478462 1250 675477212 675477223
    0x170103082b110a180806010e0403120c0806011403100902090d0816020a0e070512071407240b0105070f05030913020408060a02070201020c04090c080708150106090e010b03040602120405 81
    0xe41c5071500364030300c1a0881c1c44c3e04005000d1090310101da000704014064810010b403004d070081d200f41000d000100120701040c0603a0542d030b901100140540d000c02c0142c5d13034400c2e03100c42c81c100a0044903146040100030303200c0300c490500071081403d80004820b9825180c0592881200d5000300c01241c031500c3c0c109690426000440040e48200050350000ca403400302e40c116a401084240c60f02e5107080c0710081c0300070038104014048030602c004d00e8018031303080040e84000c0c002c062044105c82e050112240598419030080704491a0305440e201c000682a60003800315412070b03402440c9d18459030750610348030749588505484140c001c1c0d8454604a6001440d07005001540c00e80030070340762165103803e800d00890142800290059000c403404054505080e8810b0b8070150046100b1401662078500c46843c00c0020b44c0f0800141d84030480580032409880c40442c050081e500d0007901041c500030010b000100180144490781c0c41c000007003410010203071b0440711030011980c4500d0007850303d400c0c00d03910345 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 675479712 1250 675478462 675478477
    0x6010e1906020102180a0807290c01020c100c0212030a06052d2b020103110c160806060105120703020d15050f181303020c030307060c170103082b11 65
    0xc100001d00c800e451b06201e180242c1d01603000402030540750400c068040b1100d44600c19000b45911801d0714030960392001000091803c600240e5214803d51001e0310384011005900840707450106040b0f145030340400c01400040c50324200315101e0b110010803c00a1496034000c6030b1103c1c81c0030b03040710118662402300a0f6492500c010405103200b460074400f2146518517820b5003405100751240c50300d5415241c00030740e82c1c010f1500080c551460996000c02da40f1000305a01c03564010b40d01c001047e851080804050110780d40607000038180000049c000b401645a012040d513240d500091686119034161406600c000e02d00f40803404640c1030900c001c500c640a09401520304400c00445402c00c01003201100010348030150b460790f9082c0491641d0b05101d0011021405003100d0028245d41c1003001e000d58078001e542c00100000303554405000014800c0303482c55410443c500400c04a00c0c0d0000b030346e00c035100c10174506c5844400007104241c0100c1c1c5e808014962071801500541400d40700c0041d0000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 675480962 1250 675479712 675479737
    0x703120f020715030c120903050c12070b04032d0507060e03070c0501080c070b09030d140c09091b03070e0109050f0919060e0106023306010e1906020102 67
    0x603510242003240c031054980984010040c282c60102d10652013075010402140407860000c0e4031105140244040d5842e045042d030007d00e0208a0002d030202c18080c800c8030b0003000540d2441c00460740d986040704078000304082d003130004600c034040002040440f406020001c00e030f1a8540f80e0702c4004042c146030020002903603003030f10300b6900c4200c800c000030413140d05641100928414074034213030044400744e40003020011207040034031038080010034082482d030103020000091922202801e82c0c0d401120200e03048610303000d0724801481203003c803200481d600c4803029100b948040d9070340c8255541d6032000d6050704889940c00020004450340c0705141100c0d07c00309903108400340d942d4034100060031070010f1560b9407001114011072150030100035020b5040b00540800b0540540c2c80520310000e4409030310200261304004511a1605807090302504d0480100b07000c0021a80b20301d6001c0164200289080d042c44000c01c08480e00f59a15070b1305840c184500c2c03210703081b516181c080082c040d400c20a2010354 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 675482212 1250 675480962 675480977
    0x60a240305060718030b190b03010213080d030c23040b160302011103010b181912030f08132604080c0a170c1003021c06030b090c01120e01020c070312 66
    0x501ca00c54003082c40c2200d400c040342c6d0110381c4071144010750b140080044001c0c0c1c5641c40c2401e500303a490a00191607403918800020780514070740f5001c0360601d024900c50004051801c582160101d4002c0c4a10b9001c004e814500c3c1c0084e07902c41038980c03c5200329040100080008615110440c00e801130f0340503003902c26402404401403400601c221404280103100480780240114010b10708015003401b01c030f04006000803030089681181065140383d50304108440f03c80c0741c85080c1415040b03200c0303440c04074480c0f070051003074600080d2070707075a02025801c0100300414202d80381d400c114040445942855402c203080307507507030341c3d59005540d94200b0410f04c034000d0005101c0090a02030200e0342e180c0c00382a020140c103441c09194100302c41003c009920705c0034980e007403010010b2060703020034510610b80b06c8080001d40c036045043c14070440e240105500130300d80c0b0088400355541d0384640700780b420741400311020510054407144503019015825000314030344503018000081c03060211410309000c5141d2201b41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 675483462 1250 675482212 675482237
    0x180f050f01031b0e040902090f1609080a02040b030a0c0b031803130608060102150108101d0a060f0605180103020f181605040306051008010b010e03060a2403050607 72
    0x10240d4025118180c0f03540154046041e4880c0505a940780e00301d001080098a44000d80c0050526842a110010014405002c00140c800c09000444c030003034a40c2088181d140c5440c01080d0b0b241ca24100003805181c1301c00d100545610100148400c66911022054070142c0b5400780400306d03042111200c20304225600084003600d00807040714a45150401300220441c2862419295038201900c01411407003451600c8510014001115002c0c0c100070010703000b212088600c00b8103903900c000c80c9591019001002010300c020000720b10b1190b5601210100d9110082070282c3c00a100b280c0c0001d410103034150a0282a9101d4684d05060342e20896118400076021018451070213800c0079031200000940c1c0220b804403204589a44840c2c1107442c10034949500c0e0b60f0f9000580300d00351650201c08a0095060040ca81c00b0700036000c6030f00f020b10303010210406250010b90b40c1c51001d040c1c5280c0e1030f5a00d409800562585019801c1d6034880d400e00352000b5500d1a015030f50b030408980d00c1001406111261 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 675484712 1250 675483462 675483467
    0x11040c0f0801061b0204050405070b030403050a03050105102f12041e1206090f02060a0c0c0806150909031e040914010e04060b0a0905100302151315180f050f01 70
    0x82c0c0042130103820000000e113282d82808010500540191580d2140180000e03940d4140c03c0110301c590300c0303507540c83d0b29404000d90103001d42c2c1c010381145101d600c0003c90b2482c40d940c04010300d1410410034a03c2c0305e4600c2400c014841d042c0d40e4044582ea00d0248402c03041458511707000a1040f2034011000d1510031044e0405070481120314059042c0d04c2e510520f5082c00f0580c150040f00c0000e0194030b9074401c1c54550390025400c0d80c00b413910300c004550407020750018440480c085034001c181e498007070074441c0351184841c0300042d070705914140720f00d00e403d01207069003a007042030b9481c0050207500c1450640b81141501c20030b421070f210701403d00b1b090207844810905610300d00b5049884444070398415031141e580d6031000e418402c8510346c00845030400021003000e45e004e002c3c0142c142e400208034550650041c8143c2c0f100c000c01100d00450304000d29614040800f54a4040b200f4a038000211403618083c125400801000c5800054002e4038020034090325400076201100e02c22648100c0040408006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 675485962 1250 675484712 675484727
    0x9051c0207083904020415080a0c09151e0917030903060a4a01050114011809050a06090b03010e060c16140604021017040f11040c0f080106 61
    0x183c1c5000b20000c01a0f2a201d54140d82c0b51a100c4083d0a030040944100114049030801e9111006854520b081800c42a03080310b5000c3d0000a00881400090340080e4040c01d0010140f0409000749100c80c001d168840c400c0601001007000a400030445007146940188040b0481c09a0b00a114040d2440c00901274004101ca0a16901a0142c41182d90b0009035000900c1c1420400001c43c4850001500800c0e03c00340318103070707200034101e076440c1c0049001c0f803a140c04400d05280d1515a01d03060051003c5040307025044e0a000091910300480102c49072840314200580c0e02c40300c20ac504146c14000e0080d0240c01250903900740480c00c014071100d0104040c00c1e02c0034184c0f031260b00e4100c0c101055481004900521f401c5c4021034000d40c44080760f5407016140703089003400440384d4000b40f050100b1817070111003030316094800f841d118080c00b6606241000342540904000c00a0310308500020410080b40010300c1c4000004008215690345000054080096045500001460100089101c034081d60301e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 675487212 1250 675485962 675485983
    0x616081603020c012405011b020d03030b030601060e03120406210b030d030f140106140702032b08220222020f0c1c08061309051c020708 60
    0x4921009856801402080301821503103601055001c0203c02c1c0388500900460700450284200c50016602d25091a200016903400c050b042010700c00301080b00190503012501701c95012240e00101b02242d00c0e0036030081801169054042c0100b4000081c400e421950124480307c06400380c0301000c4041109160314810350003030b0b2011441031030505105410003c0da0703965010901c0030010780e407208580002c1c0f50900a4182500280e16405480500c200e640600c1c411010025005c040650604002401d20000416058a4024003240c21000d540d020441130840c000200d1035081c01d44090002c0004652450684401080403007010451903461202c45081d009400a1200ca0a03071140e420040c150300e20451941d14800303c2c3c00000345042d041d1000307100031103e04120f280d883c034000b01c0103410320352181c00050748040c4400300d59654640010015500040490300001c0e010140c030b034040010305d4480030280051044115035070f914100350b103441105603599000c5820243d642c4001540d10401040c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 675488462 1250 675487212 675487217
    0x1e240503180c150a0e0303071101120615080618040b06010c15050a09021306031109040f0f060203090f0a08121810020409050702010218190b070b01080616 68
    0x108030000319000740000c0c00050055030008840040054103582d480c2c1c40c111001c01d000500c561265400c945109510a4203501450500e00641ca41549524102c812a41440703d40798074040070b60400da2107000a8468550b11442c00f00c10300100825030707602218058000c2d580414000c80620303030390003107d02c40d5502241c80d0807960b8410340111054901d1140484400c003107000080442c0c405805028895000d0000c001403d0300240101300d42da180c0c0540182489250a0091010a152400485242d182030b100c02200c0e4a80e49403520480300448000b8003941354411022080210b660015409999020112160106503c52950300c1c2c04200100800c0c40f0002c0040200006a80c0b0f8544e0b484482084680c24813180c0724031030360407c002c5040280503507a00107024070251805101e0a030304285148000c40c00c01190f000d240e801c00d4070099101d4030880308040780b113105030002c00609014002100c0c585464003002e15203890202c0083c0504607041c0201c90010360001022503c1e100c40314902e9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 675489712 1250 675488462 675488467
    0x1060f090b09370614030601051f0f05090d050106050405100b1e0903060115030606090803030a0e01020c15160311070f030e060f1206010305060d0611041e2405 70
    0x48100b18903443d08000360b198861012203840140003151040e04014546003001c0d04201c06a1000c040c184081604a94864016404507003903450020022800342486070801001031300356a0f8050b140c60040e82c2c0380b0f41e03003c0000034500c4104001904960100c40055030280a5501c45507602c4000811310b0149040030101441202482a080d0030510044e4207050001c51400d50468003090900c04260024441640c000010350012603051048030010280d03450301840c80d900788a03107a500c0e407201528582c0c40300e03120400510494400c0d411a01503407400c1049415103080d4031181c10344102c0031a00b00c80c0148000a003c0b4415010f0f0003040120110303440e44c0ca15044c16a07441c0c3c0805490180254200011180310343c201e51103400081860640d504000b0341c9500d00c0004280c01307418010200d41c10541040d00f40100742e1035004440e25006ea0140000c02c2d443c1e08020030b0041400f49512403c810a064448003001000b0280310505880013024000c1c1c031070344051046000003841c55503a50005108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 675490962 1250 675489712 675489751
    0x1709101b030c090812030a0609020307021c020312041407151107090b030a0b0406020706021215040c0203040b0c0313140306010f3006140702010c11031206010c0501060f090b09 77
    0x180c003d560040c11401f0029541c1d841e411040101d8204448000c0942e00c40c1559080820481820300fa140e2041c0c4021481c0c21054056403000220103030001308244000100400740c81414400140030301288074011401c5041a0001000040340240c401918080d41e500801c03030182c180a48088048043c0040ca0015000e45d500c001910000380144c801c16400c1c002100014614002494130509a6100f503400f401d00c412000840321007240301c24403861424024121003900481510125511304c00c503252100221000541940320b1900802c06140704000085a140c8401034488907020054003100c0361a81c0322113030402620154052042c8601b9114180d21900540c8074820001c1031003001c0d0881d0390709903aa27070304050b1001c0d98a00702842c19081e0070080e0b0554248281c0300400fa061070700310b10042101d40c68030348038400d0902da120f0340d42c0650005020b50f401425081d180c50361000082200c0350752104008100091801040e401c0350a003030b4100070394a4904510781c010105928500106883c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 675492212 1250 675490962 675490993
    0x30f1403010821070506010303020a1401020711090a020405150a0206011703181f120e0d0c080c0109050d020307060605090402010e040c020c0a030b0906060102030a1709101b030c0908 80
    0x1074008183c00800410000d80094810300589009501c241c000300b401440724909081c0328114000c90700740f2a0700c18031107440411400455a0101d49040d141c150503501c6042c0c8540292045070042c13900500074030b0464040c0700c00d00000b050b40801950035100566201c0175650424140d0940000540e0710078041d800f00364071070b01807216107840020329018814501c82e203075080c83d07003110001c080403900c001000c0c403028459004400b015400400a02104000c10783d0103045a000a81c000c0c0c45c0000100d65010004070950040403250b41060031038885070b8030001d0003980e99218070300440301d440c10b160001131a414614a21b60159505071500c2500901d90803d02c40106041030107001103200340103c1c5000c9403129030804000c1e50154407201e00d1490b040035090318000024003024115070003003000da60324aa1100c00480111445a10510f20b1349139940c4c0c01c1d1400030700c000b48020043c40e100180e103d030000744454070018a100d813828002c1004004007600c110340c1031710841180d5040381190005245 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 675493462 1250 675492212 675492253
    0x312090a0203071e17060403020d0306080706110a0638060f030403090f08030d05060634021011150705222105150c0909090c0409030f14030108 63
    0x1c100007a4003132201d40d52001144603120618040400d600110305000034103030306022040100c1c0d075500b014041c40d8508a03003599245881d10802c020003074181421141250f00388081108070f50050818020703049540707900004c0300e00c81495110b2807030030400040c010180800000d82c0200005000c681485030b406074420407075100a00071401c218205101041c0301d1103050050014010700d41c0110344410240009904941001c1d166511420003402000350b0740314840e0000184290300c685906210001c6541c0814900807a04002d41c05600050720418103a03000400d6040d01c50b0034021500e0300e8540d00290840220700b0b44003580092300400892101481c8010381000c2c4a28600d10038407850fa441460300c525200103c0210340c2c0181c0c041e8540d003481010442c48220341c1030592800c41c0b07800d00409210540c07040c050402c0c0200c90950020700c1100041c404002c0f9980041c006001036003d5140080540c10780b08404c90225200d908000d4440800780b050700c0c103940c2400e00503c03500000c00088903184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 675494712 1250 675493462 675493499
    0x11d0f060103051812190801080d1107090c050d05062d210f0606030714091504020d1b142205030d05092e200a050312090a020307 57
    0x518040010914040c040000000c90380c41641030360f46510180f4030000c1c07503089551b50101045440401445920f0700030070024004065818102c94092003084410f0810103140d0140661502d40441e1028044d0850300a000128901e40304001da90394a9041015406030030b18011050740060341610406202030040314580f41004141c414682603044c4210a445034040c807034602c0340c203c001c0050710b0110400c08140c0050003200a04038050030001c0e85034102c0f2000c52000c2c42031304500085100302b15600ba1002d140706000d003003503665554410402d0060011031080c4a44454040201c5148500c10701c502c400e0f03903101405240ca80300c1e0600103406c1007041044001c28550f000100000c030380d9010051060a9040c540b140d5481310344000030041e801000d400b0340d9110711500c02c2030341490310b528108231225002e50b0914042c038044014100500345003002d0312540344e2088580c5e4100703100c8004040e055100e0f00c40c00c60301003540c60f940010344550f04804000d4065014900038050003c000d910080749 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 675495962 1250 675494712 675494731
    0x80115030510050a090902040c090501020a2904030c02010e0114070b06033301061407060218030d020a0203061f0b07051203040c0e090616050715090605011d0f06010305 74
    0x42d60b45071400a0416529907006110700c03940c0386030910440c185070042070604001c0341000a101490840080c5d110014040000d0007010f09091113001d1107070604070b42c00000525442e0b02c03207074609480d000c0d0803070180700000e83c00b041e0341c2401744c581c6622607002e52a1120300e03980e030305003840000d07610b8485115001d0100765142c042e1107140b080d85140392a28041440e0300004039045020540c12460070510182c001d0803c1000d100c0040c09043e950070106d0700d4455000c030700184d490040188909100c410420515407500a034400c9840e21540017a611300b900b4001c50030342c0c040d9100c00d003141c4140e031055140d4849820710000204110780e101c0001c0e11485004a050740c18154181e804101c50703038030840741220740c0c410083c0180669104815090b60040040c2d00174601070504410403d018900da01240c41005400210344c400c0200030428450f00c60b11b1072000384802801450000050310090058101c2c0c210389850288a606050910f94050728039070000031099150701c401100a0140200b03410f41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 675497212 1250 675495962 675495991
    0x801051f090b09040b040f150b0717030403030902030f011b09050f060f0d02120411030a1104050c0c03040807090b0307120201030903140a0c030809011a0d140f0a03020d0801150305 79
    0x1180c40380d01403c40c1c11003d40500199840ca070725510958152127130803c4503040814002a000500940c4035070b07088480800c0b6081d103c2e6100d01d005c41c09450400c000030b4148c05407030a020030880b0305406c00381ea80358480706544800014003408588082040c0b04207a840b1840e039801d01424200752008050684580c0051031030044220380f8102a40e12410b2601110148078041000f400f440500080c0000e500301d01420202c0800c1d16454600d0920782e1085108590b44c0021503504040c1100311095503601a083d46d8440d0307030b00c0010319102c207141c0c80341800b16400c0001d038507480c0c6000f0450034140d5103001c40d00400c00520b500110f00402c074101d012420701012030204007600c03241c80044d0105003144d5889400707000c07652034014070448001e011181507070705088103d0040e124901003103524039800e99002a10040c00d0400400c9921041d84400d000c0c01003040648061101055500400d4001d03000c507154a040000c0072a00070400b407003103036900116008449421846900483d810010000c0b0446 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 675498462 1250 675497212 675497231
    0x201090b0a0315060c0b010f060509040e0f160503010c090f03064b0209030d1416051506090403091701061502070302130504081204060e0d0801051f090b0904 69
    0x10a098684e40180c0003143c810243c417010007443e140000e0142040840030340045141160183c124050003032990301c640e464601401c040e040c100000050304171450103e407a1040c1c1e82e801e14145028078040d40740179508007460b500655010304d515070200c3e0b040c4c140f50480f1138a0340e120764008020820851001d4060083c4041c00d000c2c2c07602d0165a0394880c83c00402601038060110590451a0792001c0c1c1054014414a002568042920400d40b826400c1140020041d0281d908107445102d48142120045a9000c03082c04130000741d104510342d0b00d071030003409034a82c1d0701080260341d03040714010001010a00c00340003180c0c1c5003803081000782c640310010134600d8880e01554042100284050010b0b0702c856400c00c00c0d441d00c0100008070104c0c14808110351304060311350401d05c1c4180d8000f450704002003401f040c00c000555002c401c4801d4107000b40d54802d2000b40c0c005041003000e22a4a10440e02c5a00360100103028010701130158100c0d40302c0c028103c0c900f65440c100c50304403e0445a02a5480a411 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 675499712 1250 675498462 675498491
    0x71401091110090e0c1c090c140609040207060b2803060b030f0a03030b040b0f0913030c1509030f0f0f0e12010e0601050a0806071706040b03030a030e060109090201090b0a03 76
    0x503409000008045605c0c1e001d60341c15000c0941c246e0348450a502e0031b03e001800171070940c000c00400e441012150441500340b241c081a0350380318480700c2a4010f03100042540034401640d010f46203c0c0000c458000d154a80d854500c140100840d0a411101a009404000061969000d0f680c840c82c06001c0d603a40d09040d1201d40e050008a01d0103030046034031000704007440d260600c29410400002c40c0e001081640c4000400c032104030050205481d08070840099061501841304800c51a80c00603909a20200301640000908403a8408030b000c5105020058900c9002d05110414880559280441d0004481085074506c1c14404000d80012400c0509544202c0a005201c5140300039002400c541d40b400061081000041e030010310f440d0011400e00030720300d42c00f60540014206001c1d08800585803000007900030800000169810b00c40042d03008505a01030b04480780d00503640d402c1c1c075181e80c1d031060540191810301d0002400200103503414000d812620f00508170b0140149400107952000c003150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 675500962 1250 675499712 675499739
    0x2413030609030f0908070f1401030e0a21110309091510020a111207090c05300f06010c03080408040509010f030b22121205070507140109111009 63
    0x1600012443d0250f00c03103150304020410020a000c400600406240002c41ca12a140500078a16a0310401c208020580c0c800c0c1c0044505000000c01d4844010142c03802410034080490300c451100001d40d01d0401080c0a8080880d8102c580c80296183c0b80d8070340c0800428081c001c1045080e02507002100180340c4030582e540081d9101500103203801c075554102514000300403107496101d08122040c01e070841300f01140040440c2c561038404206294040703810307152401000300484070381c4864034840011018079017100e106c6000807101c5010340d071510040d20004120480d84103001c42c081c010300d81c000920412145610500900c50030303040588510004100010a9121402c202660300040c03060251503038029070007502d0b0340c2404000002c00700c4940c078502529040503140a19880c40824030300c0c060341c8100d4401140e0f500030045440c0c103810280c41074015020548049100105603104100140f217540ca1182d04000d1000c1100e05c1c1004100c0d60a0030082241d007044a00c00b800540c15000380076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 675502212 1250 675500962 675500981
    0xd06020c0a080c0706080606090f0111240105040b0118060c081309060501110c0a060e180108070f05030f06010e0c0403080301030b0403080a090201090524040b0403050c24130306 78
    0x9800d0251130490001d01941d405456244941020841c4103415030356185e10ad91040803c1c2800d04490001c9899241403400d4a54070300d156030315020302c0e5900486240c0030030741030310012501040b0000000c001151509031235056410742c203030840001d1142070f01421480b400d403032040300c00130b241001d60090340d003098255a10003030a2603181c0600340410360b00320b202c003400d031038405c4003c240540e00f40c070020340380d038180340301f50001c0c440000c80030116038403659030003036681d07040034011052540e5604129039034500d039101d02503102c2e0404101061354640030421840baa00317810000c000c0c0e0b03400c18000c0045044003418514401c84208070000018401c01d0240d8000c50040441102c140b42130b003409400c0501c000c190310701d00f92501d0ba81c400140c1c1c0000826080d0f800c281c0b00008030724081605203107640b00781d02952401b03500c0401c0c00901d1503421001407054a00c0355081d1141c90314080f0900c41d02c0c04042090741c0c201820200c400b401c4102c0c110141c00f64000251228008a03500d460b40c500302d8080300c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 675503462 1250 675502212 675502237
    0x21e0c040e0105100501080408041401030f0903021b06070b0f100302030a120806060c0303070f09080a0f060e1612150507031523010e190609060212090d06020c0a08 72
    0x404000b9001201c13403070500102400e090202c2103140c1b41d50740050500c214010303c0240c3d20350107000c0803280d2003030f4031015803c40d00503003c01041081c2e09003c0e64550105581072888040394207804600e04121060b2425158461a51750740d603150f01140101c20380c0000e0109900101d80000003016079800c000b101e1109020740d107a410f000841040090415500421042c0503e00c1000181c42494000080301c1d4025410301d0540b4003c0d5103140d0841c1c5c5c1031281e522401c0c0c503109007907100003400060511040d80c144a440e041180e240010b84462716101c08807240089424800b030104a002204000d5503401d910504502856115030510001203407415038503240080c0d50303600002017681c9420305500190281c4c2000085811101005000440040292504102032585946041c0d22103c544c00c085400c00c0246510213921480028a4042d00e032007000018820a0200020810b0782801c56280c11006048a058103640d030321030300d0282d4403000480c01d1601c51008078101040061000c1d20005000c00d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 675504712 1250 675503462 675503471
    0x272d0a080a1107050f01050a0c240c2006010608041505160324120f021503041b0819051c020717150a0b0315160906050a021e0c040e01 59
    0x920b245880c003081500564042c0d40501541c04540e0303005010b94421582e1850592031002051800084210f091803010031100b00340c04c61442588020b401130000001265900d035008043c00e480e820412440c0321140302070381c00040c018000311348910620b550080c003900e900c0e02d910b032600e0320000441303408803800c19559401100c4200d080354540512000100c009039105c1c031044001030440b6120710107104000d00118000c002c4170802060412207a81560010702c40240b10150024403038081e402150101c8910909040c440c00700050031015409035440100100741044281888003004422040180c1d943c0c030a403d0480140c5001062032000c0c031929a0240401c01d1a00b00b44c0c01191134a450b4075000c1c1e400140c901840c101c50a034807140e000214807000703d5100071000120303041c00065011415543d0440d401c01c40d450142a103c0d10341c05246940340307a9810b548850480341802041d41140040c3c0082450452440004800d0005c50318a80e05503103041354000b0000303013159070203d1400040d0b5140d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 675505962 1250 675504712 675504737
    0xc0d030b1807200c0402031501230306210a0f020420090d0807051501030203060c0c0309240c0106080705030706090e0a0212272d0a080a 60
    0x141050a40811910200c010030b0308101c40054440c0e88039a40078000408044112510780c5410030004a020130043d10031035582c10031031082441000300c1e1001d1404201c000100c040d9071041c0d12541540300441003200c60464a45404005041c0c0d058191590a45228a26070044070020701c0b031050350342d2154040a204e011188117103c165125136035040a424184c04200410800200807074014220885d02c101c050069854070100b280900035001c0c08500c40e401d0440200300d295178886042c5e0340220200c0d500d40d81c1d0881d41d200144581040100140c1040c40400c0140c140507a83c0c44d10170b40f002c0480d807121140d40080c14580c6c0c002d400c9038522070f0b450300420001c0342d1091241a016240681c0900300250900c5409030602281e4410f44091200480006071f00d581c481c3d060310801d0003c031115203400c0c10f040b84240240c183c1d0914103078102001000500c0490000103e130300d60070b5001140510404071008a05403c4500e24440091601030700400f4030000300040002c040c00015511410648241d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 675507212 1250 675505962 675505969
    0xa02070213090b07020c032d0106060f090f03110108040c05041a0a0f12120e0d0609030e1032030f07170423030705150105011812060b01050c0d030b 65
    0x5004c072801d54000c4100081e642d00c0125004010385014030030081449494031300401e0700003d01040810f29480c005021620a600640b4030480c2c0c01e444d560642da913911808902c000e201140300081103500040b0200300994060003000e039100b03020b4880741d00515038900102c5e0a60740d140003d02007201c20344000b10010b24180c014540501005504c3c80c5686040900003410080030711000b41007007500c0350080c2c2403e44580ca042c42c0782003016040c41b081c44010310b4060060881404c0440c0403440440760303c000c9041c0501c450320386103443e03681d0445102101c00b000e00160070812080341d50f4443d2103030b040d0303925000c5c00045000d034142d1502c08c070350707494200c0c401483d0741440c0d1403111024041c00305020108045100341c043c0261410481210060340e10502032840c400c0e104010454018400202e10000c8206c091034100c031000e80350342032520521001441201e0300ea0240c3e03034407603038150030000105125911000b4031030b01c11305145103450400c004a62910013900400702c0002c0c1c80e0040907040d401c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 675508462 1250 675507212 675507233
    0x160206070825031d010e060430020c09070e010f0f110318030d0914060a091d07030c02121206060714030a0905270c0405040e061f050303120a0207021309 67
    0x10113000800980080300079298030b882d005000508442c0500381c108282d10150240c1c4c00010311024100c4900c0060800080c3d141c1400144003072258000000040d5118021151700301c803e03405035601c28811072007220580f943d41218900c0d03c10444401e0a180d02420104010040a044011f10b0601d10040704205498104030701c1c031242c100302c0c040d4010070040901c0c4203a055003000c101c503c1350325803902070708c00c0781e8038442035010409110820418109a038150404d140c02404643d1b001e1155030040207051380d40300500040b0225400c01000701361003058a00924540203000100300030b160200c161035201d0780740005d00032050103400018402e915107400c9908200100001d841842315000c0300c50700c2001c0d041038914403451040d40c5800007203140b4190720441380900801403007001300804e842000c903030324041101c1481c1440c0840710300c20715004901a2003011540014002c0d49080390b50b6506014000000e0000c215a41d0207124060043e81c417200380700116105018002051030302c1342400d01940c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 675509712 1250 675508462 675508511
    0x20306030705030705060f1c0603031101060618061d12070f0906030221010b060c0313050a0f06050a0e0a120204050a0b0604050d150c02011416020607082503 69
    0x1d600801c42017045494880503146811080f83c1c40c80d840300b007403a07600b805051a400d0000001442c0c440c0100400d50050902e103107448105c40200001500c41c4810b6454084480d00045e0300180300b1803c00025200f846450300354807910000c00942285100440c0d58615150000481b07138020942c14048002c0b0b01642038005d1640c0502800780b28034640208070103800710342c2d10b58154a0600104481c8250940000c0214840136201d540d0380c02d00722400c40c0d00d1b0f1f005040c40321110620143c00240c0c034a010034141c0c1c01e0300c100c00118512146001000c0c0d445610025001c0180002d5643d128025139940ea8148010706403942039914001092041208444000f01481d0b1580c0ca030811610301070300c6070741c1520140d44003650168481d10560815140c1712030329001844902d8149101014415419080f103040c00e5a065110a0b050312408002d04170414100446001030740100c000651562044642940004899a010f4202d00e44409103140455007040c4520100341c991750120f00190008295910f403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 675510962 1250 675509712 675509719
    0x80705061006120f020c070f171c0e031c031509090c140105041205030a020607020307050c100507050a0302150105040c0c0b060414070f1209052e020d020306030705 72
    0x4505104000e0481003440150303603800703561307460098003294036541121508803c4408a500d07040e912100c182c3c03280c1080c09902c0124100011001ca00840001c4903810302907065110f0340081003902e400c0712114064041c1580c103208183c0f41e004054105458440455075590780400e407110380074628103210304580d1188445919129508010030100d604090641d030110a500320b00002800c0100d62600903500180700700300b841042002000701c0000288000c4d083e40d003d460700347c0c1e0b9588081c2c1c0c0f64024208041c14a81209040b4195841c1000c0704034400c80304c40c2031840c188503050310f40301d04d0038483c000c00700c015034400c8410351b8a401c03a41c08882e0040c1400c87c0c042c0308241c61b14030300901c83d0661110091042d034451000c51034070760f140c0d000008018030f8013105120710b24040038014030a50b020440034001c9585a21081e604501d02d015a40005420100518030b09400510116640181100700c0000c0015010203162240ca00d0005114210858a0250312810324004041c1041150ba001511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 675512212 1250 675510962 675510991
    0xa0c030801060e010203031605040b0a1d01030902090c0304050102121906210b0c0f0a051309090b06010c060b040606030e071211090a060e0a05070e09040503030c07030201020702090408070506 84
    0xb0f03245e0b40002140e5000d1041c1402d18401c0c50010000e8441d0701032504030703203034001012610700c0b042c0790301c10b032011060f40031482c00d002580e1324100190111514484003942040c1d040c03001405610301103000315001031041000502d4108042d00c0c6d000c40303200641c0d650503001100c1004440301010b500078040900542400015900003200d2034001c0a01d00300001040240b01c0c00000303403202c0090017902c2d0b0541040140d43c1c0d880601c842c0003810717a8045d140d45042d03c0360710708000c180039850784240c0d0f0381280d1200a500140e1146001520302460442044030b500c0d8440070501043c2c0c48502500c8010505a280400ea090305542e4032400c062003504070407620410300d4482001301e443d030141840200750035111401d107615029645406420341c0e42041e11414525000e0010901712030b4482ca02c5070200e40c0c3c4117a1010660020001c030008151400f030515801407000c120942d840704000c1c03c050b8400d00005140c481e0710382c042610300308210340c00c3d00c80c6100458a02c0074008140b018603840007038041d03142d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 675513462 1250 675512212 675512237
    0x420804060e0f190606080d0507050607050304030507030c050139020c1804080c0708100b0402090f04020912010e010606020c010f0801140a08060a0c030c0203040b07060b150a0c03080106 81
    0x550703078440743c0c100e0580310400c00078030b105100c0c00b40d03c03c1c0040d01c1c141c0152901401c8180003c6d110b6403103141c0450700ca20941c800070350306038070034402d07240204e40c5a41d80328504600da071811a00300c02800402d0b58155038641c2003460403e20101c003415000e132403103820b251000103a072401c04205544d01301d4038295005240e800d401030b660700d00b4810507555603030f00d5a050b9446a04004039603020b5908000d00c20b02c960180400c2c54100042c00800c81721040c40d05001007030b5500b040c0003d0340074190741207030040c003080b86508151415070003400c081e000c05044c00804150042d00c160030341c6c860f20304074480d59642c0c079801d100c1903906012800b42c0d000300f802c02601503200071500401c074080522910307940d1381ca0300000322465070794400560f00403c624400c464050902c50030304001011003081c10004285454a95400d00d0b00100030303201100d04544003e420302d0704a8072210058020113048075031044001201e010392030440006400044000da49805a00354940303405402ca00041e0880300a20802c0400003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 675514712 1250 675513462 675513493
    0x30c0102070f0e070c050a110a060c030c060f02160803040b070809120a0201090c090e0c04061d04080706020a0c03030501050d0f060b030a020909160b0301420804060e 73
    0x840480c0e0a003500d9200c0384d0383e4a6000c0740e51617520100240380b8000c698002007400358800803607504580446500c0307042a554001611000300310403000340442d002000b0200406c003154032003810320303002c00009440c180302c4000c0fa08140203441d0045500160200c10301061108540815604c00e0700350500c0c106601303008101960319601da04034502d11903000150602120310030341046125561108101081540794060ba5001d845c07040802e000340d2161690183d03180c40c16008071000c40b01c50f1120303100060888002c00401c2c1e4002041601e0b00c000030840c039000513402c0c0c4020000d55000d031fa1135904043d0070385801010740d501a400f50303115400d491b8601c004110184c0201807502e07404600062000710b60b07000309082015600020307502c0524881040810a0007280c411540201249046c0542d0344408440d506404203000b03500c40082c440800c10441003007603106201c40c6451010103969050352524442c0c50304200c0540100140140c170a0100300007250054a00b6900038501600000683c000038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 675515962 1250 675514712 675514739
    0x706091e08190525030510090312180b090106050a060f0503220204060608160c11121213060f0c030f05130503070e0f010f0608010b0a05090d0c05030c010207 69
    0x4203641c0b50410150b00040000411890701c04140040001c00203601000350300d041d802c50340c441641e00b0b00505030108020400c500c2020042a415290000d82c21125600100200400720301010840b000699502c0856000c00e4011710401c6200004186941003000b0310914610552150303083c45005941c0f89140b9400405582c5d00c400000c00980e6000305001419628803018240039421619182021810b15071001c101ca00c5a942c04c1b8014502041280f400c680d142110b0300c000c0c09405480d4030922441c034103100c40c0704154020f00c044071424404960500c01540c000c120311440c0c51010344040050a800035840f2000c058681807008207903414ae10050210b2085210580070400005040401c40061031808405840c0213421610011307180d82198450020a544038140b901e441c0340000b85000030141240d0030f40380e141c0d5400d0502c1c0d107003180e030704c600d50403003109542440401d00004050351110784041405601580e00030440b185840705060a024800140c507045400568003408551002e950 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 675517212 1250 675515962 675515983
    0x60608070e040b1b0d0b040b0d0819020a02100c03020601090603081c020d060602070509090303090a080702030c1f3f0e0a080403060506090415020703110706091e08 72
    0x100380203143c0d14840140c0c4100c4204ca04402d00702000309001d80c00f00c42c10b500c59980722206031404c0201101c1082088404a0720403c01440001c003000807007001034144203100d0a4108030300458201145990000d00b880d86019418800034944011440926a04200c001d00405011000700b103101d0854031800c00710710070071058031545450700d00c0040c86066294101d5451103180042008001d8031424000c0d120361030b178070886105800000110b42c2d85080442181c1c0942082c1d030080600701d1030795580884513001050281e0b4140034a07107441019072581c040d442d0350000c0c5000300001001c7d5444020f44041d102006000b02010412010032503c8c0181c100c908004039100500c080800912108d14003414003090f000300d0714007801c444103041142c80005001500d203c2c01060060b580d0710780520a044100f29005400c41a42010280003100141d0007000c102e4001d10780214201c8402010340c1c58250320303034404000902899001c1140c030740321450a030b43c1c80d51402d0820b2010381c90401540d0740d545400d1b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 675518462 1250 675517212 675517223
    0xb0402031918120207090b030c011b0c0f0b03090f06150d020301111204120305060a23122503050d0f0504091503020a0806060904060c120e010207060608070e04 70
    0x162810b540034004103003200366a0101502c1200c0c000d80100039160080b6100e5509a5418904800e00c20b19003c0340c211141c2c0d5040e520317507844941c01100f0b150f500c1c0f50030006442100203038401103180c88004501034041d20380d500006640c1c2c00e00300d412030320700201e04000c90007e4200b2028003412682e14102c8961034202141c1c1e19000340c165000181c010191200c10710300203800019071150103003d000c0c1c150700c11030148044603502000b8800031380c00d69000300c860640c44000d030f00003404441c04418403814801001d000c13034404850780501080b2600245101005540d105208001d07034505c0201c0081c0c00020b0301144c40c81158a1559100d6450351600c1d405003e004c81240340d500340c1482101a05d000700070800c010704c1f030013802e0001c0110301d6800b0300040c2e000343c042c4100440c40c00030008560b801003001030003c40d507560719a1035035402492a68600b01c1001020300201d807404200d4058607403060342c04400160759049502c0d000c4c040300c03941d5224003060303000054100054444003008030751203900b21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 675519712 1250 675518462 675518471
    0x8070815091f080114090609060606130504020307030b1c050309100c12080f150102190302030906070b0a0c0903021302160213020c010e120a1115090609010b04020319 73
    0x20b440c1d002490301c20b000030011601460300008000005412a0080858803035882ca900d440ba00180d586410048503996007942c44140800c900c0d040680080042c0f90840f1500545c0a4075000024242da00a442100c00262529014030641c40c0410310101082000c8500c0c421443d07003950781a4590103000e40380d520415203280c0605189000d4940808240d600144840851032004000742000340c041e034a03c00042c15200004896011070302000014280580062600d50041d80003501c0b0340300d50420407000c43c0400c2c88180010740b2000050162a846114908450b00e8140c0300030080380c3c418012401005010b00e400c00240c2c507038414224524003006030150b40c0d4807103920b0000f0742c0304042c0c00003500200ca408030081011b00ca5406441c1001d00803000f40544111030384459520031900940c80e4403442c04228070f00e080e500031402c580c0d0042d95102641e0071404008090001d403a81198a01e40a0300103408000b207400d4203108030620038404407405c5041d0700304003400312940310030486040480360f40d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 675520962 1250 675519712 675519721
    0x604150f060c0f0203070b0c010b060901090b0912060a23060f0d0503040e07031a01020c01020705040c0e09090703021216050d06092a080604080f091f0905010807081509 74
    0xf14440025141e070064200c0d00c43c140c0d5249254001d6100b02d4003a1500e5180c2004030000380741c00c50460341040c505944a0310071a040410f0b02c00c040d0b000d41201c41d44035014610000f01c4003000c0c4417a912032a403e0100007403e5803441c01c11040041c07542c884909001d2040204800b070b9a0381c103c0956008016145641700880901d0000d10394030407500416142040780c0c04200d2220f03810b0300401d44100300d034074000e240b18000000582c1d4a070002d1459a01580040e4801c3c030050801d984903c00b1844146448207281411002040e00700e841620000f090f030300202414402c0d0b06241c190141d0319281200102190b1380b0452003100740034014060203201d0903010306040d003881603c0c0c00c040009a0040c4001001450684a900d030b41c40d000710390740b22402c40c244000a20710310b022408920a81e00300b21054541104002d000c1c0340355005403942c44d4040c82c4203a04855405582c1040d10f40320f070440c0c40d004542400c1c44005403034010020001000c00c5042001c07c441000c4d81000705004003c26600380c4560344a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 675522212 1250 675520962 675520973
    0x2701050121051e01020318030306010c0b1306110703090b03250c050318040e07061e02070e090105010e0f15100e12071a03040812040f0b040b0604150f060c 68
    0x110b1543c03103d46080c01d0419462044410b6008600803402040c01100c2659003140554072030004850075404181c40014020104615080342c0b903201c6400980754407034040382d5440c4011030b07001da0722200f0242c101181601c109500b010640d00640322144c0f40034114908001c90203034458981d610444024000062005480d000710001c0007280e62000c1602d881d0f152102c10803d1800300c10031480e120780e081510701c42d4074900c0071486c403087c5c507050340d940000952200d00d0507640f102000040c8046100354003001812208004209004805940c0041025450244620f111a0b0081c1040c4080f010355402c3c010b000350050b03900c0345040000d66404100c2581820f00380e88003400d0035440e980003404210408504000403c0c03000548540340308542c040007540d081128140021500101101c0e81004406103021400e4001d50f403085c810000081d414115035200301515800f514100e030302010791401e01006107498002c00064009030811380041500e0700c1e4020580e4000b40c8a40014811507807500f805210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 675523462 1250 675522212 675522223
    0xf06030c120302120f1e03310506071d090c030a05040501140903070303060803071a1b0d09200603070e0a0909050606031002030f07080606070605270105012105 70
    0x220103241c0c40e0701c80500900b1102150700c02e01c03101c502c0c442446d5405100b40780d04030540e4001c8140500d08090340750302c1c0304a0300306800c4464480401c42800154900000c40805c64680328181c00d030303150305802c4005042d200041600b00202482403100d2010000c0398000341050780e500c104144004181621281481401014428402c50b1543c00b207004200900100200030010540f082d9030800400e580d034040d00b40c40b4001c502004100c0d0141024001c082d250402e1842e03080900030054035144803003600080319036800b810140010035120700899040c80315001d2000c1000c1d055141c80141415014001200e40c40000c1c0240184107144800c0c3c15140c443c0e071480e2014109030842000303040c00d541801c0e81e440d81c00700c4078248240324802c5410b40f05036250003030b2801003221040105054684200640d03100400500300b0703070881e0080c0040c1000c00d10b2805418003e00f10b8204030110007010042d5a2000d040a240601090307040400401c407142d8210142540c040c24403c00d40d035108e42a00c0c0032810035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 675524712 1250 675523462 675523483
    0x15030f0e06040503090310020c0d0c1b060e0f010e010c030f3605030d0e040c03020702090f07030e0f03120705040b04080d0e0a060206070804061d100f06030c120302 72
    0x240300700c40400003003102c00001083d201004800f01c2d140c2d0091205240d059200703001c0107507040d80101110b403048900078068400d05610418038082e003503420303001403040d8400a900070400200c4201c41070b4030a0601590102d007507107080c688846540070004c00039049200c4203a004040043c1d01c50f0410920b4465001b03121061404803117051200c2c5801b19001260f0710802c503400c51680841400a40e03444c00040170900803506490b241200000202000002d000d800c80100c20305808000b4940141c2c1d03907601c580d100d4040d440410b5039500704034000070100ca00e1540d0385001030f446071004020604002050360001c00c1601e9081c000d039561900100c03064001c560012246000204010030f6500300400c904100750169610440d060007002e00b0400d01401600ca8000540c0015000c03da00174424101e043d400b6000d00300c04212181e118103040000401401d87c2801c0d500401c002510b040101e002e155134143c00004140a21415501c6074456100340e4483c49081c0b13082d6103403400816001f402510380b407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 675525962 1250 675524712 675524741
    0xc040c0903050a030e030f0d050d0c080f0103141608010e0c0a1a0d0605040504030801031205030f01090c11070f031b051c030e0a0e0402010e0a03050c040c0908100c1202030115030f 79
    0x216074030314230240180d0810700300881040d05000d50100d2203840f4142d55031044100c7e02130342c03070f6991031501c48800b80c0c043c02c1069200d070b0050303510007200c0340c800703010b00340041c002c6d100000307002841c0e502200e0800462140c10351045c090003000300b04030805141900b17800300d241004542e0310b80c4240a810020015580080d400a00705001c0005040e040351105048a0040c1600720a6200710f0400304c0d840d11049840c003040c02440d0005012002d495486102ca12015040c114449502d68012603c5d1035031603400a00a0b09036070405200b00b10b011040c1920012406101e802041e00304000994803424058140060001900b2403c00b414800e08100c911060054840c9a98a0301d0b01c0b210b65081404840a81c08034446424045250034408420b0040b40d07005000340c01141b07400d800300800744c0402080d500030840749540101c0d8035002440b0001354030b1041701c0001241c1c42246806070044840e80c4007103c2d9140b0601c010004030500f42d50100c641c40251a00180481b400709905005141d0b98242c0b102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 675527212 1250 675525962 675525973
    0x20a0c0603200a1403040501180b010602010b122104030b01090203070e060a0210050624030106081b07030e0a03080a0c020906100e060c0a140c040c0903050a030e030f 73
    0x4034160580d2140b2294581d286040100e01c810096448452142460840009401d040c0b1507031500e41d010060768100b0301c10800841d0402c0b1390b0080c14102e148807081a1000320003400100b003526024464003010740019100100d5003c00c1d00c40c00740c3c8a01c01141c60101a102340010107031741700200c0044402441d40048241403d5845250314002900708540d0740020034403141c0060443c2c6007240585003030b403003194020145e0010500c00080544070180c80c05420030f084400422980f40c003900c0b900031441710503408a0700c0e9032420f04002e1074010003401c032807541410861b00c0c006601d10f6034100c50131a40c0605104000102d200c022901400c60340c2d1014002c14408900500c0d00d0b5886180c0034032642c0200c2d0b0700d1581c1d4450900300032050b0031058070740002c610b00714811119070800380094204504402e080d10305074030380d03030300d9100d80007003201ca594540d90003d80c0070010a2610b4820101c03400402c1c50007544140c29940d0303299490710440d501905000c035000380010b280d902040002c0408480805030f61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 675528462 1250 675527212 675527219
    0x504110c190c0b030f04110301020c0d03050a05071103071e0f03030903031a06041a0c0330040308070e040b10050a03050a050408070f03030b09041406090f1c020a0c 72
    0x203a01e00a03030741080310180c004110015042d2610700c01c0d603024800149500b2495110342c0d846040410380460420b402d9502400081d030164401e1203403003100f03441034030049002c1ca0000d031038030101c8000814540c10302849454883d03260400005540b503899200e400ca000041201c0d06841043c181050014505141400e0b80010135525400840015100740c0f020700002d04200318803404400b110f8082500168180300030005030704107082c032914030901800c1a0f03180c00f444802403402c581c0a036605002058040d8001d01814140c102c5c2e07180c0300d103004c12040040c0c1c03c00390f0300105203900141c040400c12941900060b41e40d07942e41d12501200c0c0d0001d00e4040085481035020b042500110741a86c007103450a000180d4070a01401800d00c180c5c0d0003030146281600d1a5520f05203210f0404c402c0e0101550b4030418100c0f52180513110b80070b075010b0030000d268103101c0505280351120013807000807160003030040c0444030320000600b0210144d8645048a0400c8400c5080746030000e4000003030f05007295443c000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 675529712 1250 675528462 675528493
    0x30061205070503070815090c031915050603191a0907060807020d020309091806010611010f2703050403050304180c0203070309060807030f180201140a0e040b0d0b040516080c09010504110c 82
    0x72b800380c40c0725240d80c1c0d61b070408080145040760021140c10b038040e00030600d001d00c0e0a81c00c10342e00001c10311843c2d200400c00f0340c00d100d101152000316a28152903000040a2044a070400c0c4e240b5400b80c2988014402050b9480000f9146d0151410845c050018038021400c10241c140e58014130360901811981c15680d01c40c8010810702413692040444d5180c4007524040307a000303019002107902c010001c110040d01610705540c2031243c0c40425420403005000110000744240020801000d03955079815a2411501581080b503d0013450710701954801c10030040000d402142c00c02c120340050604220070707030760780c5415400742c0181e640c0200003500c1c1443c00d00c2c200d402c90700d42511582c000c1c3e0343c5035181a8200e40ca481075100d090840c1c0003081d00c103c100e80d140c0c0f030107402110402901500341040c81c500c5540d8112a9a001d0f00e00721040e07003110320703501100c0e041120114020240240100840b40303002e03000c62a03841c0107015840c011611101140044070303440c1d0440e01c212030f4050855070400040d051a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 675530962 1250 675529712 675529753
    0x20415020106032003060f130213020901090e0105100e01030b0301020c010501150906050d05060102161511071d13022e030c30061205070503070815090c03 68
    0x2201c4880584030013540b14101040c6070514400c01600400e1507413a030700e120074460040280b06110f200c02804610300103854450300109200c0c17003800050388a0380d19400140c0702a0071078210000007102900100990760f10302c80f07038400303881c91805c004c09652000c6004a02510405107641c0d019030000031818496041540401e04803400414141c1e072002d683e010403291600301e44100300c0010020b1045540b03010560f40000e400600c140112004004001d080c0d50106495610220714a81c410b07030700d544a0340e00b0486030320940d15150f015003049403c0902101450f03201c02c12043d00c54035440006050390103c0d64501d0703146038008090051114405040c4000102400d1890203522061460780b000c00f0701030b0090b401b81300f1142d11801541c00c09400507081c80d404c0e0007650280c20100143d0340707403212003a10408003c2c11000b414030301d0025aa0416520b480803660015020740d000c11001c100e60440031642c0101e0511401d0082c5560700e5001c4420700d08010140295414041c1c5a0b5641c400c07940c2d40310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 675532212 1250 675530962 675530969
    0x61104090b030606011e09030c0f0e0a1e0b0a0902030c041e1a09030109060507020705030d050c1902030a050f0610060807020d030e010608011b0e1e04020706020415020106 75
    0x780000321000c410305072100000d445050200b400840151400030356071598128076400f51034819225030307032616085104071182d40014042d00c90300500707100b010071000e0000c2d80300c109501d05010006026010400e030700c0c40429811602e035540c20003401c9550307400d40014024440002c1c19522800c010200390703075560061240d400c00500035419070001c1c00e9254004411907046c04143c44001e900b482d545101640101c841c0d541c55540d90a428000804230b1180c103008464944c0105078860802060501c0e0100304907020050001c203101c0381310511000111784004426007018440301c4501880468506900d00e0401070845c011a0811201c0f0304000807600d02c907140f00c0e500c103a40c01e0303640c5100b81c46102c019140c01e001070304840140410a0b00030341007080040b50040c00060156510b00c180d50071140c612408140781e05000350304242c416401121050202402c80b40461400c000848140d254a205038100d4082c58002c118a07013448035940c1510b0062070560b00305801d60004010080c000e01c02c030300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 675533462 1250 675532212 675532229
    0x31202031309270b0106050d1b081006090b0313020a08030c01020a0810320409030c05070b03071b15050403030b0a0f05011709010902150c15160806010c061104 70
    0x480e0042584030f069000000c154002048651a03401d24000312466400681c21004003900c86400c0340000c2c56802403120313030f1046507907400e683e4100009482e050055941c0038000700810178000b80000c10712541107980064810381d2007100c800151000c6081c64509501c4507000b40400315410184000c10340007003258040da0380d074101c241e60364041042c158642c1c034021007410040b5040d040441f100d00c5895180c8032005200028001d4104c0f500107015210312060460002d840302100804119007000381e00040c0004248841c11842c1854005100743d40b80d00f00c0c1c54501c0000c4004006101c0541c0103000300440c0c981e01404186000d050240c041d240016085001c0c6c14490400a40e204c0707185110003c0d5a07050351260038a101e20900a80108000f60844c941556114400d0006a44521002030500c2100760059182c008550f1480d04108044008090202c021000c220091803a800d00e14000388a609100202d92541001200e10044420005060f2131400203800702005249015100720354400c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 675534712 1250 675533462 675533501
    0x4060e0a0e03040f0506030709181a0f011704030c060c090611150604380109060c0b01050d050f010603150b03010b090c09060f070309140d0b01031202031309 69
    0x14401c0359500d00c80c1d44141e030b608035104007041c0121b10701000259002030503407030040e4407075894066141038480c00c00448003600ea9a11700394400c03040960404031904904440700721403507610100103030004024942011503141c412001400b018025030025501d0b40d0401010040c501d91130303201521080c01405980302007449036880e1300031406c0005000784d0407089511a00d255440743c00c03e000242030190250420600c001c51505417520071f840040750381000400030038114200c0c2030000b418414041d0494000c03c400c80307100b4400314030707020035140c110f0b4015585840014442d0a10b0340c204074000f00301441c55400c200e0004284158840c0c445800340115504001c03042042c010542221400e52049800c005800001034010042a003d41b20307800c0064940c0340703090a4240100b4090f800883d00718040b50150200b40440301c0ca4a0307000440020981d0b502041001030b48400d44040030511006025050300340340510380c0d0b0f01c2481a01d91210302001106000c03611041d555000d0f2902ca003007030350498160f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 675535962 1250 675534712 675534731
    0xf0a030908060421030603140105060901170303060607020d06141b0c07050d0503190908060c0304051b030f16031a06060d0b0303070c1203030606050913091104060e0a 73
    0x481e9150246600490713001c000c007011039040000f0500b800802043c0350740c5140000205034541e0301828006c41070700000519191030010403c2c038017010313006244440d0101450001e00080001140d810580882d14980c5420b52880000c070b4100c20440014203150034010100c01000206d80e0286c040c04140000c1c404a200c800b00d07101060098507841032095000d80010421410101100c001c55405081900e2511592070100a1000c5540e4103160018101c20010000e0303540611202d60007c001845031865414151581580c85840c0040454001c0c4140c2403d0019a0100a81c80155035564255808808502050040030b0200d1005690040c119482c0c03003000131070b01c82290301c40c040007001e0324185a4034215903001440303060346664041c4010881000800c0c483d100c640018030300300340e60344081c103410b00d4000c05950303081e40035009025060081c50300310303a5061144800d02c5030003079000500ca0000c2c104030411644910030f05401520702000810000d01000000744a140b0003c0144020b104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 675537212 1250 675535962 675535979
    0x306030d0e03071a0c060f010f1d0712140705131a030f1008100b01120c051b0a0206030718120c14012706170c0a08180f0a0309 56
    0x706103580c1d0303043d00000c2c410b00000c0c1041d01030001034003c1d105120b0800d40c01040d994035000e81540e10340061000c04004002840c1011f80800140080c1161440115002202900c41803c05090402404140d40c01414074202680c059005c50700c0391807001e149401c003044090007039441410800422002e80c0008990000201d030181091540305418510303556869004001d000806040d80707500100743c0d2000213413030004024040d03d00c5410000045d0007072001c00058030100c3d0485007111014280011880169003200035141c0307a40d00d000c140010040c68800044c100120100e0096008030040180504c1035404030310004607490a03031800c008251101c1c40e1610b55446040020004c1008400601c140040c1c00c684c3c03246900107040610403540d0b0b0000c01d0318401c4403901c03d142c0c00c642050b410010650701038007403e0149100041201903041008124501d4800d6a1034141441110b60114a00a00c07032003070800303400700c0c0b101503901900c9541e07910b40e11584c4291003034002a040701c03000305240f01c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 675538462 1250 675537212 675537227
    0x41520040302060a050705060103080405010306090515040b061303080316020307050a020d0f1a0a110a1704030e060403050d020106050405090a120210060905010503060c0a020d05220602030306030d 86
    0x18504125081074a560308100d180d5000100c90070800c1814071403100050810040140030727501c601459521181444001001c9030a581d01c401c001c2800e20040c8142501c080c441310820035400c1d1000f04602084001003280e9208240f10f4405128081500105000c03200000d54040c00241351607941d039070b01402040360f03a40185140940560040c401020051504200142e0100e00c01d8501018510311b544030007000401a82100401401c054100700c14100340d8811080400d0480c040f841c180341d10004010412140309544032642c401c0714000c201814012034601221190060606550700d85901e410b50b02c0392045051a0b0240d0300745600030a40349841e01540e0700c5205207400800302840d40d0340b0b4400303580000e407040006600032407402c2a032040260044402404d01580003142ca07500d040300b0b2515206d001400c01c4002d10040c000c3c0c0ba000c0d0750100d1420800301b00340c0742550301c4107420089400c40c013109070b00710a80034205c40340009801d50080003440c80750400310161040e204020405035680b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 675539568 1106 675538462 675538511
    0xc1213080a081801050c0a05030406061215060f060e040b041b02010e12040302010f181d0f1003081b01110a0207080f030c060109020306180415 63
    0x414802243c200c503045850000c2020f46400a0070307545501a8040c180304002000011406205440d000302026041b181804e42c5a80f00074a44a0f02040044071842001da040041c001944c000d5443e071081107505a0b26503441030340c0400c04101c001c1401d264070551043d5100008450b041c20520104d140e41c800341c000250840307102c14564a0400c40241c000400c02c401c22082c80142d81c80519040c05d001ea82c02c000c44104d0800c800e4808180303058009071018000c7c1041e404c4004070301d4407002d02034801c1010034940343e22000d0300b00c100d8103054000a090842d0030411180e41c000c071441c5844140b00e00800016079406040100855079121000c0140140d1000c60188940401448903800100b071490040d89414010b510080d10b4210501c038400c1e5107540440041c3c032603140d2650341d000d801150301c5006813a290034540080c010184448181e4040d25100480c10f000c4940121603008 = true := by decide +kernel

theorem cover : BRFrame.Cov 675359712 675539568 := by
  have h0 := BRFrame.cov_init 675359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 675359712 ≤ n) (h2 : n < 675539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
