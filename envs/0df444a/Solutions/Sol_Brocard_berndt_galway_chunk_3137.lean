-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:46:00.340157+00:00
-- url     : https://prove2.me/submissions/66dd41ff-f577-4d76-a57d-e5fcac0a3ef9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 564028776 ≤ n < 564208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 564030026 1250 564028776 564028781
    0x402031905030310090509072603031e0f0f0103080f04030203250b1215010c0c0b030f18030a0311090604060c0b010803040e0c0901051b011d012007020f04 68
    0x30500c2032004559a24080300850400c110303a030080c580650500040c40040100025007406560110307a4602d02c07c44100040b18444c0d25140d42e1426500000c420003103002e10100420700030380220350017000746540c1c803411a0940c01040341d48040740c1c100344005001254042010b000d500070502c0c405407070325407030350006072506400416a4054415840740000528500c1c0b00c014024851000c440e414094000c180c0d181200000b8000c0c18548050a80d000090303104455a42180b508100ba00080b40c2e01e9405055166000300d81c14500785186038040340c407800d04003000340038503c2501c01a5050035604032045001d0f2041900c104c01c0f100080c002c0015907681c4c00002c10041040d612103070707815103142c41c001c0341500059211800603001444100b180c62881e402c03480d4049000502113640d0000000140e800340100031100b810b5401701d40150440d054154410302040a44e085200c0c140c04e900c8542900383d0304002d0600001d189582810143e42800c000507101d558801422581000c8081d40070408 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 564031276 1250 564030026 564030073
    0xc090f12170d0b030d0e0f190506040b03090c15040b031b13181109090702030c01022115010509041107080706020304030807020604020a0b0a0c1a240315040203 70
    0x400740d503c140304142071500304440c280c0d40100e4200700c80040d5110b400907071148010441d0345d004452039819441134031040d42124001e082c004164544664840e154030300c06400403904032225100e10564400a0300c1c14441002c06000342d00450b918103802c2180c590f18681002c0c01000a414254bc0010480c1520402919142d0648c003400300c451032400d80c1d41ca924482203050071210520f406480c00c2d2600c804811224005000d41d042c0e12a611801002c80c51072050749111801c030351011503a030400b0100c1e007038102c42041884d6004070044c0c44409204804003805d03a40b1134042482001010a90b041603089042c103284107812860030055507490b6044983c0c000c00089a0260303000040104061704100303100d8015410f44014220380c5440d80c0441c2d4558541d00a2460608020030710004651040c4034190009038061034501100d045182c21100c028400c0e68607072102c15861540e4a81130040c0421640400da00600814144101c03810300b981c19200075205036054010b05050005c03c0d240c4408484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 564032526 1250 564031276 564031297
    0x1509010b1c1a0a050402040e0a020a050403050d0509010e090f0103030e031009060905151b030415021b06060d0b0604051305070605040e010e01050906120106080a150c090f1217 77
    0x40880200ba4200026268940c0010f4403552040c0000d000b43d002d294059903110054180060740d8464050042d2098026070b44010300d14070581c454200c58039403244c05416107860a0300c2c0ca0000a2640702046280002181c80501040e140d00c01080480d2142d080c40c8120702001d0180c542145961052800341c0b00900410340d85c103522075400070b08020041041e200060f100c00b086d98450300b041c40007105110b01c181c2e401102d140d030110119081c044030790012041c81c0c2091408640d120003481e1034000401360b01000f824580101000161642018496103a0403980b19061000d40d654000820006103409030103d0280e61071140300c10005401002021f01406041e11a96183c0d4a001c10512110a050b00032401c00200c1c0401006030ba159080003e81008044503200d92100e1201003580c01003440c1c4e408017203988030ba88101024800010040381e140c030640541400181080e42040c0c2d03071103100b03201301c02030b90350000c0080104540710b40751610010300c0b40c400b90f42c840505c1c03184205940c02422400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 564033776 1250 564032526 564032561
    0x90501121214130806060a060225050d0506060306011e27021b0606060f03072607110f010903020a1712070e010215090c0609060409050c0903061509010b1c 68
    0x14130141324100443d9070b0041d4126000100c40b4113001c0000c1d21000c01800d545454a0800341c03c0500554004a200281c4030140c008100c14402e810103d0780c2d60820b4603018000e0144200110300141006007410b407507090300445035607851074030701400e010544a01001040c640d641c502c40034600050700003000e081035a6080c1e0070506040c596054108200904000c0c803c1004201840500714044256540007a060a2103900c2c5e40240014215007010180300d2101415103200b00180c1daa00700310381c181008580c0d000c135412800342e0440340c0d089858402c1c014015900254001000620001308403195a43c01003180d07090000300b51141100f0740043e62030202041c45031b58402180c0d681000f01a0070000c401d1410519400e20040143c0c842d01c80f400c00c20301491000a00c4202901d4840484000f0840724504000520706034500f50740c55000300306031a2080c086d40011400212401010780c1c4064801080302d54580d00c0c0041d01c40c586d032b004555480150622040a0040d080c0d184181d1500d001c2681da40c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 564035026 1250 564033776 564033779
    0xa060503070f080627070602060a150308090906031e1c0314010902030a0204030503030907030c0e01181e090c03030221030406020a020c0d061509050112121413 70
    0x40505004076508404401460244100728004000403102c0d0080e0800c4185000c1040c16120102e40c0d68403003007001110310424900043d50369000540780d1080e01e581408015110b5801c624221f207404500c1b02808000080c4061500342c40d0407060242c00010003000c41c2e101010302403801d03a0004c246a88850380ea04001008a59000031100300d010540c0d40d494104400820780c031f2203403843c0006000b02c4080c560b0110000308004a5681100c3c040c580103000c40e61685010211a9902c0e0440e000468051600c00c03000503003441e8842070715040c0c0f000c01404400d607006a1180000405410740c0b400d00d0410322010f024070030940342c4551180c10307004c4c020f50354446080d0308002c3c0c07070b205134030f81e0f281054440649030004444909080d20303002540420b0260f900c00d0460800c0f841c00140180003903100452072800410007480c1e6001a060040d21201d64800c0c0342d0b1848981c044800910400ac001001561a0400601400b83c0d0201220031810200c600c00f800703020202423034224035603a92225110820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 564036276 1250 564035026 564035029
    0x51203030708071e03050c160803061203071703040c09090f03020c030f07031e0b0f07120207030806010c1704180b040902151b1006140901060e06090310050a0605 71
    0xc1c000da122034030f418a41001610b840b004000110340084c1d000c10540d891010800340c0f480c0c041200c840780c40d41048080c2015050070076031499801078490314803892981c40c162102c00808826680f203240c01104600b00d111040c1e100c2c0000317030f00040c0211500b00c1c402c1800716120f02188100b20f0194050a00101111081d01e40a843c04018004d4144641d000caa2004944500003482d2419254818400d441c100001c1d58540305001010f41e000f00f00325405020802d1540e541d47c10188034502c01d80e00e075607014106403000740482c810800042c00250f40034000444550040c1503030310401d44a651480384c032205603140015181c1081d08000c3c40c030400b0b6810b0864105050041c91070a01c41264100702094250740044c03402e040c0056180d95100307020404054100e0703408074000c13440768040141d880c542410f61006004090b070380a90908a000044441210305211622506a5825490f01d40381c0d0004078003041000e400086000d40c1c54400c54041c0100060b003409035034000d984818011a01908100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 564037526 1250 564036276 564036287
    0x9101a010e0a080712060221100603050c030f070e181e010b03060f01020f0a030905120c0a0303030f090c030605180d1202030726070207050d11060f040512030307 71
    0x140060700c640c0c2c54400070710100388082007403021280b08481024990881c0c0c40c1400190242182150703c40089000d500903e80000d0030880c0b00d01d00100c2d4002c04540c56013019030807114181c1e03003460045000e00c00600580040018690400c8650414030320140307961000070754132543c02ca180c1118881c2e02d01406051083c0c0c8000460340c900300d0804403a50740c10a80550384070b0100411152258690b03001c402510303402405500462002817003602c001080e1810041c06680b100d205135030003443c2c0004040c0c144c401c0800e1840c818800146040c0000345962001c0f80645802c1181c0070340070780c1d501e070080001182da5101000562040c02d01140d64540a10f00c40c902001a59003000550010070100781110743c8140717a58441c0844060060302e0340c9642004a0b08014400800304030b0000002e080301d84400303201c40151240007240d00711000d0544820030705c075129901c96402040d010b80070302940114901000600f6a4443c10002207003465035400000b211205907406c01c803440c0d0000028414810b5105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 564038776 1250 564037526 564037547
    0x60d0203180712050a11010903051e06070504060f210f050a1103060a0e0a18230c031f0b040207120e01050306060f07050f0d0905270f09101a01 63
    0x2614010070407166140d017178070341d0002d034001002802c1c1d03078001c4e0003968059243c8402460b00503040b1b411000550b5108000340e800728980c0350b0a480f462000900c080e02c07502c00c1b80c0999070166152258403119110540e401507450174103480554110210441601880c0f0804181b07a140a40108403420224101011509001c5042440400030802c02056417104c941a0381181d9100b09003e442d59500700440700100340c403511580c4071501480252091080f807488803d0170b610741d0008420b540c02e20142c0b1a60b545c07104100c0365055009088240409911940782e0100f0440031103020606c2a64480050101c2c0d111403c00c03161200304070000c070030203540206e80f120b40301d07820308105245003001800900da1740180884910841c1c40010340e50f0412405010710140c9030f2842048940b510711094002c0c00f8401d482c00740d1130041094000f0b01c140000950846a071032030f251310302501035854540e424111030300b0007005000700b4401c4d4103101020900c288191035070100f151189000303050714600010141c0e91701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 564040026 1250 564038776 564038789
    0xf050c1f09081605061323011706010e010e010c0203070803070b010b03010e0612010b100e12010212041101020a0c060306170f1b0a170a0c06021218060d02031807 71
    0x6083e80701140f00b03440340c00080d00c100b240c1190f226108501c4403c0b15600c2d98010000c0d40d044141400004c035140503001d0b82c1c64500742c07255605580801046240914101ea01c0d030b00145a07440750700d410354003d40c540c5092100c10f243c42006000c3c2ca0700440d00c1d1208562120712264400100b080a00c0001d11a040c054800c411a4030714551600030300e001002030191801e032041ca8800d04900c003c060961000b00440c4010b8948221940c965401508000000342002c0c0520200c2d80d04007502201031007214040341c0028840c00040c3c4907034031068060050303000041e040d4804c8010410200e11000b4200e4020000e03903401003440d509010304a00e9401d8000c000d0a111751200004401030038001ca48c06d894014092140312902d5250740000701c41c50200c4d48103180039010402000c100e24004507450044502400c500020766079218004c0b03035034a03a0300c1402c0e4440d2005010f85051441603502d4041c2a100090260782882400d406840403079005980800711680c4035614000440800d00002d80204603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 564041276 1250 564040026 564040033
    0x102070317130801050f04030905060f07380a06050d020609090a020913090c0608100306020901031118090709180b0a270b090c070f050c1f0908 63
    0x80d640e5440e40800a00782652952000882c1c00b50584225402c1c1100406051000703110b18100001c00c3c4e00050800ea40560000d800302d8400310b80380c101034044400203041a51980e25145561b203403984405503180300c1c003513600c6020601c801c0003498a06171107503500904d114038416051100500c1c003150031a511040c0609901710b101c001580e900c0e0240ea2141c9800d0701e8142d031036a61f02001400900c910b58613240d202d044615580c000301e074580d1040420351701c41c500b880d586640b548400d40f1700c0c44040300e44040c140c42c0040b0620010f041a00038007220b81c0107050115100741c03100e0311505250404029421070800280c05542c2e80e181081034543c00000a04010100c0c6051407a03a464001d141f9418003511340d19003003103041907101c0a040c0d4000300031302102080c902c0c2c3c000310360407601176143c26000c4100341400301d40941880e001c11528024081c00c0103052a0204656640d40354920444040d5807601030601114819160010060000c407003030204903062101c8048081c1912003e504582030990 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 564042526 1250 564041276 564041279
    0x1909120e0d0b01031104090b07021617250f27060e0604090c08030309010204061d0102340b0c0d1d09060a031b0906050d02010f12060b03010b0301090b010207 69
    0x2601c2c03004150540f90807091104017a451200803038054080486d009012603800d100700802c1d10780c0400e4510240038224944846242d072803501084d02d00e09074601c452640c102c540d20030464025030f0b41110080d82d202400c0c404003035440d103085610000139803000b80250891030f041e002d6025003c1d080c0803880f6581104100507802c101c486000014001c00041c01250349900040500000300c1c0490700829540c81201d5076880c2c4084410b002c0d400c01c0c442c02020410500065124200c0d4500304d40200e001a4003c098045a03104113000311415542c07001070000000c1c0d50500700440d0085420003802901c20500d41e02d05a0844075850040c020032000108001c4076001e1000280105450781c4044003142d00c1c4845840d43c4000070f40300481644020403103000c40c0d00d07072021107003144501c204445c0c101c1d8040140903507800602c4409540c08070700a0025040215400704c0500070400c480c60380c484c0400c0080c441d41c4500b002041070b8002c0e04a0300d1502c2000c4010410004280201e4001d40c2c4288080d01005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 564043776 1250 564042526 564042533
    0x3080a0e1008130605180a060b0a0f15080711100615090302090408030615221401120e010f020409061401050c03031302010e100c0510020c03040e1909120e0d 69
    0x3c040c41c00500a41e150b602151101c41c40c09003210004103440c06860601d0820303e882d9005141c002042c1b40101141c44d0300268460826404000b190201c2101c0c06000721485000c070b0350b22500038100e90500010b00c20540c0148000c2000c0c0c00248580740700010000d0402c44819400e964074079580c0d0030000c61941c28030050721a044880d8000703a003e02e400703413603072100000910a900c1c0900c0c441940400412005001d94000d811040d00c81c01020000030816250000f41e03010342c035108041400328070000110803011805900220104058200000e1400804000072059a0256202c205103588580c03081c080c01c04800348840c140d400900780940b4141a1210f0607840f17000040002d10250a0440c40e0f038150390060074040d045001c000d02d40840b80c2c0386480c02400c551003451041e5014450079051081c5d01890380b089070585c00c00c1d070000714141403602520410454000380902842c031003407070060140c070b465400740d00b8100380301c0c61820f000d004041e200180150303010044988105448100362011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 564045026 1250 564043776 564043801
    0x201021006180f200d050108210a090b03010b0d0629130b190e01030e07051c02130506010813080f0f1c0c020d050903071e03080a0e1008 60
    0x380b85006404128941400100802000c80b0403a181c25900140e43c00120700101e40000d00c2508104c603c00c10690342c0f034804060b90ba080000300c1c449261540d8403001502d2100c2400b60028068a1410b07a07210381d1070303000c1c00310503810a0b448121510004102110041711034003542025024281c0f0f402c0301c10607402c414801041c062050580320720340004103030b408208218850f4000c0c01204090075030740d030705110b9000c0c2440c25844061000964243d042d87c0990b00c40e00a0380c207a0001c2600a00c542c60810003000b001c81c2c0c0c070f01c13000101891400c0100d001038a0f0403000300080e419244000400e4508140090114a030007413030086074030903860074040010102d40980e87c400d1480081e05448010031401c6006a102d02411402a240e160f40e84400301c1080e41c0000b00315244547c00e0740c0190800240a44c1c0500074203a09903030542001c4c505025a14515001c3c50b90b1906030700d28020259520b0310742c92259800401c600c0001007144480d2851820684003802415542c1d14040c5028a00004170011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 564046276 1250 564045026 564045059
    0xb15030402011404090c0905100e0a0506090102010e06040f0203060708070f051b19020f010516060504030302071407212012070b13080102030c1210030b040803040201021006 76
    0x50040f200480524070f42604251405010710600c00c001c82c14160740042c00400c12407180138402d001144c20790321400d01c100344031140c00324058134031284142480200080d9411201403281113649e610890105d070001001302c01e0203240541c141150841071070041c0f6082a030024242000d02c0402c009000c4038941c4100c40310940d41d66468500c1d25042414564840703500d000d8980401c1c0c4c49030103981403001c410444c7c544501d03413084a1002c22581d2180056030280158441200c8418090104c0008030300320f5000580d1042c440d1400500c0c14015a640d00d8594412001454050b84081c0f800d0001d07202504031840c20091006d840d000c01e4030190f40b04c0078040c800c1c1a5840c105182000c0001c003544526040540c0500b90382c0c00c0c3d8100d280c03580c00c50038040d0040032507220340741d28902c800a00c0310018400c407400740d0480004507281121021003410340351009004a8003200c04444000089010344541a014511504c03206a0740d0915000080c82c0030700440384040000c0c9800401c06c005044000b0307426 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 564047526 1250 564046276 564046279
    0x5060301051f091502060702010605270c04050910030308060102010504080a0e01020c1e010311070b0103020d030c060c0c05060906060f130f0212010510090614090f030106030303020d0b15030402 85
    0x505000b08000c0032252034220b90b124803501c0d40950011048560042442446040240e000300304480d5641304200502c03001d9001c0040240300c415070210850040c065640d40700714507481a5150507941c0c030101e2452a01219101c284003c065000d104144e4011103c6400c803a0920082c0724034203268441141034072031001008140101581c088100364000d21056035019401007103000c2014201041c0326004e4107100d1010b00081c9440031f9902c00350801d809580d90a0307000900d4103101da0075903080c4542d0156049054080c010349801c4030000840d14001e02c100398030079039101d012001e8285001464042e0203004a0000d0f00500c00b08480c0307441c8c41d8842c10341401c0448034130350a5400c90501000810410344900c62035030000400f110f008499584941c100c4406551b4016506542042110014158000c0310300048902c102c48480d016440701426580310000c0c40c46143c2d05401c0002803c49030316900c102d010940118580d10705890034031035403401c018161030195a410038180511218400284020b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 564048776 1250 564047526 564047569
    0x7030b060909061807050a090611060a0c0c05070b1c090b0a0f090c03050109020108070c0b0105041a0315010311030f0307150204031704032904120e0406140a0506030105 74
    0x80e8503a46003e00b50300150f400701c840413560f05240b540280294445005080030030034460001600c20b04c104401c08441e001d88000d400241c0f1051603000140020b4450307a010842c0f611841004581c050001384003c002d940002a50740300e8085241c90700c000c00400c03048850b481c14810002041652000c01d901801919000030b01c401c0315501580241841040075000c12800c00002c0200001540082ea695000b600c40c440350755a0424100c0b11841c1c031110003007074518100e004001c0c90600c2c1d001040241200d207840313903021682d034012915004a9060018802060400400601c194116109682a0140c01401c0140c0d00480d186a1f44d11801c41b00030310030400b45d0001c00241a80d503058801440c0d00c64002c0708659500004410103412600007561040705106448a07003844210240301ca0b0311760020400f070107607195100c007100d403001114880c1c1406450080001075543c3d40c451040a40701d40c15900c10b0300c6801070103001039207141c1c1d040180112002c000510150740d444540700d600800c50980c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 564050026 1250 564048776 564048781
    0xf050a06170a24080111040803072d080309060a02030415050603030f0309060a0b10021203060d0c0e071b0b010b03090708030f071a040804210f06020901031505150d060f03030201021207030b060909 86
    0x1c0e10006140399042614bc0502982500d0401240c1c41c0114014000231003211a00e1b121410100205d200540d0010f110904a50317107540c001d4600d4200c10b0303000f1002420740307060640400c40307202c0c02d40c001c5541080d1030f000a401c00072485818428404416000e40c0c140d40b2101c038035030021b540d401c080e90841410b408003000281190f666010701105650b441094060030701d43e07071081a0301144041c0c0d5a000030983c808050000804c0b901da01070842d0360400110903161b4032740940901c09500c0608144528001c052004c2140d80c5d0400c001e0408400c85942030350380e0140350601c074864001d14001c3d26148440c410620020840c06004d46069410a14200c0031144280c0b00b4802040c11084c0010082030b202034000003800081d40c0a0b10400c0c4081e28140817420381d5020001032030700d460140a0740180718850030840b00c01d002e0090f020a40d03a0880018030503460b0035036460b4060b580e2b4001c90042c0e400040c0b03d0300210b5400c0d40141c02248508003402004103150000303000340141d2144c50300030600d6a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 564051276 1250 564050026 564050063
    0x414100b1819060801090e03160f1406060f0301050405120306010207120b1e04020a0e0c25020102120301060f0c0f02090a05010f050a06170a2408011104080307 70
    0x110100031009140500c400d03180c00b19805040e41600c100000301c0e0039000005a809100c0c01006800c0c490800914a0450ba0300900c1f508020001305c16282d03c11280c003210001807140f002e000e604400e000040605141030010440031103d003a854034060b90425082c040041c00006178414a00103140c1c4141e140e50700d1030b00403840c05d0364a5115440310101c8201d00710900c90980300d81401041e100040c0c4080c2c019001140f1480c1c041990001c0d0041d00c864410000001200061a080040440760b11b140c8090280c12074845030060b030f0840c02103090b80110781c08668041000c82c0581060a8407a41950b03d00b03000680a20b4100005d00f00b4006641e07100c0c0f04100c0e206240d00d0b2216401413a140350350170700011080091209000b0858106c95458011560f172500000000403030365180d80b200806011403a85806a09000d4510700445440d80060003550301044103824920040103518401a07213045c4845003512280c03825080d4459040009000e0f201c400f004950b80c4a4100782000d10a888418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 564052526 1250 564051276 564051307
    0x906040320030a0602120c0702030c0411190201020c19120c0303060e01080303060f090c07020d0204060504060b0d0c18060c03020f0105160305061e150f030a02090414100b 75
    0x10090b5150196800040401643e58064203000003001e2101c0d00c0d641c0c544500282078800c18901a40c07642c0180c40344402d91601d41c01000d515030164034042c1c1030403040c1100c0c0500c0e10740c801c50540035035000324069198180410503440b40540030001d401240480e521070100c407582c0904e004040140c0340e161002858041e800c10402000c00c115115410340e518030042e902c035003040d907015210b50b51820101c0301740e1628400040c0544090015039103404010745c20009111286142207800648690b0000b0f0340d640c981c4108402000b502242550f211040c490b258204c42054200d1000c0c4207000040303948a580c01400c00058039482d0a09416100242c01d061780350038088001da04c029030904040182c43c05c010408220015a41d85040c8400e403036074130400c0807030702002d140400351204d100b001c8491450320b50040c00001070922003481ca000f08204605d0310381e600c12542c070204a07400180003809820240b08101c686400d44000034017a080c481c80c500d000c00d180b881004202c0b5008030701c2004003032041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564053776 1250 564052526 564052583
    0x1e1503020d0b0a090f0c08060a0507020714010c06062601020304230a0f11270a0c0909020a030914010c2c0d0506010f0b03150d0303090b1503010507020309060403 71
    0x14170300358080c0402d1500c91501d814070b0040302001d00450010880500285c041d603070207a04141c014006445c00c003403221402c0a00030281d0b5041206002e84500443c0c03561088a000d40000b028039035884101e07003601052252a62030f01d018070fa10420401c40840d40490001c2c01440e0515000891000305803003252030b01021403405403414a4030b0b5000000c201e85d12441c03408003601a200d100d4009034090448013856081c1d10040818021900001c24040065120065940f2141410700701c080e101c02d444002c81e00301107404004646e03540300d00c07014401080080c158502108001b0b029032020140003d01142c0882c601080f900701500ba110306030b080c45201240600d001800c0d24070b00c00170741d0070074543e958000c4c8110310703030320341d84060210300880308804680c4520164902c1c0480c0704101000e01914801501c030980415550303403d8003002034070110300329000b00880201c0c24100f51450b4100750844d039005e0800e0381550700410110031039444400558080f20f030810507084200201e0081a801d03052031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 564055026 1250 564053776 564053783
    0x3060302041505040506010c1707020a03120507020a0f233105070c030f05070501060909030c0309050f011706030705060c061501020c311e1503020d0b0a09 68
    0x1042da50802d0105900809812500d08035070038401501d03407000640d4040e650340d0703001e014044056220803085c111f00f40100000c41c406000c80d112990380751201110f9901c0d485101000505c0041c0840c20b41c905060301002800d4440001401c251606c05000e1081d0f400c00b4140d101c8000b0102c001500d41e070f84079416410500c1d04c050604100b4881010304500710f40d00721161841b43e1426001c114054883c091088055502d900c42860030110600d059502c0c1c0c00c94441111a0341d00d40802183d011010b0140140403480382e11451140162480e01070031904884c0c004070300130700b0800e03107059880e0380c800300000700c980d801d070004651611000046420840f41b40c2000c0d4020380005981d50709508002049845102042c07030020344161700c100120388aa81c100b00d076030ba120084c1100c0303980302001c030000f40c1c12030244032900c0006191030b220030400b030701c03070850682e80b642c0e81c08404000070520704c1c013400e40110307002500da41d8214159030002c5c4111800840103030020b40c6c083c0005851000960140ca0b01540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 564056276 1250 564055026 564055031
    0x30f07031b0902180909010f0515011211160f0f08030f070206060108010b223002060d05070309050a0c0f05150d090f150c030c020f1c0203070c080f06070f0c0f02010306030204 77
    0x203061181030341c4104500c28ad20b00090341503881004c0d2400c644102e0600c4021881858a0a481400005d604041d1818181c407030602c440c10000006d903c0002c0322802600c00c02c0d2131a140c3c13506540c14600e40b04010300010540d080ba00421106a900000c601e05451a014415807030f100c02c170840500f4245003041842c0081104a0040b81c806000e403101205100100071040b021078804011040104c200710f8001c1d006581801340561401c0640c02056021560780741c0002c00305c0a03074544504d40000144182c95412485c68280300483c0102c05038ac01811056409281c06442441005070500c18064072034000b40e5901c64040404c42038400c40c66001e6000300754034039030b01000e1580764010310303004520402103403400c02d24101e602d00106030354494600c8400a4003100902a80d03c80e00c80401c01d20b52011404204950700000700d0420404010b030042d0300007045140320500e0280d2400501030034003010300c0210300b580442d071a4000d106809407503000403030a656080610041e0080d08480e000250310a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 564057526 1250 564056276 564056281
    0x7030213090605120a1205070f051e06060103061d0403110d111b0904060b03030d0f0e0c0609101b06020705030903150c070b06030f07031b0902180909010f05 69
    0x100c2e4110005031481100c03c1051001400d60340740e56200468801091000c2a22651650600440207450000d00601d1825a5840555121428590710301012a100311200070100c2200c90304010281c0d000c0300c20f090412145003401084201d000e06190111621607464001404141c03064400c0310f1803029100c1201c03402c40c483d09010703100c087d108428480c54800d95048002d801c1554900c1580e154018000d091661600d0300d46070003404180b02c009406100800c61211006614403400700c27480700395000018144807803003801d410404e916414a102703410a0005021550780c5003510351485803a401c200d40507041a504425400341c4000d80a86010710100d01d03481032090120041c01074240840c151104400b609250004404041d00d10000300c5400340012000201b40840590300480d00400301d5404140c00410149024481c1e0411203065990b441d1200c500b0b010002940c1c00342c840c40505500300b03480c201e0b0038441c0b0010200c000f441003584a003c81c503000802c3d80000e0280020034028002c0b0b2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 564058776 1250 564057526 564057539
    0x70e130506090601061e02010608100b031002031608071421180712050c0d30020a020d0f0611030108071a040302190b0c07261507030213 60
    0x20800010a45050044030300080044801066507410ba42035912464840502039018014891050100b41c00755941e4007800708007054204075800c2c0b801020306020821042c1c00c0141424520081c2c090407910b4014024410002031080113041e55941c180380041d500d61755940100c8072030032003540e01c1041a100059440c0074000260b41280302c03c01035000c4500585407003680061004070444640101c0d04582d40c00c0c0301c1c018405011004260240c4215414011401c0004007810209041180c4804001000300320050b50000c13500c3c0e88500c80c030700cbd0441c2c0105a47c4c01075140d00c1ca11038024800c40c140140003042100030a150942c05822200c10848074a0311040b4078020f5000f07008002081c41001c400003000340640f80340e0803002146c0340f25203041a103140d0034003041809804030711f91a80b0061502061a81c1e4140140030404040b000a1802906c1c1181c6039081c198401c604007100c400428030400104000100080d1210740c0c0d00100c3c14550315407104070020b015408100004400e4010000f414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 564060026 1250 564058776 564058801
    0x1080102181008040201050d0222321012180311030703270b12071202030402030c010c14030a020a0c05030a051b04020904111c0515060903070e 63
    0x4501d14050308207444842402041915500042e40c2c100103448000000c2c0194481d8000e00f00400700c0d0703500503040404403000c28445100d4083c8400319500803003420000c210b00c24201304606507800900d021070070306d810100140c500120501900491004400401c4107210f000c03500e044548840003040160301c000c42220b001d90102030290005140704100d526500d4004c411503a003264540c0340c0088140604071444100c40c00c21150822201d440600022041000d40003070205140f05500070007a49040d010203015100c00030160303142c0520501c10000181c600041d4510000c10900f441d5000035110315000d508043d007002c1c92030a034080400c2c9054419000942031907114030039040c1040e155101e030189582d800b06060041d01c2030380140c0d00484510500302042180f4140580094504440100441d0035181c00c09483c6030101400144203148030041c0f51a1264000454802c0c00682018440780086003a181d81c4140b20300c000144642480da030070003c000c0140001c8003416190303e0103921a011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 564061276 1250 564060026 564060037
    0x70906091505030d0c030c051915050a0603080711030c13090218040305032d191a010f0518090109090203060915070e0301140f090c040b06040303030b0307090501080102 74
    0x110030308001c0c0c0105003441c0100385040107081c0ba595001c0c0200360740d203080701c45c1e101c40002640e050003000e0701c02103507c5018070030401550040c0e1041c010013050300d0869044510040024501914100080c00018140b4084a940c1604020010581d291000019003004009030300c040d403028100d0411010b00d040d9400c00040300780211401a02c50803c180c0382010403208a60080c000b0f0341c100006500800c800031074518040c10440c0c40c2d648101100ca01005e100b10964881e650012a00800280100c940c0a0248550070310811000ba81c000c11300007034480f04030000201c09000000c5a41c1d00304a0300001d560861400c01003034044c155960303040e42c9000301040c1c80306034006e029140004a4002e000140d030a0801209540b0310869541d62404480d10940c200c5c900ea49035480e111581210a0b041d00024000c501004144010f402d2078450380b07103002540d80c05180614102000c05020383c1d1100e058900700c90b010308010582c64100c01c00030b81803c00c2c6400141266140100105078464154050710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 564062526 1250 564061276 564061301
    0x1005160501061505040b0f0705071e09060b0c071503020c1203040203070e010b0322050f010e0c1518030307121206090203040f2406060e04150812070507090609 70
    0xc0003000f4142048030188210b026204200504222108607101d081c001850f115000c0e1050b82c40701d03a1120002c00c40c108010010085202d154181446000c0103449844014842101ca02c0d02c0c09240d5401d035500c41019204003000d9001c8031035140c11090180e0111440304100000f9624003280c0700440d00324070340003510140d000744540c00c0b020802e804542c0310141607685c2c141c2500c3c11a603525500d150480c003013481480001e070300c0000300400110100981d0410105c55000441c00c04110f86805251440d400503052041401c17003200b800b5003405608442800008107045020003103100b000c20b1a41c42281402010340f0856460000c1c0700e40d00010b85078079500048000c0c411503a403020300c0d00c144d00090b900a8900c0090340101800124260501038205c80030031066100f00b5913805520341140d00c1c0b0762001c00882c400d90900b220a00c3c0030b208220703501e40c03040c40381203999041030041e42d034402803001c42604003080007841805002082080030010140600c2c188040341c0c513495054040e101000c50300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 564063776 1250 564062526 564062549
    0x90e0703201b060f04020102071703090a030503070204052809080403050a030f0206150a0b0a1403130204450b010902193b030109050319090b09100516050106 69
    0x18030466054076134a4003494050707004004050800c01d080c0101c810440e1000100d22080190306110b850300100d000045010341301554440c10709005200076208020803001d02d40b29034010b11844818242e098004450b4090750020754034080e17140000f140d01c1550800340407841a0018034007010342c0001c0c8288034680030313407c2e50700c9900c441c3c1004d00342c100b804038455813044038240140440c00012024003d190454508030820f80900d5915a581e82d2064403a0041140c030503c1c004c0c1981060300816a0710984660141c0001c110803080104002c0701c5000c00d030201030304c440500034a0413584d04880d81140c1100c500300305560b4440100009501c1300b01070441c80440590044c5070310703000760151460b60940220440b80740c0658008400380d0302c403840000c0d00b800e505188108058409200c0c0b009480c0c80340c001150346411040d011030b01018513080d40410003107041d0080c050885c0440c00e640801d8402d50703070414424541442910380f4000c04204014546549101006104054100301d00721b40e91500341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 564065026 1250 564063776 564063781
    0x307080c0f07060c12200601080d0806031c050c01060806040213150605160614010306151d070e1206061e01051e070804060e0a06090e0703201b06 64
    0xd581d02c5031150300ca0365000c00c01c24542d540200f511151030700201d0202d490a0300c070030340800c001c0b5401c201e013100c4070300c1441d40083d0041c080010100000362813000705061002c12803030310b2400280d4598140000132400c2604421194607a0b008405580104040800034810180c40e081c2d0395561f0101140e05038407410001128000c6401148510003801c50a000c4000b801c07424441c00b41c5a41e031141081a909440415a010120301141708115040c0b001036411300680d4510f04002041c0c0d05140c448004208002c45c0070412841076020240e080034010040d081d0a54912100b40c5101c01541d4035640c00041c0c02c01d920150b1131020038064401c082c22204900f04419110060041d2034281c03070103901090003004400042a15003c0445000c081310081601e0b000c201d0341c918a890300250b00c0b01021601d00030b4403480c4e6207821180e200140c1400c1c54040c00691902e0352106140c80c0c041c004030145942d80341c3c0200c810030078455038005a00003030007690b51051b1445107007100c0c00c1051400741a90046001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 564066276 1250 564065026 564065053
    0x90a060c05071e11030106082113061809020a020d08100501020d11010e030f0a0207060201110328060b0a02060f0610080a02090d0309150804022407050307080c 70
    0x40d40c40b4036421030180c941c54000d001040400c81912001640c0031104030481140c43e079024024100640044401303000000b850316002054000340720b16270402c051061101099402c6d042544000300c40300c9107050364500d0059801d40b01401da103074211017100c5d0b000081c482130b0181c0004140c3c47c01e1440f5603d03107850395074000e03000074a4036141c06401d0041e04583d6500310034502c03401c80c10220040d104000581c844c642d4074110310f5a84140ba80303640400000c01d000700070540501c0b0100042c0980d000034810495405504180c91100821146c0f0807035402403c021011005a02d0b02c001c10340114007084003a48070000485140c0119039500014840c90000511060908a815002c3d03030019142840640d450a400ea0782c0039001800030f140c0039404d200c3e080c040d0303540480b4501414025100c05640b10300305004608260003901d52241402000024480140c64501d1142c1d0b00580d410038411612280800d456514810000080c0140c0310200d00311051080c0309000740340031010f210485800c80201031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 564067526 1250 564066276 564066287
    0x30504150b13020a020111070c030309060206190c03020903120405040b0f030a031b060c051c05100b0903010603020d061b02070b07080306040e1504060e030705071203020a0b090a060c 80
    0x4416540080008981c8015030b030700d6401810b2040e0440c00081035103c07490101040c1e43d00028000c1e1081481c00c0002c00a260708103258070301402040c03000e07203002d1504919a4a0b4688140401482c2c0d81d9910750302041e5030703c0f030750590321681c10080c1514241b080440340308401d03403c01d0058920981c9020b199100c54a45503003003004140b80030f80079001c0815540c82c00d641120f02c5c520400250b01c99031400d040000e14a2040c0c0c02040442c0c1c59942c0c40b40d0723190061503050240324800e481c8441c030b0b0505004001442d21388000c1114500d040e41a5a84400008207014090030b41c0000e400500748002c8a04000f85030300180559034412400b0200200344501c200c1e03561b0b209104444100c0c0003040341070046402c0c08000e661154000e04081450010b004031305150085007003c2144000c0500144001c00800f400340f070310401c0340400114100283c40d242c443e2107116601c14140821500d0040804040c005d1200d141c840390824050749c011b01d0517000064076803800b00800c40b4900c0ca040c000d8134209011700d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 564068776 1250 564067526 564067541
    0x5010e07080a050703060504080418050103030f0504060c1b0906080303040203011a1c08210403020f0607090e0a0b1507150908030f040c1e06110304120b0c090406030303050415 77
    0x40041442c0f1745152180c400401c000340007582d612204000100b40c103102881c40c04030445e503d000006581d859030800504100240e0306030410000104000c0065952090010034040e400291034040500f1400b0828540300583d4007440d0305a080810024100d10044042d40c415402a0002e1040c0c00320b41c850282812144500d00758404034554802c12041d10080d04450351034851600240307041e2418030b518103004a610924820842028104400c0541c103205414508040ba0300030085410150300141011116003c1c090040070004000380303820905800078181804060169107030184480e0011140d640560001e56404011040300c65045a0910032003032240d0300040c21508584541c000c1619070b120140041d5041d20103100c01280c04605140d254a250782d0b104d0190411529118000e400904080004a040e8006102c200080500c0c80c144060103580001840302541d1120310021841c01100c00355a042450104040b040580581c001401540100f0020803034405146044007500c101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 564070026 1250 564068776 564068783
    0x31401020a0519030b032a0d0809040c021e03071a0f010312020f0d030608010c021504030305042a090501051c080f04050d08090f06191d0d05010e07080a 67
    0x2c00c61540066000703c0d0580504806180c00306070040c0980c0001c0c070f8485d0300000c1c611f01c003082000180c1d002c1c03d5103118400d110700c20b035074035501450940c41f541c01030b0159000c070354040c5807149280922944240040304d2040c4511142e40c4218100d00000b03952a08048402c50b50038800d61a9001c500c1ca0256030303d84502e00d000280000b580c256030b04e003500b419075031801030198410060000104e620030f1203802051761050303030009906454590360500b0b6407401ca00540a42d00302800d01004076400e650781640c8079400d030402082c0c0307454610b04801c00c0c12072002c10580c5407201c000c1ca1a030b050000c0c00520200e92040c4010f000c0b0366201c0003000080c0045060110503402c08410325400100010040e02403d501c414030142800e6545010030b8100740d6140b000c0722449030000e138200451803c2d50a601000c0300a071086030901656501e4003040c144880f1042050044400b24034804512000b896200c6e1000501000c051000920740035018240303107201041d450040b054041207a0000144051034540c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 564071276 1250 564070026 564070037
    0x315010504050f1012020d060e0d090f0b0d050928210f0f02070803040b0702150f07060f06121a09060c071b1d0a0b011706041a19031401020a 62
    0x103440c824101c81854030303000701d80100c000240c2d4800300d0b2052003101780e28010b52000d070ae841800d5034001444000707560003030041c41c540c074003060240c0038120040d503100c0700304610001540e84a400903146010b48880ba05900c07080d5018841c80e1035801c1040c601d248a104a1010032500d13640804d8508241400400c00d0018070703000714604030300303216000c0b0036622070040c01903c044a0722801c002d070450b8440c0e002a1070300c010003d10002181480003035280119000400c080c1080700300006846103100f6040d0141045d41c841c003003100004942e51151004040d058612405203e0038500404100f0001900c60ba0420100c4001000d404010444c94403520008020502d49407036030f40c1c1c5c800402d068a0728034411000c00306010507441c4000c480580b9101d544605114146406844481030300d0500366400c0c1004250009007070b403000c0407080d040c2c01210884020802d00350510f00114901441200c850303004041c82980c1c41d0449424450b00c00b902e000343c0a039800002c02000a900382c3c41001403440020f070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 564072526 1250 564071276 564071279
    0x1391b1a070212070816090c0504060c06020c1509010c230703030e06040302070f0b070507031e1b0602070801050f0106080603031303031205070309030212030c04050315010504050f10 80
    0x35100400003688003c1c5201d0500c41440100e902d000c0030303074103c04c52035889194140c0354800d02d075502d40020031403c0c000303000030301d16070500910300e005034030504090000a81007a0304004064060f02c0049e00500111030340c55070801c01c0591151700944002e26154645802e0b850300a114240e4040301d414100010700a400c83e10360003c01c1940205002d804040d0303a04014502c83c0024405640035900a0340145541030812601c04d440d01c640350b01c18021031104015100c00950301144020807250440118420189104101d40180d070040034014240185500e92001c006000c1011801f5200c02d94202c803145034894111a080319015184d884000d100d0200404c140c9108841c0f0742c3c0c1c03150020381682d040046031222454a2042d0340c000b200070881d10303031400380220084d04c541507100c0f4940c41d00b44114120341d00c01030b45540d94640c10f641c1040002000468001d04081185d00500010b42160016003004804e41c07690385003801694442c0341800b0200b0140f02242c03034628060314801280304402d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 564073776 1250 564072526 564072569
    0x7150e0a1115070f02030c1e190b0720061c020901030902060d02090f061c0c2303040c0504060806070309060b0907020d092301391b 58
    0x8084620005511688402c039060910121030701800d00c85200b1040113030700c0070462040500301000001498040c2128801070301800c5400300c0354940e100d800752401c4140c01102401100c40028a0700b180f022680c00107030401c20042050742d04040b02000f80100d442020344030301044031908ca103184445903024103011085804401c1d5006202200d814100040c40b0324459001c254284c00400030b0410195000c100c403070701d41c04c0a21440758023440c00c55805252005000c85114030580c51f045010181c4d07940c0320114041801a0000701c130a030041c3c550242c540020b070380800c58a0f0700c100c504450780749001c60002098185400342c0e40541303032201d000c0c1606540b00700e8101e0084c400084142c0c0c0705611420f041c0c903a0b48807242003e015030500c0c4d0283c080d2080d60074014203500840da0120140c0e2404a80014910310a010240341c408000d103001c1001e28540400702c1d483d503143c074014409888036031076109020300b1000d40c49100c45118510006e024110048030b0300e080a003500c20718030000c0c400b11012002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 564075026 1250 564073776 564073793
    0x14070602160b070801090c020d050a0503090a150e07050a0308041a0409050f0103110f03070909051c020622020f040b12060403020c2d06070309031707150e0a 69
    0x42480c1c10306203000200a070388610550001c143c501502255010300180010780407805195500792035400240b400900350f1000500d207214001217901000008808540240c4092042d500384680140034042101540e032440c10051030f101c2c0307003c03120380b14200c000034150810b1a404401c480d00035001505061038a1180d45420800c203c00d542600030801002c46c041003184038850140380ca01d0380b184aa9811460700c1e015000c407986c000e0788a100d0304c045051065070000380d54801d442d842a03000c00d60480e0303482d00615000f001c00002000890f0000c00303a240342c0c2e000030280e10840f4024900c1000f00c09002e4260428441c000d40a0340102c8032070168203441c14650480d0b40c030528058034442c1c81042c5209800d09003602075030104d005800c40485501c2928101c200300c1020020529403180c007094050343c45d004600c1d60702c520350144c98007254030418103000300007079002190403c55441040500703840081040d40030340002c4440010a410b01e0002c0311180c4620074090303a03110000c111502564507a01e56 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 564076276 1250 564075026 564075037
    0x2091602030d050114090106020102161104020c0f0a0c0506070c0b180d061506030b03100e03161a16080604110c0d0302130801090b2e0e0f010614070602 67
    0x25888100424445080300e840f5040c020030820345070311015980d41080148266042c1e018408580c014401c040c0036440c40e000c072454095020108440340c006a0012802901890020140e640180300f040b00c501d800c08115481c0685c49501d5012a032600d800401c4010b00070885e001d045c0e22803200f424403007800c0d1180104030b03041a503038404200700400c1000403d003035005541221150f440d910f50440203900d00d5a10400760030700d41001d202d007980000c0401d41d25030031380b503104800c6a102c00d00e410214034240112800800f0588003070040c15100c0c20300a181c030010500410000518078001084c450282180b00408080c913a40d807901a02c882e0300700000b43c006200e039141c1004003041880c1200b00c0030400700301ea01266031005038030b0300418880d58000c80f42d0f5a200400a9040c070102e4400a99604072442d881082d00a80d9080403040080034299403c4210120311102d641c03110110382c1d41381c8030400d984514005c0c400c18203240e8886000301c5008a1074005e070100341030180103290004040742c001c0c0a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 564077526 1250 564076276 564076321
    0x11160314061803070b091f0e010c020f0c0f1503010b0403050708060c030112052a09011a1c02040b040f1403010b0a0b1605162103080103021c02030f0606010306120209 73
    0x10707c1603800c000f0300c0c8421740541d001241130a98030a05804101c00a0040c1d25100c003590014080048040e60407548503400c0b104420720504050084c0e90499540000d5003400411010f1815265a1100c1c198403180d4020b00040d200780c800c40c1400108050001606441500045001070441e4a40b000d040c4c3c5004c2d4088084803140a803040b03040b507405d0a2174040a0790185001d00d2003074183d1107010b00c2000c40c01a0041ea00306008900504600c00960301143c80c0d207076010080764404905002410b0090080d0303000703c1c40c0c244e80018000b03042e400c2c1080c4002500d03c80225210004940400c050032203103440c104a410030319981081000d12180f802810000d07024922843e1100a01d0344e800342030403d4600108280318201d141442050040c81a0f0381c0001501c0c900340c0481e510b0394602620450051000910810f80742000360309014039203d9101d401e55024045580d0024a501d03800c0d15a54101c500f90300117440c000c400250442402c901c2e4000d40d03009400b08025031220305111083e810f1000750b42 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 564078776 1250 564077526 564077533
    0xf070203010b040c0206060f03030c0d05090a08011802040507031503061e091b080f06150a03050607021b0a06050d051806040311010501061106060111160314061803070b09 75
    0x40d015503d4901074030f100211284d01408480c60943c0401070900707001c4420a01943c814012a0001203001400d000011100d00b440b0352100b4001002821241050704244060b50914441e56400341e0303d0860314800920880d130a0009a89a0504a089070180302600700c201007402c0040020841580c0088004070215258212084604044800f620000e090403108c03030415400e01032120b0f91955192000d0b1054001414080910907140c5542e00c2c4007410700d5045204400300042c0581e2541e038034000a5911400740c0e00c2a140c9000040d4803400b05003103554211105442038a024640b5403100c1066950b651030701703400c14021403c110b0060400815a40403089450310384e000511b400c00840d0304c200d01c29610050004050b040311820340d107040c1d11031414010000f08400c6441401300d05103174080c50a00c1d08428800480c44558a071110302001d10b15182c3c0c10750000704c244800c110840c6001c490050407112241c0310305410005040c3c03244441d800c0c0ea0412b20104001900000381d2176002a5000b049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 564080026 1250 564078776 564078791
    0x170f0a0f020c06070b041a090312130b010603021804020a0903110d1a240d02010507030c15060515032a1903020703030506030d2001141303081006050f07020301 70
    0x4a03c0b00d83c82444140c42044000081104003c81c0144801607042c1c80308103100c039402c000d20902c0d40ea02030a50765008406003074002550480e1b10440f903514042c0c1101810010396590342c00030f40203503c06008816400d41d00f0f6a101c903182000d0007112210a07160b9501518680b45454000d4109122158181d00818803140c900100c0c001b024550000f01032590582024140312002c6415180b01a480b1410001c5007100440c059892100107003020340c080c24460b68452880c9022601100e0792003008201ca40442d1140110103004c1d40001d065900c00d8829102400c00818092424001129a10440b1682000c000f00450b5089151010031000000d641d04042d400f02100081004c051140f000203640030031148241035040c003403070303421080581c05007059081c0d184000701000407503900510490115a0800d4501c2400d5004040e8407418501e40c004600389401a84104e8420980c00c1e8009010b0501003103850700e02c654a0400c40d0b0381519041d01d88103414450716200e8020070810382c0c0c59580c5810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 564081276 1250 564080026 564080029
    0x10110405060406171f0608040f20010e180a0914031903060506072105071a01060201050f220609020d1b090204030b0c09030705120604170f0a0f020c 65
    0x140c00030f860310340c841c031040140688031440152802001c00c02e04c062462030002c011515441a041aa500c030f2801c4803142c1c1e01e0f400c01c0c10f00f1102018000340100c28407101c030200300e114003072964031240090340e40c188610145010030004c07100200091702896980c0010a0080c5015840152118030500b44511031540303a4090301d046401607050340798081c1c00e09070000c80441d414420000640421551141040302d50380b41d280881d40d0a0342d05008042030600c01c2142e150003501921511607009224203486070550114a00700c080030300c20305015609000104003101c4010040d13a01c216030304405401c035030000c0034180c015410001801e031041a13403240328001584030004440314070740c0218110448000b0b44040c8000d00802c6a021860051052009100241000c5a0070340c200640f04001600c07030b8074500c00030342803040039805580c0c0861084c440c03000e100008034059104500914007804c6814455030300701c0d41c1b842080c03400310000c3c0040100704e04032801641500400300140c4102c40c2284078590 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 564082526 1250 564081276 564081289
    0xe030706020c04270b0601110706120b0126100e070302030411030c0f06030a1103070c0302061b030105010f091e0e0112020607120302070f0627020310110405 69
    0x1001800181c02c8020740d12440d003040d0140b828540e020b442c6000f41d0403060134003643c2252107200d00500c050701d43c0d0003068907684180040c07021460914280e440c000c2e80c444c8081c08520300d4220814145040010146066020b4417501c0340c0700207040703d80580e0801041d4800c0d6100801452103041d400214000f0848603d0144124405c041c5620700603504d0030311342487c0b00202e40b03040b909071195101e120381080c1030301e81c190345d44480300041c0d86080e2a529000281809095900000321703441501004111240303900504504400b4025004d649040c1ca501d0b00d5915003400d0800d1000e4203600410041000d944100480103104103030f0702d400101583c07500780740f50030b1071440640202d072402c0114091000080104140340103000ca0580400c8198959020800d1070181c40c5014203540035030443d0100c043e0080d0100d0301c21590042114400000601d031080c020418880030f01e1805021000d00440701080054950507640c000740100010152002100054658040082e01009061000050036203a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 564083776 1250 564082526 564082529
    0x8030a08010b090a06140c06012606270c061615020f041701021b0c0307061b1112100504140604020f040c02011404120f0216030807030504210c050f0a05100e0307 71
    0x10601e282e840e528507901080c0f070410441d00203101cbe401c12020721540e14225254005007070301503524600c40030303100d414160410303412480e40340d00880001a20320040021041c8800520302c5508516030124604403054124010f141c01c043c05450100030a000c645600c04c0908034000003d400903142c03140002251008036141e5111303010940c000b0001182d9880e0920402c0c020f0442880d1420816440141034428025040405081355040000c0402c40751107001240c48560145030446204c4c0e842402074100420701103c2c2900c9050f51070b1190381e0411000300d999401280c00030700410070125400c0c1000000c001004150381075640e10588150001103003440140701e980a020004010604190003421140d0301003200011904440d203501003180c1e4004d0f00c402070707039003000006407104c100b40303401d031003911590704000c0c8400a4980ba80140c40c005504d040885840340011411543d134030810300c001c44102400c4140d01c4009440e061141d1f0a08120380c040b42c501526100f40c0c00d50300e07c004282028641e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 564085026 1250 564083776 564083789
    0x4020d150f0f0b01140d02130605090411070317060a080a03020a02090f040302060a09031209120f05040f0504181a07170103120e03010f0608030a08010b090a06140c0601 74
    0x111002030701c44486510400240c0c07440868280f20300550a80000c00712171403505110002140801c160295025a0341034646940003000e0401655465100240c1035410043c07000b07220700c0c01c01e0700ba04698030210055400031035054a0703100150500700a40041c21348001d100e01e400c10b0602800268800040044420b0346000c0d8003e8000c00165005001d0901d4004003034000d003c54040500c00000d0380042c00c5c940c440785a090000d080f499a00e4200c54400800034407410032414502001d0134802850500c05000001d512208454280c43c0e0040c1e441d40920310804a001c40000d40400903420702e50847d0010b50b01088041100b05069030368015514210b44062400807441c0c03042245858010048803404107100008142540c034589c1d40c0410141e11040183c01c101c0510f4030150551000d402c1600c2c4882924411301c54543c03a04c240ca07549420040445000031100710001941d112802c040b9140b00c04054403843c078160400e44203980f02c0d0080403006c00c02240400214420030020b00003503019106 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 564086276 1250 564085026 564085031
    0xb060406031401050d020a0b0c010920041a09060f01021009030305160c11040902032b2a1b0b040801020405090a0b010c03081f090203070f0c081204020d15 68
    0xb40e00741444005050700610f004103604003010700035a0b2040791207821640300e406010341d104144074460b0701500403440300400000f500c45000b60403480b903220203202c005080d1000c2042c0d5900c00c076024612040070140541004111002c543e586c00c101c0c480402c03054042c01159092442c03445040115221400142e002076680e1007486440e0b070601040004034081498035440d081c80c182c41d02c2d1204c8040c612058420b81d5651050021500c1c144240c5040e44030101382144100d280c038040142c0007854941d05e8001942c4c801005e0401c4840700302181003091010202152482141e550714180c50044100700104440250300040280d00940104041d00d95500096151351030328040c40302c00740b0090840b1020b02d00f0207800d014681da0003411894020341601d4109466101e070308004000e181d030803001d000904141540402c0351082500154001c051540d611810700110322001c9030155000035004210303140800c4000485103003c440d4641050004140741c0414000d41d42d49070282c15141034802d00300b42c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 564087526 1250 564086276 564086291
    0xc0512030a0e0303010b0301181b08191406150f030a1b030902060d090c05120705031c020607180506071406060105031006030e1005070804110604150302030405010b06040603 76
    0x15107a00a10015031401001581994100135032102c59000500800c0d0750100402c40d04841d82030306070004200ca8140c0000c904040c88046001800540c007102c46000440712001aa00d0903a141c0c4915440d0710340c41c140b83c0c1c006443c0c0c6001c11000e01c12100d92903280c80c4060005070108028000218001c034800c41002a000c03170300c1425103c903100140101000d16141c41c00810141e203c1004071107140d17059100020382201c6900e05403000403805d4010941205001c205814054000901c40d01501c0b004c03011a0901d510007030303412072111520102d00c40140c0111020484c0d29015440048500074030010b618030040c5c0342e0313012440b0354000300401d803195000c4032000900d00382c041c0001030b04540c00b0b103051441c51038440e0840c51500681e1140d14201507403051500c4440d00e040c00090b40e5013000542c1446141481e00300103020101c1500e0603101244d4440f04201a40b0341401100d046031003580440d1083c4410001c181c000f501700400640381952125507680130740d55258024070240525403400510318 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 564088776 1250 564087526 564087541
    0x82509060e010f060e090408090a1e0504060e0c1603020f0a24110a0c05070e0a020304031b020a031e0606032001021b060708040e090c090604050420010c051203 70
    0xc0d41e072940300700c1c1808000c4461001c682c90f041c44403640190008c5100d030383e4488030808280840d025901c13400c11072030011010041d804100c81c400c0e085400c221002c0c03120355103846a400f400c400c21b407800d400111003007059502d03845401c501c088800303009005a8482070302c4144228109842803100300c1c3d0054084000c41400307202c0d4855211014003c003801c102a09914880650502c540702c1c0b08014000c041d00c214081001c10000d59000d480c202e42c1d41c1c811400c0000221000e07400c1550201c000c00d903500c0500030755004115408054540040050f00da09145440c2c1105d0720280301811061240c8071840e2801103200c0b8021500218468100700070b42c28441d024409140301d80c2c006803411500400c3c1d0098410720004c600044580007101c4c1c51340d031480c40d450401d0903407060b507124140c948010020001d6464012450a0341030406035038040031350b540c1c01c04100413074400b110028000303c07c6018010103850320001940e69414103042003100c4401070b4407101d103802d41c44209004241e50020410845 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 564090026 1250 564088776 564088799
    0x12004140d05250e070c03050c070801020d0b0301060608070e0405070507120c030806030a0209041b0312080615030103120c080904090f050f150f06061204050d031104082509060e01 79
    0x209100344c02c0288070306060100819905071100c000c0c04005000c1800c01c45c2c4042032001074000c1401000071175403550711900c0c0b04090040d04490030703c2035107400300006000340079231801c40c070074011070761501c0500d510042004001e000190060382080000c1c04403800041c515101c1540808851b00c07014071038119450700502c070890085c6202d020b50041041e0304016110a007500e84c00c03551044004089071418548507020606943c405003071045100d07001c0b184c1075009001d407070245600392800c0345c140c0c4420a031001103100030310000b4046001d51000d104800e00c12040310082a21039052545089603403400201a142d031911300fa1010b0b44000072490410404008212203411244054000c8120444d589910680000d02c20b05421455100040351a0b9601e8116915041e8180d400901c501b040e050003135841610b0311040340441d1030b02a8480071600c0b0107060740c007151580401803d0303503488110a03008030090a14511041b00040d80d011a9400d22030007410050003070000322814a62402412006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 564091276 1250 564090026 564090029
    0x30c010207050d0206090d1e06050601020a0f030c02040f0e0f060f0705190905030607080a050601020c2d030a030c03080a0c0914060c0f0708012004140d0525 69
    0x1554441d070401c01c510303181e6084840c038072601110752070b448421500c041109040c0e6a00018100d11000e030290300404107415000403480d000d0310003000645d9031480103a0b0341d4428000c0160169107040c0e42c40c00081e00c11710408003160320103007010442d81c0440808101350781b00d104501500da00064044a0b0a02d0100001c44d80005841f002400600f08444003514074464004020f82c100903c60018140350b000d0000070b40180409002c8070b985140482e0010010601a56610961070a14010803859880064811040d281c01400b01c42c11041400040042d912404c01d40038a105c1c0d800660940b13561b042c08191a100d0180c0c6a100b030429562030010b0000340000e100f5088140740c50b1660400c16070000b005c1007030341c1000002080b001208000190b0600030704980c620365103d1403102c000040f00c04141c440407605a10024030280e1502c0d17a441e0040200704080703080c6030400340f01c10041d0003840d01840d81924030281c5400c401060a86400303003070801d140360606c1e403103400d4500c1c468016000042c420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 564092526 1250 564091276 564091279
    0x21011104050a03080c0a0f050105100501020c030d0503070207090e0606030c010513142e090906060203160609050609030a0e06030f04021516030e1f02030a12090803070c02030c 77
    0x3031805040400040181c5018040500084000700d00c103034070030004100c4030b44c8054000d402c203004844c0038901366028100032600c00071380221a4800244550000039601d194020003009004a8402e644d012540b641009245c0001c61040400000301c41c0b40501c83d6600413404440501203520b0090241032800442000207410803208002c00141d4283d40804c09090303c1c100150240041103440006241d920621283c109d004101e42060060043e46000240d9902072501d81908540d0b40ea0003586c11902c60f88204030150308100580315000c00e0101a8441c0c49110f08130000708506540c48903840c0c00c00480b5a5600d551000079a200541d8208408045000d0112038984c51441c069101110030349001d80001d0058100c0303140c65800c020414161034175207508114a03842800e080c200100100d0740b060f40b290143c030081e6105040b0441d000004982da241c0d5400842c40c0010034541182d040200f080d100803010b40d40c85217100020182030042d0300901c080c3e550721028190500401d82016503000940c2e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 564093776 1250 564092526 564092561
    0xd0c03120f0c0f03091a0c0c270916030507240c24050c1b0d170702030f0a090501111501060e0f0409031e0212040506182101 55
    0x6602c2c1d10150180e0441ea002c0c0b0502441d0103940380c01c3d42c0d98581600100b01b60342481d80441c240100c2c4002030004d0764106001c1700c1e00301d0103403400e015008050b6500e200da000c0401c6008030728181860b45182d00b014040d001c840344411102035041d810400c60f00b01310740d1034201d00401c001c45040da0020448000d25556408a2001d00341406003804412050003400c5406010a1280459400c010190844070460303003809645009202d12040e68800f01070304200c840c0b0205400c21420f40000c5102020b41d03140c88080380840b654241c1120350354002c00c41c1c0704520080060101410041c009010141d1003600d40f8201d80b030402001402040012005242d582d000320145020455502c04181c1141e001d800c1201087d0341000118941920510030250030600b008486030402d5030010307190071031070500c1908116003240c42d10100c0c0c8030f6012141c40201c2d600d0902041c4007910303188000745403031a4070390700300149541074001040c00440e2011022440c040382001003084404d003809940035003050756150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 564095026 1250 564093776 564093797
    0xf0d0506100e1815040e060118050c09210102041e0e0921090316090b0d0309050907050903150f0702070506030103062d0902030705040e1504020406050d0c0312 70
    0x10980390000c83c05064507000780b08003c10381c0050214200328040c4806002404440000354219a42c1c140078400d0300500008040302e107030040d0941c891240541d030300a441c249481c14100401503502d50001c1d81d200d4080f01400c45c07140d80102480100001c00201c1c4081130540d10b040c4280d0201c40107603106060034a5640b08202c2c1e1500045104650240d036500d0455440461146418940c0100b91445400d482405440345051100d003824200b110f98500b014001c1441400500c009003140800080110301d844100341301d240b800c13034011b680c015403600d86a030511181400180c0f5100c0b503c1220040b220764802401640c41d0503502c003540c020071a00060099501c0c01c408200b15110521005d0502e5030356001141c1081221038104101200140c0180711803240f524500000b80080081244280303c0c04a0004460405006040070b04c0746540c0605580340e4a80c070241900000104103d0b40696510360100d42d642d14040d0720705040b40581d81d0015180c0c1145000128080c070a0390718030038406004030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 564096276 1250 564095026 564095029
    0x812010e04050c0d050607030e160303051c0b09041502190323010501020c15071b1e061b050a021314010f030b01030f030e1e0910050a0b07080f0d0506100e 68
    0x80c031b83d4000d12140f50010340c0c000b030a00c0b8141005490700c2e0f10f42c00e0700703210140001856031000140c0b11130500b0480c00c99a510070240104100c81c541c9a519400400d0b5100003404100c0c84000c807405043c689070090325060344c010000c4003500044000138003280d5140c0c0b01d407a441c003000c941c088071071469191a524a505003070000c1c0d03407034521103000e510038246d00041100c805c102100340d0302c103140e001d40034030012607203041d000300d0440c4039000704039000d43c40d807614546696445d52601c0407034074161079070300d051300005142880300d1043c00710540e954030401881c5c1c001030f02c4900343e00d1440d8481c24000103050000765003200c2803c006070b10226554a21410900c0880c6080c07c41904607588030711180c0001d0420b00d000c0d100245100b01150780b0914001803c00c0c1803204e007004003000441213891120a82d07a410f010194070740f4a00a0603040444032800740a5800702c200144021030041000c00e0900380e002c0c990f52610781c0710f1403802c1c100b00e0702d480c103120303440c100740000d000fa001d540d08104d56005510300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 564097526 1250 564096276 564096283
    0x50a0e0304090209010e0303070b1e1509041110030b0a0f0503031b100903020c010908031317010f05010b0408070e19020d0605062b061805040812010e04050c0d05 71
    0x21168002d07030003c4d88200c16801a040a004944003401f40c1c0d481e0b2941d13040c981040d0404840c2d40c1400c42040c030328a1a00c0c6242982c243c030881600c000c0301d6201e03e04d030381032040d403060081c001c81d00001145c1410700c50307944801f400c0403400019600070030003140f044240619503000f0343c401d5903a000096001d00c41c0f41c0d070202c00c1c0c42401691041130080300c2060403005290007001c5902d04681c0349000e85181c1407550100d00307200d80030f00a0300d680e0302a90b9074141e0b040c1e8901c201040a140100300002c103001c00d024160b070384410261040004038045c5418813040b000c40d5400c0e884003440040005080001c10820b114500c010030010301140d0b40387c80c200160090000c2c010703000344c0c4140c2d80003d50041400f015400840038240141c00c0030b031502d88001440165107080e005d18820741203a0703c8900c0d000402c90080d00c0680c2c203600c0c050070390b42100801d0000a814041e0040310b0710101806130300c1c0c0c01410301c0030450003410508200e40701403c182c28a00e0030a80000b8669000b41511840100400c2000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 564098776 1250 564097526 564097529
    0x201060503011404080f040f0306230915090708030414040c0e01020d08040c090f050f090c0112110d110d0e0613020d02011403090706170f0712060801021606050a0e0304 74
    0x1c0b1700b0564811520f41c0f43d81007480780d40c00940d012a035004002c01485125802411401c04451010b00a1109542d820103108421a1084c2e855406100b015000c5038038600f0300c0343c000c41e401c0100d43e84a1f4680c0c014904580154000c06400c6ea600d000480381850140038448000c0c1450412428440e28240001d40700e4000114143c1445010710200e02001058040c0703030002c00f0840c008002110650a070080602000c0d40c1e06880007034180e001c90029039020a50099682d016104c900c00700200050540c060006000c640c0300111b0140704402c040096030290700f41141c1a59101c50b9540740d000350350421a260303811000402e900400c100300400c2c41c680c00810405404448100c0c14201500c01214840310414034881c0000010090000382e000005641c02a607c5a841d401d6003007520142e0540a00c400306c0c0d440341c0c20302405010405072070250707141e0110005160f42c0825130586814400b42a6400041b04024011542c40070000b0b0108600c1503d07008010440107200038a0149881640c03400b96 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 564100026 1250 564098776 564098783
    0xc0a0507030c020a15120605012312010b040602120f030a0f0906111c0b030c011b1e120509030c0f0109050901090b030f06040506040f0309030803160201060503011404 73
    0x1a00d4001c0c58080c61403452400da0041203903004d00d486031070381104400e81c00f02c180d020881100c0145500c00b80340c090003046d02c10613500e44034410400144400c0b01c0011100403141454104108809550402021806405030824050b910f034a001d070028600200c03001c00220503581800360108810300c901c100e0307410903a45440428489200c0480c0002848112001003d091800240d03e1140183c070740540118424200551342c410940c1050300152101c401046078150014011040258040c0f43d8420100c1c0c0c405105405000c0280e80e50071807484241640218003111000c41e104010b544e141c8801c2d003030902d1419608007201000400d5a44014090305072240341000d042c4112648183c1400c002080000c00300d04955a5802442c4000d001022100c0d01070700484501c29000240052602d0003160f004001301000d9640b502d5200e40b644461000f10b080105942002010840796405113010300045050070a800c0342d40c0002070b084481c07640c8098040c0c1d0410809600f00040c000100d64000d80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 564101276 1250 564100026 564100037
    0xc050c06030c040b0d06091d190c031202010b030709090302060a0f18140d0e011202092403162c0f040e070303020111040f060e190801090209010e0c0a 66
    0x580e066154454080d6404c40100b100c40800c449854440301d4010008503448031104000340d003042410301c42100d028040214a641c45284480400b800724000c140344c241c01407441040c455106e60b117102c0300f00e82009000300140e441d00d90f01d20341803405101d00001050000e00411420030300fa42c01944400c0000d09070f0707880e9551000040004a60780d0040202400065081d00c0090741c01d140c65981880400206035440c41488030900d2040c0c024565501900030586507140d03000c502c190300d00060740c4040809500a00d4508100c1075100c08046484180000c5a141c2c0c0d459240102c115107100003465400010809000140c036492008210780c11710b624031400b1000d880585c010701183d03890782c92001c60340d00603250005040e0840001304855064034030942c000e0181c2031341d481d050aa20b01980c05107030109480c0c1c00080140c54080e040d800d0411901138a0120411240c4034100720740c240c0c0390711980341a516040c03800c00318904120090b0262900743e6208101d81410320315001940500c8100c20103004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 564102526 1250 564101276 564101281
    0x10f08060d021f080a05010b07021e030118060b0d03081807080f06090f010c0f030c120e0d030b01051201050d1505070216050402121f081501080d0c050c0603 69
    0x441e00c100148003550054481c0c48100041003580a06039a01c106080000d611030703004c0f4400760118044e0a040701c1c051000c01c3d08182031a0200510140074079601c1c5024010301c000c20400740ca003070090060000030540d29110b05101800e00c0d200307495440e00300720b2289081c4440d090010703800c4142141c01ca94134690701070050243e460311a242c42040e4200340140d00c517420954691920000329544101c044105940440f0664901d0b2802d03560020005c0300420718900048002d54407a910000112015150032102005940d1500c82116500100d10110b80c02080f00c2c460643e40600545502c0c40c400e10300f003403030210b000ca02050b80344018001c5900c1598121541000d02940340081d10780b14080e16001c014906040d00082e669070240110b0b0300900288880000341c0785001e01c00d0b51800102030b0603c0c00e280c2d41c3c0140410040b40350082424032207000d5880401d42a50412254003121801000c9642950606234194540210014594100103080d00e452002450101e05070146040a82d41151640c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 564103776 1250 564102526 564102529
    0xf0906181005120d02010e07061b0809120c01030b0102071a0c03070b15090705040b030a0506272a0f0a030b0612040b01060810050607050c04021201170c010f0806 71
    0x2614642c809603120500145074820b000c0c1c080341840b0142d40540003002004920030000d5111115803044001140e04981c074049011621400001c0d418400c080307251034074101c040002c00302da00801501c011544101c5020015507010301c20070303044400900003041a01e20707020010240a000000d60b100d42080441e0242045004005859040780c0c42004141180760511010222028151405104941800c041940300380584100c40540700343c00201c034a55601d100201c000f5020140819800c501e840c111094030b4200348000c070b040c03d0b80e2040b0388800340c00c140440911080202c1911008240604107035141400440c0441e100030203042001c40d2664007004094000300074003d41a90405400510580075000c2003032400e00c03551046002e0350301640c880d5411650707000200c541c080c3c03050710103605200c1c80c07130800c000e08656841403044030090b07c58240401c0c10303604541c0c0c20350313000020303107005210b0403480d240c0071190080c0400040104540c0d40380003c0100c0c2419442c0c0c130520100c00c01060f480d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 564105026 1250 564103776 564103801
    0xf070b0726030414160506270303040603020d050105030d21020f030117010f0e060601110c031002030f150102120307050d090b06040c020c0a1401051e04050f090618 72
    0x40c501c1d80c010300d40e101d180c0760601c820000031481c103054050040140000d510004e085118040d500040c186038204900507080380180c80b1003003c0d150510200940001d03066804100400250415603030150316401800314001c10b80304182c000b58440e401000c0c15103030640d4810002d240b003403071400326213020f149201d904100034400c80b240a0110300001002007030310101e4083d2940c0716000e0100030030450203811120000c8400104451456400290104515610400768074800041100c113403400f0480b144e000910b045074084020f5005900030081115043d00060b81548c402040e0314000c82061a28000035152207212041d00168000803012034140da2003136081d03440301c0e5001c50301001128507504000c4003510003160040e1269041c821440c0041d0b1010440c0740304100042c3c80742611030b00700094908100c418140c100d040013814004902000d00000e44041030b08480d00410742c0d16820300d024400d0a180130740781540101d10071401d00182d602c5854114001c00c026441c83c22260300d596440b03145 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 564106276 1250 564105026 564105083
    0x304080a11060a141e04020906040b1c020109080d05070b07090504090f020a05040603020310020a0c0b07081603060b16020102010612060221040210050702040f1b020f070b07 76
    0x16248105410054920301030b03072094a610028044c003501ca40c2d00e40c4404180f42c15895042d220f07010058002ca001803c0440300c0a4019100501c00309a07040c10364041085111203000071070b000f1190450100030755130400e000b900074161400242c410f641030020054450f02c10210700a0001c010200000c4c81d5910900b0041e01600b0000c200740254485400c000c0c41c1490b0801069100d203000c0b10f000100341c43c1511030366044070b502502804910810710410300c020b40102c4c800314140114111420000751300c41c0340152059201d5201c0103900d0a20505c2c2e80392138110b841c460003c0c585440b80034022610140b058a0100c149201040c81d040b40d1440101d01600c01d070ba01c1031111420008000d01005810b8010f85116920610a100c5001f42c01480a080140603540a5009191070110541880c81140206401c03400074002041e07106003084da480444003400141104c2d0494417012403161039040c8002024890b000000341810381c1000c046000c1c0384a5004002c020710750310300c045107400000d90039000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 564107526 1250 564106276 564106307
    0x308042a080a06140709030204111e120f1905250f0201050a091205031005100804060b0d110118031b05100c120324170c040b03030304080a 61
    0xc28290380c0c100150340c400760201c040300c89a04240c90081511042c03030703c4500c1100071b40e407034401c12480c0d602440b0060070210000010204100868010040003604d1800d03400228805141c2d03d400e0540380503001030018002a8442c1081b409200c40304c0030805240802807980b9200007440d40f250001c4c100d000e0030b1140ca96914550000c00b560515400000c40d01284480ba0000d210a03034820719094200da00c403110050004019110720505140300d80007555101440d2224614017584445c000b40701c2003d08107068001910020800c010400c01e4020b0402600090310f603001040c0285e41c59000d03041050100504000600070a10b040c100c0e0315041a0096401504080444403803111001c800c910030b0207040d0044d540040f01c403c00758441c00b1015072490f0001c00444103102d4035601100604420050070400d606000e110400c520347c2c1d202d154004041107c02410001070000040d8102001c3c0d580d828855450010840317a00e44010049030303405940011072980c0c13a403a0074015166840480c1c4a070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 564108776 1250 564107526 564107603
    0x90b060715140c041d060a030b10082b08060f040c0203070c03060624050a0e040b0306070c03350a06030b16091a07062028050304030804 60
    0xb00d440d107030081c02031083c0c1700c3c00241500b0520100081c004010b000b83d80054112941c09410004117041d601800d8108840504440718580d50384101441e1507603091000c80c10040d103403220044d49020150203450005181400c18603440c00c0e40000e1608a51141c030a8020b580b1594440000b62080c4210344003298003181c0307260741c2c0380c4900300000142070500806050b18540340a42d1007840b440c9060540e9000d507580c696240c070f0b003405411900d2008122034280c1198a41d6107013942d07940d09002c4541b01e807030386945101d0380305154100141900d8040c0c5090340542d40c03400f40340b0000c0f150711165800130450381d0a009100d481d40ca103000001c10040d0b001030001c036101014428100501c00790b001081500d0760ba10b4240c00e8560805030f41486000c0340301246103004000020001d012a0001c4980c0301300b21318036104911a06424101c1540306000d0129031194000c001003044400c0c0b200b81c980c49800e860280c1c1586810765020b040c4002c00303040030b005550400d0900540d5040702c00d88606410061040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 564110026 1250 564108776 564108781
    0x16020316080a0c0504050c1b070306050403020d030c03020a050427060e1608060d111f02010618020702010e1302160b0402031506011b110307080c0109090b06071514 72
    0x4442d202c8800c003808075421040844001010318140c0201c6000300c0c003040c0c02d1481c201c400e4039110040000c407201c1c40403500541c4000008100f580c0301d120310442c000d40241c1000344691074010b00302c450500c2c02106061050050380c107940c1d84a820f030750a03204284240100b0700d40b603418490601e6190f03c1e1840310340342000004680365000d50400d900958010003102018070400701c040c0d0b41918115017098201e40580c82d01c501142442c00880720050303000d030099400b2104611302059140f4041074520241c0c1d101e400c10010140d400601003400c101c101e0b02141044000d40c0003c00b100c80c0a00b43c0e9108002c5c83c03500300c1e0306500507170440f03200500d1020340d0701c8a0345062a080c4202c1008441c10780c400d00606420b001080c0561200790300c207803016074404400f0f80d2001000a03256007001c105483c004144121034010fa01c040140038003500c21440146074101200c000103260120300e400010240381414110403080c1c0703500d030a5810711580001207010890403a65000300411020f07c08501c9a003c2005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 564111276 1250 564110026 564110039
    0x9090718180c03050d050301080a030503041a240d0b132f01030b090f04120908010513120f050a030b04091221020403030206040209060a0b0f03010e0f070516020316 72
    0x502c20300b10780c80740c41500c40d030184100041d03807180024418106690820036610000034418401154018482c8242d1020418481c1c07441c1807003101164030301031003000c1c082c4942070150254407210081200300c503e401c5551143d41c840041101c0501150420070454503440c040054081b09108550724000c40703401440e0030740492030403809003003000030f02107442c1c1076101c10542014041d1604c585072400000010751600d07501c80c070160410301048000c0042003500411040300a004050240b0f0340d00e140c822000340c0e1410142d640782003c0c0c0420080c0501905c919118980240a44847e5034031b5040c00515142c400b40420040c025001006143c5022550b0140b6826000f4a6510744005c10502161149540c00c80720340491140340409005a4009400200149402d1004550001001c0c000004550381c03006030000c42d4000c8895490b60a4003c4014054035510b001c840e03500c40c1c41302c00904041d0070040006803c0c1c6c4a485012304540f0141e120503015503d0400203440548030b043c503c1c030507465aa80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 564112526 1250 564111276 564111293
    0x4020a030b16080c0405060306010c3809010c021c0c1202010e0111041a090f0301021603080906010b0d0504062d14070503061e0303030a06140909071818 67
    0x4403590200f12810045403842440005075401c5d61700c06494645107440c0c0c0750042d5000001c1d0001202d03401090004106c030031098424200004c048000c0d03c0c3e81c80c00d0341c11890148800020301c4000d40c0d03890710f540700e00c40c071341d00003180e0b00307170342c4090300c9018600294150455000c1c001c0e46015120314080c000c210307030165056000141400e6000001c00c00e83c2484e0061141c82c0c49240f040203150345d05400350110a0a803c001040b026000800c03940074111307039601103420790b0801c089a81c140717800c4592a5046c1904003c0c5594016000c2e0050304541d81001d20340c1c0814055071500c00d00c05135480e000241000803641c0002c0000201d41060f000054903e0304c0189030720000a0745c8400e241c107001304230f00c08442081700240108441d40303d0900b50fa8403c0d09122a8042c01d5111081e200710010001c0100d0b1030500055004103010039000c5422418004d050300c131005100031081c0111121810410301c00004034510b0203603840b02842252141c0c15070700b8800504210041560708a148115140800c020b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 564113776 1250 564112526 564112561
    0x1a0a23070f030e011e030c02010905061f0f03020a090203040206090d0b07030e150c0c12070f02120a1709280f0f08250e0f04052802040504020a030b 65
    0xba6600d0f62010100350045800d0818503880112400c00e8002c40e4074000d00a070004010707400140300004883c0041e48406141036020340c4c0304548203505001c0350002003440241640544404110487d01501c2c55000c42c503009a144181800740c3c1c3c0c00320101e0215074900d0201c2d182050000d0084416030500d04104070030b0314042d10700c10b01282c6007580141306c00b0004102404054102c1102500d42e941d44440c4402a510000d50360345c007400350546140c0001c075200047c049642c0900721020041c030503441400498401e28002c01401d501140810b8000b690140400d0207000404200301d8a03504018049507500d404403040e060005452408540403036014014542241c20348017268001e20380d14510b44000001901484081341c102224001140201200c01440780c011005206c400580e00c0c071410035001c4095402d6010300755080140424090204540f0758210b840c60346100248080c1ca0011b44030f00e0007a04000d00490f01d44c00040c0a540d248800c040c001c1d6000804862140382c800d00d6524a550702 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 564115026 1250 564113776 564113783
    0x1202040e1006030f09030e240406020109120504150c05010209040c02030d1406060a080919051e070b27030d23030c0f1810050408071a0a23070f 63
    0x1c00404e03411103c0c2e140500c915841e0540c50b034150244210381441981408651242044800c1c41c00300c0c50300082d80c800a0000f46403d500000e01c0d401c0d02c1c5000f00c00c1402e003900c40c104014041c0014003007a0350103820f19841c020b070703810a08000c409600c2c0c09802ba015400b041c0d0b62091a001001540c03035004401804028511307442007042c009401c1070320100050a4940d00e4204405003c0e04607128002d040003608110500c084408200103041d80c01a1440780710740c1100c482e040001050010181c0c585400b0700c084014014010060030181c9940c00c3e4041c085c1d203481076514010401e420496100385c0d40d0b0646001400303482d4107003140d20b03010f8900c0e00d6280c1000c0160302d50320035034089520850144c900130508883e07803518000c41e02000650725084032103140c692068075038090240b556240c8040e0b50300000340d1940c41c1c4803460006024144072056000c038031201007040219140710b030380c14120307032411415040c500b01000d9100703420051414807020200c100c1e88002002e07070074003450350640003010f2b10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 564116276 1250 564115026 564115031
    0x3020a0803070b1f08010501261c030b060702040507031e02040303050a0327050124030f12020a0803040501060e060619031a060d0b030606011107061202040e100603 72
    0x160380a959030780c0d01c124400a040c1d400c0d01c401240a406402c0703151882c4c80c81d4118901c41040c0c451400500b10b072000c0c5e000d02c80303d45901d10208901d4043c42c41c1612070030400c2c800750582c03008040b0000a08101594030382c081540e50070380c1001680d110402e45a0441e00540b00f0001071030710030030280081c603081241d4201400d0707408a02800c881c8500860341640e44c035030b03181400d16148450690142c03c13071005162074624100e902491030079540c0740d0a0b40c0a0701400020420525014584031a2000c402850b01c0700c0c07024010034400714801001160b0141c0c0e20240c4641d8084000e00d00700c1c1403480d24880104242c07000020f20081c800150006d2041d2906d4202c407650b141c80700020072146100b58400c0300e40407000341c1d44004a00d0300036400840e84d80500160004484241000200940c0c000190300d84005d590304030307418182c1402c003c050b42c082d10a007000348031a1009001c56a0303420b418814041003000c160700306030341421245c041c0d80043c41c045103884028100b00590214001e92401004000703031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 564117526 1250 564116276 564116279
    0x3070c24240b0a0203091306030f0302060f01060c02030a151b0c0209010b120f041e300801140f130207051b0f0d020d0803270607050f0a0e09010f03020a 67
    0x20b00310b6084884981198000303510300014002440725000910340c40e51401990f4040020100d00c80542c510b144a00c0b83e80908400d2901c004100042001a0001010002041d5085c001610000392000009810140340d40022051481da203010304070054040445245100c1c03210a13240e00051b100d15110302c201e42116060f0380b1140f001c0703600e00944031134031a2801c013400810039120701c0c1000e8680050080005440106c41e210024000d02840c2c0c1085642d41c03000c00c450065a466200c0c014103c0c154900340845204146400602280e018058420329040841c01546141d81301019074003200c034050b204041c0c101752204413600030340042c0000da036540140d0b0b90030844d40003504030949002c4001031800c0024400c07502807240400046c402260070204d04202d240102c1d481d400654840c10340260110180342d82e4200010f0441000030306140b8940c04042407040854001094a004042d5103190a0711649000411561b03450500d85050b0440f9403e400401c18211100c440410359009456561625 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 564118776 1250 564117526 564117539
    0xf060106050f0403030e030a0503030711010f0501080d050c25031101020604020a060e06220815040c030308062202031506040e010b0a1e080f0c03070c2424 68
    0x1842140710200e80110b08000a000180c020416049005ea01404848020362190b4a840c07a41d4001d0764000d0100e48001c800c0c203031418090146030340484003800e05004a51400c401d41d03a981202042042c01d004000c41d03c1e800303000040080240b124880704100d14900c01d54210640003080070300060b6500615030042c140035500010b0200d000b44d81c05030082c40618035001007102c20030440700140d6030148041084040740e00e5416000c030184e400c05c62800401d0b45c0382c400722500d030a80c0d10303a0003e80d43d80782000f00008160072115807400c50390036040c41000b507030b039403400540001580101d0201c0e071a200c4089003414505039006d5449418100c1c0c1c1200c900381d10200300440d5000e10320a5460300b240800040c0000541e1704041c2041e203207141400d4030b9086009104683c0b000303803500d010707001a05010402c05214603c1e2065604210f000180d6851410542e1001b0f00c49105170070060403100f40a42c03094544800030b40300880030324030000c0c10001c0300f409040200d00041d2403411000c00c1c00d104000854031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 564120026 1250 564118776 564118787
    0xd14061303110a0b0a050a06080601140f0a12060b0f0904121812111f0305070f0e030c0108090c030a0506040b0702010608071e0506030c120f0106020a0b0405010615020f060106 77
    0x2035070040d818035560b07605c0004c003101030304000700396050441c1c6070700000600703220400c50b0b90301a080282180c15803450010130b02c205401140c030881d2090f00f000350704222941280414600c0c44d0b40100000c03c18031009000700701881d00607000640c102d0508401c1000748606500c0c0031481325200e40c1c034014050102507612924090502444164241c112031600018502c1401c02d110000090820311082d510f00c9490482c1ba64044003e002281d01e0703c04010565501c000d540303035607400320705162140441c1e07580442c0d5200c00000105050107510307408105603900401250401000040c1200d680c5040e518050791030301c50a5070211802a20a00401d0302d05d8018015030081d250042c00804815182c440303030175400001c2401403d40d614200401103840d4685100440c80360b1000300300d1598032113911400c981024402400e514206d14004c006104240c6d0103d00207110f240c00511180780c40d143d0b414518010401540b10310380c1030250b00600240319401041c1b040c010000803055455a0b07a880d00107681 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 564121276 1250 564120026 564120043
    0xf14030115051c11150301030b010524130902041d090f250504020a08010e071e050a03020d0509060906070c02030a1226060307050105090303090d1406130311 69
    0xd014207500c821010b05119050403000301d030b000d00c0001c440707003000a0202c1c405045c49007101c2d001c020000014028402c000b10018010b040569075808480019034001c0112644645602d60b5400005100c044031440035035460058240c8800071561541e41307054001c4c5046483d9100f4010142210008180781c03c00b240c05049115140c0c05041181b072000d0104c0111155851a01d100403000310340451640c443e403014000112803600e4540361941402e16002040030300400410410810030a0701d94000d24140c981040c140341d0381403040d00e070019248190701034000c140040c000180740c0010410b0b403041c0000c0c468003416810090320301613101d4450494a100b2804070294240d8403800ca05400241c2c0b40c400d0a9221000d07241840b110a5503032041e00d02c0c800116014003c08803124280300390751405020b240014102400e200c0e240c96000c1010030b031680252160940b00b140000034250912450340034081c82c07504480140c440c030707182c8004070f920a98150213007540012901c41c0003004980d40000c5502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 564122526 1250 564121276 564121279
    0x6071808061b0310150909050c0c070905070212070b04030e060f04030305030403050d05040303051f0819030e03100c03050f1306090c21020909031303080c03040f1403011505 76
    0x6884100101c40b542907a0000d01440c40c0034919940001d00b0701c0d000300100d0030012456441e1030031107181103043c1c019950302401d00c0110302c008000400350010005001e00813252160342c04285a039807080141d08001340c4021300000c0c82d070002503207400c0050f51072400e4400c0d8440d44401c02c0c0780030b0903400e104c102e004601440c3c012250401090001c43d0040d03002c0e59100f0b219160052406003200340301401c0c1d03a02600c007100869101d03414401403800c200040403241c0b9101182c000c82a2034040f40d256203045400000d103050401e564410180740c400d20f62030600c940c010f8126001c4c00756065490307008050643c00300002a28000200c0d0840c041020007a000702800e480c81c00d0f40c0e00d8151280802442c0100301210840c80408002034041251071758030a1107403181034664440b0040b030051003500c4000030702581c4541c01c2007042d500c2d00c0194164910a1340e030010340031602e4110340300c5114618412508644400069220002038860307a160f2041144207041d8001c0c4a04801401055100c1c03100d8040d00307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 564123776 1250 564122526 564122551
    0x252d1707050f0d090213021b010605040506010e09040f060e1e0705180a0b0a0b04061d0d120203070b0a020316020606010206070e0a030f050d091208040e0a020c0607180806 75
    0x4441c0402581c1044444d05c0c0003c05401401c0304042c002001c036803101d401e00c03100c0d030088880070a15a10078481c1c0c5006180603a01800a0b10342100002d00c40350590b10070324401c04040012806000446601101320b942c01300c0c0800105460075401aa0351481901c5c0c070304200204888144100c80102e5000f084400c0502082d11202c0c02c2b45d60a8007a4038010481001c03a03648a01100e01640ea1031140070041c5003001030f942e6101e00303260004215070032004104948400303407010211680c503101011421103800046039001000540d41c101e007107218409002c0c0501003080d013404001c004541c000d6004580c90701200a15004203601680c841004494650150700403d000030549030190202c010981001412001039544964031406110701000054615a112048813100c09401881100107801c0208052000c581a03030359030036103032049001e82186900c005003c0350051095030181c4010a0908055480302c1c82d19582c000d03c2c046074840c1280003074001090010ba0f001003c80d445001c2c2000180d43d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 564125026 1250 564123776 564123787
    0x21b0708070b18030f010f0204180203041101050702060d0e0115080d080105040513080c0304061b081804060e040b0906010915050618031f05252d1707050f 68
    0x981540f90f0800800300c2d0036001e811044600d02a080c440c0003020303505004010703151404d04504200004841036200e01076072041040c00049640e038885da0101c0d030310034600103a58468510100300a030081034400f50440f81001880450464190080c0a82200024074100d507695103261250761100080018070100b403c2c040140710320300301030700000d40c44040310300c142e001c0c0783c0e8598940744141c0c003500754000c00e40c002213000c0c480954020030040001100c8011220111510740390100350340314030120b07882d117840310b4195200d440c1c48a4005800030a1124824005807415040c8040755410031100322120780210000410359036814402c0812120a00390301d03000742418030044c810180e00800c600303075030071040050039290707a41d0802104090b40503406024032804c9080301d12205030754001e80f5000c460302c883d041d03058420403500c110800008203031520480c126006000700e04c501220401c400c100300c00f10032000d007919400100ca510401652100d01f0210b5035440000c48007801040300408030080c04010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 564126276 1250 564125026 564125047
    0x70b0c0c010206071e14040f03080415170f060f0915151608070f1707060f0b1003050402120f0a020f0d030e0d050c0a0303091d0f0a020d090204021b0708070b 69
    0x740106d211029100f583d240030b448500048801c0000d80c01180d0344800050107000400004254641452880c00c00030103240c01d80042041c81c070001401c4a140658100c0010708596031038000a1250700d010380b00488038148101c42e142d00d284003440b03160290381080410240106000104d4842e80f40c41c0000601917035040e80c035910035520401c020b55003028001e4410303021403201400214a1030f402c010781580ca81e064075042082e81e000e03508005090b407400c500d814003521807158400951140740b40c000360640e184d01c00200d80300e8000c002c044051084440c1c00c2119880060424041c40c021110345901000040400010110f0b40000a000960360701804171281840444484803a114500b503030422545100401d00c00c20413940300f68000b5409090402440c0004d0000c1c4030200130b40056020030b40b418410210314280003804000e20154002090141c201040c0d014803041e5500900544d41d0781c2c80705515002c1e003540200345d03103a14042d0700800a10a8000183c10048840400d09141001403202 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 564127526 1250 564126276 564126287
    0xe01030c080609060f0f030d082a090622030305210903091002101109040f1a12010f06120b1e2406030702070801060b0a02070e060102070b0c0c010206071e 68
    0x1070081b50404510700b01400c0365074040c888000b05452030707a90841107107004012101c1e241d552006140c2c07000e0011150807409140c65007120b0f40410b080c2e46444e55540b44106099440150190703c0541c1d01b9220710100402d54400014400d800c00099180503949694422010049003518000100c0d0f00801080940742410f0403010b60356091401915038802e15141c52380140c904070600206464400241d603034143ca003903c0741442200240108008990901212181c405c0c1c040b0762031885100302c40aa62024402500302807a040c010810900c526a42e8000b05100201651b030200d408000e2940040c1002d0141582020300c4c086c500d540c80c05a490f0413885030310408018030407240c504000448900e440d210b5400440c040d41c1598000c100311481c12400c1307400c4807180d40028117010000c00c400a400c40d4000f0b201e00c00d990034046404165100c803c0182d2a08607030313500200e11000045034011444201140310701c4801804c2e000c0e00c8856840c88812281103118070520002c0100c01c1400149592194 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 564128776 1250 564127526 564127549
    0x50612040609020a0f030605010302010314073f02030105031b0102030301030f05070317030709090e0c19080601030807050c0102011808070f02040f091b0f0303180b04060e01030c08060906 82
    0xe071100c11307070303a480310b50808014429420654100c0e4031040100110f59042c81b0744d80144c1c4101c0c11043d058246090010403c110030140d00c0c1245814a0015100106038130402d5440c00800c0c01c40e4404d0003007030901201a40091107517602c00d0080410a4001c0b0103904034000030303075030164040c40c42e5a0031030ba100214841440b030281e903944105e61000c8001082109034052500d101c0c82401e03140d1501d844010301c10002d0f40c02c0201d002e410407a0079010442c0c000385080054004840b0f544400500012860f00c00800f9840100d580c40f4440001040c1b2480f64000d0110340d0007002914603045002005a007600c0c82d8820034030f007a181183c8120007090950010749881d03407203548540100c0341c1d00e4000a0076501c1e5a28070802c22580d03031805104000b003110281e20820003407460320240515051540c034588441d8030015003031004041d080700c0e03910340708081c003400341c4401c0c44029126500c402004200380c40c0000d060740881d151104a00702c0c0c60080360564800d1000620742c00e190f43d08c0900344144890403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 564130026 1250 564128776 564128779
    0x801060e1f0e040305190504140a050604051e090412020d0e150d0e0601030c15022a0114070b0109180507051002030418090308010605070f0b072f010605061204060902 73
    0x10f00006d96030003508030342d01c208440587d4895071102d081c1014549550803030f01110744142c1c40e07008104840d8503100f080d04c0403582c0484454800321044051011645500195a68008010f03020802004411218400705174525402c03503d5007280908240e420850021800380d009540c203000f043c0b0031042c41d004102107002e048000c1a0301c024040300619141007078108503a01020b4140c1840000203d0380195035460482c4018150410150070310f12410340050014580d2061b41e1030a048a89d00030241c0d00307580400c01c0307041a40d032440c90401001c0104203000c1c80d45200d080003510300328100a2940c1d41e4802d600034002d0029a490041046200e61041042000f5808103000010b4404c00462140b08038040a81020030108201e150042141005070014810310405000103000f00e41c0c00340a142caa039510400c42181619004010b40e02e491841c2d1001e0740c41a98819851419050307501d4000e111100e0000a04c40b484d165401c2100a019011703590412102000016011611540062100c0ca00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 564131276 1250 564130026 564130037
    0x301090b0625060608030d062c1906031a06040c03060303051606060906080102070c05180f07020111210105090c0f03130f05150f130303020703180801060e1f0e0403 72
    0x280c0d03400c1c1030308641040003a1240123603140410000b1200c24072100401c090125030320324003080103064008426002605288070144204491525002c503580444080d40d00800d014604000c403840c42c1103003500c111402d5008a044c0104007401078000d01684042e80d906881d010706205042c10449401301c0301c62019140d464a4510004018159119020281403040700250307542650341002541c82010b030740031b1030240c14104a03a010a1100002c8941c0103061216144107a45a0810881c050024500c1c100e44e403481c009591590141484251901048041102d21007a0303600d804104041500302d9080356214010000d1842a0032103900a50b4001100701040c540c402d241d07141c8100b8200c0b090342c21103a950020350540b19854450324429408080e43d119944035190205042200d0318062034014181a0013080d01010180200c4032180c41c0803845000d04040c554440f0418040c3c0780500c14400d91101000c0402d000c1d036056040400c650007102d110074a55403030107800c1c200100d0000d000750f04014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 564132526 1250 564131276 564131279
    0xa05060301080607030e0a0f1e12090504060b0301140d06060503100209040f0c081609030b0108010e06100506090108150409080a090909050d200d031e140a0c1b05030301090b06250606 80
    0xc0100c580c112b41c03406580e440c0200142403000b84000c40e50700c0c0c6c2012120200c18001042144040d0545c022441c00554030b6944449062038540050701140d00040e505000d0083c034070a601039507031b016000e126001c0744e05104214100c0190000c6900c800e5000e80040c801c88001504088a5040c4084480107440e0080d19a0707601d85450400345020f810091543e5140c190f4103141c10402c000c2c050b000320840700300c14003141c54000001d40ca403040d00340031814080c4090020705001c0200c0104402c50001410601240d1480e02c3d19403402d40c0b100c00203070049400c040001c10302210500c80d4031801540000100740281c0341c4103058404041d240311195241d4035a402980140000f8001007005461544012800b072035000d80403d151f0a01184240d00940341024041c5409411601076070406030395000041e06401c00f000465905110110304c0c07010b2220503c07e0400c11200100a42c129010148100041d00c069801c02100e8810380c140000801d15843c00a403010322202003114240b40308040004109 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 564133776 1250 564132526 564132533
    0x603150b0f070b1803030a1d0f0708010e010902060301090209061b01020c070b03060306042303130312170a0506061323040c0f05090a05060301080607030e0a0f1e 71
    0x39800340d94009070140020520504004420300e08642084600c00000201d42140c0310302952808000c24005045403940350420340500c112450164011007081503619560480c00c1c810340d603041b00c0c440c4412030340c41c0c13004140101c035040c0308140c0c1d019401402c0d1407942e403a11510802075080b0a01035039110904001001d02c540503851101240d1a03880005a01c1d0003560302d299050940d80e5125034003881080080000c1c81c0e4002c40d82c950f2140d0f0111400300b2039079000001d014030303081404501700c8500c00000c0c00503804407030401c0b8600f26032003810a60103101c8088003c648100002d0100000145c160f00407610490407500055030240010f04801d0800c0e01c0701c0d510b401401ca06034450700c9070141ca08400442c44c0350220b01049182c07011346d014040c0e2024030380e0042201c2d03080c0068204010000c6440026903507850a56001040024001516561a05411501c0d04000c0c0d4813800401e1500642c0038020002290080070903400032006502c1942a0700c401c015408012101c40d8400708550200307000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 564135026 1250 564133776 564133799
    0x5160f0603020f0c15090c0a0302100302031005090a021b010e070b0c0c0a0311030d0309031e1209030e12070b0906031305010501060f1106010302031b0a08010509060709050118060315 80
    0x101d14041c0e900d0300d03680c00d143c6e101c28101060b4299040c050040c807102840035868040100d01300918500e030060b901d83d19807141e80000656504096400041c608c140400803110b83c02609070007104400104100020040060032942e1168000100b40c202100422240d00004060001c406c2400107840f000100c000001c0c4043c4000c0e00101c1c1d59260343d40e00c02a040c201005030a03650811030408118188042d100a004407a114103046561211081140d072454807807403010000107503411007802031030501e10700a046402d10881d028000e0744032900d64690700e8030000d205012280320225092901d6600b80602045520040c207814864260036000d90014500340b0905000f0496642e03070402007030030742000070140c800d10904420580d010400501c013594010407505c07104041c40e1a40c42c0c0003406c030400709042c0700303481e4000d2aa551030202000112400420310610416656070784101d400c1e102c800550b082d0396409640b02411007000c10a1010600960003081c13070005804624440320b580e000300d20300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 564136276 1250 564135026 564135043
    0xb040308040905092b02031b0105060103051312050a05070519020102250509060315010303020d0e010507050c1212180f030f0604150615050705160f0603020f0c 70
    0x8910310001400c10000100f4410250003801c024042c10744500040345030502181d600c1c03421a0703e500b980034194850b900800898071b480070b50200720208850340701d2999000300380441e031160200782008002800ca011580c108070445078080c9100b401004440b1044900790031040c642000e00c60100290f1001c581d080004550344d040803c84030b80001c02c244002802d00c0562440c0564030b4042d80c0301541808101c5100d101901d00a90310b0712210350380e030000a480c00090283c840700550400d40040149039008c9601b4007a00401e45a6003400104100111980d04c680e001c040c1441c2c0019610710518030302404102503040301c40040744e02400c425600350030260b01000f204c0c504c100081e41c0d500103509111103002c5003042c04401404603a00d40c440340544421006000070f00041c9002d0040c01102510350203a0301800085024681c103100d4102d01604540c0a02426a594490100c2d02c202e103e04404000302a00d08908070300415900e020800c0c0e02075001250440321500c0240031030060381c3e0041105c0720303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 564137526 1250 564136276 564136283
    0xb07080c072403110c03071421030702060f15010305060d0503030a1e020c030403031803120306080f0610060509181003150902012a1208102304050c040b0403 69
    0x202c1c00103102001d003c64082d8000704181000512a22040982c08400c0c0d52030660400088401038062440160030001c0c1a0306e80d5450310b001022404c950350818025500ca046d068003101d10380c0c0c4500000c0d00303c002080315540c0840700d0403415000c0c154403e4220580050024001d418207642640e1000e04680003103d1f41c1c0300c11991078036410348034007201c04600c07408d04440c0c10442c5400400c1500e03944038800c030300019080c080d0040c2d07070410403550808140002c58210b060301d2800400701e0f2005024100328070580e00349104001078000080341c040f6a0500500c060b501c3d0540b480d140140a94240d0000b10009a02281c10360598402c0c0e983e680025105c0c000709645012124110710b03004004083c46a5109100b500e0300341d0660050341c014206a002c81055503607514103045804407408003004010004103101c0c010180d080d0032079004241107009416500c4d01c50012900c420140045400c010751030015014000c6020103603040541c0f100b50007404040f0303214505901d40d84081c40c00c0c0d125074403c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 564138776 1250 564137526 564137579
    0x30f1523070e0a0f03030f110111040905060906030c0f01050906131e0b0a08131505070e0312030610200a02100905030c0103270308010806070302040b07080c07 70
    0x40052030b4000d02c40c41c2d075031204882c80e40c10141400c0c0480c003034038454040103040c0306d407091101414900503c01c03d8201c028020091001400304004a00c1640003446480006410140030980a182020415104440160081c401d80904108020b0144079018503603040c014200300d00b0849459150040c148030960014000b01b80340382031584c15600c41c5003444d030b03001c6500c0d03070b00300748559800e90701161101e4030b851422405907141c3d0b012031041940c440d04014006d42c9101d0500c2d104c0502074000ca807081506482d00c070300d150020020f141c0c54001520f4203507400d08080000440b13500c0d00f50007514101c1c4081c94040403000310800c107211244203e290b840300079480340a802d411840c06000e000c98114041c076100074030070b103000e000c40d41d68096090242c0c14907032034041e00c030144540d42240c0e111a4010b4070040300b0492290501620b03c000a001d54900350195800045003540280212003c0790310507410145415220303201c008541d0001404002c03240a10840020700840f031000328060118186042d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 564140026 1250 564138776 564138781
    0xe1014010e28231206040c06030504030e0d0308180d020709020d0b060f0d050901231801020a09050f030607051b0c10030e0c0a1a0c0c060301060522030f1523 69
    0x400c030840c040ba55004c3c1d101c1d4010703010000000c005860003403c03500340303090126940d00e5528060700d121000c241a160003500401d03110342855403265106004496400a26401304201c0404a0b1a910034401100140e40071400c1001410296801031880041c015030010f40c482c0c1500c0000c100e40d2180c010602100000b03c1c0840425040c0d00c6038035045400000208105a82d195400c84030740c50b9178000c88054150940020a101c40c402140d0a5854803500215954420b000014105803420300855000e241000680c076414140001c0e1640101007a07100c840c200385c601c1c064a055124101c1c03c44101e0f0190040040e0742c4d07112743c9445002c404043d28003188186060a42501e0300710310328402071180642e1142049080810074426a0403141100060382d81c0e5581d0542c546005c0c1100c5100f030f001040000006603c03903110001c1c05884460741c0b0346040d080c0743c1c2641c458283c203c41c080a046080303c2c1d040b0200080c030618100d0508000172002048070001d200d00c1d0580c01da02e55480403005000b0340308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 564141276 1250 564140026 564140029
    0x906091b090e190602070f060c090f08060c07021206010933060f020c15040611030c060a02090d05030d091203061d040c0e1014010e2823 60
    0x909402a00c01800100301514802080c01d555000e06502544001d00b40c4002e03c00780400c85d0111541c0d070390000903007201050185001401030603000c10440009401c110b0102d030901100480c0d4013121420001401c00362207002c582130056204140499000b001002c0c0d8905d0900148401802480e40c0c60300014a06001111604c40344100d000c00041950488090f840c48010384a41c042a5034251426080390101d40310145e142c2441c80340130360350240c1d042c4210703440d202401c0000c4c001d4403102d03600c2680c05402c02d12042d65070b000c2c6443c0039100b5044940001c40d0b544450340580325420300242030081c0410700c0d4903000e08503400110b131000038030b490700c0c601d80500290a4041700c4014035031404110062a0800b0080000700021102080307044a0300410244001d011070900607040d007058000c050304006001c030a20015920030f8800381e580010325070b40d0642c004e03484c0641c3d40701d000d8118035148544209840080451501c000c210090070000841c1848402541d110107030805054150180c01040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 564142526 1250 564141276 564141323
    0x301081b010c1502040906030c170f070e0c0d0c0302030a1116080705100c111006060804020d03210e060a0603020f13110a08060f030c1f03090609 64
    0x300489103020003260301980740d0340118526070321038000c1900c19416051840c207070007920542d800103150b0740c00d110f0084144051000a002110b1883c44000c11010500400c1500c0749800140f4007866040f44104100c4d0f501402c1d0101e03400480c2428062901c0318412580f0225030280c0ca0400009a002c030070408141128401c0a20a143c42c0d0031903400c08580d060f041c1d41da0845004001c2c83c500d00410004200701080192083c03103020880d084c0031000905d0b4000380105423081d00611746101d0b0b11424000c56590744140415100107680c1c18156550f5602440b00e0700d090101d007101041003d250100826240706015803104030b12000c00716240c4150101c90740b510f113003d0401c4002510301241040145d94885c0a060342c003400381c4070051103510a000710310050491403031000c08001c00149500c5d1859000c124503209120496541c00404001c0d02419030302c00d01d004116070000801942141007000f085004803d4803141d1034041507551084e80c1c0c980c01e0b5682400100c82c2c030010f40c3d00880e00103848a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 564143776 1250 564142526 564142543
    0x13c110301060c02090f040b06010c05340b090109170c03010501080303070f08091e0a0b01060e09010902031302010305310302060906040f02010c1122050a090305040e2505030108 78
    0x11801c42c070780d00342600c84418400c0064000ca05004200c10302f61f082141c24400c404001c01e240201008085110700300c20405120741001d040a03401440b008102c1d50203050a1302d102e0b00c4180d42e0700810a040c45100f11180380c10302c290460901ca61030140219a070240102c0c0d001c0d00d2101d018580b41c6c14401c0d0064110f414802400062100e000200601c40000281911004207014480040b0213401800c8a003400141880648498500800810920741018900d0b0840c8801e03136003540142e0b80d51903908103e010554400c40d03071120030940c0b50050340c07180d001b10780c110a1050f4404507540b03801c5034034161521044941102d00c40514181000e00d034041c4403a56002110801412084c6842d40d03a0664000004000a06005607403030480c0c10b02111655540d526034000d0100c140804c2c542020b402034040c108039100106082200141c1030b100507000d8800180e034185c82d00c50420b0300300f12000035400c20041c006414413000c3c201520694004058041c0d16403096210b0aa49504103d01305040080c003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 564145026 1250 564143776 564143791
    0x9040c0f0311070308340c0512030601050306120c060408100c0c051218090916060f120e03090d0f030f02030f1b0c04110c013c110301060c0209 63
    0x81c0582d03c0441d0304001c0d20341c0e202e4407480402c2a0000081260103405a800b000d81c80e030030010320398000c0380030380055400c07120341c0c0104202d0b1410003000280010611040700c1c07050001d401400850b19030b040c414482490507000300282d41010041501096642d041035000e22940e41c800c00514149072601d00c10564000303054507140000400342d0700d942e6550002412101400c2d0300c0050361007440b120000c1211070415004100d0f01031401c04070300996582460b003410105140206c42d000500e14016103500700f100026071980010b1101030300c000300007001c40c0d00c94194280070030030200b9481e54070303030100303c1c0c0d040d21a04140311100154100107218065840c116805c2d5402041204c0312070400300d05a5940d4408001410780142149940905020620820300d42040c103280d0441050704014001c2c01d03c1050781002004460000c5110028a07201c111200003074000d92144043e0b222101450900800590751020900101402926000f41e100f64032240000d0840700d0001e0842ca0040c00c0f86401241 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 564146276 1250 564145026 564145061
    0xa060509011e06030f0308043f0f090b16080d021c060e040209150d0501020301080d080103020a0b0f07080316110105061f11100f0b01091809060209040c0f03 69
    0x1c40e82c0e507580300f0305100c01c05410f01c032030b00000070f0811072005016890a400c0e0527011105c2299024903c245840c80d102c4500918821140e10641503c24180c0e40c920500039503400c98083e203041c04800140d400602401e801d5a04035550300045200e80006068000050000680c0c4401d00c9151349030141c00d400a81c8485400c1810400642c80c14855281d08150121521705241c1c0b204140c101000303a50758082030b004040d0401d25824414103602a40c1281c001505641c58407480e08000c4a030600c003408001d52215242000340149440d000180040290142a40e0300e440159250710441d0307001102c4400409464000c0c1069090703200c4070440c48008400000d101c40c1c2002d4001400080b143c1c11b098040c07030340d0000d402c40300900c02c0c01c1c13101c0488404c0090360b03608000501e010002c2c14441035040025810320780040c050b544104020421a12010403035078209003801c00040141c14002d000350f9178150244600e00c0306d0340d60b0340701e82020312840ba110640070303142544000d410b68000440300100d440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 564147526 1250 564146276 564146279
    0xe0909060a050a14130c06021504081308030f0d0614180c190513080a020d08030714041205071e14040f0606020604050601080102030705040608090a060509011e06 71
    0x30410341040150001040c55a0b03000300c2440140485150343d142c1d183c400050014980390b004000000d140150244a812501c58200780d0340c510b41c0400e1102120203d100180c041038241028003070312500190080002640d8000081c51600f0503050290038010010b0003600c0c2200a225210043c05401c4001d402c500c0c0c0200041c4268440c003030b4214051491100180b9102c2c0c0300001c4810244687c10121004800080018907a0b041500100c0360100f0560b4007042030300000030800346403940184002c240340c50980d2001429013015103850240200021100e0032240c4504c041d2024041201503207038100382a052583c42c03d801d0398043d00c807059000041815806c4520f40c131009480c007800b400005109140d0128004142d981c0d00140307510b103410004505668082070141c01940200e04980ca2a41c03960012400c03440191102400302e04100700400c01c1a004a4106610450303002c103031352146140b5143d043c240c40b000c4540d003141c1c0c0d541300d1003685c034005c240c800c504603800c0030750007003000304d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 564148776 1250 564147526 564147541
    0x2031201081614040e06100518091207030c02221404030f27030804051e0f0d140105090105100902040b1222060504020117090a290907060e09 62
    0x2880c19020300c00fa0680342032070095150f122600a02c0e185541c542c12549940f41072080c1205000060041d94803484a1001c810290364908040741d02030701d08030029100100121404210380e0b031180104070180300b0060030503005661480c0c60182400c05440070700c42e01000e01e90000e411100009641503503100b00e4014880401c1d07210304440d0980607241400341000e10104203018a04c5041c020b00c00b090508500040100820100a0300c200ea2007a5020954035200030420340d240c400c850300054000300d5080018010f842c008121101c071600a00401065240007408542075400484c0c0e600b0b1075039120801c0c488080741c00401000203000701c0d00118142420901049022700c1600c1c503d19883e0010001f09845c2032216410600f448256048010704040f14035008000e0b10040310143d002c91b800460010085503c0409035100d046424041d0444c6132195442e00b201008004032044500c041302010840b07580700303607a441c1c00b0320035070801006443e1034040e00800c07140d0304100440c012080c200910408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 564150026 1250 564148776 564148813
    0x220903090608070c02041a03011d1c080a09020409080d2405030319090f080a02091b030f04051002040303030b030c0a1508091002120609011e0b18030109030203120108 73
    0x715581213074080307101100c4080d2807208a403401f500d107505500c0d01e04150b44414000358804442e013407004c00e07501280912007108900f840070405400104520a0004051800ea1740c0300a50403840108000703074401d03042e1201c1183e0380052900c030081d6540e0701c1106070348001303010742003816210b8462039400c09400e003c04292a40a401150039100012889200344035000700c8510024001111035030307a0003551044015070b00c40f160101640540904800301e180c4484d00b0b8001110941003140c02c17459511481c0c50b01b0008e0764010025150790241a41c0007580308964001800194080d0390f000c184842003c040501b40f600d01745d4014440d40c0941c40c100800440d8a400340010091818a45050360360000c070b032800c01103e608261261440059601100251040c04601941c002c1e500c2144603a25001d00c404209000711000f0a44904100c0070099121407100034088030b01d80341c0b01c030030340c0c004144042030030b65880c00750880140c0c0010918800c10001440c45074014010344008109510610904042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 564151276 1250 564150026 564150047
    0xd05150f100c050a08070818040513110333091b1509040507050408010507090308091905060403030c050622021002011d010e0c041109010e22090309060807 68
    0x14025940b0300041400000c0c4404889241c2003e4029541c0b400ea19000c1030300d5000100054858130344c4907040e44642814411a07100d025040981580201d181d1921420f40245528a540c10b20520f15101d44800841d080181200b800b515490001020150b21003003806005140511503032104a841440c094204501d8101e644141c41d68140c0e1200d580b009441031140350f03c007680140c1402d0910004981c040000d201b1150000000c0000b6110100200c60700d080310321001c0c1400c8030070320140c059440e00d1321a801c121420400d80707070310381340d5100e02140700790f00140e0055020036600b881c1681409424002141e0280c1407180302c2c8882c0100840c02100b81820440184c02000011501e0155074001d50005d02c100711104a40e000c030541a09800b8040e0544440080090041001100d000c1c107250203507072031a48991001c80d06054540004403030000342410555403100300030320301120f503401061645800901800001c0b0b000a440e00f405449180140d20420401c0310000810085035030046404c0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 564152526 1250 564151276 564151309
    0xc010c090510050f03040b071b03020a0212060402180c07020d06020d0612080a030f02091804020f01030903080f1b030f01031a0c090d0602040f080a05010f050c0a0c020607080d05150f 80
    0x10301e248c03035086d0f0444840c0d065002c1c0701003140600c9803038001e15400082c0140458401c4540300c5010543d120b071251200760a071402908112818480b202581c5000e4401d42d02540c00102c490500d2141d0300000d4510b820580d081e6052640010051843c041030b006541c0544151034028442c0c54103595a9225849034858060070950b0f40c7c250f44220102c07580441c3c02042c0c0092440c0c200100303138030070401c841c3c1080d17400300d100d08001c07055000c03035502900411021540548440805079948220300302c5070f4000401035003590007210319000c0211842c02c00307540540d21107212421507604514181440142140e420386410a40100300120f8103045002c8035694a01603800e40402403991400310003074042d07a0400f4070340440c001800300c1d02c4400010298a907e0084000380003662269201208445082d03681980c03c10003009140d0503540a0058100d0706d910140400d49070041a495202d820340100300a01c01d402d0b151024003115021500c4800c620300d0007140c5807010b4074510400950318441504201c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 564153776 1250 564152526 564152543
    0x30f0a05090a090e03120106140d110d050103080408010b0f0a0b070204060b2d04060e0105030924010302180c0315060c070e041a010303021e030c010c090510050f0304 73
    0x1094541c0729042c0160003820b522409022544010103000d440760020b07000c602d1040289800000d1491180c04e00b680b1016958081e10b280c815409070301000741000500402110781c1c10459941c803c05140308050007940200100d03929181041401c0e13095a0400a8152007070101c410035440a81e9071a92141c00c541d49002465650002c0344045805041e499100805800740402e190080e0782c01006007505181a4448448180109204001040c0160b0003030400207450011000303110350040004540007113040d8103c0d1030000005e0b9860a03c1c460300c040d451035104203040104214288900c14490002c98400018400d14144480d50f8040c0001040c40280d00307000540300503030780c54000131906400d40520a40d111551503000440c4c1d40e0300240e07002c48054010390b1401400316010304109050780d5042e4041c05404d00320840741d450080c292007000f8102d0004000c0d681900b082403207a000d81c030f03e0030386401da00d2500e000c0c1003006000c80d00201806002c0100010b40c0f0b0103090340308a030b5100c1c1d4483ca0b403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 564155026 1250 564153776 564153787
    0x1b0809030a032a02010b04062705061306030606061103030912030601050909100e09061e0a0b09041101020f2b0e03060f04050705060702030c10110a030908010e030f0a05 74
    0x26034001c2c43e0019a02d15a0181a0200328041135064014825214060f1024080e940d99030341c0c420a401e0710031030f0030b541880917401190219170702ea80025800c4a0014151030700400154410011692264002c4071082d50300c0d041007043c5504062001032035502000603500b18680a080292103504206914804040001c000386030750303001d802944e0780110044c006880ca454000700e802000d00980c0540b040c01000040066040c1400240e0320b481a108601404020048550701d01c03550140a4500320001c3e031500e40c021059103814600780d20483c025000030140406c400c00190a200214180725450740003103083c0402140002099101103041c100403900489091718112a50710310100c000d541370081809012000c0034144c49240118040c40548003041d0395142005201d106500e8002e4054009113986002c1d86440800500d001e00f081c01c0c0001c0f60308002c07059a0805c02c40b8241100405c0101320240310b80c83e824415101000900341c015450001001480d1502d4041c1241d52810805e00051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 564156276 1250 564155026 564155051
    0x70309140106030503030612010b15030601030b1005190203040531060807080d0504211103120a111203160225090c0201050f0a0c03060b0d1b0809030a03 67
    0x14915890040e10080080a07241d103480350b1654400c0e0340b604d106614030081d000b0190f0b010322a00070001d41c01400b000401c061000020a01d0704010a070606140c2c0d140c40f03c000355100d06210018210f03441e070310550b82d040300303525811201184403030b031a0841d80140720901a64640b552608030748004410240c428501d08081c41c0c1c403144a4a0740d00e03096604002e0002110600061041700ba0348078281a0dd150024140c81128140218481d03d10701e40302c81000100711890080400320a940a510216900740544c4082480e120441c1860700700d0390000195244001e502c1105001400703a01030141c4400d0f111300340d000c11140005080c2c240c0c141840030249079014020444801050840790710404c07031503410985009644041d1040c02c1c0440d003800401e00c00e0740d1041c400c082c45011810303410b01040c0c8807120100c0003041004044020305540d80400324102c0ca10704003600101c0b0300300d0310200d40c1c0c52090210f03120071202d0003641410b219809080c0f003a006000b00c1a6511155603240c00543d1810200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 564157526 1250 564156276 564156293
    0x30207052a1807080a0209060c0a032105010305070303030b180c03040303051e0414070902040308070507080712030f350105270717130512030609070309 67
    0x940d4031601038074504900110000511a1044020102c4580d2038141800148094042003254040001444c02c00020840400ba07405400c503c800039003818184426001a6890450600d1054011410300a41070301e400f89074000480e00f00350303401010f0002e945169550740d0380300f2036400700130145030702d8186484a81e142d001104850510600b003194007401c0000d4201e82e0ad900c1a80e003600041d043c03100045021200d401d11101e03603c00422500c3e81d60340c464459407680c6a038215204d01d0307806114000120691b090010f4005140281c0d40302c8c0c0d03100e01c90700d052450103209074004222034006e4082040503408203045a20700c5605800c200010280c00007089681e40702d40e04408000e1040310070660307201c0e480407960500e0320381c19840c403036100e0f41c036801001807402d03a0071004043c0e001c05021146038114940d5203560004042d0515407802c040d1610701c05c0a039441164080100c550042ca02c0b004d0000c104004044001131010340740c511b00704500032030700c4040001d00603024507440b0702c80700c420441c407003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 564158776 1250 564157526 564157543
    0x1060f081b1309020c010506040c080708070207150206191814030f040909200303040303120e030c0a03031a09010b091302030a150503030910230d060504180507050103020705 76
    0xb00c40d2402c0c0c0c40d0b010b140001d4011045004143d80b03030000280e13030782c1414407031251080c3c0503441c4e04040f695581d40c100d4808000802c07002c11400380c048005040d890482c4034004810380ca8014000901c1c0100301201c03450f80c00c84810502d541401c010600001d5001e01442c200fa40201812181c0f140300c2250514510580008912110f00003900244134031450b413048450601c142032900a0780700007000c2c1521624140722055241c2c108000400c0064056000b207452410000030104508011002c414215080b001d540899a000801d0240400da898815202110860880100c2c080c28501c042408414140503144000c0c0002070410120350310007421001600f07003140155600e1618080d1107001c0c00105d901203902da001d02d0404105440c000c8165000041c0c06030001c40d5030031111000f252080c0010310041d100040d0102170f03c0d0100c00981c001e0400d0241d9541c081540340c80c1505010485e00100c155590552240c0364540c0000d10202d48442110000d181c0987c17100c03040d050090034005034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 564160026 1250 564158776 564158797
    0x60b0a080717190b0a23030115060e120f06010501050705010f06060e120705030a0b13170a090b3105191401110307030305040c0305010f1401060f081b 66
    0x1c050801001c07440f061842d030754141c0e0850084c000014800180528030345a030251004a00c0350807101010700d00500e00003043e1480080010031510b0b40b44c01d04000b42c0c1d08139003080000445c1148520801c1c180721603800109858a002001d143c035650083c507031150018042c0d14100b290010f004018040250403a03680d450b5241001c100d542e55a100203042c10010200701800341414119a00e8420004100d00e0100e078070190181081c1101c6070785402c202e400003050380402d0441c5226036408210780c0302c408418078000d800165540c9064810150202da2030340c0c801c212141c0c08004612030540c0240402d1008503412030245403400c1c012185165142840c3c00054014401038440b0104901d00b90808085176101c056285820150200440351482c0065400d42160b00811120001034800d51019a2042c0125a2440442d40703a0b5102d901395001c0c000018102500c40b0140140240c6290030b060042c0300345d08050950113000c0d00080c0002c2d01c0103080c620300300c0703841071340d6050f500e8030746c080310a420003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 564161276 1250 564160026 564160067
    0xc0309050907031d0601090c0f0e061b03030c0901020c090105060a0c030923040b0402030c03041b0e190e0d210204050d030f02060a020f04030b0a0908270301060b0a0807 74
    0x828444d95580003d1250005860074010306506817030140e140400d518201d036075040b50b48031287c01417017129481140c1d44140e00c1421030404c8100d41042c070255018808c1c18000d0369951014030002403909101c2003400f407003807030391400411141d41c510b011545000c8643c240003411012a00b820703030781402603a10030702c01040102406c0c3d0354254104440b089a100071039082008080e02020311040340070440c1c08294000c01080801c02041d4810841410305007044020800070307441d05a208d003180d6003a100b01602c1c0300095207a402120340380c0122078480090b24028003e060600da4002c154001511103130340c41542511030a8011f000c44e404490140402034403401d40e41415140052501078034182100c014040c41e8042400e0341e9060003255042603801480508003401e54851050743c000250000d01c00a81d41c10b41c0d83c000551038405080b0503040030612200c808007102440100842e80b04045219900d03021007400400400700584440c1619807a2030381d40d41c3da94640a80d00c041003120340401c4d4a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 564162526 1250 564161276 564161321
    0x20d0c0b040302150f0a18051c05010c02010504021f03140c0720030a1101030b120d1d0a03060510080a120e190302091b0313050105070c030905090703 66
    0x2210340208202c901c2a201d40c01d903104501004a070724060000c0d17000b08241c0030401d114040d481031440e80d05412011940703001e040e17501c5002840d0190340c3c101c0c6801c5c82030061010000c1c03150a1085550003400303030000380460324143d4000342c0c03420000540e180204401d500744010151003036201608000c0b03003d41e40300c1c030350a020300002140d030003460040310050ba00390102c9200000781039840d2010f103400380040c400c2c55055500c20700d5002c80780c1c02d044e04040e070303d190100d40c6075107980007180c1880c5504042c107044000c0190003040c500c1060081c001d45003a40980c0c00342500c0300d40512040b42d400c20b400040c5078032002e000413800074050380210300c5881203150360400d02480e0050707404048590303215034410036403c1c024000644140c14100401d08040c08003007026040404a4541c480040c0f14a11139003010455880000e41064820603103000c82a6420340800000748520b581180090800913448021581c00405090701802203900031030341c44002c42c0c001030081e04401c07845101c11034598030b00c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 564163776 1250 564162526 564162539
    0x330f0e04270b061c03020a0204110f071b0506090f121e250305030a120b03030c01020d06050103111c0f06083d0207080708030106080114031c0c020d0c 66
    0x30102540c0061142004500300381310110300460041d00540d051300a00582e20003502000300034010500344a801c1101080700c0e00c801c080d01001400a035106466030040c4003098152a0103a481c142c0217140100f1080100304155902c481c40041003040c110b81c0f036018108072403245400c05120199050060009003030f070300007622012682c4608242d81c5000c0b500308140c1e44265107142d2909200180c80d0740c00801115480b14400c403046002064001008101880e903200480d1859000e049544043d9502080c000c2243e9554045d00004142c05d190074450558250203500241c03140000080008411461090403406950841d04644040140c104120b0340d170703407159585039008044680b21603102048020418101d5650003450b50610f91405003000e181403804c080258040c840a440d0380d0004d100300300001d1a0320b4001c5010780380d1690b40410300c0d494242d03403000036407101c11141d1082d006904c115140326034100b10001041090310b8454031411090020904a180310b000180c968500400c01082c0c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 564165026 1250 564163776 564163793
    0xc14090d060504140d02030702060d0222090207110a0f060c051f05040201020f01110a0e060d020705010213090e100504140f1e03092404330f0e0427 65
    0x713900c8480305451003e659124201d8982c4250080294031180c00d02804c920701e100d07a406440c6603000d4088a0080e0100351308081c840180310b610850b20340d5000505901004121b00300455407007401d940304000d850034820312503101c03002d40c0124800c0140403150441809010000f00c00813800e2121204100ca0320350450034080c1a0454050340903220303450002c1c40600051092410700750071100c03801d041032181c0c20111844020304800c198404014003000115502c988014a00b01780726100044c2d545c0c000c000c1c10b140d42c2801380e07c84c00c1080c0c64602c106845200108481d04441200040000c0554171450f19400b410601d00c103c201621403201f019000010000b0541c0c4da84500d58016074084c194030104070390ba88601d10760303e034021458040c2680001022048010313580d50305298103003859250072858640b411003003801748141120308103000031200740b02c00f4000603011918000d0030700b850221024010503140002035004994803d140340318158010b8200250400d4003004503e40c0441d820465036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 564166276 1250 564165026 564165053
    0x709020a090b0a0e0f0d0201120c02011d01050403030e0a0803010b0d1b021f0605030a0f03030920091003050d0809010615050d0e0102091c0201022409010501090c14090d060504 77
    0x1403400c41000c01c801b071030010050700e4000da0507035070301000031880c460000c0500004007295043d5903d43c6445a00e00c0d20980300e0a601c138444900028103883c10742002802d642951450f8040c50300a0142e00e00400d140604072815a80150803455454032550503c0f07001303228041074956a6203040018648180e0302080ca101c040308410354000312040c0110b021801c0b10010703c901c56141e0b09c51010040043c0d41e50f1075103418540a8140010744400d1905c840840d418039680c01c1400c0751004440c01d00c0780c03406003111600140d458540d1000981581d0350903588020b480c0003034041c0102c090000b040381e1401d4202070003500c40000d080044600081c0c018080d41c11880c11985441d0411144003c0b142e014401d4583c0c018000f850144010082208026044a1038909030704500640000c4a240d1280110541030f001400d150301d8002e103806030340c280c21520f06800101202c1d0400b00512031140d40b10070000d84241c1e0143e030b415a511180030000d24109515100148064109410032044c030110340089107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 564167526 1250 564166276 564166279
    0xf1107030b07030e0c06040807050913290708150d170c030d23010506071109010612050901061a130f08010506011107030804120807020307091b09080709020a090b0a0e 73
    0x12a40102c0340c040101d58051030088823416440044100100c6c9030032450320790000c00f103203484a690800b0342c403a1103000c51207020440c1c200d4000d80d1000c0308a140080d10680c0a0104d190910403828996103000c110000855414415030303240f13560b80184801d00e503803a10a01540f10b0500c0d603805000c000c05071250003500301e5840c5c0c00d24140b1501d41403c8501c801c142400384000b0f0107003007a8241f008100d125008a102690203851249685042d5250003000c28040d0920b03841d10000c1c10b000102c42000d5400003800300300c107a41031400400554000501e6007840780c2e0310500e4191502c0c0031401c00c0264500c4c540c40404c411001c0d0100159079207065001c00d01030502a69180307191104020081e584c0c40052000400002081004214031445d01043d8114030380b081c80018038005030360300081c0c0b0340344240d00003610035559a5408240d070b50488442501052607800e114070400d19005170303e03440320b005102c0c0c1007a807900028a946c0349031050000d44c02400280e07403201d444050300f01c401032252500c0011035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 564168776 1250 564167526 564167533
    0x20f01060b092110060906030b0c070c0302040506040b061803070b0a020c0405190f0b0406080a020906090402010513080f06220f261207080103030f1107030b07030e 72
    0x200d160500242201c1028a0141c2024483e2102c1c6204454802011550841c10b00a000040d40303042e2450051000405034050046146402c508104140c008041d041190b002410000b013400120a0300950b42180e8044030001507660b13902001c00c0260507040c0b0361550081000481254484094003501611207007a822503002640751601c1c0e40d0746100314070b120809644100380f2820945816003106d94820700c034400c0e0355070000002036034109403401d0140030134006450748a011303d1400c141c810900100a407000505000c041500030400c0200b020705150f0080b000d0900140030359000320100c4042c030000c0c0c001035007a03541c0c0d82890350321012242920003140c01900c011034511406655004542c80c0c0280c0481840c84003a84c6801c0c0c002100c0c03000311188921000351002046000140f0400f45c00e5449900385e503619101030f405c081c1c0300014115400c0c03191240060001c25030009041250918509200b140c816010800078681540c5500c0100040c080d1810001040d500d500585000040107044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 564170026 1250 564168776 564168779
    0x606080702031608070f03051902032712190303180b060d06060305010606120f05010303050412330507080f06060d14040305190203030c3403020f0106 66
    0x2152140400e03a404001a4800d121002a80f101c040740e034003040b031107502c0142c50040d03e99559444003000400603408154041590441818004c038801d10f844004e10155207049800e04102c0070b1116034021105403c50803a201ca81c0c6a107030700b500e5605104080b800c5400c0601d50780c03100e40c4101102c44c0110700003801c0251300c0d5610214129651030007548503c00c8a1a03645040c20300c4804a4520420b40f0101d89412000010503403c3c490312001c0c0c5081c1e07a5a0851a42c640421001d84012910404030b40c1d140000400110b5402800d80e8140c0f541040c0903503010502d4101003282c820320824000724814100d40c048110f0000c3c044a42c0d0500340715030240300c0c40d0348080043d121a4412900e01320301e403800d00700140031407610b00c000b000d941114a034002800c035114510005020000c4604801260000907101c8803030f040761020914148040c0300071840c502c2d11075445002d6000718007404425150504408600300046070725143c41c0c5000c040c50100307500300d90070020350300c60410071944059480d2840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 564171276 1250 564170026 564170039
    0x70512041a040806010b0708070b01090507110703150c0c0b0705040311030609060c09010207170709110307020a0f0c120605061c0f0b150619080c16060b130f020304050106 75
    0xb03460840c0c1009001c3d007a66846d040c003903241c50388401800c4541200c100241c10005a00c03054480c080e0014450002d90392510703150182c070746203040c0308200c0d10741d1040d900bc10010748482e4500c074411510200103e403035030703c0c0501680c441055240007010803548108101c2643e5015001e002228050f80f116070300000e6074000e054581d0307020784804550f600101d00189001c2c5085004040044040c8100d0f80d813a0f03643c01c0340a10619142c41c1c00d000d160844000ac1124012074004d02c0000c0420b200170b0781c0365007001600a90340e8070304010001d1800300c15201e088113100800d85040c1c001c2c00c202d190000044140e251183c002c29003280c1c041d1254812260f029203c2d041050403007403159000c000350341a00100e49404034400401031603031040d40c04071031074a5041d0b21030401810000f2540c1c0495100610091405041d1402c018804010310100703104e124a18038008900d000050742019000824030203181c041080b1044505801a009080428151020701036a0085104a0140c0000c2050581381d070b8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 564172526 1250 564171276 564171329
    0x30f03051603051215060703080705160b061503060d0f020102070306050a0e0106060203040506160204020409060618050f0a0b03070e090112050c040b0a051302041206022512110307051204 82
    0x86825801006c00d01c05500000d00a0944981100f0241402800c0810741242403454420704c1108032081030380c40e014800c481c24004d66850b104400600460704510340540445c0710824894809421907c091a1502c2076900a0104001454120106101514242492001504014141d0390480d03180c1070780003848a00c00310503034064a1004148620700801502d41c0780038403269042c00da9006508102c00070381110b092040c00c004056030b0316030840072940ca0422082540095000501650306161581f8540d0b64a55100060341c0348003d070b403911707504c030084200c603450030101441c0d4000f940540081049550201404120780c4900125840d1444080a200070b2700c0d120202e064000f43d0801c41070202d880c0c00781c01066075400407080103061540d07600c001011001e4442050310810b174009841c048052522040c88003034a1000c100d0817240b90ba941c0c82d8442003109107030307031070821041d02041d046e5802c05104944056404c00225021400e041403810820f50042c07140c0400000c0c40051f5412004584 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 564173776 1250 564172526 564172561
    0x60903170702060a022b0504020a09090c062001051915051c050f030d0204150e01020c0103020a03060f090203090d020f0d0f090905040c0302010e0613030f030516030512 74
    0x264040d03c259101c22801e0406034018402400e4400d80c81e00c4e880290704014103c1480d00c0d248401e012400b42843d0050201e442450b4003d20381082c200b140001c00b140009c80e0100c1214404d2404c007418030300800e40624050207480c207010280d4207060510030708880281d040c4081b45503600c010440003020201001e0815940c3c85480d401800e003030400801600c80c400c0e0350858034003c10603182c2d60036107058000d007982d00507951038003520ba000c1010f0141d5003204070080c2404209080100d000c0003c00b002079502c0060f940c60b2030405800051542125110790484e07801884030043d00c00c091919040c507030340690001c075286550b910a4507080d100d95480010210794010215014181a006684045030141c60908440090010410000030100150f114162140707024150507601c113070541c0300042c01e0f40400c039600d41c4148410f201a0900004031034211b002ca951045c1c0039401007c003464251003a0259003000390b00d98090f90107040c1859004001400d21410036851103280307540d18481465120b440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 564175026 1250 564173776 564173791
    0xe010e01050412080906130602010603120305040f142802090a0c0504030b090304121110090b04181b080a23010905060a18021e070f0308070c05070306090317 69
    0x402083c2011452000060450f8000a0107261038907015403c4608442d0703480c0d1103807005039513a01c410000d000c80001078000700151450144940e08194550310a80c10b070300000580681e0001c480000d044c0c40c10004c0384031001c001c08a646240f012070750b905400c1108081d043c0c3c05aa070a000141d400e0380c0d50b02c40c0f240e40c3c0350f40c2c1c5c403568141801c685817001002070040c0007040034801044046030080300d05e4502c9158a100752400880912201d00b44402c86c410580c2650901131304001c2403084180150a9406894207028420103146106d003030300020b803043c22136294a8111214040003683c2e130000041c0d115145c44801404901980801e224000c9006da540e80d0020760108014402c0b03403099040550002801000b0140740d9490f0b14400c010204c5c142c0c414450541d0014540e14dc445d1901c0c0e10000605102699074101305481d1101100c00c07004500c010b04010704400003450950098846040c881d4010703086070100c0713859240043c0200401700782613011480b684c00c0740761145e03483c440c01d0b8828102e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 564176276 1250 564175026 564175049
    0x8060f031c180803040b070507030b0103080a02011b020303070c02010203090913170702100c020301090c06031d010203041223030118050f13031b0f0501020a0e0a06050901080a1b0e010e010504 84
    0x6e440b04d05030183c5c125400840304c601440800001080c04200c13a207018502654915503201c0701e8150190844184c4001c00807590b050f6401c11403501c1e00401500d50110042c2081001504181300407815407044c4801c03076920850340c030103001c00c03440c0010550555034441c504400281040081c2c403041c40c014028029885199408112070302440703002d044205910140c0040380850f80d41d96001c0e041b412542040700080c3c1c4e0f07021502440d002c4041d0b484c00d1756030140d00851450074a0388079070703081d01002d0a000060201c082211540d0341450101e440601129014003034881d40c40d25015201c014003018100411814200414850711400d04100e00035019080c842542c00c900c0d0b64185e40e402c070800007148461f210110042c002c41d202841e00c400480c450400103a81e8034982d1405071020592003c1070340582c840c44824004190000d0881d40c810000342006003960b514581a1400341216072a0050b0304208600569401504150b07031102c154800d0300c0300101078024100440b03d5000f5413181120395013 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 564177526 1250 564176276 564176279
    0xd060b0c0303130c091802030c0d0317070e21010b0915040917071a01060807080c030622020d051803040302040f140f070206130305030708060f031c18080304 69
    0x1003400103812941c42c400d00481c0891662061321801b00e410036104040c60044046000b800c624040c0318141d44c03030030103d8001e110302403180ca0050440ba00f942c569800015100046031449005001000800030006c14403089030744001324410210107000c05240d07040d82054401a46440c1003410b99108040340412920754030540c01c1040040e100d05903003580c0e50038004914407681c42c8580002c1040c1e074040c2d208882c185900c1c002c0300801100580c041010400c0000c00d021141e03a000c14080c2e0803120200304c264403a2160400604000f13400009648646c02c0c104804040603c01e4000d441803905c0480c0412041e516103480c5d101240c00146080942e0708201300510051074140d1080e80d200d80c1650300098549044106ca60b1541e00943d286461040130208200e481a030400002d9800310301c0480c4074860711501c0c3d03809013141c080a842e6105000040002400a0b00c0701552440c00282c007c0c121024400e02200c003011000300e42e03c1e201e00003840840c901d1004400d6110803011100780500451405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 564178776 1250 564177526 564177541
    0x7060e120307031505041104050909010c0c0b070e030604030c05010e0a0314220e01051002010c08010510051306031512050309040915050408190305060907180b0d020d060b0c0303 78
    0x18280d2503401413003401c4002010407243c55510030941c007a10b032080c0c01681c40342890304019402c10010314076242d50381098800c051240d170000b0015095030380140c001c000f540340c4060544c0c1401200b6038072901481000200700901d580585c0c104100f42c0564020040354140c171040d50348418003c0405804551035032018a0074080c01c01c0100003110400d40007107039084092810100e800c0301ea40c083c4014826442c010b0015140001c06441001c920340020044007400600150000c8014401c3d113100d81000c405803075509010f9012070f50050208038007403151545603040a0004d0400c00714104983d01d103c107000c00c007a460005c032246140d0f0410001c500b001c80550401010b4140c0c020102c07161000d4501100184865000e40c901891017600031030389540100040312800006010042c0403d810541400625260900c081da00080c0501d040c1c0380a26040c03154a14000d81940315119000000668848007042680036000a14800c10b05000055403810030750034900031807000369240d410400200322403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 564180026 1250 564178776 564178781
    0x18170a08130b012612070203010b030a0b010e07050c03030711060601090e1504090222051b120a0209060706060f05010903080f07060b1309020103060f0f030f0204020d0c020307060e12030703 83
    0x1032422951144044504c16440e00d414503001021501403420085626001c40c542130080320441441900101103508080c3c40d192840ca00600c62200328031843c0c1e0100c0c1110348100210345140d02ca41c02101d5480c201a0001052060400e2000080740901c0303003c1411580f017042074804a40f0141e2929401e40c40c2c5038005425200b40100382a0b206550750215030050700c0d0414402e400440c294022413441ca038980e0094260f80c002000100c40b2665102000c59a0640c00c050790b0340032010103601c01d515074682c51310400903c04c0b03503403055002c007002c100303001082441e4010105850391b1307152103240640d0716030054864071700b9404010b0040f42e0a103c095810b0401d607001c0c190240c007861010803564881408901c0c0b01b0000003054601c9511800c8003029942c060003410b000782220300301410b10b2840c101070080505964080103040c00012031000040d9990368044d600300c000c451000300840148648040d680c2d501508085610504224041d0900d81000c10058118150038400d24510f944043c0704500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 564181276 1250 564180026 564180059
    0x706020c010e0f1e06041a040501090b011715070c0b3625050103150b0f040828020105071a090102091813030318170a08130b01 56
    0x805640c1d03210b080d10340820410085802c441c100340540320b680c08010440600c000b90f2426400103501000070300c400984a0342000c0d0020400b41c40410f034688070361504902512280300040d10740c401c254000304181054041d0704003124048400c403500d100d05048841c15080d4202c508034042080e4500840c00310b80781102056200000d051044058205030003040388800840810103c4180483c0d50503260440401660041e2501707040c4020300920704148583c2c1d40b18881c003a142c100360300c52408813803640315943c400c000303010780d0040b079515601c5ca50748010458200f482030306002c0c400e58170341014034180601201d814040101840045030041e400565166200600444003080a0b1141180c85a01c0090690043c40d441c80056650003948017000303401c401e40846180100503c8043c0415842d40e05040c02c031302d903814100821000c407a5107000c1c004048000c0082c060001d641340485502e560403004010852490712240340549481080040c00240b6120013400c40100d42c00600c180c8440221440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 564182526 1250 564181276 564181297
    0x6180b0a11150105040e0a020a1403071d0f0c070b01121a0403080708060118050d02030106150302030a0f0b010e0f031e0c0a0614030a0e031608030f010b040b070602 72
    0x1a03048407844603980703010002d1403501a003106410050001c1d2a00d030182000c0c15203440010b0503409640c2e0002400a20144a07080c00c2d1102c5600552390303500c01b403100038002c0201c3d003015410803282ca203000000c00070403900401110b039000b0019040c0450f071070640c1d030000e03004a50001540e003803c1c41e462003810b07104001e4507921646190100860540038007184114070030b9461b5586800c240c035000e032a00c0c1c1e000c0c00c05d906001d00d10804000c004050f4000c50101d81c001ca0f40d1400290480c00400e0041c409034003c5040071244030181050960541c0045006020481d0100051919000d80504403200c0c40b640c5800180203441c0c4c0d02003850451034084071540e004007079503180e2140c078084ea0503007060f481c51041960420382d490081c0340b8180c4140f0703004010750f042008410704c848064030760a210040075034610640c0c50000200040040051350302c054a0814100862482410501ca147d0400c035195224500404000b051552080068500301c0c0e80200c80300b414800b46650f80c00c065040711440b031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 564183776 1250 564182526 564182537
    0x3371505060f070f0201031e0903120209030a20030111040608130b041101110313031a07020a0b090307052a01030e12070510020d2a20010209090109020a030606180b0a 73
    0x403002010034040c8e00850022034500021200c12070b140c0580b14444904141c4003003841480711001c941c43c00b0907a180100d030700040e0120203100c1c124a00c0c4040d1070078039210307416600e0705002d14010524103004000755480340d21142d881c2d07038130409e0288402c01540c41c020136400c401004140022180010040c3d9400c05042c200c0e2640d2482607600d01c0e68102d200500d014950b0000c0400c00e02c103442c41f000361814044442c08515181241700690348488034940104944212000681001c800b407040c1c1d02031a5000c026250b928030490155841516180d0000c1d8009040c205440300d41d600038400c002d00014564042c100741586003405940980100301e041e134003800ba02f10740c03124628940c0300525134502c0e00d080008204400c80c58000343d25800814844801000c41030540865400036480342001c1e0b0345800a6038880540e0f41300901a015a014082d00603021200102d0142c03059000b4103181e114035a000c1040759a640012580512040188042244001c805000f01580c400050400a42d9820715 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 564185026 1250 564183776 564183791
    0x11106042f04090804090b0916050306011107030b2502070b0c010f02030f10080a1505072007150e01091a09090c091302040b03371505060f070f020103 66
    0x105080c1c4002103c00c94100c070380001c00713000740b03170340340c81292101202076907a0840313464041558419240003002800c103020011000502907813288000c1c500c0f15001e1000e903003099039a45040014000165a8900d101c03400213400749000d4805280d90701540c41030b0380207244003031604203004116880120691442c1d504e4800d2079801e210070380029401514030030411001845e01c1c000304811000290042249500800b10990128503140302e81c00c0d00c51076405000856403030b40041075441c40c4808a609001c1640003d900c15030b803c001c50850100d031080400b00c42041101501110b074400d02c1390440e404950003140600183c01980406c0b83d1b0700e0340e47e200e00d91602484800084460b6021075000281c5880003c4060b5a4102020030103c407201c01c0c50305506150500717841e04214040240107542c5a5204184502400c1d48415a0b2041d045c500c034250b0549002002c02c0e1028284200d80707401a083d0018001800d410420308503546440085141c0e403c20b0b0340d03540c0300601300080c96800d030304064407207a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 564186276 1250 564185026 564185029
    0x6040f140301150f06031a0d080a02120328021e03010305010b0316030b13060f0209012003040e0910051302040c02071412010603120806011106042f 65
    0x5164058000e58880c008a10824010503003518804410398055015202040000c40581c2d0b10120989003d4200841c010740c22080c81da0422001000c800d0b846103010b11000d082c07052080040c442c104882c0d0070b4906840a65451140510081c0c80014121000400c10304012403e010041040f420300c03d00035160104140410070040e107411a000905038000004000b00582440b652900030820340151a4048c0554401c000c003103030318071002c3c0c40032502c00c002900a015400e100148640d00c80e504004501000d02c02e140250000c2d003419000c5a886216032508121901e0040c403c44100002145001c4c2890800344090320098a598541c0c45070442d010702a0301140030309807107a40c0e005c201e440f40700c105004000640da03c041112003550000c84c001d03c801d5110008180c403a200507140043d500000000c41c90040086600242c0580e10100c04005040c0c2d010710b480c0e01402090345c51403250b4a001e6400da0f101c46081d01d00a052001241041d100b8080d810b1034030b844c002d4500010b1145410150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 564187526 1250 564186276 564186299
    0x9040f0b04022208070f170a0611180607080d09080c0d021501060806030606011b06020f041514190c021c0b0a0c0212030603071a090f010c050307020108060604 70
    0xc03128110214031007140f41d0b100402c200b0000050100e480140081890080c900070225154060746840c0c407204044a24508405c01941c1981580080d0030451500d21100011540d084200004c22103020003842c045649007c000740c030b6400da005400340e858542d10001030b000030b100c40b00c012244402d040c80804116001400780d80d940e101590090404c1d0006803400c1c8824031016004041071040305400d025160b240002c1145d8042c0f0203091070400360110075010307481c44c00380c4100140524000541c1140c0510800060b004841d8115040f01c071a545102058450f00300c0265040b208000601041c0c010034800100542c011105003040c50100f8250b4022500000148fd03041c00c0c0124072052840030004074083c255130100b205e14040040400c0081c009460703404802500c4038201011001c40d0096130180043c800504444800703084807003064102685941203a07584a1040e03c10000200c16540a4040c0710a960707440009145800c003e41d005581e07041c40541403e405c04003d11022581c503c008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 564188776 1250 564187526 564187537
    0x280308040e04050c18040f03090b0406020304051e06071b030f0302161406091e0901080a050c01020318100309060c030e1c2a020409120806010e030309040f0b0402 71
    0x341d03940c10481c0b425040c11441c0a071134140c124040c03144003210404c01c4610f0740c00c2035000780c0d200b000171034003000d681021541c2c01c0c419000b00090010001d03000071440c0d00080100300311882511243c41d50071120001348810054101c0081e04807074100100c00c00580c0b5140c2620304808107a4a060701c1ca80c0780d4661406588642c4000ca015a220b1700321281100c0c190304880d4010119089210702c89140c80c2c001c54114002c09144900903650115480603244d0684908402c4000c0580101880e41c0d49400c4140d0b146506141a182801052040032407548040211504429940e90310200103034800c0078090f0303029119101d00d003090b980b9040c00700000c4460041103008000e6541c00b0440154400080c0d003800702c070520500385d12500540014007140c004412200c004400722090094001c06a002d1f0207210743d0342c400039485071501901500300300801c01464410281030f038400300169a540c0040d41c07480145c041144e03041c1d100b40041c514618180e001240084a000d00110341c1c5d440070700218090b80c112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 564190026 1250 564188776 564188789
    0x120a0207060506030d1e05041a032d010b0c15150a0b120705090a030516090b10090b09030717100b0108070815060403151d030928030804 60
    0x140c00d20500407a4041c06412200480180401007503220303001d06170224500d5141a001210351201500314007510907140204045446490840210030249010744d004881c99680203c1d42c5c00c0c02641e010301c100d002d0050100b500c01c04099a42400d814201a4100c45e124a149201d4803000d0a00e040c0ca4000c21401060800c050180c0c00f54801e040243e800b00ca070b004060b07144c03414002c0e4011030381c800403203035000016820408c0c1c4d034080c0200414082d8210b0b4001925901c41c0207504090120142e160404640c504d02040141d03050035010003180c05401c911640000302d4000b010b0009441c09001810110401000c0783d06446c1d865650f128904840a1103903040d0b0000b410b2403c00355401d0180820b0580b00b441c0440c100c1c034104101a0804030050070140901a1040ea08441034031600d040b200550b4000c05055510002090010080c0401146000b4860301141100c6003128000050703035510030000b0070114000c020034400240c500034400c00368908403504200080400ca00703000500141c00c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 564191276 1250 564190026 564190031
    0x23270f07030201091a0706020304060603050f0313050906030a03140d1e0c08071205040302030f03090102030a060807150e030c10170124050306012c150c030a050d02120a 74
    0xc0d40c0005010322109038810801007450b06001c20301701c2d14070021200d0303865000000507200d480d181002c4004119a13003009000d0700c201d01e25005070b02c0002001d0111242003402414015480b20103001e0004401d480540c0c16030300004c01c800010b409110403c1070020390741205400c00c03003200844000d0703c81d500c00700308076503110200a01c07001040740600004803d40c0d0400b080142040381d4001c15a40810101400407a5074002041c201842401210304101110000310340b40d0a264504600030340c815905000c1d140d103040b400080d08000883c010088800e50301d0b800348040c480e00f0b4140c54004800b02c14542c18001e0304001d403041d680b284403c080410040c0d132080c1c2e5444140f00580d8090b941031700010503504071030405520a070440328482c000781d88145002c6460b521034a005035000c01200c845c21151307a110303032000302500100640694141004503501c03000242000404002d501c103140701d001d900d800030007012241ca809440141115048644018904036007068107070140c030030030344941c1c04654 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 564192526 1250 564191276 564191279
    0x703150f0908091e0907171b03040210030e0d050c0609070506090112060317040e0c0f0412030302070b04060203061314010302190801060b31030b0c0f070f030323270f07 74
    0x510410b69000394003000d10100d08c81d02d401c070711480f8040280020b1150186106500c400d40c4260051840c43d81a082210805215440d0140040e00a6620070300107209400005c0d5103c400010b0305d20880301c024150a01d400c20340f4004550403036069a170f85144036114500040000d03542802c100c0b0b21408844416100c80c10580980700082020704841c400d0381c0c0c00c0c4031882c103a002140440b030403180991b248070a8405603141c198041c0c021084003810010840c400c000138484542c004500c1960f040f9a1420026154480241110384d50840c0c03d01e094a0800140014140050007403094801921140d200b00e503500006030075600d00d50824854000007040400d46103064440c0e660340840006194403203002c00e81076031620a010b62001405440640b40401d241120758002c46445150022a4960322400f13810810a4201915400c80019280810201a9861484920f40051900300740301c44c0545540101000220070080d108048000000300303000c005408106000048041001504095 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 564193776 1250 564192526 564192557
    0x3071202030d080c2d0307110606010914040f0230180a0b0c0c030a0203130b071e0201020c130b010e03010c051b0f0703150f0908091e0907 61
    0x49011030b080e5040c042400240040446140161031459084044070080c03108804070101c41c601c24070071a41300024000007030050381640301d40c0c03040e02c1074a590b08032a02520340e030303004480100f92403280d04401ea03d401020310942c6002d800c55240b5440e404009418509801281150302c0888003180c1164540441c41184110320265040d5000c980310b845689001d48544a6540714a01000014251007a8000203281c0080140c29038441100346000c80307459500015010355658010341c0199011200880001180900b020884500300c0c1d111001410b030103401d10007803c0c00e501c3e41e10120705501509454060907103820001664503105920080b54101c0520300261006035940082e6000b6414000030700b40e42904101102c2208500784141c0c0301d042100d10000b810401d502803000903c0c040c03034800100744003004080702640300480e00108500180f10040004031403000383e0060444409004400103417030038407070000c4802800f04842039103541003000124862411100c0b8804200300c1c4003030740c0030b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 564195026 1250 564193776 564193783
    0x70b07111008011409161b0c0602100e0f0d080702010b061c0f1a0f0a051314070c05070911070203010e0106180506090133021e0607080f150307120203 66
    0x60940d554071850a01c0c180103046c40600b600481d0500c015410004944010b030101c03203070344580180243d10f089464031402034a511078043c64109450900c0c0030900000c40108083c6c0d04034a4180081072202c801e01410307038801400410302401c0d55030310b0288503010f80303400c0d0041c03205407200c0103509600c651038003500080303490407080070040c1483c00104d4040785980d0342c042c41e1000e1007141c14401c68001c000016003d080a604019040700c0401c40d9800c49019070b421152486501c41210b0100f50307254a0b0480c0c0840d03003040058403aa10150040108810310b03031102280c19640c0480501d46032040c1c02107800d4446900501c080c0703a540c1e1904100c0300080301c240a48618020b0400d00c102c0c140000000c40c20f2038180500c2c00b01003a0901d0801c507a51500d85d082d54119101810001011001000079444401200c1d049512803c0d2044100504101142aa205082680b2505803a40790180c40d20360312400108005001203d001510b0500e42d01003100d40000e089810a400c150551481851308 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 564196276 1250 564195026 564195059
    0x5010209120102070f080f0405060c0601061427011b0308150a05061801020c0a06020703020a0909031d1201020d0204050a08010504051902190311040e0609070b0711100801 75
    0x550340f042c41801d000900500e502c070b0a040c0c1100000d5110354000f02048841c0c0304641c415540500c000034081c0941030045600f5040300c1c1c050321003004803076030f40703d4440aa1190ba04085401e42d06280c4642e040c01c0c0140c042843c216041c5441442c0c0f100004c1e8500f00900407103015004034410300d013040300c00f40140302c0940400d1403e03074119010b140790001164050041c10340034212480380d80601c0080b0b0340b08100103e82c00d080142036002c81561810041e40300c2c402c0f400181c0c090301c0d22000104a40b505401202c0b0b0440e890380c0c5031301091650102000512140e16030083d40050030416040940b2424000342411290402c0010703a43c0b0300d8041001001003050f0b002421903414402044042040803c507240c80d01c6d2101d01c1d6004285071480040e105401c4c2d05c3c07041246189034107021041c410b50f03c0c9101c01a040c1a1020807a2402d0460307141e94404044548001c5075201d0403044c81114502400350003158421000811002e00c00742c001100c2400726010380000aa65800410412684441800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 564197526 1250 564196276 564196309
    0x61b0302160305211017121207270504051609030b040614150910150516061b1403040305030117030c0a0320060903040509101205010209 60
    0x103280c40070100e809401040000d4024040c010080748aa60208078680b203800003c0c0030119524152404482403141c3c3c01e03450260010b812080e0318031000e00c503400034840400040c020002420712250f0800314110300da0003065082040840b80214554444403188807815003051108031200500701010300c02101c00040c0350741640102d100090814a070051148026260081c1e0144031959481c1055405083c1407954900d09030303004800c004050390000f101441c481d0048688840d941c0318010780554410160140c0409082e508011283c0300707006100410f102c0c891040981030403000e40c2c035030710111240e02040580b4001030345201c109480d804006c104451042c8001e650660030301d0f440090040c04140074600f0007004003500102e080000f0000e80c1d450b0200c4808407030387e244a52a000f00500442c0c036840d0b1515010380040b07901c4d2200450482c2c4550319a20003141080d1801082011008002c2c1c0713051058007203c40046052540c10302802c4416009000240c2d903200101c0c1840300c0c2d500200d00d07d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 564198776 1250 564197526 564197531
    0x9030c1202010e032b09030812061c0c0302040c0c0b0c0c1e0f0606060711090703111606050c070302030304110402040e070c050d0f08040204090507080330091005040501090f061b03 79
    0xd20005408c90305a60380d001601c1020b44e0951340d41c030040381e100d8079520b0829003034800c80010f0008002401c0c00307070b0007a80c1c030907070b07083c00b050050200070744d860048442c4c0105444025000195540c5a40000e070040303106c00b2003128804110081b900d00c01c000c00d4659401c0d140c00c90303404400c1c2c0074401c00c0007a400600c140c4041e8909019612142c03081c0c4003c00d1118030469400380030442052094020038600703000864002c1d5104d01c0354047c0c0c00000f191b4001110084e0518000804d00d000f5401911314007130700b41d00030f54074580d5180d944850100c2110f01e0580c3c044d07428000440c80d00b00e05c2c05224400e42c0261124118034569050803450710800b000c1c40820070004120203810103510051694016a060710041540400c40c6440d40c1410040e03000015207201c0800c85e0101c85007456401d11640c200302c0e8000030040d00c0c0c00b89200c060a0100c40302415640701c00c902d0060503156900095206018400010b0100440c2da1414010410b1b03060035241c1e10f0700c8a0014103c1d6000742010003e074100c03400e04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 564200026 1250 564198776 564198779
    0xd060b120714072103150609050d230703030809010c0e060d0f051303110d020a030c060e0a0809180f1303030615090602060709030c1202010e032b09 65
    0x642a0300080103021008001d19a40c003030400740c0004090f540700340d501c806a04001031020380000d002c0c44403441590002400d204032518140308204070306003a41d80e80d80e208005a0f0400043c4800c00b07480758011201425410014a544007002d10604c4aa44030380010b41025031840c01c0091159030007070885603143e4500000201605d80000000702000c0c0c0c00d44046444220190b0900700505000356403805030340c10482001600081030084140e07641c441e4650300d0600b28401c020035030f11422510600c026034007491000005c40d006015440c096403048002040c03c800c004c150300c0c144124000200e44282011070400311a10342040a544152213411028a042c90300c50350118424102421040a00720580c0700401450712903003000e8003030000c05d81034404028603403800600c3d060b154132a01c0c0c01030091901003110b0b42c3c400c1c10b402080703c0d004030828040a0410310340c022021882c4604034140502c810100d54070351001d00c54522124032101c624080c44100034210180c240f820340b80f100800030070303840 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 564201276 1250 564200026 564200047
    0x405030c0f01030b030f011e020415080c0412030305040b1806012c131a1005010509121608060603150a050411060d0c170601050d0b010e040f020d060b 66
    0xc041400c04812181d1035440091100182c1c000c04400300310a0b014000d00381c1d05044000c0540082c0c4d10070003002c00815030051000f69a071f04030301442c060443e0b0031196000d481c0c46144070b09550758018006800c0140740603914112420041106e503c102c1c0460380f508100300602201d0043c09511003002c2c41503101c40012070034080d4654038140074607107071815060f8020100402c0261808100620044041382500300000b005e089181c1d0020b007115411205007031030031402c00d11b40c1b59500130007c01d0f148203403041c02c010064549420440e034403900907451000d1010340320810040e202d00000c15008006d146802c0022039401d1503002000507010754020586804c2580c40c500419a001803a0940000c89840c1d520b0148420f1f0040c6400c0d5a100e9000704603da030f082419032151044c195203440d00c40007d0103110180c2c11039141201c140e40890303028800c3d0b4089406641000440710814540b020581c910200090708a550700304003003008035404100100511642d00c42c0704090b0216140da141410900d05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 564202526 1250 564201276 564201283
    0x1050604181e0c0b071103010e4326010b01050f0309030705060106080a05060109030209180f0709091103190f11060a050a020616050301091805030f0408070b040503 72
    0x15040c150844010320500f40503a1a070808003508140c1c0030b2075502c0c00a0308060140d1101c0c1080c0a12035440d10010341c181000014450428030b20100f401c81c0c064230009410158003000e403960114880070b56118806420100165070050100c03082ca080713080101e0b0304041d110015050408540380e1500c3c145c0420740e030700003040d90080202900f03856565554424214218001d4074002403840c4104000410341e540c0004441e4450300010008001540e80d0000450340a9010321019400c034411002141f0340000ca40c465400d41070f0764000310382d41204250240362034248c0380da0201c402a6901c9080d0810403080d40d10300000c3d00c01c01c500038900036240110410700300d100840001c1c40a0300705112101008114501b00300152002000e640c0c95072000d10015260ba40000340740001401210300184030310003144e0036074000d41040d548140c1981e003445809002400a03c0c2c0100c60100408104000250100018034a0154940556071144d00d8941503078a13011144d0001401c00d0030038002400640c8000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 564203776 1250 564202526 564202553
    0x6080109020705010b0a0303050406170705030a050903070f03050a1206050609040b0d0b04030306030b01150c06020d09140d2a0219051207080c100527060c0105060418 73
    0x40d00010703038880c81464002d004101d2007441c15005901c5070000428580c0040240084441d95141c0c0505914031244006402c0012581c41020a805001141500100340e2080380e10820307440c01c5928200164442e010307064980001103002450004080c0805070b40900117152010b00e8120910105e81024002032584c0206048a40195641d0f000404160358203c0d1207035503a500010805118102420000d02a11040c00b099a00a0a0308000110b140341e42000c0d1885441c26669001e0b006690b590f118043d40c000002e5a45254032012102c0201e560544028241c80e2a40000e01c44141c0c03400f000381001040c400f400ba030700303d056903240d008403078221341003036130b040d030458020000303a482241c0c43e0740401103900150341010352144610303110000020050181d641400407203030700e042c2100422a46c0800544204002107041c041038182d1040c91807041301d0310351030728034440444a10300041003468004440c524116034441c0300b409051306141c0709050071610410286045082c01d51105480030000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 564205026 1250 564203776 564203789
    0x919030b0a1a030f071518170106030b1801060e130605190c0e090f0106020a0303150b0403050c03060105220518030a05033c0702100e0f070f080d0f0216151107060801 73
    0x4441c4030b08c3c407000a52180c1d0245070f200e8400780745420000c641424412000035920015860240041030000c1a02c460314031840e00325a10305618119aa03c1e10040c0c078020307188145065030400306a40404d200c0c0230700e4210350500d56414407201c100320100030200270003034100284204a4401400040d0b4089901403180c0c0c0c250501194a00e40045400042c844944c405020200086004020044041042c59a013202101100c80d0341e43c0762820000e1381900c6500c0380035030711600c841d40800200c16070003042d400b048401c81c4452032103034030308014107583c0075054110015100004005500b4140400310400340c0c7e2038641e06d442c54005c04044001c1001c0c0c141100e1411408100190081e842041b0079541042d20780c209000e80c10f1003900c541d940c3d0351003142d450348030302601002180034404841440201e070071f80b1006200e07800703171880280d0344100e0030030110085008010200382e42851840503000180a10705482454000010000f8000d40f5044d02c0070840b5040703800204441980282c1e0941507409 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 564206276 1250 564205026 564205049
    0x816090e03090616020306040b071d1f030f020a05031b040e04061a12030409110c03040632040906051c0b1e010b0919030b0a1a030f071518 61
    0x40f051244c0071910300700074002c1d41845800e04120811810180e003a0080580713888080c3c200300702100d00d1403100001c1c100303103801074011001b1208144401090131201d64107424001070504030140e218041e0780c406160407020480c00400c1c0300c40128403c040541000300b40402e1800d182c00c0403c884c0c000513010300b015200544902821050007030000c1d0303038007101d00700810002c5515a501142074998021303200b181d00c01c0345454802c41c0c400000a04170f03000300368410040c1d407406007042c0b42604d82555030781030140c40110200002e840266425030f41d2801844c041c1500e501e6034030b00380004d000e903200d50f001680a4855506c8004010340300554012002c1d034441180c010746c0c2c4e80e5020306980b40000c3c03162403180794081c00001400b108207900400c008070042e5847d090205516241005c0741c2602d00c0000c010820040001e0b89440351a84411040442c4280b036614030301b1721100103490103071515140211600300881c10010544800e1440615001e0350400f042220491448042040c103580304031259200c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 564207526 1250 564206276 564206287
    0x6011b03090b1c090f050105100506040504050c0c0f03181507140f0d08090d02060c0f0c01060b0a030f0b150a0323010f06020d0c0b01150212040816090e030906 70
    0x3034142c2e441c0000740f622118204001c966605080c442080c1e01c90041c0c1d019460000400c00c201b554644110554101500e190b180070310f01014032004042c020400120400d007407010001940d418413030007024024040080d034441501c00c0402801c84040c5902c00c0c82340103800b11000c404900c40083e47d2200e5044580c4081c00c4821054183c1449503c0c1c400510134000c1400313400046402444080c0143c3c609001c64020006a00c01039a0320f0364140c5050b8800c0c0c2040c82040c0707482c0c21702c3d002064030102010010903040e946585504598000e041c2100101c0e4030340b95000a1121244543c41800c0400c0320015141012010303584854451400100d0405403500c11209000c613642030f101038031350b0481d005c1d0300042d030f0340741d01100c044001070007841c2c0140107510041314050300c241400300681b82c000010001c0d503481c10740842588842c0154410030360041070941000c500542d00600300400d80e50000c0c02c0101d0429000d00700424054009048861401d0140d01c03022400000307445c0c2c0303090244c1d00544d803032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 564208633 1107 564207526 564207547
    0x60402010507021003140703050108010507020c0609040f15140901060201020a02060a0c0c02031f06050d051c050d060320011d310506011b03090b 64
    0x10703100b8040d034005454100d030071441c07a42c840d084c002801001901409424001141c40700e0103c0e030f031400102302a04081c01026404041071014040107404900003500740d004560980e80a1595452480341c1e9001c1e940c4110070403c09814a84000f070b035112100c00c07003020a45041802150210700004000d4014000c0c0c540408136a0058202580c0d84040e600003401e20b1038807401080160b41e4107101684043c424024003075410010300c07140040c004500010b032070403607110500403100c1040f81c1000c40d501103046040000c03c0341000035001440b010440381d60040d9030840c49403a240000010411a03040c10076540c0400b00400c4602c002c0301ca400650301c040084514205001400d110082189480e0000001038240d500720802c00e44024104800e0b840c0d9940c0c450b90040d0b0784e54042c0b0005d507030028100da07020007219040310b02990103039400038403815003485080d011920229108841c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 564028776 564208633 := by
  have h0 := BRFrame.cov_init 564028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 564028776 ≤ n) (h2 : n < 564208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
