-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3239
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:33.004166+00:00
-- url     : https://prove2.me/submissions/a31061d0-af67-4919-bc54-314a3833f63c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 582374100 ≤ n < 582553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 582375350 1250 582374100 582374119
    0x90118030507020f101719180501050c030609010b1c020c0a050105010e1905180d08041205071101050304110901121502090102070e1f0b031608070e0d050c04020406030b 74
    0x1410070540e121940c488800041440c41d00004503507119030540d400100e0048251f408000c2c6424650a90b014282442c00b000647c2c0382450500c1400d0260075001143e690032a03107135040840110f81f0607141402031001a660001c0c07200f04a05002c01003c0510240920031912400580700b1680c0300c0c0007a160a5a0540c2003030008600800c14100d10342c010495001418211000301c600d02d400341500900c1010721203180c06811940c00ca05002c0100301058503541c1c494986003030b107403107c000a50600501c040240500c103420000c2c0b0302e2035224108850900b030091310303a0f4407480c01400e502c100c240082c3c0c00c007105c0300000500e1803512404490061103400c0007401d1000d0a10000708900915440c00c4c01603100c0e060400092000050706a002014166507807402c5504021348410100d81c0d52007894045400002c004214200d0202042d008100340f901480c5400c000400800b510452140140b250084030100e80801008105007005524090302c00d540b190f94441018000b03080907202ea501030f08126 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 582376600 1250 582375350 582375379
    0x40f060b01090b091306030204050f01150c080d0902030f2d010b06030105040209180c18010e0307061404031b030507170303010b16023d0c0b09011803050702 69
    0x1224401d043c1d814482c541c60400108008201a080c0c031860305c6080c00741c0e030312000300260b00e840c001c0310b110321891175010307807035514040008112158401ca6030741000141e803482c5002460b0700c0211202180456404a4003c4160000070b0402005101480942c405c1d040081c9003280c210190a08001184034a52540d119884802d170036076030030030240e50b07202c1c408000612491805030f020b030400020141c00390080b0182d01c41480014a019a500040e075080070410f07a003107483d40038040e1007000c001c0ca480080e204103480400d07a90b049a000d05030074440101403034020b00f58000103440042d0f0300708058400c1d00041e90b45c940354111080c00305580d903014598011030007840034001000c0501c0032900451a581c40d14403403900603040780d110744d154624400d00380b034050390350b41d894210201c00456250003003000c0350000c82c2003021040c61114000056103011003442e50001c01e410101d0360000360440480da0f60350030312030051000c3c0c0010b0001030b01181881d014150b114018101c454801d170344c0140c084508 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 582377850 1250 582376600 582376607
    0x50c04090504061416050d050901150308030f060d020609211e060108032104021807030b0103060509090a1e14061b031005100903061a09010f0302030c190e040f060b01 73
    0xf00b5a5400100b0810400614000f515902c140e5000c220103000103501d0041c503034be80343c15401950054070ba0031400300900c03030314108183c007041d00040c0464140c02e0348140c5a000c1080340c0034460019100b0240820030020482080305511a6580002d0036500200501003602c000c4440b0101c46904a204901c00030a00346000000c07114590040301501c512105c040c1581e03008040024012a00b2110044030b40541050341c4041b1401140c0d01d403404a80309402c00b00050443c0c0d03081d84500d1042c0740705000d100e8010404610803074080d41086490350352950242441c0d40741c1b590007800503c1d10092a1081e054074201240c81401031442c0326030326004290240400880c6d00007500d420001c0136244204000d9880d0080200102d0300726414401c3c0381558a4950300120307151702c40499030603d500300040c1c3c49403411100c0c80e03026107000741105290505640219950719681002c490082c09990172010760902005141802440419401c40c0545000c0c0713003074184510060800c8420034145240c20610390300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 582379100 1250 582377850 582377881
    0xf120901050402061905041509050f18070509041e052d06010c02041d0f0c0402040f0b071b060c0b1e040b19060801020a080112080d050c040905040614 66
    0x8005090504202d2500c80038003040c1d20aa04032000d0010402c80003a08c21484143c840c1c1c40c0c24aa202e002c4a50710b8a41448a20856a03000b1880780e0490000b8680700c40700d100c0c01c1600002c071442c0950720340400d42d0100d4010300c007580910742200d0124071000c1d103000e280e03002030b44078294501900070414205c40007000d039055440100c403030003000d440c001010ba511940c0d40041c80d0380002c2c004a1b07204203102d00e80e0081d0b03d180390301c5020358101a5a681400700200b0a5800f1200d064404618040c038140c2001040b03480380c0654007601d0400682e800c18456546c00d6400034214540070000380030356400014001180424040340c13202c40c8100001c04080034002c00d60303d490040701010900d540d5665610580c5000100040b40240700d0040c5089040d079103210b031074050300030710f400143c1c0d4000c81100a001c84005170f01c400111401485040009a643c0c2c054401aa803008008116920340205001c0580140d4200500d000d2400d001c01050040750707040350a0300c1702c0c5558480d110b920344501100c000310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 582380350 1250 582379100 582379103
    0x30c09210d080118020901141201031202070b03060d140d050a030b090705070f05190803010806280207050102040302100509040b0423090c0a0f1503090f260f1209010504 74
    0x200c28405104090444e13070010b0894110506d08103400c01268a0031280310b4006000260740d1000030801441000585a041140004140002e040851805c0b13102107003880000c1c4079900651039591244100310303602502ea0710141008056905010191074014015001030301c800f00000d00781040c280c1e8a0a094560381c0c080c0e60380765149442c001c103645500c502125800302c02c0385c41d0321527440021500c0400044c8014018412007045540c0d5240c1030340c4618049019100301481c010318480700100310b1900c2a0810010401a00036881d11524149140240035980c030107908854841c807242c84403648017000308541d0718100c0b42041002844001c0c8000ca908040301900035000440c9466404034a24200c1d0b54042d454a0031517240c82070b10b4000c80d1140c00c0d00d9014000300800c143c014410103803880e1040002d2001440c00300624401a1240641141c1a80001c0c2000c29503041c0754408140309031403040008a0301c100c05549031a0760002d003106501460942c2e84030010000030824a403018050680a41d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 582381600 1250 582380350 582380369
    0x1302072d080a08100e1003140114071209051024060503062b03170a050903070201050d0b0306042003030403080403020402030705040312030c140a080705030c09210d0801 74
    0x450010945003250b000d41921032116000311300080801c0c8038007007103100d01c17803a03107001c820f482c030b1842d15081c42c511800300702d18280d04005c4008041680850341c290b200540e03240554160040200304070040082d0980a0a980070b42c801ca01350804440d000314820300c40c1000c0c005022685c40b000100e0b110410700070f150019404001049880c41c0085002d4100b607401e020164400c061040d14443e0b00c4031a40084011404007a00344003500054800940d000300750820500c510303d4400145a124030032014000c2c10b01c0800720310200c128072164040820500061b04440b500e081a040c0283c0c008030818030f0507a1000d0004109129043c048203803030840307a00c024690b04080c19a0f0810010b500000c084c142005801d202c000f020580e14980304002d040c2170384002920340d861360300c01010034100c4144030011080411480d0001a880340c0c4c1700e0b07030155079458441e480b0f4955292500300c1d4454010090740c40100610620301c3c12507813140840c25203440b40119070300c202c082c00d4196015a0309120b5000300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 582382850 1250 582381600 582381607
    0x4030912050d12020c03040f1e03121202040905180609070503060105100c020307031104060506041d0a0b130e07050910030b13060f0218220b1302072d08 67
    0x450140e0500350524000143c054100004640801e1442e006541314003641103c00c041000010400301054a0f078203003070703182041c43e203045455003165100c44003000c208020400410503a164000d0b03050b207003d441010400d000c2420800580d510070a03814295109600444001c2a045034001612000b2071b0030180c0500b810b0b0703280600b044000b5031041414010b10802150480040e03806001000c040c511401000c20324070b403e002808115219074010f6409240200000e008544144140081040102c05111190b54aa0364803101500201039141d400c01c1c80340c52032100304440c0303030400a8800d02000c21140c03410b80d60820400482c2e42654010500b80c1d18110610100e5140400382e684001d440d555004001000e82c0c41c04d044410398202c81e96056130125800a030445003c000d480301c40e80c110b81c0038200c2040c101e0491829000561141e403a2a035480003031155481d00001c1008010f09d290b4119102c5540f4180043c08040c100c00f1b0302a01c841d00030100756050030b81c0700c500f400c1c0758000851070308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 582384100 1250 582382850 582382873
    0x20304050a1709180a0e010c020a150203130b090f030315090a050421050c030d14070f08063102030f090304030b01150c0512182b1e05060403091205 65
    0x704d80c07101405201d003d64a94041d0b01a400c024040c10094410310b900410b0000307000d081190301001c04042014503903004105108485542e0f10211040c9504207110b07030310729118040b00728035164070748100207414080441000340c6080082440c10502400f82c4000a2903565038220804031501241d00814402211000400c0e0000036182d004020015040481ca40102204803600e1078100d105050fa840c0c1e00c54404801d0300c0e10b808156a04980b49081a2048100e42940135020340402040076010359100104400700b640007100080e9046001d181003602c001c00103d01c4c1010b503004880380c1820f0000b000205c0d4918100000300c40072650010181c000d143d09042c030070311000305052820300c10010003003c401c0204074280800584020100a07135aa02c980060620102c0c03400003107003520031103801180100c2a0500d0304145050710020b52609810080c0340b60554078403180d0390168042040340340d821006c0110006649014600a80b0780b005c030607960310701e500700b503400744040101182c001340c06044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 582385350 1250 582384100 582384139
    0x52b0f180c12051608031b010e0606040b03010f060f050a060c030c02100306051009150f0e06030a02070c08150a02030903071101092705090a0203031813020304050a1709 74
    0xc100f80300300151069448100b28040c620301183c1c00000c1a07400c005916040052883e080c2184030030b1120080c0070b0300c00c12010464990314002e1840707000303c0e25a1070800a40e0307030a40c002024244003078410003443d522044180e0701500c45008440c01000d1410010900a010b04d030700a00c020f515545000301d001107603090003101c601158000302850746904001c1065030724010000e844a0302680c8044071907143c00c02c1da151498200701e03014180503d48511058071035011101c01000501500e00700da03241c540368141d000038490b400002d401d200d00d404010a80d07a2020660001e110760b40c03451075429488a1290360220b202c2512070101d26070080100a0000d171040b01c0c1269000320504213100d0341c0e50781d0600c0e6211105100b2050302c0d11400c401d80c1400e1044c1510078030360840c0300180200046102036020035500d120300300c0e0b80101000705040c60152551500d0948910104030030b0255100d0400345811940c0303810b404003c44103a5100c2c28541d0010840000781d440d0f410008001c0302c2a0544260074070b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 582386600 1250 582385350 582385379
    0xa23060a180803040501050403030c110d111615030f0204050f04050910020c010c0908030a0906080a09080406170f04021c020f0d0308040c0e0f010501052b0f180c 71
    0x184800c0c0c1d5090500c201044203500a9846580218004110ba1500340380003011075072032400100c00c2c010800d85070700a09600081442a4100d1410500800d070080c4030803600d8041205c1c0802031403168000e003c110751040100104948441e03441c1030258550078481401039015600690fa080313844100182078900d0550400c6420945d01c20982d64002c064048840603a808203402a8650b03454083c4d51041c250721400c030f04c00401074600070310b00303040c00000010200e0a451141d4401c00448202103071103058140d00400d10190b01c000c0d1a5070b66540d461018142054403a110300c1444207040c00921003413210941c41d44201d07802401052a2111102c0110716070f5000d40d0266048660304500c1c400035105c42e000903481f6070091300d4604091400e490721904080c81ea40014025010f030400740984000341282040c1542c0007400c0a80c0c40e80319242d6070704c4030081d6028000005040b24034040c4080b10313040d8403404c20318204420502000c032561940c01d0452a03001d000808105940000700a100c2c6c8a5120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 582387850 1250 582386600 582386621
    0x3082a0906130e060a0b0319020322031e020c0d140a02130504020f1005030103030c08120708010e0c0c250b0c01140618060f0a170a23060a 61
    0x6480c281141c0748200b100e04066034101080000d2604107002035031800481c040010f1401404040c518900609000d0540001c603404c4d01c45030342c0110100700050211005021303a040c0c00d1120900700000340c14010103c0300425520343d01d03c0c840381c5c23030345680c9440815a00c902000107001c0c002c0b40301035503503091900042c2504850140c02102c0702d032001661014600c81125450200200d11420140104814030034110007080c420842014060302954100b010350b03046940509000d0b807d6852401e2a110500c10307002c0d1501802055400c00140c660025491030503034230301c500000303841d5440d4900040340d407246408203041507000d0200c0304c150707542c20220f0056000030b49601c0c205183d552000510305421419945825944480c140002c80300074000055020f1001c580580e40064100c441c2520080081e10742d60003121240d410200d140c80b40325002009003120b02511080102c110321041c1c82d90707442002110652103441c817034140c04500e00192114282280007810464035510306035801405107120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 582389100 1250 582387850 582387859
    0x21009090e0309180103030801031b0504020d020d050711100b04020c0d020a030e0906130b01020a0c08070e1303020d110a0c06080a0e15060d02040902030a0f03082a09 73
    0x1012444080c1401000c0d40041100700454440700d002c020000416190400301110060b000010030200340c2c4140250304481d0000c19004200101c0340c0a6980d5400c2074000a4010340005074400c9810f0060b4011b020103014031170100200d4450341401c87d00803203451940181c55001402c01d08203040650f029200d0200020001854141d51003005820087c0003012240540c01c06441c110515421804c180c04130b500c11078484206241180000702c41543d54054000440e42c0c41d814400503900821004c81e03120781100c540e13071517150b8428030f05941d048503001d068030340a084400308500b4241c1849000c810703030f850b8000c0c10381405c03c00300071958180c80030103408840c0700d0400f114001c60b003820b00d9000a003482e0350300d40c070745450800b41d08025500b0944285515038014482c8848020300701c0780d09500300000701c80c4c454032003455000190280506000c0607606001d12050107041204c050941c000180c0303e41c580c2c400c0e0741e5848002030225005180f00108518100a441900880000050040c00c10081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 582390350 1250 582389100 582389117
    0x1030b0306180c1018090b0114090303071406070f0318020f240a091202180601030b04050a02030a0c05120c1e0c011e02041202060309030403170702010f0314040210 72
    0x800100c40c00e804c00090000304103500ba003052110440000070018090704001442030404100000f80f0406858130189404003000c1f52911107564284226458181c02100c0052151002c4000340e031698000d860070404601032804066102c2e000f8020305481d09090b4403c5080d8680c1074081c070800300f1f84115a10390018031194130220305021400807044d082d8458508a84401d1000d401611050443e000540542e002c84607240040e921080c0481065442240c0740e03007103454140060f00a040e00705c042540c814241010410f0354603c0390701030f503c107406d04e62041c090a82a41001c0c1c84502c15a102041c102e0390980018208188000045c4034120740b0044e074405e180c401103416145034019040800c500c0c1d45880544c034100f1714240e0640900c18401a08504d414a01114200788180800c3c000b40100300200011b55521002c0c8291401903401450140520101800c1603c16900c0140d0403800700b0034200e1940b501c0ca10900c00c44030b1311040b601000f5540e840fa9000c120001e44802902c000f000441c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 582391600 1250 582390350 582390373
    0xe0a06080d120b0d260f040924081513060c0c030206060301020a050d0e10150e01090207120c02040e120c010f0e0d1d04020f0706050601030b030618 65
    0x801030250340c00301c00e994619520300c6541ca488150364030105190b1061081d80a118003251240e81c100300c504090600c034051100b0b404006400b5806804403002c01d1070740c08600050a4a0503402c03480e440c400c0e085c580304141034450035112451040740203800e150381c000301041860b44099100b91b40c005900c550482210b440e103030354000589452601c014005651881004100341c1c04010290f00030404a0095042481c1707044000d1103401a61000407140f5110044004035030802e015080210244c0c042c00e0000550b500d00180c0c820349188684034a94806c10000207080080d0710991301d200d43d00c1140f160381c140050108070b0b881a4a8031040c0c1e4060368502e80d0402c48101001091281c02e4020b0307010751a105520300607400c40305151104041107051410403007400d0340101d1152503441803030030109800044e65041c140f140c0d5031040c2c0d058101c1d20010fa032840f451700e040302420149100310703024005a980c6800440640c0c110a0303200d900343d4000c901080c54221807924907104840c2407811180a501321 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 582392850 1250 582391600 582391603
    0x1b08090709091a09120904110c06010e07081006020709021c090b01081b0a0b030711032821021605031206030d09060e1003020408061005100f090e0a0608 67
    0x450040350403201e03a001c9401c65810140f03106600a0780d00c406400351500e01011105140f0582120a1045a8810f540045486400142c0382003a88800c200c40143d0b0712250502917005040d28590003150f0f1280c00211044100b031003030f205540e0a90b010b8819186007081c00d10103504803200b82c225514150030381508150443c800d00700034900904860040e54034150b005410310142d050303910402c035000314060890392242003104007211403441c001d542c0e95640e4001200e03007001880c0703a01141d010016004000040e0040e58a5400e10014074110302c40441d45429100340914801c0081800c9841e401c00f010030082e58050300300c90304007002c891021186556400d040d40d2021075442802d00700c1e041845800d0508201000b119205410451000c60070550050585514094828410007409030700e010030ba442501a5001480d48004458880c182040842e400c40124081c10b40100040804403020303903c961082ca11036015038403070348803e40c100300c0001c00c602c1c8004c2c03003801285d40f5944001000c080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 582394100 1250 582392850 582392861
    0x30804091e090605070e04020408060423070602011e020a021f0b1201200f0706110403022115010f0311031203070908010506030703150903020109020a080a151b08090709 74
    0x803c0301c00041c00d10f80410042c0c11010203991413802030740b05120500c121500000d0507034202c1e8001080c080001036210300704900c8500c589141203903014070900042c005030150000340d402480b818101605410000d02c1c40c00300e00450254030f006034890002070f0314017401088c00790f000e0001d0000103d400f0080b00081010386460001e1500940e542c1d2200400500700c400710305c8030142139018545d191003800b0180000c10f015000001d0540f82c2e4400c050700300c01014200320b0b070003944c4c054611642500c02440b45243da031105d20116030340d8080c402d000021078002da1200c41c16190380320105135006043d626403500c1070210202c0c40381c051051a00341c1058131510805140b10350b8595a51010080c105001a4252900a8001802030780140014400500c4078809500ea41661610020315090035007401c90250551144c065000507803401c000c20701107004561b03034407030354055031b10100b01d4001c0c905d8400c00ca42c4c01d2487e07100402800e209000080344211a003580141e41704040345c56254892031050304440307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 582395350 1250 582394100 582394103
    0x1032a020c1f120c141605070b12060a1a0703030e060a0203010513020a0e010302030c0d0c1806020a0b07030507021608030706050702150109020d0f1b030e0601030804091e09 76
    0x1240403100700c0e902d41d4451500c2c02008502401071101845200c4045c1c071090b120480003040e640f020800256142c4c0d10038044a945400c101100d00d4250303101202e2215034045201d6103024503004000466500b84103070f061003240c5000701e40007078601d6a00680c0e00c441e0400d030303411002c141d11b500d007036071505404000d0140105c0c1021381c0140e40e5450078040007201c3c280345400180c12401402000c400710303000406080038036000e00b80580d40350b0b100f030407541b294450301540400c590302c2c141013440407591010b5603854016600b850144040c1d2911001e0f40d480f20588001005180c01c080011911803107034005039006241401100c4070b0142c917161002c9041080c0c7c0020020794404200b02007440807902602c2e4100c000c43c009414001c00c03050700130010800500034094039030380000b40b40c030180960758042000700001c541e04100c0c0420003111600c0c2105840844800030703040003581c07040701c4c4011501c0b504aa50000c0060300e01450504640c3c00b0f410801562440440c04110490b502101d42c0500d03403055 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 582396600 1250 582395350 582395389
    0x1709030303042d0b070807111c200309040e031306121505010804020f030c0d0c081605010f030b011b0803090d090501090b180d1a010501032a020c 64
    0x48145064041020003d06484002072000000100105a001c1c0310342d60002d84502e0091400c2e95031000540390f1204120864440348210050700070340c1e10643c910440c5405141d5140b8841c41d00c510000716603600b070000078452580003040a20302600c0c15074071411007094a001500d0800491820800c82e011300c81e440900440c02111005d14180c2c0544101183d000940320020341c0079040100003040240e00410003030107480010929805982c0400443c2c1c0d01c0d2000504a9029000610b08031901210501c0356003c1807140003806e44c9a884203803011410740f0010b035218580045181e00071005011691141070511103c0790b41410f1401c0c24508030350b034003030181080740e60380d05040009500c0c096400302c0b50030070820000c009002c580e07401203003403044414102546803110b0355000c00303500c90700c2c00a1176a540150042170080c00c0150703554180206482e4003019100a83c3e0302c000540641c0c111031000720400c0b0420f810303d0301410341c038404c50341880c61500c1281e001401c80c601080c2404040100c04545 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 582397850 1250 582396600 582396623
    0x60513170d030e010c1d040905030c0309041103040f080706060305030f091e0a09090303020c030301091508060c09040906330609030c0e07050c01090c091404020a03170903030304 78
    0x2140d01400390403003c02e845002003204141841c4010240301c40c18065200c0c8011444020007241c4d2a60070401d8056001401d81c0c6d030700d1404112250342d0b907202c41440c90141d4101905501100740c0c04e4181c0c0d2059401051800e440c8a465440251951001504a5250f542c0302800300200d03004101078500e40d0303141c04855070740e44021010040e07880d107114a4040c4c0f030201c40110b02d11944800c0d041d5411144500c102103131000321490300f68081e0085000414652002000025806c00180c00149184981000d81124a80c031075400c00d4448104884481902c04104481803440c02c003540301031181d500a180000311240448980e81520042c0c00d440451000e146000c3c091210342d0411400080c0301508000929520715501c01e90801300070310a912105001e140000c0c0b0ba43d01400c221215039070944000c209051051402550080a03030140a20880c9010703109900c0500200d0f03d1801141c0007403880c0301d0710f0724540c0c40c03240156510754406003102c8248a40c51103030b1010000b450060744201d400a00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 582399100 1250 582397850 582397873
    0xe030306090609060a03060218042a050f040b091f080a0e0309130c0c050a06090c090204061b060227040e061314070b0c01020909060f030706051317 65
    0x40c044001e442c4500c18000388061100a036248140501103079070100c400f603155000c20100002c10800c01203aa50042d00b080b0b0056120454003203000900c001c40952090ba49503d4601102c150140c94010030280b5010001808400c0800e8060410150700070000211440c0c0800d202e09041c410300b50350004949401b050200c011040d004074141c14925000840c1003694410014441105c081a04040c01d40d55601c2224968802e600f299821600b02c0221003010f1444c0c07070018014030f044403098803c54444200881c45102c14001c0341d04135152542d600c0c40a02c2d0300c2c80130304c0d2002c00c032460440d1021b501f000703c0d5040481c0741d8040a102040e00c2d1401020010300014417003a00c042e803071006090340105003080f901d100142c0815112541281030901007600c81241e2a160503940d40008107408404101c04210540c150001c00114a0a803402802038443d6420300c82d40351100601d41e603058009030802e000c0709128602070103400700340001d1030390240c1d52140e18001c4d4400d640400e09a50704a50000031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 582400350 1250 582399100 582399109
    0xb190f0b3a0605010503160309020607061107030e0a05010c06020d0b100207090b0d0b04120c0b040b06030c030f12091f020601050a0b070b15180114030d02010516030203070507060e030306 82
    0x10081c042170a00b1803551801d841d0703070031842d054101d503038082c15035800d50038055441e884107980310300e071b40542c08000c1030410a51300c00ca07540000350110002002c03440f140500e8141443c14000301c8606031161036031848941c2d16a4040d412640c00340c2d01180d941e081001c5c4075a959140c1c90fa40e0300058002d8101d00b42441a89825250707050b00003070291000d0707010880012031490328194410b40010800d0340a65040360126424004440c0103040f400925041c4070611580080341e60207810210101c0d079070400d5105c2855110f81c8517016889694021040740d1902050440041a800000620180c50446411200d50542403030007010801640100014003950a000301080e025115900c5824103054103661804120100202080c0300c01017407515205460319069000b508400d00c50032003851541c0c445285040802209541340d101e80306000049540701c0c0107101c1c0300d0042d1032521610300c0751030110100360040d51014054008100d0100007900110f04507108040c21a400c0501550b5607080140400c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 582401600 1250 582400350 582400361
    0x807031103161127010603150803040605031006020f0a032f010c0e1f0c0f022101050618040b042405010f3204020c07090b190f0b3a 58
    0x1c29510002c807481014804c030010400341180e03405d00d4041607500c84aa211041e5080507404403000c0c2c440410702246058109002e10720030a800700100c01e546550f0b25040740c0d140b40251030340d00e0907080147c145001c24414401c515110280c1445040351025081d0042e0841a41c940c2c80d00103a555640705107440c691042e8134604001c400c50b000303030f4405401450044290191003455060141c1e01035200108141d08840d40c403600d40003020f0380b82c444400c040320007146042e01240000c84d441c00001804034034100b403102e843c211b180e44041c0070f20b51b180d81c0c640c0c5040300081d00607610907040c0c4c1070020420201600001d028201c1a0b00401d155240425240030074a1580011241100c54850042c02c07941f4411110030741242030505400d004503000c0824024451203000c5400760041190103d903070a1507170401c3d41400070039034006804140001180f030040e05c0d036004191401c460b01200300000c04408024143c11100e12241c034000c98840001c1072900c030b03030452000d001a1040b2445010a081c42d1280c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 582402850 1250 582401600 582401629
    0x402030709140c0d11070501020d050a15030209151f0f09060f050a031d0a0b060402070c030f08090910050111070303080a0e0f0106030812010b0708070311031611 71
    0x2407014119140702e2000d101002002c141c0d0b02c4038041004810000b66800122002800000c0c80d9954503441c10020b020354401420050803904210209445562a11a80484a4400400d81c0c40b1509580c01c11034200300140200d400c0308080805520142d44181b46080d800c40c0c0c024900300c050b900317840c001d44a00303580480c141c14040121b8040100c075401002c0000484003030b1034805c1c0e035034466046c142e005203a07a03400036402e17407051500c807030108000250f02c09400380540c3c1d10301c00d55075491082106034483c524004180700a441c0b01000040c44003809030113943d1090759840e0810110002250314910f04403116000066241000c000f1541c204404c1c0156000240180c03142600f582c4024000020240c07024140550b101d038a45080802802503038000d00100c00240702c46039403410b001c8041d811a40701080e10624010000403603221100c1115811980300b440386040c250551000e641041040b0b0392441c40740000c02c06036203d60b2201c1032400b00c5910030405010114028018884c001400d41d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 582404100 1250 582402850 582402869
    0x9050d05160204020304140a03030606091707030f0314121824150a0815010501050a0207060804030e0306042001052a0a12020601090b1f030f1d030304020307 69
    0x254280c00c0c881c03109000c5a4040c2d40150fa00c1c0c44914020b884038401c41d2092486004404c41c180c1010707410f4100404035181c1c0d6644400d00ea480e4a114200c90260390f44500700c6510078402040003d2040e601c2215107070107030410f0000c41e05514408151a400b0b0b800704100d02c0c000504100080c82d02d4290000c40721040c00040102d6010f00d00c126402d0504448458a0016550001810400304000e0b05041090140060340080d6440c824555241160011a025810341600100e0309500c01e9007916100e2032280d0051065a1a1400a032010140a8400d03404c011107440c0c40c1d0501d881c1008464059445540b0040c20b00c1c084104101c0c1c1c081c4c8086400341048000c124171610000c8001d64a5510207e800382c662414206158545c0743ca00742a000410140025510301c20b03a64000c0352403412139804001c28001c00c144141009200b070b4061071701010b049420742c0a059000d00c81d0744088040e4602c0000010000c0d000740c40145003080791004151185c1c0300008100440c00d09000c0f6100602a000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 582405350 1250 582404100 582404107
    0xb191202091c05010605040e03030a0e06070507060c02031b030304062a120b0d0f050c01030603120503060307030204050a0c03110f031605040312080a20090609040b1309050d05 77
    0x80c414402c5201c1444034030580901c1c4000307210080d44004010400104100720200f241c1844503166001121005580f80c03074070f00f10441c004804540385100780001d50794a03185c0400d59032140010b2416541c240114031040c04605900040030080d60780070480d0000468903403402d86089000c0d01e200b0034105440001b01d8854020800d02c1c00b00c2d121310301d025410540401905801070307100a0810302c440b03991101c0d110008a050150386800c01c5c07241030281c02540c0d02c602e110320055050340c0580c07000620318108004103c244510450195401c03039030003002e46039240d549400240c190b42c000e40d200031281e030703032403220340c41e01a00351290f0081060395160a50901c118050060580e0000801c07141c44555103402042c880c62080c8202e0b000303550b0180d50081905410003000f4080501140c0300003110389802640342d410400c41301e0507c0d003201d0500da41c2d440c20081720140985070b005503900503001600c2d115004c070349a903065414582d078004060000303558030003410f101c1c0c607140c944809901072207002c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 582406600 1250 582405350 582405367
    0x703230f07120905061804151410021b040b0d0c080322030b04170f0301060e011b20040f1d010b090910051b0c100617061605040b191202 60
    0x1c100ba01e06c1d2040d88140c41c40305002120103d000303800c50300c00b0f180c010240d074803001c14040c001c0c0500d000a03079803d941090112200d1181aa0b40e94108035040c0c42ca807600c0c00043c10a0302e060f410207002808060902c45649100c0e661b030b040d003804030760000c158039000411400e0700004021070158001201c0001030780268507544034481000000f5001818604000d20010485442202190f040c0c1404403c1c2d55a07d6070b440c00e005024503018249180080c4038942e58004020000301d40e52081d54003c040940c40d0500313800c100f54064101d03d0a160456106d00c40907101120034860180c002c8950102098141c0848060900f19109003800368402c2240d18180550404005a10300c0441d44100300094a5140c010a140d4266190741d003900c00c550700010081e00003440410180a10b0411a005004c2e10340c07189142e45c400000421103800580c0034100084903600c1e41a075024031007e0a05144d440c29803542d00b410019445810454184040c1001c4000140d40c09240714070600c61102d011810003480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 582407850 1250 582406600 582406609
    0x200702090c0c070b070804050108010902040305030d09060b0307030605180628090c150305010e061003050c091021050c07121206060c05010e030f0703230f07120905 72
    0x54200707280c404001c01c95150b881020800c2001403d40441501c0c1c490b40107140ca080d0301e50013805101d0008040c4800000c6030712990080d81c09586c0d006002e107041c455080b140000401d90a10191511520741400c12000d40302805504050350045802145c40e180607107803a00c00030302c5814102403503030120f400c0040343c4c010020000a0808c0a8600c10383c0c3d18168115500580500600984001010310700019002c40c02214402031850a4a0500150782c3e61b40b800d010268040365080c0c1c00011803070300d10100502c00c0e481140e01c503c4061106062040d0180400d141c05e01500f201000b00f84103003815202011440303c9011100c2e410201400f85250100d0f44070241d00409c4030080000000c90f42d6403206034024409091081c000e02001c1242aa0f00e52005003038203c00342041e202c5518290f01080c1d032001c0030007100c85038180e0800382d40c42c0c00201d035022512811701e0702c03000c0510509881e4032880b07000220010100c000b5610081501c0e501703039043c5924a450412600c41c180108418108084c1c0c6a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 582409100 1250 582407850 582407869
    0x60905031b12150f01080d09030b060d03050d02040b2101050d14031c0507030e060906180a080c0109060507081e0903090a03120e03032107031e200702 66
    0xe803078200c2911200d807038807850400e10120100307240d0f098404000502c840b144000f4100d0740741004440c0c2d003c840307220994854501c0d00004d000e00003140e000541d9801c3c03005074095030349d00c42d24102c0d10301481191010200d801c550013081600724005251020303800302c008070104080310011818219490000085d501103035200c0010300c84404040308034100300d400d00c161149113101481c421b0060540c0701610b001048111124000b02c0d00d001c08102c0d001030006030061191012000400580d250302c00c0d00740c010791401032030802c4c51291032001c80020b00b9240241092605420001c07411100c14900b100c1a6040203003548204404a020440103000740b008442c84201050b134602c10b50384079001143e056104280b04a900158407013000030802c01c010159082030b040e95520868a001c0340000c050f10391051340c0c0c0401d400209400b40c440c0c0d92a100182940001290400003803210f802c03801c0005000c1c0642180751107988d55861442e10b85804c002c110810102c00041c2450b180040d40094060b14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 582410350 1250 582409100 582409153
    0x504150f0504050408190305060321120c0705031318050601020307110301061505090406060807050d0e15250207062a02090c0d0f02090a0506070f0209010801020406090503 75
    0x10f4580300403906101d01c440449031004e2400c00c1c0755000000c00c1002601412080c0c3c1c0c014024850061480c2d90040c00101a2038180c2c2110007030b51a220800c005442e01140280c41783c2c1c0200801c028942c0080e00030001044081040403600c000c0e01e141c5450740c80d07826403d961960b240741c00c04007004820307070740402150452540800d6074078410402d0404640103040755000303d94580340003040340c0301e03868108001d481d088030122014411b00d41ca40900300d07605017050b94030b080460020701c0a44c0d06001c164020301c88000c06c880846808880c1b100c44e4605442c42590a11145000344d050038014a04640c2d6003d4078007080e000801226140c18030041a45040c411415004146421001490a540054803803041c0e001400700915041c04c0c42514603550114082031001482c00740851fa08039030302c3c02580c07200040180081e049502d0803003404065440048211000d0030765a051000607558160780c2c0f40a82101c000050b1214203000c8090940302c215001240b09510101c0f03001a8040310081444040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 582411600 1250 582410350 582410359
    0x207080c0d081623010513050c01050c010f1503020f0a0b040b070512040b0306190e070f110a0510060506092b2009070f080109020a0504090f0203010504150f05 70
    0x101d800c489035808455111400070135016400028690261020013107448a400010080041e0b0f2603400003d0386661404900518603080001420324560081000c1c05454007001c0010808400d074440c0007046800d4002280086103203020b060056040036250b41c03604800c10303034003c0c50803800d040c6c94203542d004510030b040f0250340c00076020302080403e00c031010190404580740e640311506d03180d0f41e840c283c104032a6280940c03000c080e1003840040280d070300c1040316840d003e41251500e8890088601541131076510040c0305180c009691001c404122440da11406a005000d03d07110301140a000d0342c810b03901080c4585414003055074070340d48002200c1c07c1c200c0b0815031a240d540c0d020b00084004080c2c00c402401041003200e0412030b102c08400405010074040b0f070341419a5441543c15100017100011881c00240b0060050050080c0e030f03801812041003a0410310f04059544940754203852800031181fa100750003000400c1141418050220407046060304d2840040c2070084e00d40c2464254411940304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 582412850 1250 582411600 582411607
    0x6040b0105061e09011404141f0509060a051215011e020c1c02030307080d140f1602011e06080c040e0d0c02040605120a030e010305091506131b0207080c0d08 69
    0x284c6c050703511800e05106400d8242d80303866580703110161424102107524003403e11504c1c0c50a141079003082505155030b08d40c940e2420034520b0014040d0b141c00c8049410240a810030410311100c1c0020601d038030466030361030a04110401d0000040242d69407a01c0041d4403d488807030079400b6030700030907203c4101c0804c1e81c060296440030013180c10488119000079425000019000e414007020034014283c1c64201c10003406154244c1c07da6a4115030112145541102080301095070900d0f50000889007110a00c0046022000580034050546800b00540c60040c1c2c4c50b2010070207000c0500000d030490318104c508002d4020300850140d2144011000380042004412601045680341d90001d0080c18016220004210490300b16030b80c0d0b440584410b4000c40c405c1159070315190711a001d034034803980303040c4080c0080c001014541e0768600005000c1591241f40381c0c51001e0000200e1146401c2522003070040c1040480303011000e07040454540007881c541c1c0103820101c4d550f0700c030108040d290590080b4015075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 582414100 1250 582412850 582412867
    0x7210e0904052d0d02070e01060c05010b0a090e0601050a0501210e0d0306050909060601120c0212070b041205030f0403050f0d0e0c1912031b06050906040b0105061e 72
    0x800403014006146000040c03840c50540c0c401880c06040c3d5207001d000c5810302108034809a036900d46612420f600441c0100040c40903500c40d46000000c0d5204000118801d030300e000004400990581040700c0c881d5803900024400d4008010181c01440d09442503141c031401c05000900500c80c440059000032680949019012000e6124044010144050350f80400d180c3c0c200802608080c41204d00c81c803d170b90301140346200049451401020140c4a5164000e50f207058080500900c140f03400030340c000c0343e1284040c03218030300c000d00145120b51088840c034601071501c144141031042801e010840300303100308002000014000d5400c03076054100a51586150040c58043d44120043d5084060901e40070301c0d10800000351480e180f1004941ca920b01140300c480701c2081c1061480b5181c3d0790f03031040045001190007444100f2100d40c0c1070900381d410480ea91106d0043c0d84003a140500035a00c0300f4100000c0c800c460440740d0140500311805c1d0314010420801d950340d08070307146644510301c02c009003a50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 582415350 1250 582414100 582414103
    0x5090402030a06020a1107060509130b010c060c020304030b010e0604110f03040201122a0806150f0307200f3306060c070306060f0504270f150207210e090405 69
    0x8a06d2103d6030100c0f1a40c60b15020000c040744c20480009024886094501c01e170160300f40240c2000c42d4069440e4049580b240d11008080d01c08102038a0560100300070220212b003004801d14081c1429401e900c07641d04241050004481c01c611903d60700c02000e10641d6010700144081703a410940902e00016101d070300794800001091850100003006072038104881c611b0741580c51031860303a00281c0301c015050781c405080c06941182e440401055420402004401305844409144c00420038030303200050310700c0c140d00707500544074a400a0500381d00807060654441410000c1c0e0710130724095103104001110590300f122a81c65800b20200c1620005800200035883d1841640d06011510045074a00703030756800c2450041c41030b40030b4120040e02c1c1a4000c0b030301c1c1c2011b000722200e640d02702c0344a24980c19801041903d5409030002142c0000c1c4620b0140041a849401e20a0340c0703030841401a5556500d01d000c2d011354000460a4040c8035038090140416034001d0320300b5003130880517243d01d6036541d00e52034041d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582416600 1250 582415350 582415367
    0x270312030615032205100b010207060c0b0c090d08220308040509040609020301110408160b030708070905060d0f0507090e010b1b030309060106090f0315090f021002010f0605090402030a06020a 84
    0x4180c010b9041c0400d04c2032100000705403420b035400080c10410345c40b06200490300c81c0f0300ca024048c00304e04041c52000000e1403410790641d000c047c180695042100500000707150080c0881c091b02c0b07007003000c22480c4415501680030f16101f4120540b0f150854595602ca03445401180f00f401e00c0f858504000400780b00d62904101a103d07402002040300580c941e00c01c1c115600071340a005100d06c65021000a0710341c900a1070801c3c0d0720b1580d07406040d0303030310303410212580d1200900031400c0204c42240099251140d1001d0712691a11280220301600c45074040011241d004255408110300200108044a14402c4440c1543c00c81c00c8484daa80b5043c121107659851010500a80c5200000400c00011004541c56050b103582d65580a03185684403a605407810342800b01030292480c440381c03d0030912265001d034901921031900d0601003001074002582101c45118440c016035190030107601584d45601c1004042c001c2102d008100d41010340100f56105a00b040041a40358000f80d41032813180101c126 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 582417850 1250 582416600 582416641
    0x7050d1517010e12070f051c0914091b0d020405120109030801060c0507050405070c060f0c0207051203090402090d020910080d030203010e06010c020627031203061503 73
    0x400305a580e49012080290885400031100d55280c903d1000c10507901103401c2c05550b482201c5203060180513100c8020098041c2001c40d01441034002d1140c112000680040d409100350711540c00451030800008030f100d1070703007a04038840ca0041080001e000b0804801c2c1003420074551046840b5001e11160000905c02c640020b64080040380030301ca191441500031180d800c0c8179603601c541a0340c0c0c81c60180e605000140700140107410403030045c021030500750b1100351301035451700e442c01c1c0070362860312820100d8002101c101c5106840b503c001d070036590104101c03802884c2c1980d6810443c120003d00d1620390141c2d41ca000d2286400207000c01d00c607506c80039114280780c2c00030040011030030103006480314050079101d10a29401600405411035000c1c1c42030b03034104c412040055900d9603e0b000112220361365410201c5e4008418440003455003641100f80300c2c440075983c480310803200d01b41f003018a8000864440c0c42d17501820810031a40e51242c00701030240c8a4845500c07612034840e89210045000e81d80740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 582419100 1250 582417850 582417881
    0x40c050301021308150105062b02030c0a140307090e0a2301060201060b120a0902040f0f060f05030706140a0912060203150a06140c010f050c031b090907050d 69
    0x80000140c0718003244502281e1450044035200c6002c0c5c48550b000e45c0382403140d154030180c14444540024086001402100b40d0b0f904104131070302c46444004226001660000c090510101d9880e21703640d08614481d80422a0021040c110700e0124002400010301d400303007001e03c2401078007184641c1c145402031960144902e540e40d810300090404425603071024410400150f080000004510b5042e03000c550240c0060907900e0041d84d60300d2003020143c80303641d10481c3c2165680e0070041000845108109011101e0080403581030329003540704005420315001244a90801441006607a0704a98080386c035100100502d612941e007108146c038510000d51002100100304480c1c00104030082e40214417030040d5501c02103201c6800300600c0012181c0b406880042403d544840081c4030101c0050304c4004610b9001003520240c04152600b541c0094481198191000c002e0108009140740d881d540d05c0d034111030050820341101c0025100180c007030043c2c01481070000d061440114190041d20b400c4a0150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 582420350 1250 582419100 582419107
    0x902010207030c15170103020609060702010c060504110a060e09040605100902180a140a0605130f0f150c0b150411130f08030702010804020f1212070506010e0903030f040c05030102 79
    0x42603100c6001c125003000e400a420801c40f0015482c074410170506032900604038138285940701d07081c07003c1c0350f109400580c140718800100000151103401900e200318440c0c4103100c0c81404003818032540c082560400410b120a00782d0b005001c0c0c171030003060341c2d102d5000280481c0c1910f8243d0b1004001c15907400c1200f11078000615000e004004d5049108008401d1311500c0e40382d0f50f00c90700104010b0702070b01001d50000e0151002c00c0200c0c400c03406465010101c030805400e40c0da46404150100155a1017001100350750b403010800004c2180c00403108203400e0510b02080403103541e5211120070014074134006944000d44102d6640c90b00d9021505040243c40340ea03940c3e6000d44c1560725154840e100c0d10b00202d80d2142e02299620010090b80c4050341d061715100903a840310344c01c00080c9400a103410750402000340404043c15020004200400f4000c000c665032442142805810100b050300b00c014140c02010910003100c00000c1102ea1203031a08a2244041d19685401e0507101c4a641c06550b1660020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 582421600 1250 582420350 582420359
    0xa1d0d050a1101080f0601050304140102130f0305070605121b250233030c0d02030f0f0901090317063715050f2514060a1e0902010207030c 61
    0x2030300b038008010241c03030f000440c1d610314108810308a4126005800120702748003060000b561101940356800940c1c0c0098108400f408030300100c3e405c164005030103e00980010814844280005005071226242072890116240d005841d550360140411050340b442c0076001e52101d5000003605c04042c040e82800c03007007140001c41070710803142080060740b00b603818134142d04000a00c001058100751040e88180400c41d0a03090480d01a00018107002000408010103055028584001c602c2030400d00d0110321142000829041e000000030030741c02c10350f89840303545800710380c015128000300d1091404a00459070f8200110b001081c14460b040c8400203110111810b2605582d200c0424002c01c00d00024010354901c03401207201601100c5c0c00c04600700b0000c00600c000c48800524400805482c0d4103641040301c02444250a008032054405880d20304965801040a200c02c4c2d0b040340c3c1804050222000e03800b552070f44440c5501704a014643c0d42c82100d1704690087c00008025034200b021221000d1b45e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 582422850 1250 582421600 582421613
    0xc04050c03010602060a0504020f1519030507180506030126010f020901020d05040f210c091d0105060901050405130b040605070f08040c0911042102040b03030a1d0d050a 74
    0xa00845015000e8174000075051a0039208483c46503400038011a401440c2c10140024002241d40614030b03000100248503c4941d000c0c00d00000582c83d540009051400c0032004151644e000401c01d01c52081c0301c0200a1641d0b0b01003a681520301050407500360804800c6030b00c2121b0994032100b0b001c7e50800d203801420340b0055010345001d06081e000c0e11f00428503550304540a100d80c1c0560006079812200600c954940d0040c070182400300400c4800c00303143c0a845401d90360559620000c0700640303598100c0d55420094500509901215001380203034280b00c0001030211005001303a42c09560b9600002d00f05580c4111010400d503041906e001141c103007820084040c010880781b81c40801c4103a03840c443d0b00392103800014815900489910150707400c003000701c801707020b1140741d22810002c01c6c000861a000c0204e90a040701d03060020145480b920b13441400b088d034258800c520711a40042c48078000c0c807030308012241440409807280444c5043c104000410318941c145001d8842d2107990b2842c0c01700020f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 582424100 1250 582422850 582422857
    0x160506090705060f0301182405031005040b070e01021c0c0c080c090a0507030f110c100203070e010c1505010b070c050409120e0a03240b060309030403140c04050c 71
    0x640a09441d25103482d4824090b05111310106064512401c2004004000c080c071080900c40344ea01ca408988814545619503104c00d901d00060000c0101c01c0c0d08204900d4100701c00d0b02d8030051648180414681030321500c508503c0106020117004e41002c400885a1080c02149121017845840c14070031452038200034072015180e0000c64800141d1b0402040c4540c00084610522a00a02c040c6241d0744084401c400303410302a10843c01e1503181d140860f4a140d05015a003080c4241c41529030302c1d0a00c503130381146410220401d825246104001b40607400360f21a159141e12a020700f890000545180b0b0000e0218603c211403803025840d140c000f048603841440101407141c081c41c03100c2803058a0300b08200c12030b00311302c1000300701d80740c010b05c09103103103018030030110b0b103104000c145140c0c01b41d032600c0300c2951008841c480000c0209034481c007004080c00b485800c840c41401d807002070551a203172220646e20300c20360002130101c80380001007426180d0100950303004120702910900c010705203510340040f0784d00b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 582425350 1250 582424100 582424111
    0x150f0c060c021e01150503070e010b0a17180c0405150d080d0f1509050c0702010e0d05010c02010219020f032d0703030b12010c090e190905030406110a03050a080c160506 74
    0x1040051700084603d4001a901d080d60922041480b880e40b80003544011f41c1d000440300704c1400004c810b0090103c05004400380300c1c480b01400c800c0c8072a44142a24280060540c4451145190509000f100444c048200744100c4094407105c1c040741480c00c16001c0390160f6160b580c0000e0901024200f01d0460b600940401c044d803030004580036807503284280590308222400d80c074959007400381c54050341c4143d841c40032424010b070400d0b521400903110360b402d4800104443d00540e400050240380303059a1641c801c6800300c0ca10140481d800d0703400940740c582c030489842c0c500014200001c8402925a8407009041001c080d01c810384c0c81146280c00f60142c01e48034031039407081001101c080340007101030007207089003070184d92000c021b1340c00c0403006004213802410703942a1202c01c602c01058429a4401c0c176803c14010350046845501e0140020701644a4951800342900803201d60301c0043d8200003070700c04100890501404503034035809a0311150049000c0c5d1400c040d180340101d401c4c880d0109406001d00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 582426600 1250 582425350 582425381
    0x60306010513080a0209070c051911042301050301110d0504050c030f0604020907030615030e010209060d021b030909040803090c0d03030903020c010815010c2901150f0c060c021e01 79
    0x582c0c1e21003003230f98080400200a4216040482c452910141d807a030305001b0f4900c120554520780e1910004281202d245480c440046000303440c0b080007072804030319801c0c01088100d00a1061350190654680c45010f05600005055110004136040000c00e1041c200e10010103011501c0d044203078500940c0d40c03402603c050380200109000300b441544030740a0325041d1002c954207008509480300088009282c12140721049540c02d1049950540e15140101043c4100f4507015803144083d40d0394200b08003103929616807580c010081102c4944074031f06000d03031150304401d1480d00c980d42e92a000e8106002d5414090b40f00003c100000d042541650016010321300907402c942100041f5801900c04400c00e40b0100e401040484a4104039841680c1080300e4a01c9207250a01c0400380540900003002c804183d181c210450400600207000c50509040044a0303501c0d0a08620b01091000b030194a050302c000741c041c0e900c94a80c05101ca0003004088036500301d04800da5003160b00800c0702d40c0207154503060610030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 582427850 1250 582426600 582426619
    0xf280e090303011e0e06010f020f07140406092c01060302150a260628030f0b151507031b030503070e06030402131d0a03050703080123060306010513080a02 68
    0x2213000f0308034100141c1d03174110b280c40d1081d01d844c801910711103914145403086120302c0507144000301080c08008000e1080c415180c000e4884d1100b048180e0301c0d1500308030402440c01d140980700540b203206c4002e41000b1650201454040001524003410b150780003e07402c0789a64274084a00aaa0f4000344184a0b507035603100101200780c50a10007000c0303042610700c3c403095203402040891074801e2802d2100010f0172191005a803134111605550030042e803054402d0014102e14000348204069100d0b1700a0040300c3c41c0070b680090000180004d18038020084d0200c801040740342c2014019030040002c1c281003002e5101c054580e1500810582c81110328000107021090007214604021040c2d9003d20340c001c000603040c0d00130b05000c40040041102d140a003404000052140841c00d20403c13400c5402a079945039140c0007410b000c1c010a106030310000030b05090810703c006081009044405009003100e01a6503919280c0c0101c60314001c1880f81c1e04503030b14408001840d09400160031054030b01c00d5a0711a007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 582429100 1250 582427850 582427889
    0x140f09040608010b100e0f0d0b010e0c0c1f0e01021c0b0a051509040902060705011a09090316021306090911010206040f0b0606041706070e0f280e09030301 68
    0x3130300c1c07002d14140d40054005909095040c014003844040880207400103c005004a002440d540700c3c282055450f9101d240050242204420742d042d40f040030714a0903850b021510403502c0c7e94080c011984143c0c043c040340c030040502c00c1900540400300c8408002d5440b00410056031002c20304000c090f10010345002e61040070b9080032020071046a5005003103c001c00b1442e83d800b0711a61042d00003d0313100e503843c0b80240041c0c2c1c40d80040c0541c113000394000510030300d100c4580710318180c003180e1300c45c030031105a030810045000000c01c5450307041010301c2000d00440c030351000c1409111044440300825080080104402041c1d51290384200c0c044d030340041d00d01c0b030644010fa0b00e074541520060104c81c0c85d8542030700498907a17101716030004c001800007403a290792050340c4100780c0c0c5000c1200c00350390003030f00900a90035409084030b00c420b04115011004078010b600022425043c8688113a101d241d16158955a0044801568000d14803221a006c0620308551800c0e2030f030344240035040c01c1c40942000c141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 582430350 1250 582429100 582429103
    0x31603060b09041a090405031308120a0c0c05061603080c04120209130b180c090105310c050a1211070308040f0f060507090512030d0507140f09040608 66
    0xc111a00070001e2458000118140300c05031200710b40300f000c81e403020000c21089440750074040e44100e015802031a1903980030810301043c0c801030303813089159504c4a9040640710102d00110741850581381401081d4151501c0c0c41c04900805511590344000086041141da064807901003031858800d40c2c884e500c96580c8100b00c01e4500940c05901450213616030710000501300440c01039004084c103242c90030f02e154641e03160340c02c903c401c41e0000c0d40c1080042201c0d003031190800444c0d000e201c0407545042d40350304100200784081e11a4048910002000c005610308010402407407010a2248a051002c80968000030b4101d5010072040320008518040d03546040d415881900012003490700d100f45000842d0700d0885049a020f08150346110001080303000090013070900b071000d44d10a44001c5001d143c1460f020b45a1400ca0703002e58090301104131241440b110102c101c5440c8424201c0c000f8940c1c960100441d42800c0c1c4d000c0c0300f2441540081d034405502190030280002c00c504076000e00000c4d4031100702c01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 582431600 1250 582430350 582430361
    0x130b040803101737061e050702100c030608030409061a070807030c0215030411040e0102250c05030609390f060c01061818021f0221031603 61
    0x2054540052a4a505002c007001040105500b0300c5044c1c04210a008501c074212051144116203c9545a011040130300342e488004869a10b504401c008030302d4001e80c06500c5d8801c0e0118007003116968944000d01900941c4400041c0c50401d00f200d07211500c070384050008040f01e008100f0300312400005140030800000403150325541c4194803904040041c1d500f516860810305040380c0c401400300304c00202e8140f12000c0d41c80f841c0524400b25066070400180421164080190940ea0b4010030040c0f14134a2034850311502e41c041d02a80503100c0d9010300b0300118110300d581200d0741c5401800140a4683c0d0b00040c1314a02d0301c0e01d04040203010b401c65a28641030003003410710900c40d007801c103c82c480b280780c4115140c0280002401940c50a42188030b080e003150320030b4012030011800807003000101540c80c4141c2a10042c650744000081140e90001041050f042c0441c007000146296001c20b41303442808440400a01c140c10081e02d00030b0080032080c142c00c01c440000d81150722005071060540301e402007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 582432850 1250 582431600 582431639
    0x1d0405060a0c020a030807170a02120601080601051b010609090c14010801030201120518030d02071e0f0206031b0703080601111c030213030210210203090d08130b04080310 75
    0xf000300a413195010f0f0f41800008114005200c210410035852040f5050100d11500c51040d005a41705074000243d42642c5014001d541000309010412480742d8102e0100c4031584c41c00c0c2d107981c0500d450980703218003500300307900b000c9011810401c0d110100182e074095007054418071401c4862141818004403844407003444042d00044400c0480d0440c040360350302154101040762692059000700b5a130301403850303101c4403503100001c4d800a010030a00c40b0121102401039190018845281c0d01d81d100d07018101012000030303101e00300c000081080d00362100d46490001c041284150b41310b100908001d03003150700440324580403c0b94070b81c1d00486410042030785000a0800c801400c2120341181080b0000e42244901c59003100740c0f49404805039903421121040300d0495512000030651805d01c01480d54580c40d0480c80c1c50b4014414004010300c082075150b000a060705e00914951b40e0a0b21900c4120004000075111200e204107000510076004010b5100d184010101e150f010741d0b80381d040e1f030288055800d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 582434100 1250 582432850 582432853
    0x13090b0609090f0703050f0706090312031113140109080f2112090715020321040f0b102303190c030b0c0a030b040b0603150a1d0405060a0c02 62
    0x40c0302450100e114681090060007280e402c04031103c45149003c1c400d82082c0d420303a10150141d20100410844907002d45440d24000c90058519614500c074611105003001c14103840741a0b041001d082c403810349402120108800304200d0740e51b554005441441c1c500c844c0000d07101a80071820050014030024800201d0009248408107903200c414000140420000422001c00018030612511690782d4011034080c0d014110039440d151032010584500040c0c0d909540040c03050502c9020788800c2341c01002880c407222105541c851400307401501c24203000a0068540b0000e101c01042016040d07030540c3c00f030401044106000b5101c00800e00c009a03003082d0f2503031100138140300404c3d40c812400300c00b52150464411207612a590070300b00c803500712002c024026012684041043e4140070b140911903007520104512004880403816500c8000c005000040c003050455801e0389450034120020044440030749400c0000602c0806017850682d01138600c1e02c81c4201140c8a86418030800707510642540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 582435350 1250 582434100 582434123
    0xc2b0c0c0f06050a110d1a030c060403060c090306020a0314010906050607170c07060221031005010f11030a02010b01030e07081c030902031203040524010b07060213030b061309 77
    0x292501c000c0c00300280b40700c01150721105c0541051280e90007034042c5001d120008141c0c2100f00c901c1e549201c031001440c4e031180d48488403650035074450700115015203400c41b0740132070b03c00c0c80800c0982e1440503590000709003a01c0052021101c0c3c1e4141d01080c400c0514000400d0542d903910f03c00010395180d0b005c4d580c5e12190400501c800500c0c480056440900403224041c148515050b20354108100c5a01042c0560490740d54098004107003041404081c881e0711506080d41405000b801c8a8449805000e06200c01111003845246c0290512000c0307005000c1101d0b07450300da10100a001e000b914017080d011078202521504e2182e0041542029218000300500554100380d90b641c2892005131140b506055035191142c005da2401c2c090040e0716000c0680d82640d070f080519000b441c0501e00044826041c1515415084c5070001017901e42c1151241000303191501c0d85414503000912410810341d12010070544000100402d60b00d040780b06a0084518070a050000e420081c191168000300406030580c2d00e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 582436600 1250 582435350 582435353
    0xe060106210b1e220c020f060f15031c051b03040308090607080c0f1b030606100e01200a0201090f12030c080f0a020a050105010f0b030c030c2b0c0c0f 66
    0x314000e0742c1d4000000d000681c00c0341500e00d40d0200b404a4911044c916442c0d10021302c00d00d0f0100070016034050303010300421591030052445001c84901620040a0360046d40c0003e00c540d80802010014518003100245500c000c1000074015500080c1403030020780390400200d12415021050743c08894000b400d80b0f191403030280800865910050381140d0b8800240a0140003000812000113420500c100034041d0030307030b941c0c900301c0e41c0003031703004032070f110740e225504210f21500c4a8140c555540042d0a1100e01c2c1e6002c400103075100c0a82c90001c0c102c0e11001a500d004402002803005a0b0718001e1f215000c4082e1a04081401e0407040d0242460b0613090420a9001a01c100c5201c4035050040402d141080e0401160316140c0d400100c9910041e44406280c5003441420b105060040c03c00500884050303203002004042c0d0300004000040c0c61201100150307052220748200c0c0c0007180c03c001c005804082c5020b940b9441c004012690b0f084529211901100300c2c002c00240748155004400402014142d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 582437850 1250 582436600 582436639
    0x1101050c030f3601021207021020030c1c05030412180506030c030601090b16030e040905010501150305160804110f040c091a0f1c0e060106210b 63
    0x410110451104400d04840f440c424401200c5240d030040c403a00b1a42446080028903001014031000d210355000c200640060741c44007503119051480d800c00f0381c03280d0b115020007402c030703c818074444846001c0018800c134000740100304800c010399200d04040c01c60130001000c44850200b01c070001d150944000500c201d05008a0310100f421380e0107603803c06226125004114141c0007907401105001c00401809040c0d80c2000e54800500700e86040030f4201000045200c0c0d034104038083c050140b10340c1e60307990021a200d0b40c00404141d50864020710013542d40d0b03c412024032142c448200002880e083c0456240c1003001d684a0209a80b40d903401c005803101d0321022200c000d4882141d52248000c911121640c54502800c110039400741c0764507000c03510b881c60130f1030780d10f099044082c6400d204001041c44034503202d09580300c8030b00d5021200c844613009010b2a00416034201800d049208031000000d560b940651034140d000e1110005007a143d000c2c680c481d090300d507a5001a42c1c8401e24403812510482e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 582439100 1250 582437850 582437857
    0x308090d08010e0907030c0308090108060f010f1d09090604021002190b06061c05070216030f060b0307080a050129090c130509010314061006050304110d1a041101050c030f 75
    0x20310540e10700740c0c4e0701c3c0e88887e000c0c1c803d40d0045989440103d6054a5580c00850f256807180c0c6c2a14200040d1000c0760008007020602140b003414000e01c0105e045003103007035860344845138002408030b5080b4142030100c641e640d5400c0350102e00c5505802845151244045040a10041c5100ca001d043c0d038480d0781c0302d01d602c0744000c103080c0d0084003d00000c0310f02c0c05d014040d6940c000380035a001500742800c4038024202002004007561010556900b0000181c401c8200000c0b80e03000300c0e00181c80b29030500040d00f449031541c0019110300c00c0680c1501404030650101c60355103d4020707a5140030000381d510300107031294002519880b1503588000390030030845070001c04107a0108110360003a02d4a40340054a258820b800c141d5014008038100c500d2007030200070080d0014105140c1c01b49491509000505900c00100010030304584501961072030384a0800c48a052540460340a95200014a40d030b120500212400c0d01c08051000400100f540900101d401241000d80503504d0300810102d40a03060b030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 582440350 1250 582439100 582439111
    0x919050604061a03032206050f0301090b04090506010608071709030d05040201030f0c0e1005130b09130614090609010501020a020904051c0809151504050601030b0a120308090d08010e 80
    0xa80f00001210303550140000d1507808001e4010350034040c1902d05079040800260010408d100c010000700058103003403000c1c0c9045401540340822041700d0b40d00820050103807100c1c0140103100c0c2400205503141c0281d091407260540b540d030074599400000902c1c64050081d2900d4001d50001c0000407207400050f0032450748140181000b0503502608800407007168403103010b50001480864428000b071411a0800700c5080e202d01c0c0441c2400003d1801e146241e040d441250440c0d400001c0340640b40e15a07401180d003e00c4010303020045140e039201e0802800302289001c600c1114048009503192401042c82410fa07401a80101781c0c0c060540c1c240a0450f8015100f69103500c42e2040e6404441c0c0c94082c0701c64084807aa03190600f600f0314414a07841c2c0581810341402000989041107111840300d0241151080211004526522044016070042188403682e0750800c2100c10041000a001504080024803954401d0419652003216648880c44585210006500403004103c0d0074501440300b0b030400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 582441600 1250 582440350 582440381
    0x4060906122703030f0c020c131b0806010f030504080405120c06031609060201090b0402040f0f09060204061115061002031b060114120703150609090b091905060406 72
    0x8002c4000840381401e0381c071007406001104000d01108040c0d041c0070b03040f8100e00881040c49520204c01001e0b44842d030566000f401000c0c07090140503028825008141000c91101034000c02404c081001400076070125142404a03081c00c400c1c003203071440ac0c45264800c43c0c104d2012801c107420300041101121004000c0d0a0610403078007035001c640e6402004601440750003100c600c014083d42030140c000348003584034005591504a07030354042100042c415510a9046500040e00141072030182e000345087e208000c80c02d0300d4481c0303075010454681d008106440e01034881940d54000c060580707030745040150329820801c0b41800803500038102144116800380721030054034240b110344012802840c56513070150030f03140c0c42000104030a49280300c10f10b0b031900b01685c1d5a00400c900411082da07417002d0307105c000c0c0013000d2107226940c2d885090340098041c144400c030a104c124080d0803c0354400c02c0950300e00d001809845004801420300440901c0c4041d80302010704038507512511020000c0038005242c1c03981 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 582442850 1250 582441600 582441611
    0x308010b1e09042d05011e0e041a090d02061b0412050114040b01090605010903030e0f010327050601120f03110a0c12051e03071707350406090612 64
    0x410f540c601030f40d02c0b000403c500811a810138082400ba0351041e800301803100b69101c0e0028000c0048090901070740c0a40c9030303c0e41c40b6119071818483c4120075841c01a41c804800c0c050207190300340072031010340510507642107a4450b1a03141c106058229000000030711014208801c000082100f804580458014000040c21b4007900d50310b080702d0312048070202c49500001006206820b030600c00c141c040d000078039020700c40c1415036501400c0d5141512280c1c2c482c2c1c044a0301c2e084a070f807007908580c0344c0910400b550120710000103000c51030258554030840300c0340500f80001c030344005480d80d082c08458000c0340300307440c024040d1000d48072486404080b5800740504039040c00821f007550207460080082c80030140803078005081440c1032580b4408224499a0321080b121140d400000580c1c0a85030082c000300001031102841c51306510a1840003403192070100c1001851190212034400d456460745c40e540d08540c1d03080c0a96515104034050600441d0440a050140300d01c1400321014030421880002403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 582444100 1250 582442850 582442871
    0x207030f0203101104030606060206060d0b18011803020c18010b0d0e061503060a090b01050609010504032003060907060c03030f1812030b01050c0a062a0c0308010b1e0904 75
    0xb44c40c0e8201201c418204002020400c00440b40314140040c2810310150280c1e0030410009048143c000c000506540c0500f00480c5d41d50010260105900c46294001c012003c05103c040881048092042d070150094050814007810080c0700300707221600c03450950050b81c2c02c1c242e0703000d001d401528508030140c1e40e5001d01402a402005013900682503c10701003c540c8001080518141004000e64826070928050700001103028500d9410341c0e600f12102603e5140050040301c19003d55807000c1c1c0380380354241e4000506403141d21190b940301820fa0940e580c560f96003451f19a41c0d0b00501c6070f02c00080e00c540c0c281c00480d110364054040a903403518040780761481c1062010b1850400071082d603501140507115139244e134141c42030541401081c2400307402c0074000c2401c26119024000c0107008039403201d20312079016013080d900742003410a119900e08580803021000340304042000d021004034004070004940b003005034055a00f945c031402c61544401c0752040318504c040d08041c05403a0021388481c2c1100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 582445350 1250 582444100 582444133
    0x131203020a1202100e1605060c0f1b040e06040f0609020d020d03020d021608190305040317030103110f0d03031a0a1409070306030c0306020a2a05010b030d0207030f0203 74
    0x2040381c0a41c0c010f210b00f09842c03110004031145c007081a049035100c103901c1c41c14075105001d00c0c01280e100320b9100380c4601c402c0002a0030611031701e081381598050054620340c0901f80c00008890003000303880c10003180c12005003440c0d40315070036a8043c00a881c45150400040c070541c01403018035102920010140708680d0124502007029a001c0740540c2003031341c0e0000c03020740c10008081d6841c1401440c180051030044e01c581c03204540605580009200c00c188424035000700100c0b0004e59001201a20811210301e12050a81007808119455654500c6c0307003e40c1d141c440007200000d44018000c8040082c2684c06034003c0542d213030098004501c03189105159030340c3d2a0b07004010000484001c034443c08180070090000d100070065001d05141444c1440400c1c56020a4000e1f80e40c0220010703034401d1061400d5401c4080844407410400441c000c00030018140e880b80000248a10000e004081141003010b460304108281b100041e403291000f0808124041058100c5500180a4542480400400d0b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 582446600 1250 582445350 582445373
    0x906011b02040f0f052413050c36063a0509030c0f120307110715171308030c0d0e07080d110601080712050c0406030302071a131203020a 60
    0x4a020f5650360104080000800606d40700035240c90031580d4080306160010304400b1400d04c0200740307143d4540c00594410700c00c0e000ca611070f600e1030b030102e070262544020507050041249415061030080850080c01d03402c1040c260b03aa6089003903e01b40c01d940d0764521210803200c0c8007064404072080d0b050300d5044040d9600c140381c082c00400b409140d46501d0b10198519040f1203942c240e04540c02051000200b61948003581d400102c10b2078402c800d401300c010068030706142508094000840e02404240080e04074215074480580c2c1212045503a50780c280034070035862034000180c102d050401c0041d40c1c1c40020001444111100400010b10180c44040a0b00c1d1600301d030030200b075a0340020601001c194200b0301c00d080c0d251124005085039814110040c1d2500c8403841103139000324068144a003000300501c90081001d4014004000d000c0d43ca0500960358035440c0f140c400070080402e0b808209106000c110303080d600540d84000d04041c039054500102ea40c6100040c0e0840c02020510320008080c01d481 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 582447850 1250 582446600 582446621
    0xf03020f040b0a0c02040f061e0e040b07090e090618190b07180311040605031f0b12030d050601030606030c0207140d050601030b010303030f020c0d140c0312150906011b02040f 77
    0x8006050120709d04c0342070f441c4580f4050340b2000310020000805e00c5030070194030560104214000c0c2d2102d0000341c0c2c80e405035420490004014400300003040303400081c8148100b041452504210700c5486100c0d440e28040c070180104910041003402c041401650503079049001442c00c03030042294103d13a4164500181c100320f0703d180c8941d4044415203081d01420010307103001c401a00400c03070303184441c4035981c040303070518000c5070745070400340781180e86e030100b13411100010400746c03903880100c158104001d1030100d540364081f0b443c0040104030140310f84964154104560010410542840048100d2110401003e507100f040200307001c0008005200c2e442c001c40c891031241c0b00035415860050700381e07102c551074082d14501c140410020700f00e0000d1150415102070800b4003000380400103000c038510462100b10882c0c0b00001c0d100014440317961646103d0314529042d2446004400100074146500341d4281380080e000c12800100c908030502c003410943d100420014202401d0083d04060300c245006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 582449100 1250 582447850 582447881
    0x40c0207030b010f051305100302060c010c08090d0203040b030612010908030a180c0b09040f0e0d11060f06190509041208090705030607050c0c1806010f03020f040b0a0c0204 76
    0x1003040084910180f4054002c0d045240380e55810040030542c0400301c401440000da0301c0e14041024401124504e00c05103401419241d5101c005540c024080e100c091404130000d000c000020325610303000b00c0c1c09240c1c2c5007a0b9000d5407070241342021081040d040a400140d001d0410302c901c0f500306509201d000b0582d44516811910ba1815200c0700c02103441d50341150140c0a526200380000860414022040da05400e01c01a1108000c0b0080760043c41001e00102c071051514038090596800084d100c60781284503960103460300e8404624603200d070415a00340f031084031707441d000c00d196207484c44ca500015056214171070740c910303612000501c0301042610103450f1500080b01205c40c0310b40c8000401c0c0d00c0010310006200084ca0b00002c25900c58004011408001c4003190000d80080203001b4110741c158024602440741015003000d0307020680c00e80f8002d000c142044c0801c80340500a0003039600007900b912449042c54681402c3b00000c0d03111420315001c01001c035103030000594542c480d001d0020007004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 582450350 1250 582449100 582449113
    0x4171b0708060702190314030a0b130f18020d020d0302100603030e4b0d140c0117010e06130203071d03032d1207180f1809030905040c02 60
    0x704040d0502c0e8100300d00001a9a007140b4005c0485e03040f241d84801501e500e00400e54030758540f10414010828030954aa0050214800300c03407400260b04585040d84084104006020790805001689000000000c0d04401c2500c840d002600d810496610200d001340103841003480c1030301246003120403540044020480d518084244c9007031801850910144e0703011a5425040c45254903074074800d0010302e68910750700c40003103402c5218840381001d0721004082c0c00c1c0c011046130780c03070b00c2c210302c1d407030038041c03128600c01c1002c2ca46030b0390301c601c00201d0581141c54203000641d0070140e040031138500003003401e50400b103008404072070051584015445802103595203ca2901c0b114031220000304400206d07071099000f070103580f100381c1030b4107902c0f0300c4080b03208246003132201c0b01075448070240541031200d02d10017404030400140540010081c0302c010852044590203a80300c56410954101c54010041704481001e41d80f1410740540c0c2c4034008940c040d043c1528034540d50700014042c0d85010058800603000340c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 582451600 1250 582450350 582450361
    0x4050303011e0503060411010225090f06051f050f07111206011d100b041e1a07060b03160807050109090b0f0126040606150804171b070806 61
    0x1040240403003440b40211401c10345040c0010303903942400341014001c0403940c21107818903802000403882e01a00d00c4580302614180a04142000e1038500c039081c6014182800c0c800308490a10900059410040140120040c60500f081c6900d038030305000c40030b002c0d003000200300500d070300409090341030300c5481e48841ca00064001c3c4425908801401c5080344d01c1040103010f11101848104c2c064280d5054804195507229611021030103980e2001d00280c4c000a00461084401075410b0f4500d04403507505e00301d041e543c0200303480c480f4896454540d41030083c00968000b8001d600503002180c401411101035484a6070b140c00003040d143d1058800b03501107203041140d0358000c200440100104072081107101c03640740104207011f0001d44024100500c81c0101c0c81c64a0300c080d034921886000d070b01200d00901e083d2a04500a084600410a5220700e5070b81d00562944114a414841c41d480361a81c42411260b038000304c10354001d00001016a811101000703121007042017003000414034540108400d003000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 582452850 1250 582451600 582451619
    0x19120216050c01020604030504061d18061e011713123903050c0a080301061206080f1203060d020301020d02030a0e1b010c030e19050a0510080a0f140405030301 70
    0x25001c1c0b45066400182c200008280c02000380c40894070142003841c078803206c1c140d500c0600b2203601c05542d8015004000384000da10132080040c4121030a59652161305150b800c074151000341001080c0c0090004c0c0403211401d034804501c41d800c020516407144143c00c41d84d80e030841b0101070032003040009007031122040002280e003e104494880459550254001140741c54901e1114240058280700d4001040080c801041104042241c0c0000d8040e4582d44c50302e03c014488035140c69503e40c5142045030200d40101d0108140c401c0010040040003240010070910f00341e42c04c0240307000da00c0071001c9011009620203000800e40e000712006c005a0b03c1c600040154100e4690202001320341d40b00005003400e104403980288507008003420034071a0105549070032154180101d5066800019148280c0b84000600d40034500741c800403034081a015442d001401070204001c8400b00c0010071110104411a099500001c4400c0403c0008100b144140250703641000f03041c1e0741100c00750300010040110303284 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 582454100 1250 582452850 582452863
    0xe0402211902090f0904080c2410060215090f0307151812030e160e06090106050c030a0315030b0106050705060f0103081c14070306060206100b1912021605 68
    0xc41a811424110b10802246005074007030345aa0046100c2e8001ca130510202c40d042d1a03040e14080308580d002c120341c25400c6002000410301d90427000c54200420200b5840c1e00c014019142550b008050000364002061102d420207030002c44a4010134820981c8200c00744000d010680c01041c08130a041d041c800d641044410000d0121941c1c5041e0000c00000b270048503c260f0314005070f16000c00c0b04181e2000090030b0035081401e50300f405020742400074000601181c0700d480f49108840c942c480e1f0381c3c1da02041e6502d20505d01c115203182c104100403c42613010303a0211045152603481240c0302c3e6104d603140c1c02c00700001c0e001640411000700d0740d4400c001c0200a05648240e1000b0b1300400765145580e040c00d5030003031b0105c3c205181c110818558080640754000d031611141130700041d0272801c2030000940181403900444006004038030000f0f1300442040c00c56421200980401841d065604c03d04607001a1810329180400c207003c055020600341a0002e080c46010120180740c0000e140d24029241c1ba4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 582455350 1250 582454100 582454141
    0x40c140f0c0c040c0c03051c06090b0f0904020102070b0f070b1f08010213090906020c2a0415030204090311010e0d11010b1806030a080c060117030c0d0e040221 70
    0x28144816600690b0b84000d85c039104d20380c1410103d4035625106c0f60f80d441c804088005400036403820314000f0740d4007a00d1708a200d8450082d0780304040ac0c0441020b000804c401142e01038090f03400590700300400b441c504001c102c04900c1301d00131400c0224664682d144108140c2d2034081d103e054481e0041003142c507501040041600300002c611b80320003501c0444140c80070740300b8800c0690741d4040c030781c0610046404540e09001c0c10415202d054007108840e4000001d04645c10701451500c210303401d15400c180c4200b07007980c03405000301201d2a240d542003101428907894118100840c0340c030890034400007400340010060307145000c0c1c080c43c007403018010401c04401d613010103268100050701c1c005440d0191181001300c1d80d103e00d04903503960031001c249460380130f1000909008000403e0780c0c2d4010040b40d000e050b10900a001c1e50084c440c07000d82d81e40e902418845c20210342102100410b51409403241d080048005800581841d901c921104a642620b404001044103104108510f1840c14204500d820 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 582456600 1250 582455350 582455359
    0x21c020907050703020c0105030a021207031d070f0b0726120705030f04060c0905031203180601230102070e0c0d141e0a0f050c0c0c010203030c09040c140f0c0c 70
    0x300d07544c0303000755501c0c03000030b00038144180000825000d107410340441e0488842040c1402040c04d0141004008040c4001041c0d1400008240581e400c58041050811602203009401d8102e040402130f240d0340c8e01501c0704540071107412040402c1d80d038045101103405010915580d4442c5030024455411504c000c201d0390030048100300b00140710100d001e225030040e400030300000781c5110406050343c07044000d4000176414444d4000300a00c0b07880910080d44540443c004d955042e159466550756911802e02801215a0728510102c17002c003040c1d11100d042200501c11200d810b651203103a0540c4034016100b005004600055040c04d0000d28040c0002c040b18410f180b02c41864040509902140042c00044c07404c003802020898401d51504120030710400020b04001504016030480703081c0c0d2141011900700c0c040e00001902d42c0d800070094074410b001c2c0078841403509550f502080000e00420040c003050204250211607480c000002402c0d01a40e9000e041e0340d40c03121111614940032840d03815034880c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 582457850 1250 582456600 582456607
    0x904020c0f0d26150307030c1806050a120212030d020412030806030c0112020c120c0f060903070b1503010e0f0d030e060103122a050d08070810050616021c02090705 72
    0x61040f04010541c00750750b4030304205070b00c1c1040300080c2c2080d00302c0e48007038951441080701249155130090701d010310f0801d030481000940d03512018414000d141c0d120b03001c0c603880700165034400350801429942a684425099901c1d00c0400c41000742243c01c582c12000301071064807014020590403e10454000b0011001001e43e000e20f100002d000311130701c0e5105586c441d0040303010f0450083c01c200000c20705104403c417035100d81044907101c2c1c1d11400c5c80c80144040c4110804120403040100441720034a0300152a66025a98404140203c070644c0c0d03030864140d0340c4c0e01c3d85c02c40c40540c21710105650800c03560203000d102c80c08641c02400d8071244031154906401041c01040080c01808010f90520114185946040e60014451301840080b0500104008100044000300000840d10350045421521b5681e07190312181c03800c44000100700d600350f0b400c80b00240f00340000d181002c080c05040c5121140000200c91603030200d00410b07250407103001d8106c040c1840c50210b15080780e250394403100d81d1914508 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 582459100 1250 582457850 582457907
    0x212010509060106031e09080c060c03011505070312050a0b0f15070f0303061523070210030b0319050106030501050703090b0708090307060c0203190e150904020c0f0d 73
    0x11108018880c840500d669012012003840b2400712552002022806c108401401801d10452503400854021000e00802000842d01304940041c0d9040c0d61103012064084101c042d81660703203070f10612054081c030140d11075149801c2114054680b00320a41e240114195900c03000344032580c41e0343c0b01c40c0c0b0b11400034007200001d5940041c0c251500300c1d0b0000d0014038554224241a001000d10340c0000015403003c4410341002034001c40025413130442a8800366108a0409116245008115000358001c8510146178140d902c02c0d0058945c0a50050603100710780c0b04414074010481000204a030b01c1c0e51906020405e01000f80f01d03069000c4e0403818188600c0c40196900b0300307207503402030414080c041e14801048058404209540c403150f8069030030008001c00e440080c0d43c0f0b4100e820f60030410307a000740301004154450034031071065440140041548000d0765541648a401c104682a0050b5003417015030015801040b6030045004000c0203415840319001d00280341c82812410039600f0a4050070150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 582460350 1250 582459100 582459103
    0xc0b131a07020c190e01080604030f0207121b150c0507090b060f070606030b0403030f0b0a06021c11030f03011806030506153007120506060418120503040212010509 72
    0x1101c42412142400d4400e14a1483c01c4d41100c640c00c000854403920f0008a0400300024240e8021406600c3d80c40380d00c0280c21080313075240070364010b5103a49600e143c1d240700001d8400381c1e40c0e61040000400e01c00650340300e07424984520218519400010000716010040c002d0901c1100050140410f00344070490200012900d144603442c0114189600020356505005066001c2d40103580c0c8070480901d54103213400c00a01034040340f035528080528100310001c40786031800c14902203519580240c803180303081d20a00a948072425900d4003c0c0a003250101032240010b0000b010152801c00302c15441c1e50500011100310403004028518051920b01d0034004039600145041d4480a145500e070558030103030001c100900602d20000940b007090b40400600c2081c3d00c0f0800c0b100700204030031540c4140d581c50100020668640340a0032980000000c03460700d0400750440c40c01030039040d500c40c640e000c4a54414400e4190900030500248000c401c2c081140361009070502c1c03a004060081c0031071308010920f207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 582461600 1250 582460350 582460363
    0x16030e01060f17030c061306180b0c030702070305060c041a04030f02040504080d0f0903110c010c0605060609060f040504151d0a0e010905010b03010c0c050703080a0c0b131a0702 78
    0x78180070400b1a08030003d8004104943c130410514040d41c0060170401d03514148100038020442e0400e081404140c103084507101c81d180d045400c40c64101040c0c4449059a24541c005803120046018010b40440031560401107680114038603030001c1c1e920b074600b00c2440090912100c180644607010081003010556060000341440c0c0c04a5002505480354640300e0458030403a2a004e24044c240903449c425002a170380007608250090726510500207000d405151a400c50b6144603020901800550021440b280e10003940081c000d070016103480c0c08440040c480341c011141035400010005818082420980500c11412940c3c80c0d08c4181c040c1408010324886030000030b6406865400341c005009100ca0f60404107060fa9100001c1104280340d08000d0301030030907820710318029800c00b84910711161103140304120b51904407001d04045429551282d055a0041440c1420840d0044440e0081480e04c43c2ca14011080c0140f0480e4400c0180ba0413202589010f0000940032001010048265004a0031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 582462850 1250 582461600 582461609
    0x7050a03020d081812100c0203090a23180a0614010f0509152110030825021017060109030809010f140d0203010513050907050d0203010e0616030e01060f 67
    0x15a601c0b4500400301452404104c1c00480d400403405006800590001c5000c15000040e144180580060341800784d035680708a00e240e40d00404625001c0245181a000306100c6d03900d2210010720060703124000a21540316800c1086070701100005000501d40e0610a074801410480c1c07081302140c503210b0019000b110612248414400001285a09962064a030786c1c0c44240d600c05464072024281c1c03000044140c5010b00b190140850000700c0c0d01d0050842d46041203c0c1d20508152420110b84c602e142111814032001d034403100034201807001641c4000f803029101c107042c3e5406050006c480091642e280f405000c06060002c014801d1000c03515035401c4801d1560213003084066110031802c119034407006030280305c08181010500c01040c14003030300154125003045072908120311441a9650480304143d46050305035000311000c1001c0e04007565080c01d45800203000090703940e46004030506005040350201c82103c03450303200e0a24941c00d40b01c0c4a0f80000381100800c40c59043c00301100c440f4040e8047c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 582464100 1250 582462850 582462863
    0xe07020a020f030c1306080c0a1412100203190b040b0d0318081e0705120c090a020904090311060a0c08131b0b04061205160806270907050a03020d 64
    0x91400152404c10500d5045100034140c280c3c07142c3c09050f1080104058011000507007c2c141c0000c0070f910342080040c0540b00030020184070076000c1010052994070781901080d880c020380110a03100040744c4051446075104400c90014809040249000c03500b180740500d11071880c0103c4c5020589402e1844840954141031180010031120854807011202c2d0f4802c410501c2985081d030013052000c60003840c40161039045030482501d4604200042d003001600719080d82c01b6105000162510010080c0c01c03842112005140640050120b0159004110140c2c04200710403007240c3c603820104511540100321110410500d14aa10002c000d42800f070001e29049884500042c05e00140030404482c52444c441200c1d40180c0d00d46410301c85070000d10401d03011840340010300302150454000e280c40340e200c0345000401c084400b9000d0780d00c9000a006260041c0e41002c900510342500385082c0b5510071001c6640f40d051400c4884c4d2403510896410860080300307901c40c01c000585035a518042040e81c400d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 582465350 1250 582464100 582464119
    0x80306090403051e0405031608030708030a0204030c060806010f03051302040e030d0203040c060e010807170406060f0f03061119050c240103020301050f0c0d0905030d0f02130e07020a02 81
    0x1000c0701c0034002c140c0b600c198100b40c0100c3d0510400c8000c0200102c44003036065507400238a12920700d84114a501c5001410742042041b2800140010000c0da404240303400010700303140c4c480c1c6400c1b42c0d01509400440c04501c03001c1c00e011103583c02034138000070742c3d17690b28041c44245030000b03883d40647c1c0440c0f0001e000300c0c2c0700c40c0302840100c418416901a0001c00300d0843d20780c60325041c1880710342064400c0c080800e07a107041c442000c0d4450600d4910442054031891b040302040408407612510051003562507950f41c860105a507011808180000c0100c0030f0030782d00903030035130420404031080294400b0140004010440800f2844080e07420a0070700e6003000d5407201c1c9a00c01550400c0d06080302c2083e8402c180082e8401502c40b01c524a059038000e40080056070b482201e10103030206c00b0b56480542c1c000520800c42002c0c03850300503ca10a208406481c104410458864252140e41c4490b11100c3d0f0081003048035140440a54002050040159015800d000d50040e44480742010080d00690020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 582466600 1250 582465350 582465353
    0x507060e0409020402030f19020a0e0d02061c0e010e01060f15090e1303110a020d081303050102190e0303070809010336050105070906050423060d140c070803060904 72
    0x1580415030ba66000340c000d40d6203240904540c00c0c1410211501c111621a044c0000030444861080d200d04000c035840354002c40825008010b10b42c451804100c0e40030104008510b0401c0c10341014655440c0b4090001c1140c4240d070401c142540e451114011071a031504104009000800c0001403c035444480d80c501403005003c400c450300304554001c1e07100482c4060511543d1501400301c1c2d90750500135503074180da641c202d0704a0741c0c480e009100b01a500c080340307060940c00b0421b140010b1100c030134a03020410b416907481c0c2d501170a9030411411641603440d100642c802c03060f048040d00071400400c0700a545008020745d22419640a13111510341010b540304810039149031a101c07a15560b9403540799405240c241d2400001070b01302c2c1c010341102c9950030702000c900014014000707001901c0c020740300c0c1d0381880e0130216070681000910200c0b200c41c0f9203a0344a240c1944400009000d060005200803820800300b120084a00b003014006e1303d92000100320280100380d03080156504200704596400c0c1c0c61f01c1d01d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 582467850 1250 582466600 582466609
    0x120a050a09170909070504080607210603140c0a0e01090902040603140303060f040216020103180c030c0824010308130503012405040506060703260709061b0507060e 72
    0x11580c0050080032240e1070010b060203000701801c25001e049804018540d20f03400d04440c180541e03c280c180035808840407901c01e07030148202440d0b07102c0e0101028003144000c1c011205072103480c1e10503120313083c02c2039403c450054188500700d1064015610314070394914007414031140d00814400c59110a0f0340d0580300c070456442d60001320007540c00c041c210021030302070500300b83ca80e802035a10070f220300c10b6024001e800382058026211400f5008540450000b45500103501070103030110310300507051407032800800041030b16081074060b50182900012031420030ba91a85410101a06650368043c452219004001910410790649a21624098813094026400c000221081d00065455401c0080036080000c103c80502e0080e251011246100e41c0c3c0d500600080701e406556a43c0c110a0420151011034050301408600c040700c46250192070038051040c0c42424401d40d0720000092070090704000f19540455120100440161208010661a41c5e035a60b110300302d00c5944d040c40380200c2c404910381d44 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 582469100 1250 582467850 582467861
    0x90b07200115060206070c0b060607081201080a050f03120403052107021b0d0c050906060d1a010807020c0d140f0a08040303090b03011202091503030d060515120a050a 73
    0x1440d100034002c58030348a40e01d1411024901600005205080000d0121442545141c00d6160040d1184403961548802d1040f0355002a000f610003950400440d03480e401000c2c545c42c000d00313041010f00043d03800c0b494658141189060480c00790750003840a884080c580c0300481d508180e140c02c0056480500d41c2d07088800b1042c2c112070200444a0b0810803d507143c01003850441c224030b40707415a1030841d0760410021100040c0c907020703085002c688414000350411a84041d00100010607403070a04502d184040c00343c1d0b044502540385c0f0a1072003403800943d40c02c03010044c0c000c1428000303014181140c4000c580307100194400a0510894007040c00c5d0215014407942d446c900800c02566902c040c11304003002d50780d020344011000a00c0d540c00001e03940054a050340e0503180005403203091701d0744917001c00c102031401a00405080c0018207003210b03613560810040c1103104070340c000407030107134586020084060702000c45950060320401c01d00e07203074182e414a000d500180030200094940c448469000041c01d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 582470350 1250 582469100 582469157
    0x70f0204050906010e01060201022a0f0f010903090e0403080604050c1e031b0406140705030f030106120b0a0506072910030c081b0d050a0c27090b07 65
    0x7450720050000e034007004601d05069038290070000b4000d0b683e03800100d00702e205100c18101c090030300c40d10312081b140300d0403e9a0011411141100c048040e0650021706000b45882124440d030f43d100d2001041540264031603005203a11001786105240c55100070300118802490107200d55521000100015540425195420303002d090380c26603140c19000c40c88843c1c5c41a40d8408414138007140c1c0d00100003190003210705907041962090840d981062a205aa0b0441c4500300c1c2c1c01d01003400001c0c03030218141c01441c002c16880d0360303010038113082007000801c03104010b1806004880c491030a0045880304400c0b00d05c92640103180d0100c0d01c010400580030200f03d0405110340d010990103200003040091a0782040e070340601c040541483e5501e00080e03952022482c4043d002c1b054850601e1180b0f45903070000c4070301e8050002d44545032002d550f140e510015035000302055210500e091200c00414608601700c1f00c2c80064100650360f419100c0742400c0400400d401c003040508880d0983d12100c4550944021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 582471600 1250 582470350 582470359
    0x513021c1a070c0203010e06010f052e0503011403060708061e0306010b07021207030510020c15071d031b040b06040803072d0f06020306210601030203150c0906070f02 73
    0x34140403400800018000f01c050f4429800d21080344a40e410108083e8103c840505d0700d40c94849c85c03d01888a4020704c40c801d0030f5005d403d01314040014400380c5403246d4800295032890f07641d41c1001480a402084e11260038029446801040220740d040503103c0c0c0c001c28200c234010180108030106e000e19014210415415010728030000810032541009801c00502c01c580d50344000f141036160b541c2e03d81e9030b40b10140ca940d100c070f2030719440c0215560050406040c220103503540c1c41c1c60b107400414000001c1e140300c400641d104800c040303944010300e5210042c0c40c0460152040000040c102d440b03070200c0c2e00c04680b080e035580c41c801d0000e941e007400719402820b400064940701c07003681c01c084034880000100c5151300920700d103400c0c40001d82e000da07410380c140c2c0c402052400b45410342c880c20000e410082809402c0501715200c0300d02098100c101418850400c0005c01507907040d807041c942001c80014590342d4002c1b101c2e0910003d0f100350003d0703030440c000c1130b10071303e40705c2d20700e400e001405c0c00b5001c001a410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 582472850 1250 582471600 582471653
    0x30405060c01020d0b09090d0e1c0f0c0609080a140312040c08011508030d090303150e0a0c050a0f0302090f060f030405010e1b1e03030f030a0513021c 66
    0xe0101c1074016141c480c40c0600c00b00080b241c52028410720003800c6418840a800c1902c2c10300d0300a01038844544200800f4000c282420310302e0480c403601407020302058a0803d40500c000081205030442040602624036240070950301e80070794a0303540c11005000801400d0100308107100c1c1b010810680e1040c0424086049943c102414581c0851244c3c0c050400c00b54240b1030884030314810a61030301c04481c24040110301c2d0007000440407000300f0880e081141016229000c0e903601106c14100040680b04628100c08182000d9000ea0200c074800c840b04003e0002c00d00c001000c0c5a0000e000c4503c451440c00d025a6451001c400600903000d200501684a100890b000001101031009144101d2040c0c1c000c000b1446c60144140da6442c02c803085412140d4180c0c184090f90514032100070b01c2806c001240d00b602070114000a040d0b4200b4511001040e5021003000f860828a0141a401002404015120816070380105904600400e507444914840409540800120380c0c0d05030380170a50300300b00e0700b02c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 582474100 1250 582472850 582472867
    0x1e03070509061207180c0903080f03040203010e030a0302210603030a1d060a031b0c081c0b0d060b180603030307140c120d11031e0402031f05161d0f0303040506 70
    0x1910f942030712002145d145805040c0045038052002031003036a1700800c2180c1003005040c0c4c032811641c0010000c9030195202c00c50414400c004002510401c10302d82c40c0907803111062110381841c015410307040803104000c2d00500603a41c501004031b4510f410607107041c016507540844038020041101d040542c00102c002a6007600592551010307034003040002d03100d001c040348900c044564601250014045d10001c100500195542c00c18003400c01c00074082c003203410030100c00003509207032942505446050701d4036009103561a04506050f030307503802c8a5515886041046c0801e94a01000301400c2c1800710b81540b030140c14580c501542c840030716000c1250140b480e903048c10360a0790840800d04540600301031000d03c542901800352481401c82041c4030b001c00004070f4000600402c041c2c41642c05004500038500303c001807420039901c8041944000c101820036107000000845088002c004012803111030085400300e01c20708608c608001c9a02080c60a040d10020b811440f65502035070b40708070000307404c51 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 582475350 1250 582474100 582474119
    0x3080d0c110d2c03062208030c07110307030b040b1b070609150204060203161e0b0906070c0201020318130e010b0a080718021309090605061e03070509061207 69
    0x240f0310701d00d44000401c3c154000202c20f100b06048616681c1c160465000114415040c2603509009091100107117000346503511104402e80c0300780d40241400200281e60384c14841c403526850115007054001307083c0ba61139031300e8880042d000900010040c0e214480422a000880543c900b80700c0800c10324182c0c0e8000c9440c105004200000040b035101e0b098402038030084985100783c03001c55a80740c000d94503003c030184180b0301c5a0b481d02c604480d10100000502070440345a0810075030244969212891400c00c4c0090701d1602000a00075400c0010302c410507401030b6808425140c00c40c2d07055610b00c0140704040b000685039442c44440014561800644d0442c0300c138150002107491400703075190440f45441d41c10107601c0765414050070750b2840d14212212001001c5900030050070a080b0b01c1c003090a6121070840050b01c103c0d01d0281c2c0d0742501d031f8090100e5480d0041d004440b00e2020803500207410074400100352651014428640f1804480740003600179202c180d2483e09440d40c0600340c030f81309030301c7d01803c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 582476600 1250 582475350 582475367
    0x2100504121e02040218040b010801060f030e010e01060f06230d0e0f010c0507060506090f0403050307030e0307030c030f1106130203151806010608070e130f091214030103080d0c110d 80
    0x180b11f2801c0001018241d40103200d80c9041e18003d5440324003881d80030005074060443c10411041641da103100c0a4103c036028030580c40070b17124110f602d5010a1510710f0080c82c03071500e001e541050001514010584482040c11151058500c0c41d012400604c800c0300076062107414110350b01c0650a2900102c40c0551060090941d14031070902000241c9429051003005541203581d0480100100d001c900031178040c1c8081d6a20940601d00412206845907486013142c100f154110085499044c0c254101a01706940c0d5600d03500f83e00d480b0401e000070302005d550b02c0e45c011346002c0721041808000803e6460900598004407010f140000450a0807601207000e10203150654a40e0700984d40003150991183d48514011055030383d07081030350034001081240c05072141007407d107000d44e101d000d0710079501f1070702480c071849000300000c0700c0c0b0007894070010f080a141d4500c0007000c040b04000510000704408240d490980c642c0800080240d5400002e07522003c00000e1400584583c1c560200ca8a5126999 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 582477850 1250 582476600 582476647
    0x215040c2303030706020702030f03070f06110306010c0605091002030c03103c05211b0a0b0d090c080105151f111608060402100504121e020402 63
    0x4941060703515003020307003240320745400c00350341600200082c001190050300900401c2d40010180c5607036400c81c0c1c040ca4074562203504102c81003040201100c06116040c46180c20030f150000c0018074518107070000901c8030340a00d45c010440b0b41d41d00b000c220f028000b000780f00049294080110340d641803100100f081c0c4c0d0030444103841500303000e01c1d000c1900c0a00984d11449941c1c403040c225040307040081986958100d09291901c2e80145036000241e5aa030400d40701c81540da10141d10080c818044500d5046c04821400448055118100484aa00c0340b03d11a400c551038210704030380780c48030761440780007820b000d02c0f0162500b102458042185101948524014100420140c58540075042400306500c01103804459440c4950b00c00d840e40c0f802032206800c2150580181c400740c0b94a640c1308500441d058002c01010740c41701d001c100c1103062240300c242c0340780300c641881c500702803615500768201592120001d101031840d40d00c0310090034100040209456000304150346070600d00b09483d21101c405940b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 582479100 1250 582477850 582477869
    0x121509021b0709020405150a17070305041106030106020a14030d1d210f0304020d02040204090b010207240f0203250318030203030301060309022d01080705040b030103120215040c 78
    0x2c0008241e2090702c00c40381110805040460001000c0380d159107030742c000000c40750502002c107050301c88882413800c425204141c0f80c5c0700003072907091609280780300035000d9115034040c0a0800050080540020740e0100c1e1035030003003070485003a41003d0070038118042e042216002c1e5091400c0e5403080c686c034a204680d01e07000c0324101c03040c8441c41a00c01039650501804082100d200f0081d100790b600d4800000c42d44240003901b441360184080d40441c0883e4003582c010600030740e032551100001d43c0c0c140076941c010b2580d0003003109104803008000c042c0c40b000c0e100c071400f84400600c40280d65070090042d0b036071311010a03650b4911000a01c02c0c42442c0e42840c4004c90015088200c0445000310441003601520b4014000b5400d5078202403064004000c03042e405c1c0d0380010703800da030034002d064040c00d05d03c001001c0d50208260b10040c0400901060b2002d0414024803200f844184a50100d210a4904490300003080840e10404070000343d0a003c0d46c441006000d2210208201c00d000c4c0384200002298100741 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 582480350 1250 582479100 582479113
    0x12020f060f0103020f1002012d0c020a08030601230301091a100804030e01030e0f0307120c12050a030204031b03030e0a060206010b130b04060201050f0f0403121509021b 74
    0x5041e401c24182408000c2d400340d009841083c460822000c1d0003180c0c0610300001494a55510213030800310b0b010300541d283d140d0380d40400c465a03440c40c001c05940036550b000030b0050b2016540d030320204c0d0000418941c1042640d1000300503400011802c0c64500400c80c074056030700d507100c84180003e05501d14001c11445210005c3e4480d0f401e2000d0b400e0100318081c0d6a81030183c94a903404c4603011000c10206040503203c03003c140c00800180070718650850344100456486072103180c810b2030826540500d0050000540380f8002168800549641005403803400c01d90750700d01c03482c0540003070003250030140c003c1038110740c4e4588066401124009480c029103800107200120800c0140c1429603003d0180140c004000412501001a01400da0902040e07010130741c0940b14102260990490740c08031006039100c03002c0c0b01a012500800640008203060800340920780360720092301102c032811894403603da49850303d5645000e0007480310050410494155522004030320342104846a00118080703500400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 582481600 1250 582480350 582480361
    0x70212150606040605030f06062115041e051b04080a0b360a02090c03010618210507091a040e030a082e1205010b040c140d0912020f06 59
    0x1010750f4111407003070b03903210b18503a0b0704c81c04984d892002078a20780d0085414018100340340001d000400351a0098041c980491a080a113845100014103155015034900704141441140541c80e014003098035040108003600d4039180d066240200b0a140b00a00c070001c60301284d902e1001c1041410b05004000300809501c5030b10100208001781d541340303180b22101c1251110362000c0c944031840f2041c19401034038502c11440d00402d80100d800c84440040c1d020020040c88540d801c000c000c0c200c0c0740f960405055490074244035624000702c0c908000c61440410f01740350104402048075101406083c402404403203101b481d91002082050b60b10f0b84558140b10182082e0b07007001040c5c0761080c84550341c10030961210309480c0e40007000340c0d072201d0b004002e680303028220742c000601c540300034030000c03111401058213030500d035007120034040c00644998101135040400340d070302ca103071000c15000404003190340340c1c1e03011640e000034060500000c002c2e420b4940421882c58001c01d00f1101e0030b60800684900b550382 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 582482850 1250 582481600 582481609
    0x70f0e040b090d08060d020a08010f06081c020c01050304081b0102030601031103090a080703050f0f0a031a0f1905030703120305070c0309090908040801150810111e0702121506 77
    0x2d00143d001410907000504189031043d176400070680050842d240c3e0548500b02142501d0310400c4180c5059240c103c20440070b80d04100b020144801c19556100c1040110b030001d448103800a02581008004070114080c02480c0d81110400381075003046428114138181001d01135001160000c1c0480c3c50700907118040c60204084912460410b00070b8802072040b50713183e00107a0480b076400e070304018080c404a41d61201c03003c0140140d0035502d95058448020741e000030103890f140c52074180201e00c007000c21405a01e40c0aa0400c0c1c0e007101f216440041040e40c040f0148100041d8041603051007141c10000c01d01890030944902101c1c6580c09210581c3c1c2d83c00e0a84142d000260010000b8140d003008004c684015480480c2d0f09110315003051030a5a41d20605080d940070b0061000d0200d0500410010100200403401080340d1002003030041410042e8202120f00071003481401c450f00d00c920280030010194100e80382981e00910600d208001c828413140e5802481e09000128000280400c4403441e2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 582484100 1250 582482850 582482863
    0x25140c0a0503150c0c06040b0103020f0109181d12180603070813030203041d07021506011209050a08120912160303021b1e300c070f0e040b09 62
    0x40980140801020401d03070f00700844008081c2041e410b41800861500c0c101800000d009034014613485c0b000b9411070040000f0311080e5020389060240b82030782088482e1300000f182441c804001400a042414400c0380b480c20889014500200d004200c6000364031032021f000384c007000e05402c92502409030310105000c0c4030310040d0750103c040303406040041c81c00038520022904092082c416a41800c2da6240840f06c003200001e110001020030000b0020071359810003812000a500d840000c06c10b0800c0c5001810484101c9100b0420940750780e00d441c1130040400c0b090b59170346c1c2d00648441d40c807400705902d40c5d8068000d0701c900340311b402076039103520480c2030f80400d8902c1c00c8a0b40da0000620314941d5000e030000d601ca0540e903044800c11520b0b03036041d105c05203c500654108000b04038520300031643d40700c2c100f80f507001c0c600080b4030200d114900f0800c01d070301c00780459628070b030080e60340c0d0281c2d00c045900d81100e41c1d004598849002a0204e42d01b19062a2a8000d501c240089852500d03400c1d41c1c65151107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 582485350 1250 582484100 582484109
    0xe04210f030b0f012316061a04140114030a120503070f020706051204050a021011190503030c130b21010803030618180f060609090a0305070825140c0a 66
    0x40003040700c00c2c24400d10312041c5044001c00e042c5c181c54601a0701001d100100816000d8481d50fa0300d403c10307284440121010680d00b10229004c0000c040141d04100d2406410b0040300b240c1007001601c408261810410301c0800c94101e4800344061454001c02000c1e0751044681c1000604800b00c2c040c1e40134000105801070701d0700e40c2c86442c01c12806a400140c00d62004001b52071511a800c03042d005600c642c15207002c01e00c42c40c5d0340c1d11856015014110b182002ca64000511088080c40c1038003c5500802503179001080568243d030340d00c115135591041c1c9440ca40080c905010001400c0c02807a10441550b0b103c04101441240e450f82e881d42c440d074982c0011a00e407908007000c0a0314540103c06148516071014440c80e181e08846080040b8510f407101005082181d80c1c07143c011302c9074615000fa100b44c1e004041d000101603504056800512500030030303c1c004c000e0140403640d00301c001745014450031f6410300000c0f40305c08c0800d51b080a6020003603100c20071945004d08403612010707040080d03951003600d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 582486600 1250 582485350 582485357
    0x70614030a05040c030f0c0314191101050702191e35010f36030e03010915090b0c0414060c070f17010c020105100e04210f030b0f01 58
    0x658600c01c640000d00310082049801418200000c40002c0b0011714400410f40282019144141513150034030702880041c00c488490b07400b8030074400700074000721404018143c0c0b00001c0300480c061400103070b59a02070004d00030b40c0f007214140c40c40030660204003404101d44040c0d400301c090701c141a40d00b000c40c0265005843d4a014001c09000b0100c0c0f40d50401501c140c070803404621150840c240050849400c1850800d081e038403040040c200b03095141c1e905d0000964110315001c9044075044161850074030590086c148281e1108071025a6420b41c03000d5101c1c2d8011075085401c2c410300004000919124030120b80e2090f070100811400030740c0ba0309903000d42c1d54134120000c2003a08101040102d810501c031400c0184070b00c040100ba00040700d00c41c40c00901c88000c042c1c0c150601c01c10200d003510f03140c04900c006c680c5864108140e1001d0f2190b00400c848600210082ca915242010031509000316010840ba5000c00310604000d540804501041d900d90f40e8104030300388241c0e042000400316880c10030b002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 582487850 1250 582486600 582486607
    0xa030f150509131b080714061b0a17070b15031e070801020705030406080a02070c090239010c090305100c021009030906120203040c0306020d0b060d060503070614 71
    0x40d414103091081c0c229540e40c42008848805588003604414a140080f00400344d000041010b08000c01a05018002d0025406081c3c158103001c03460b41d00039401c003110002410452a2a24030007030042180c6a0b400c000da49040c40c030310000c0c00d041a4008041101d4071102000000c10b0780b14030b0440050f012030003e010749050040c5240c508150000c441c81c800a9014000c80050005c40901c000e01c0f51510a0010756201d5141c1b601c060304102d030040001d611903004010f0480040d030071144a4013030f241e0000006032206448a9000c0c00011036000c21500300e03031042c941d500c03a0040d030026001c0c61742c1031030001d001c516201c090481e40700c0d00700d1000034110343c402103200c10320003000d030001e0403850528411252079410500181e026108003001c03d80c00b16903c42ea052100350342c414112818402080c40030361950070969980700041442d880007905e020b5000c901081d00140e02c0d0403000701200c00500f0545c48041382d0302c8140c000c24051260600c03d1241890000c0c1c42402200e0000640003480c0c0110709 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 582489100 1250 582487850 582487859
    0x5041b0f050c07080d0f0228080405040c030605030607030207031d01020f060f01080601060e0d060f0f061d0703090b01330f02160f0612060e0c0a030f15 67
    0x9054040d4800c640500c4800e0000c51082d0354204080301c018250000188045824184064172001c0c605003990304540001b0b02c00c481d0482d504c500c016110711403a890f440e0b5040141002003860049400007079010342410341070b000c074030350542108007511000c50544100f41c0b01e03582e05900324410303240010081501201c90304004814921030740303002c10041c01510401c000c0440d03000d091031012180301c0300300c4403141c0061242c4881003103500c0c05043c00d4140b041151030003c0002d90103a044c82e00c000c01407074541220b0001c150442c0c00190034402c8404080c005580c82d034442020310060b04841205803c4481c0c00182c1d142e1290040c80c00d481d800103000b08243c1d00f824800100c010501c003c40241c58007c202c8024a24803c0031a0300d02441155540f190052415800030b00700003007890f03a070003c6410510705000d0981c800d4000b03000c0300c4290410300e07404440d0303900887c06001d00b6840741081480c601e04003d400703c45600188180940e40e981001603a032100110002c0340d00c03d1003140450840d0280502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 582490350 1250 582489100 582489107
    0x80306030c0904050d03050901141914090c1e010c08030414030a031406150d0b21030403020a060512010303031e29060315010503130f060c080105041b 66
    0x64110001a054400d001038070000704440c03100540f0304440c030703500110705480101d505228103030b0002403110080c0070648143c08405503984000e800409100e1100c8200d091040256202e07a56404005142c0c032103a1516040c002d89402c0f000c0022030003081c1031101c03503043c18000404002c0701441611400c05040036521041419080244121010f1541035183d10780102e0400150080840660707003c5180c0c20549455409c0c0386000c0e00b05801080040054403408000301d05442451040d541d00140c504600300000f4540442007608108160040404004004001c0010800d0300d0080c0c80b20200e1036a2520100c680b0701c580d1080310f500411410050000034403a800003c0c0071441d0f0024101c1d41c0401b960b0740780440381d40c0c000c401e0000d401480e11841da5001c01c82c4200706810100d808030b080d880c0500310003004030710050a80d8104440000000c0d49010b14003400391070340750084107852801c400361030b06000412000050700c0202d80c0032000001e06203400e000b42e40d036254402c400d881020240d8a4181e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 582491600 1250 582490350 582490357
    0x603070516080f070c0e0f0f1f1701060509010614030c250210030926040f0801140a0c0c0213021e1902151306110a08060109170a08 58
    0x141c4025061100a2021560002c0540b4089103503140240d69901585801480d4070080d900680a0a41c51010040841b0000481c21750001c603442c0c6914490f510034416502c6800c11085107a0000c3d580c0301c0c0491044081d0414884480003036008002c0c0c15164420400c1c044002d2040f407000550140c1c806048500c0000a940c014a0b00c00240d8140305565818002c0003000641c201c019104049020017540303082e418114a0741910f04040080001c15110058102c0c180f445203a2942c805402c46084040030000f140d000b44003080f0400700b03e03911000d4080c080c0c42c8901e45205102c581c040812200c2c0a507210b0307100420820780341c203428a031190f82400450441ea00416031508d600b403100d8408030f80440e19842031280036021580c3d42e49002c40b41c811014014081303c80856110b03915200c010011190078503004036015200c00503030112031a01601511700702d402992a00b40202d290742c0210f411140c050f020314026260171406503100d014180c0d000105d02013054071035000347c4080700411001d5008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 582492850 1250 582491600 582491617
    0x10b0d0e011b02010e10150e0603150702100b030c10030e0109020a080c0301200f0c030f040e040506061905010f1106011e140307182004080709050606030705 69
    0x1140c076590a102d02001c0d1500c500c03040d00580d4540300d0175485076609003c041010401c00100b002400018112004400c070305000340880c030f660000100b10166020015000c0b082c40803450003900380f4100c24001c4d1160403880c807440381d90b4100921981d613442c01044030b003010000900740002100c00340c50110003900380c11507440b185541e01d12040300540c907082c4400002c3c084020081c503044054100781801c40d030b900885485d0b01d42d06036151510039180d00e030850303500c00d01e400c240c203480d20118000d01d03003507101d01013550f41030000009000914205040019102e036000d03d0503290641e4a0600b8044044c0045803110752112585070184625030107621040700d450b0032468500800001d00102504d031240c00c3e042112502e1103c118442103c115416580280443c8110041c2c0b1070f50220120307030b03580018000c6203040714840f002401015090307844160000003114503d4070480342c2c54074811040d03101c0d01650989008501001c2808085405a10701910028020783c5c915611810110342c0b41d04100394 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 582494100 1250 582492850 582492853
    0x12030605060d2a03051b09060414060d0501120b01080303070c060e03040806012312071503090206070303050103030f020c010905090703060f0f06031503020907080405100e030904060e010b0d0e 84
    0x1034a90043d980d40785800d84441d03880008060070252218580015840075030519800108581d40c03894a80d001590700700c0c0c26900e800c480d1202501d0000e1518000d1210b11428036290000000791150030100350f100c402d00881c001082a40c882140320344906c0129851030216031541e407000d0002e0500e501c104002000c04040d681171a0300d8907074150410b0b200380e04c114042c1d60040d84600c60f411410b00355444894045a12009038070001f03450a0300c0d40c182d48120305000c04200e00d21030a180c003c1e04400102a8002c18042e41e52a05203070207401070800780410b0b400200c0c419008004103000203005050b90405848510b0014903200400200d03000040c00082050303111300c030010359003450054400141c03503140c0f0450300b11070400d0001821550004ea107615070b039001d17060820268641d140c4594015016142410700d55490b4100203140600441c00042c00b41e00d068281d0b200048084083c22400004807018030480313541c1d09900800307803801e024046520100304014a951400d59105070f45442d0000d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 582495350 1250 582494100 582494141
    0x180609010c1b0b0a0528020601140a03020607061401050901120605190603030903170a0e010c170301080c01090504020901020c0d06060f0b040e0f1605070203030904061212030605060d 80
    0x1442880c240d0004841e050200f00b012410361400182c0907aa050038912003181ba030002100a0002941d464040c0b041015500c0b1503400034156440d0607070b580c070141da0040d005954480c25442d2032001040c690310800501c8407154000f01c2e4520f490340c800d5040300c0c6441000d40345c011a5466071002450040c0c45120300980040080403040704501501c001140681c40301103881c0c4c51400c00007122003110100000080d020003840c400c0a03001109584500020300e01011464900e241050154000b00c0310312101910110000580740c0001608800c0300c40c003a070fa44000d0a58500620040e030058000660240c1c00840300e102d11420403003c5411200e01030b00011620507950031041c07003003800b29040301c80d42c80b50008040c41850412000e0381d42002301145900700c41e240001c02003245031205201c00741007140000b198019581d040064a00000b00140100689642c0300d000d200020041401210700c242c5102400b05603900a2041c04100d4201425a9140c404c286401b400103006164106104082f00d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 582496600 1250 582495350 582495359
    0x1a0d0501031a1501050a030b030c0307030b0604200a05070804090507020304091404030903110604180b040608070f18110a0e0906120c09041403030903180609010c1b 72
    0x2406440d0080d40103400e505504140410070704072008006005400114940c000c051a0743d903c00c040320154169440c000032082c1c18100004d007085c004141c00da9151080340d10100a2111030071000780503010840f000c00c91100300e10280b003035030400b04025000302c590a000070010340d40600014121644180c46c0c1c6817503c0d448462050490740c0c1581e414005910126040c4801202d82c403501250080d201201c808501d040d82d4002e044449500000380301c0d000910303460250340c8440c001e580c0540f101140240034142007643c010010300c40031829600c19400c1c0b120004104001094000644003941403005880341400040048918502d002020042d81c03140400402440d41c1c002c0c0142001c2581c0c3c5604240d45002040401070002d8040c0f8441e10075044e102c2d80d4440001848000c3c024141c2c0d59800c43d0b541c1e410b060b0900b0b543d0003030b0743e01c0c2800300108200e00800044000c03c1c2c1c0c039100e071250030100c2c040075040c00500d002e8400c80c50b011988114000b03000c41c01031810710701400c0b504141d040b515502d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 582497850 1250 582496600 582496627
    0x901020307020307090c020d0519120b0303070311071a03010e27010c120605030a0b2203021608011a062212060e0606011b05070509070503070305060d0c1a 68
    0x4070344c0138171741107940c45002c03402e860b5040c80f2000c00300c1c41c03a180942c20815409000e150300448840c20380c4c00e0100c4a0714440d414105074001714503081c0001d040d2a12039141d4107016206603800d440361807160154100c0812000d51028103400c404885400186c00c503824449a6100c035140a000746201401b00d80c0300a1003190341d8407010f04148101c400200b80080944400380c083d04d031890901d0030b040e0a007501070041d502c00103581c2084503001000080c41e80c030340c0c0780a11165107a061076000c1000d0391100d00300605d600060308040441c40d0041aa00d0259252000c03404ca0782d00c0b00564114103003602c1548038500d0540007038408551a1650801802c500310031540d804021035000007050040c0c0101c030421b0211f584550048003405e4009010700e40342034000204103a52042e131400c4218070000e50b0805002040210501410019180e0000c0c2d091540016250381c10440d8510700103030420f4002112070904990307111802d5400130700c2d81d0965061081d55581821145081800741d0310500100d842d0004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 582499100 1250 582497850 582497863
    0x120e06160509041e0b040605060d0b240406021203040b13021207170c0919090c0e010b0d06060c030f05030a0f1a030c0d080306040911120c01030605030d09090209010203070203 77
    0x302490650070f042101422003041c3c4020144003880340703243c0341f410001501c404e0211048030f02c1d003d4001420100300d50004890181c0b95995003812045000d00c000e1011105006000307039122602265031460001c030b460100f52000300c034001d00340c0240d00081100c81d0403120202c1001d0b403005182a1071900007020403460407020351b203d401c0d00c20719981a8004500e040c404410480000d403100425403601d0341c48611190328800304280e60360f40c0d5940300018403440c0700c030740b101424140c050000380d0f5a640075a4285504070000302210107181800024546008400c1044c038250305031507c009140d5115810b407802d1304010009181c1c01d4444280d1495504540309102c02d1002c032400c269034480000d420700d40381c0101103c85501601c240c40c21800410022000e0f603620410840380802c10007179070b141180c0038482100410b604071000340c00d000200301e00410390341350001c82031f602003204540d110101a902c41c480449030020480140040c440340703c06400a03c0d03200c00c10300442c1c0c07500c46c0a82c0130034507015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 582500350 1250 582499100 582499121
    0x11e03111f0207060807090609050f01020a0c0602070f1203120e0f010c0c14071a0c0c270c1602010810170703050c0406180c02070f08070501120e0616050904 69
    0x208010f01c18090302da08a030903250410b45c3d40c80c0400c10f50b0b051190142c160801400340520032604018507000030381c420800d02200c1d40e0301071300c00f494582d50340801a54900460103107540141c00a84085110010301c503e41035010b8155031032082e0380030413504e107a005140c05040040765014000c040b09500600740641c1c08404210703580c1141c90003071810094003880f081b28108405030011082084100308a0140a8580d0340e6111090b5440300035680840c40c085a40d00b8554200500c184151403020442a04120090409120360802d9440703150301c00c0184552810070314003080680c107440c00f5520407500c80c0c0d44001c026502003d2283ca54260101450703982011003070544c0409424000c1010a00c100c400203031066400303011280c02c182410009521889110101c42c2c2c1d140c3e00702c00303214401c02c034040040c481c010030602d4140e1190046620360046001e254003040149002c1218421a40720b24403451000170054003064452028060310f0b5640340c80e03044100a8244070504556980c1e1080c0b41654 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 582501600 1250 582500350 582500353
    0xf010503040f06320c0310061214010906090c0f02062d090606010f09030203070e1504050c0a030c091d070c080a08100501020313140102010e0304090e06011e03111f02 73
    0x8002c0d011010500d008001c05c02040c010090040c880c03108000d058000681c0c0907810069096021070980308000e04402002d03c0d1080303042c1000103142c5845034031030300545107154401d20542001d54029140e032040c541004006902000000b4681481e0150400010200103410b1150400e000c20f1040c0000c001d550b4512581c00c03d109205030b640e00302c100b207507240c3c81900b009a000c0d4a584c0000b9281d50091145524045118000909011070401d04d03403031011008008222500706071520300100e800c02c2508402280c45c003082c90228500a481d002d0864619140d4162014400c440d03d1070000006000c1100307014000c0302c1c01000a80d0480546410f0368181c1e03070440903207401700004100039000d03481603066400c2085042d44288900f14820250341081000b01e0755801e2400040b801010503c00b641083d000102d00451030744c046820540c0d0b4901c01c2d00407251070340d0f21041c1180208060720003029030020309140400004d03a075884d02c8103e11078000c05100c2810080c003101d4140400215444005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 582502850 1250 582501600 582501671
    0x27090f05010f17030301230907020f0706110303270a08090306070f2c1215010501030e03180d020a090b010314060105090d080409020703110c0f010503040f06 69
    0x14035980c010b080010040080c00309203100c100b01c02140c882c4018069001c161135111842c0100ba105000050301111001c0c100100901e400e04000f519150300c00d1000400d8003404d1000100d40388505070413113441c600c04000e07510b5074555010400701000a500135095503c203c0d00030440928090040d00900340c01400099075503100b0300c1c2018244270001f804e0b0700c24405502d9090b00203542c46590020703541b518905c40610400e2541c0c0181c44041c0c140e995940c0301d030b00404419855400402c1456a07140c0c040308254150340c07114019029101c9000c010103c5034014400701810b03e040d905c1c902d4403103101522543d0000d45d650085030032907600da04041c2c512512682c8400055907d0b1080e47c620b4190799014007460300f0804002051380c450001c3d603e03c5031002c2c1c4801d03c14000b0f036504840080606c1241155100030303a1502a04181400c4024a100c2c02040f0402150303083c8140d5080c05004140d56051440d511659074400c00031040b0b2058030b8480c2d4410304005000782c01e148044188041a0403146c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 582504100 1250 582502850 582502859
    0x1e0a06050115090f062c28150206070507030e030102070309031505040b0a0b0102030c01090506060307270c020319050c1204080705060306060f0d05040b0a090327090f0501 75
    0x140c074003907038001080c03a40307103401c1000410b90044400424840c0d05084500e1b04003030032040300c0c100300319001041c2d21032090016049441211130f41142410000d11007410020b98a0342d00b061100294502013000d83c2100e030000310406d100703200070030f4032a200c1e0810092403610000407900326006540124046103075148144140201d07e4001d1f002104801801e0007146400d030b46121038080060107004d41070b0703200c41075003403641e000340250b400d01f10101008002c07041003800c1483e5038080582d4664000c0c002c13024042203d00000c81d681e8840007554160340150214030035400020b05003050032404601081c401814009500450040380c11526503945845a840307001840c2000c2c0c1510084441401c00c0104018201c030200e400021220121215600c030350b01e81c00420414031034a10034802007800050541000400c55021602480c05456603100303d6890203410000c03150340304030250110760114880c8007040c000044048200c0f002c0290103424a6840480d0303010b644502000c082d195880e44010320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 582505350 1250 582504100 582504107
    0x60c0f05061501030e061603111c14060604080c060a09051003060609080f0a14071208030f0135030408070605090420070b2503050610030b01021e0a06050115 69
    0x11007a4005c0c080c004600b442189020724032100c003c1e0b40c05140c0c6801205002c078a44405551512407442d41c2c070468804000007034002040d914101000d03d54a244c0401c0c0d40c0d08045003540c0c1601c03140c0b0000d02a08458004100807604000200390030840d103081c011400c0d444048000c4010000780e00e01041c601c0c00c0c11400740840f4440c0e000000303240e000c0e015000115100140c6280c0054000c0f40c0c100010b41c480601c3e0b400c02c01203070030402c0c401405c07048460400100c080254031a880e010b6000e44180d817a4140380c654082c1e09500c2030101030103c42c0350441c01c1100f80300e1550261603c82164074065a03200881d04002891b4442408108085400f00e103505290103213203020244501d0070b100c0c4d1000641100114061000054104e204680001d01c04201c0c5814422112140c4004004100700d400c038002c3c003034901211420b0150103100c540c0d6108074080d00480d1690307941600504012185001c0441a80c07074001420b00d5944500c0c050f010101c0e029104450182c000d0424111000c0c0c0c4800f0040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 582506600 1250 582505350 582505361
    0x110a020d030507020d020709020d020f0c1c0903030804140c15040e0c04080706080903040f0306051906031e05011401150215010807050411190e120a0c060c0f0506150103 74
    0x100c3c15904248041079034a9400b0903d88141c450f40c480c0180c550340b0a108180c024090102040f080b004009007051241d40001000580b060101c50a54030030010180212002e50603848014040b03a02034010500207543c84c0c2040740c0d43e0036200201c1d900c501d80c002c0000c900c9150191a050088000901403000c03084041c0300c00c1e17011015508480c6094500000f850341d50046124910820214401003820b40705d00b841168020302101c1c0c0b08400d0103880b07042290003001b0035140110480042a00b0002d0911940141b108880e0001650034024a008030394424401140c00d007107a441d5a21501c55000d89500d0102601a10f18401c825100d851b1544000c0c1c075001038020b80300d200c08e401c000100b105102c00280002074580aa03000b00391802d160340301032524001c1c026945900e40d8045c000011035036100c40c54aa948000310f41c1d203040801d10f016440c0c0c40709100980a00a00c0c904002444200d014080607140b5034801c1029241380450385c3c60f52810400300381e501c450141104c0b11002c5070742d039040c041c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 582507850 1250 582506600 582506611
    0x230102030603030a03090c031a071205101701020d05090a020109080613020d0f02100f1d0d08090f0d0b0a0c0f200708010c02100f0207020a030f0501110a020d0305 71
    0x21803640c104007000983c0c03402035040304410191544441010010324200c0c0100469222964003140c941c078814191880b041103605800043c6042080020300d846409068002c580b105000351a050074902c0340f104e10304404a040a156400f003240e540c04050600c590b911a012513000741002200610005041298682c400d4055030b00130828031450095600708848800e034101c0310b809188820b07180525010042800180d40030307a0b2100c80c2e1090641000e0260f182013682c0c0e803071007004040544d101c5203d030000c0041c55004024882e0740c00000e00361000610482c0c41c01841d01e03402a41250014180b070080c401c08507a040540e1081c4290700030706009201c85403020f030601150041001d03170000c10090403501d038a12892010640c00f4200042405440e004c1c0050301c00074000800640c0020303680b082c0f16650201d0252601d4901c586046281c401c2d40c030819802400c4005152454981c0240e8040300700e42680d03655070340e1000e0312003840142c00900d21500785401070a4141c10400c006400c80741c00609 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 582509100 1250 582507850 582507853
    0xb0a0801050f0c0d0f020a0e0117190f020f040312030c05070807110409020603090a140304030305120702070e04060903081528080601031b080d230c060423 68
    0x30300202e016500c0340c05520905009049071606086102c0d64084c140f10f4448050081c07000a0b00308510750322440d0f84080800a8842c5c40b54030303c2c40880b04040c0c03038048514120080324843e803440b16480f0394100c122101c400d0f0a016080403042d50303400d11541c1c0f042d801140d14280198403482043d03010300402040780310302d042083c24501c80c1d071a1754480e80f142c0503006100c1c0148410001a80c0d889912610307026401608182d10f91800c0746403d9607900300e0b002d0540f43c076203c046031304007440000411102500c0e4540e8038603051070704490880c00d510701c025050f2410350103162001310382000304510140c402c40c06142c01085070303075650070041d0000902801562030321040724280310680d152501c969880000c540d10011103100d200a00c1300c414071440e08070004c207000d003000004c01d01070302e854000d10f41a4929400300f20250b0700c5090303a40c0e8000b1001244082146580010080c0b42031810071550f01c10404e5003a231804c80c060f003e05043c070004840403921003600544581d89c08805d140c103c08011402c90 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 582510350 1250 582509100 582509111
    0x6080f0c07020402030a090b0108070602010f02091e060d05070e0f0103180b07090506030408030402090f13110d080c16080a030c02090915090102090f010305010501051606110c010b0a0801 82
    0xc0184280c4a0541d0280c040c0d6000400f04802d074600d584200d42c1c00ea0051190441c80d41c483c04c415455080f1031092000540c20200742c44801111842121200000180300c0c15500070b40003041d080d2101002040c0751b02520a01005103240410300038240300e0319990740c1d80032000143d01c08009842c034640700b1003810545130540d004811409026507108060708407281c40059910641d084a80d481c164010581092011081c0020803007800c002d10f0041c0c0c800c03075482036691745241e0010700106003101d501201d903042031400000b04204554444513210090054100c401d40f0792240c0d103140d800100a82aa0351042d0703a400c1c42180f001d8080ca0180c0001c002502441c031013514010a036032a548406441040c4400201c0c2854508001d82c411050f80704000c00503a140216050703001b03400c00720074140206c03d11218841e03590b109100e518140c64050712503d0900030082e07400480c890345008111122540c50042c035500100f080b02404404000e68008a010004441032101c202c1050340164200c1c0c1c10719 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 582511600 1250 582510350 582510361
    0xa120602070c0b030f0a0b151303021c020a0b18041409120a0e060c0102090a1203031401030b070e01021e0a1703061c1704030b061021180b010b0406080f 67
    0x35800006c00341010840c0000d00300024084041000c0d0540808800222099a203a010f661401228021900740034900180504880c81d6002143c1c009d5110181450070f00a080300b200180000d43c6810340000b0000f0101c070040f41c100c82c4100038902500302000708014030140104441105c4003002040c0034244106107001401514507000c0481c410720010a072144844d900758192104514010f00e41ca102c2913035901480003440d04c00e801500028280100d809807144801612170403243e110500302c903640c1d81c00c1411503102c2005c4c0e00640c11401084802c2c4c40c1c40d0a0003150b1408001c003000501482101c0307151240c20003c802e441520401c0080c000c01c40dc5a5441540740103171001300000c040840903600d0002140001c44100c11015070000c1004010302800007606441807200740c41c02d4890882d4a00140c0c0c00c0000040700701c510b0301030401480403030360b01134200d013001011820703000d03001c070b9040e0f500c480f5161002d8000c00d010b803002140c20481c40d40d21035440c0e900310303d0942403801d05043c603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 582512850 1250 582511600 582511621
    0x90209090a0b06160812070519020f120a0c1704150e0f01111501090504060b0301140c09060403050708010507090f0b090d030e0904150b060405090a05060a120602070c0b03 75
    0xb40a0341340300b0242d50107042c0007030110140448001d605030900c00200343c0350018000d4481d03004007a1368070b00d01056400c0740c1c5a075400051054136402c4208020300324501c40b201d40303001e6544020981c00c200404c100c0d05000007122486150050001000000d8840d070800b00885204950f0200c03c40c208610700c00340310803035114030380142500035083c60601a020400541c103460a0126041511861a0200005003c070301d02d0348143c1c002d6104607000d008000c002c01c105400d03603281062144a01c0700100c0814100540000201b0317140402810f110b04059480d01c40c1d0b41040c0082d0f110f40c1e0750365112001c200c0e85551150100025040412800404605108500d002c5004910f11107009050800002080c54000c8000c0803c0e00c0008042740c080b89000d01d811100d162401440351000c0e800c0000c01141481d064041c3c80540b040513008842655801070610f0160402030040b070f4000d8005580413484891950800035224082c40000d6a1a0210f10f00001425019402440c41030410310038000c03507001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 582514100 1250 582512850 582512857
    0x50f120601032d05060102031c0e0607081504050426091309030c0b0604020729010e070c0f110d0f110f0906061b0d11060906041e06090804090209090a0b06 68
    0x441103c0080c075955082d0042c0d14620608126130321254140c0d442c40001c0e41d050b00b01c900c0040402013a01c8140e1078100b01540c000605885034103070001e080618400c01e0405a000d00e034010701403c41040c1e901190303d40b004080070321483c40c0c00c0c1203c00082811382c1d420802420300c0b41c40c451300c4007005030030101c3e00c0003405640d030344400911540311000030441541e03580d010b9414242c2c010b0455403a2441905c03810814540030714422400800f03010000800c5181d40c4151441203c6c83e44896412516950303805000441d040011150303d41c0103108500305448410607032849600c038080313a01c1d40c1d0406041c007030030700d40d201c0c42d25a20560740e01e4001400c940b20f2600081c0c208100340c5480340c43e01e580c03c580a10003c1030b140404178920500f49d0705041c1a0b400603483c504c08071213500350b5260341c80b1340d12403684070b0104aa000d060754040041c0f0340031000ca2030b44010140340c0591701c00180320403076540c0c80300c096010358440c106180d008202c80344a0318008410315005421a64204581d108540100b2441e00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 582515350 1250 582514100 582514181
    0xe070905012604080f13150206070e0a0b09010c0803150a0e130f0f150b040b040902030304121b080102070201091d1501030e06090303040c0e04150b01050f12060103 72
    0x180101c5c044006400e0581910880050a541c144079652668805458402c501000000612541c401304560710300404c08942c00043c098190900142418903501d21a8010315120b8100f14a414485021501007000396029480c10420003050b5800d00082151241c01504141e003019200424044c2000d40245412035039540895036000203051401c011a540c100c0e0503000e031014003a542d0580356030703080e03078841c054042c0c08480800c2548080030070700080300d052000007501035001700300a10200040303d8548881510600012810f9560364000c150640d2456010f2a1070740e401140045c11582c000761004080c140c14407035a005400003030303800300d08004003400200c044c070458010340040c0e9100c0e80141000350740200440d030032414480242546d07580103c80c1030341c1e4080007000210700e801440d040725003c2e5410401e500710202355807141070b00074040e481c240340c10b00008002c603142100d046d00c00342c046150b03103d801c810b841ca0800c002405440d01f004102d000700701002496044c0c80701c0c00e0650482c3d403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 582516600 1250 582515350 582515363
    0x50114031c0e1908010216060f0b031005060f0307060c03030f0e3708040e070207050d0605060a0e0406020a0e0a050a350303090c01050f19090e070905012604 69
    0xc40585080800f1512541003101e25500020f0f0b45120020201e150502c2c3c41d202c3c041c05c010602c0c800c075106007110900c0034015490781020a43e040b1300340f902c1e04820780140000b05008142180c24000900d4500c0319482000452250034850342419014415441c1e4019400340a10107000c8629105846030083d402c400d003018010302c0f00c550307903010341c0000f820400c90201138500c4007c564101070300e8581140c41441c03c0141484000342c142c82c07007c02c5107000c40b50054040d540c004a1951088064103009042c1d03070308520b07913100019075100c83e0035560780030b140500f50041c8e580c0f202d41c1d4010301506020000b580203021a100c108503c3c2c895030b2085044500100c200035070020803205003031a40d0044885520000004c0881440300e540c0403005500640324030044030f1525000400540d0f540c0a240380d0326038030140510100301020005815081125524540141301c00c1c2c44842404240c0416580c050001c0c60600041c8a40d5801400d43c82c02c0b0345440403401c00c0c0201c2080780500400000f40001e246 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 582517850 1250 582516600 582516619
    0x4060801170a0525051e010503131e0308090106031104200a03020a08150105070b0a0e0a050c0f150d1508030409090b010e1306021804050114031c0e 65
    0x70a100c20b5245651100c01d030384941e081400d51056001d94800807490303820000000141030710b01101c1c400c0c10750150020041088000c00d0064506420091601c0680c520040266000a98460680030891201040c11041c40020304004015141c001d0800702181c1c5084402e0000c510390039601b01c04000c04803008034096005001031000c8886429405804420210b044c094031505070300a0b040d44040740e900c9891540c2c0d01e003200340000e280100e500e40402c808110f0100450aa101c2c0c455100e064038034045100300d0804280e1745020080b0405451a801500071460789250a10900582d100101c404e100c64041c90700b010201c030722861000702b11042d541c0d00d000d13040da1905c00401000300800d01c2540e8445549681c403801910054108030b403c03041003400450003a80390b00c0858050390482e205501005a03c1d074880000b0360048e080e403901c4021030210302900342c1c0c0d0382c05207034081c18010b000301c82d510445034181441c0138603914000245000c19a150343c1030551042000c003072070400311540e491 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 582519100 1250 582517850 582517889
    0x3050c070201210209040908070528060b06160c080106080106050102060a0b03070816180c0509040f0609150905010b0c0d23070b10081c0e18240604060801 68
    0x31704c42c03405007135005420081040284126030000d009894000c1c0103440349914185907103200c6c480102031060150440441c4070000c101d00d40d00211a0319000350a040c60728042c030600542e0f8a054140c1219465486001402000d100703018810080614000034081c00e801c000020b52500001084d01101503910b101e514003940d01002144001c0003441e0541c6c0d03070300e4016209401c042000d40a800c0b00a49015030142020300700d4401c0c075280185980c3c5850819204508000c0a041c0368113030040c0320b130740720340740444c0c1c43c0210b05c00c04005400c4614000700281c41e100030501603e0059014800204c0280406244500081003c0c2140005441c00b01c103605017842400001d0448103505454012001c0307641e000f00311555104600801d19581c90804041c2d1721035200d59103100c034000804c1c51050000c40c10f140d075405494007626011000f802c0d0040c01210007058541444c0484034030503d4402ca20703442010101180b100742032031200361822850325040c03060103001c0790010b00c240c0e001050389030210130 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 582520350 1250 582519100 582519167
    0xa0e090c070602030f0708100b04171005090a14160b03040305040e040c1d0105030319030e01020c1c030e03070f02122e0203040b15030307080d020a03050c070201 71
    0x1c081507800001151242031061490f4008401256880e011808410104c3c2c1d101c1c545038000c408070b5520714100303840c090409a07604c49850355000032802c284181d1320a41000d214034020213110f100395800415142e03070300e82060020a07460703c116455540149111140f40e02c5010341240c1a142014003450343d13034550b890b080700c262044e5400b000342074015205200401812020030000c845003070a2418140c142203801c0b4446000a101d0242c0c103038010031811050103100030700e07442c030170300c56007000203000b00700c000c5403400c1e07a0080c00c448800d43c0020803600034052402010180c00d54032031901f0001403440d500951390380d00c5110405001d05102c40c1051045640381400c0d41452006c40c070940e4940700c58200a1010140310030288031120b49401c4104446503480e01c26244680d070017098003a141d03220b0f86c2002410180f0180700c2d58040c0820000382020540384030003020030410101006a585130280001803c5079005804442d8054042100c0300250382c1c0032040b001c2c04400c01c3d862158841c185100304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 582521600 1250 582520350 582520357
    0xa11030a060f020711030105062b0c030f03110f1203040821060418020603040605040f0b01060e0a12081801181706060a0e01060807020304031a15060a0e090c 69
    0x14541d90800d036005010000355000340c50014861008040d08840e00d00425099a07022228030741c11420080080d054030714a070f0304080b90300c8550070303142d051a5141d07100c2c054500d5540d001600c2c0020170901002c10503a0003150700451041030b20107010000054210552508000c21640c4010f001c080086409d10801c80100c42e0002018102c1c901000000402c0150540003110702e0303403003240303080c80c200d4003c1c02c2c00108100c0c03a5030040c00c891941c0d0751b50b51140020310000e4400e550501c510141100040c2c410b4011070701900c4580c55a40c4c00c1d010107010021040440e81140c00c40403142110b00001480721016076030602d01d030100c4550b40042c040d004a903104a4400714030401e000d1801c00094441c0c030040840d0a15500400382c6085d0b40d200d0050002e80c14191046e440e03c8440344004000040c89964250f40120b001c1c41a01c0c03a15a0b2034035000c08181240b802070200c404c10b54248403c1d081111440f001c0c5510540307a590400300e6121010b42100b040f060480e004046150001d8005e040c100103d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 582522850 1250 582521600 582521603
    0x610091a1201090c0506130314010f02030907081b0907030f0b040f0c1202090604031e0203150612010e0c040b0a1503090b010b1914120103140706050405030a11030a 72
    0x4000c100001c44207841c041e0000ca04196501c149460340450682410320440b84003090140304150310910303540c2d5801017400c03521400240e5550320b5151030005c000c0d46c001035002e00b010000824180e824200b07071038109161103003015008002030000c03d50544074080801e500c1042c41c280000da2000103881000070b0891401095840f5107051041400343d03140e544002c0e82c40c41d40d07035104103003885070b01c12442c00ca220b1000007561006050004000141100c0c90000441e0703c480c0c01410505166408640791418044454440015110820180d070900400405140c080b01d030080c040c13420010765860303c1c2c0030591075003406076458400c1414540c030380503132450080c4400303078106c9201062014010010007014004807403c4441c0400000d0000d1510180e60924070080341503440300140c48011350341c600f14203030090715001040c03100509030800e8100c80c500840c06812800100d0b6100300070305041c40c03203c3e0002000e01000340f1042c082c0c1d8a0000750350b58001e5001d40181c4c203e203406030010303242040241c0e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 582524100 1250 582522850 582522859
    0x2030604030f2303100501090f090507091d071d0109060815030f030a020732210703030e040e0c0d080c030a18090218090a0e01021602120610091a 64
    0x141c0c442c59451403c0218441c40d5165401400e580d2220011a1400454801d0358240c4100e11303014090306805074401a00102c8504050401ca0741d1100d00c2e43c03c1210f454140075242000e00304008050340c100500e5070030200003255100700244e088001815412240c00f07507200300318610300090640c24600b4100300340364000070308450400c82038004aa607030ba40000c0907036005005085d0300007002d20010710560442070301c04d00c142c07100c1000f0120301c4000e20b601c0f501e4030b54001400c071820b904412324045d4807103509032900c0181c10a81e0a43c00c01038070607100c4240380d0727008519100d00c0d03c01120000c035006091340c608446080c41950541092142d03400f9503803000741c01c0d0200290030040030760401040310303d1400c603000102e503060395120400c040f030007070080d0000440800d9001a580b480c140e00d1042d40180b503004005480d01d400042c281c2246c011030701c0803022100c001c0c01c800a610b0040b8242054201000050003e89026000c980d1884010311130700720003d40f0740c0014049124100500b00590b0f20190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 582525350 1250 582524100 582524147
    0x9070806130b04110711040b0d0b0c030903090607030302030a0b15040302010309020409080a020d0e18060409050a0b01081f060803042102220e0705010519021006030f1e02030604030f 80
    0x1002195256206e45140c800c51900d0390109280c2030015180c40441e0b0419291441683c1700201907180394001001e161250000304008109661004043d0880380d0080d540142c0301d00c0d1400034041160078040007503100d10703d00601502d113558403a08075000c3d82e03420310313002c18030328500d1020401800c1018401040e00c000400c180100300d500041c21540c0c801e01e9515014850240030901c1161703203a0955852503104a0307000100d41c0d08160708034001262003401100c914024036215264009801c0c4c01400f80c6400080c07030300050000d088820500c0c00403412003044003624000c80c0307594074403403845001005a12250015455000d0035480014940c001c2d03d025100410000d11407440034021400756031217450850560031101000510700180c50040c1c507070502d4040e606e102c40f03460060301501340c41184074030500ca00701c0d00b4041c0034100045100300c080041946452604d041452303c6070306803403c03002c03a0b00020b03005a5000185a900aa0142080404a20103100443d403407011718443c0c0010712500c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 582526600 1250 582525350 582525353
    0x4150e0c06090406210c0b12011a070203010c080115030b1c031205090c010305091c0809070801060801020a03140c0f090f030d020f0d0c05151005030a0602070209070806130b041107 79
    0x10001055602d20035285078034002d0322104040b00304c0c010701380c8d07600b092035481c40180701d140041188002c0e0a00d0b441000ea00706009039000a003511038082d00a030004145000401884000c1c060b28034500070070b424103221014203000441d0301020000348900c600140c101010013414011848590440d501c44400e002e11329183d0211652144040c140ca40041d24100010b07180110110b000c0346a2001e00700d550b11955041e46040301c8139040604030040a02404600043c410380c240b040380010f0034000300250b1180100c000250880d007443d101d00b80c43d440204104141c40314250100d075060310707040401d191981010000b040d050900c140a1940600ca001c01111029400007008105500c13002c1c101c446003400c18408a486548030351000f040e0358013142400d1035400701a02d840303600c54000c95108540681e18800246412843e4006607103650740099824154100310001b25804280750030020450309220003c20094010800540403c65031a039100380c2035a00d0f90041194080010000e03520348815 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 582527850 1250 582526600 582526649
    0x50102151b04080f0717032a03120103050c010c0305030a021c0603051e0c0d0b060f0a1502010f021201030f03110102030a0e1603030f1119030804150e0c06090406 71
    0x1c00751314111a00c102d120001346542c1140e03450041c1c3c10716002842c00c00707003050244102c44a0111011483c0c0ca021043d03015100d4003040030b001c06031408071001d08154074606240c0e09011601d40d4450410000008042c00b00f034000d021650015a441c1d030060b901d081c14240d01100005240c40001c0850034048000240400018000d002c01e000081510300c4424001789940e69a207001c070032540041c210400c034004204408079247d1302c8a0040c0c5541040e10040d000241041066000f1444100884010a900076424401d200380100c00007011485c00c01420301031100c000f01440001c02c0c10007030915000800d40305201c550700203021170000755140d007020b03810000a401a000c0c0d4074020311951145031030100c8180e4038002140e8140d146ca06080c0e221580840b0340050356180c41c52644115030940603105146001d00d50a1402940d40002c203040c079242540c5038010a8686190300d0741403051400c1101070100c0c000755240713000c50303010341d480c09420046005081180d01c2145c103800d103240d01e804050403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 582529100 1250 582527850 582527863
    0x1030f05150a050f070207030203190c05060307080f09060108190213050708070e04021201260d030b0406080a1703090705030f0106090c1407020904060219020703051204050102151b0408 81
    0x180001da80e11245e0f2480f90481c1d9544c842c0c400a5855071040c5920ba60b14821020000d10a501460306034010940712400714080307a1099030503000003044d1004002d9410b00d5450180d800030b1008015200720f500d002c031002d070381d81d09002210210f0900c0381a03882c1159920b680345401c42e441c000c001d211910307020001030805c00342111014040358501d01070013101d14142c030807603e01403500400c01c4981d0b420301401000a42c03e9000603018015504c0100d03c0010040147e2140802d441c0d6000c00c5840410b404d0000399182d6521034145948800210300c00581c0c010040d03140348181c442469201d546109613030340360a030603070b21080e058091104c4015103100c064000509807206500c00380021400044201c82c3c2d100c0f03519000030039607800c0c094680140b42c0341e808190054020500541000200744040c3c600b03841c0348218801590010904108000003802100c0c518520840d855060515040c0040d440341e25041030000100c40c44030006248906503440c44502420740482c2c0750700d40d51603082c0c140c0e4802 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 582530350 1250 582529100 582529111
    0x60108010801060308031503010908030a0903090506180d1b0617011e06031104090f2903030901110106080a0c0e0109020f0412032007050418020901030f05150a05 71
    0x4410500118001c1014007803a01240d622041c00752459440c1c600d404001c00c2c05a81d503035450b5480b0005107001c2901d24000d50302400c28840001400d09442c9409005a251544014015071080c020031003028800c82c584410010b086c0c4521500c044e2500c0c022030714862007075200c4212080a007011801c50f6114a6141080540d42c0c00038041b0b03600c03082942e003401d1852113100703c401c44c0201d060010328840d8008000c0420040e412505158076502002e00f5a440160039141d150b030b41d4410102000440c5080c461803084e00d8040912207490720b00032a459100e0281c1c260706019602d100c03811106801d6000710024845082a203031044c0b035500d40050100004c0c401c203140b8090820000c02e0056181c4200e4900d041000516450240f030800100422807050130142c050160080b58024040e5101202202501480010300f00040c180002c000448101c034500d203805000c059540b00058580c0d0700540c0c15240c0084032124030112500c1d0240c542400c5240840300d500d0304030700303106c42100c840e0401400751 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 582531600 1250 582530350 582530357
    0x91302150903061801020d050f070e01090302090105040b03100207060510090e07060c110310020408070602060130050d0c021e01120213080715030b0105030c030a020a170f0601 77
    0x4880103180845030040800050340764200744040b40c13190034000703541c542c0d20480800250800000340c014408840d0304580705841d4142c01e50400088030b41c00303c5416944502420500c54480c1150041400c0d254140036440c05903503a8440c3c1e0500c0e580400003105030010840040d0340e95903407407401c000500801c1d40c020084405102c0b012580c00d210740206003c44074414020114240381445c100c3c0c0e03801d8204805e071a048190001c003011910b090021400103040d13002d015030340e2882c1004442c5440320a074031210031034010100500502c5030701488078405e01d04910b50303a45414190343c000c5107903c4c0c4512008040c0e2280014036902c2c182c015844100b024000c03550040f50807040516030301d00d041c511041c40d000130818495113050000540c0034040c941150242c0504448e202c0d040141b902100d500804510082c0040d1100040d52500486880f5102860858118100300140c0b00c2ca0b80405403107010101d4001c114440c525210317400242c0212a08007441081342884031980255060584505002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 582532850 1250 582531600 582531619
    0x7090213032f180f070e04090f02031e0c0d080c0304181118040f1803110c03010c0f0c0501020d291f030b030304050d0b090c100903081305091302 64
    0x81e00d00160401c0080f00480403001c0d1941d2002200501c01c80014407103028030140418502050310380c1d00c10484074510401c80f03a16101c2c1c080c0101450001501c810140070084090b00e8080345070080740600182c80180c400c00d000201c280b806904900500e0241c1c1d10700d20002c42d000411121f080d00ca0207881c55410b03c208601c1c07881006080e11486400116174851140105c50080e60034540e028244050070410000707100401c2c0c41a0801c00c208650301035000aa91201035820190107204800e2045400c40003040030482c1024041c1105403014600020b0181c2485c110050010a4041350551002a141004055556118038017120400c0d13584601d0346640710031030501ca00b030a00c1c110074081140703005210b00e0089640101c01074907850340343c10b425000034000021180c4800703400201d0288140082c034128030f019802c59140c80c0f95030464610034041d4070300700351045800c54a0041501c1e0840720340c50383d600d00030780301e19035940c1300390300aca500180600e0804c031801e4002c9940301d00750b510841e44400c0c0e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 582534100 1250 582532850 582532943
    0x332030301090f090b180106030c080c040e07060c17090319030f08071b051e0d1701120b0604090f030203090f060405060d0513120e1003020c0709021303 67
    0x32184e081c000148020314010100c2c005068018021841d02509000030404036140e0742c0c6d08401c441d45030311540c010740c414903d5140714901406160400648200200100d5141c01c10041201c507852002405030354154050100311040036081340c54441c0041d040b601051000b019010410122030000e90001d0034a581383c044c464400d00686000b180c40c0c0d81c4401860301000d00c10b421004002404079000c2c410b035420810034100f4400d904006a84510107004c58240c85600600013101091303a58446401410050241024103001801302c250081c040003155136130b03140070030021709020401400465810b01c41208040d030010003000b06103c240d07000c40700610b4042c140085805180550b651094060007410000c4d0f240781e1141d070b8412030980225000f8043c540302c441080d0130500001000442c01c000c0703820541446114003181015500d811803902150090701030f21140d2a0040030101500040c42e80020310300c4586100265804c2140101e501d211540d200ba00d90300341051307600c0000004403600c0d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 582535350 1250 582534100 582534131
    0x606060e0103050f070804080d090f060203221a1b03040b04110118030b0907170105045f1608030906040b090a1206090201020609030310033203030109 66
    0x1170055100780c1790303214951030350f40d203100e0300760040320303d44d2409517030707481a40081040e2100c607281d100d0003518010b13501d04040d40c4140401918a07041042d02c0e003911084000a8000b0502c803070420b50f4440694550740342e150721000c0038600e822854a480744080203000510801c4021580100d2280461b0155002c61200540d16180844005038030202858000c01c0400c600d0070480d0741c030610302e10640306208d403150349459030300c40b040202e0200cc5c0e569404000400c08041c00c0c01d03807142c3d030014113282040e2021020301c80c001844400000141400304a1146401c2035481040c00c4042610b04080c0c1c12100e000e05c540e5841d440f4410804041045030001488080807045032200320000e850f2500d028142030040c2015807112600030342229400b80c1c0050352a00700c00100101c1403140d800480d0070360fa240002807071b050000c0c003450210b42041007880080542d00c28410b040b00e9020031008141c0d0b410350a4405070381310784203000020414441001211000c0031000354140c4112610030000000861141d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 582536600 1250 582535350 582535381
    0x306031903110f0d05120c1909080712111e06030a1a150a110c1309050c09100501140c0115030314190c021f020313230f0d0606060e010305 61
    0x1d5001c24010842d41b81d440d600c41842039444004a17011900d000540c101007103981414466074000140400720a00c816442031204034011702d01d102100500c00780c030392907800d1207010f800e10300da1203810340e48107524240501e1954405030302002031600ba00c038039200e0f03029000380045001000d0002c4004034a02c8140c81d01d00c01075100f80e00300468490a083c4c080c0000d4411501054a4001ca481100c0340030810b0768480185189e00c400148021031420300c0380c039100f450900c003150850702c1210070340f04210801001241801c00c07144240707400110709002854020079071140d802c0c810841d500b00720304544580443c0d0f6a40084901c0703a03549030709070100c2c0711021103680a16183c03020601c4550010a080c18851a281c415107030004010a00c0350081c0410061500d4005204601603040413030058040d02c20744103440c000b4241503410506110740248060b504080b20510381348140c040203880e141a07220300d40c4608031380760f100700c003080216140c00025100d1540c9031144c81c000303414200010340f0406264040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 582537850 1250 582536600 582536623
    0x3150902030a151a2101080d09050f03100f0f09081306050a02030d0507050903060f0a18080f070314040909060b040b030d080402060c0111090a06030603050d03020306031903110f 78
    0xa51241e40134038070b00e900306540014850002c1c98144100c5030921401086514001d0100300000c0644417403d110241c86c07008035a11962103056001050b084035100481c0f05010131540500004451007090800001810354222040440b8070f081c014034100b0003440001c06040c8440701c202d62100d44d494204649501c101c0a0700d500507081031010075050070640c0c2150b5007181d182d090550400340420086850041c00701d0b030440031890110f003441600b000324492043c82d5000040ea044035080c00352901d4a06105010380600b4446c00011401c1c14548500300320320180030503000142d0783d16134855030702c8060902560280ca25a16018004180f40351904c200d29441402802500520060040c2a941c4403402042641c0003d410080840103003020711544010200201d0255190322010f0140040c4884d90380140051600d000c0e000c1c40030400000f00d043c040c0c1c085160169582d502c1801080c10048400c20981321004046500c100300750300000071900301c540c108111007000400d5035803250340d502d41310340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 582539100 1250 582537850 582537869
    0x110a0503191b090906020304063815040b0a030609090b0106030c12051e0a0c17040303020c0304060c0615060f03090f0212030301050310060b1903150902030a15 70
    0x4030007000840701c0e00d65807012484141c00034800c0380d403001e03c0000d480ca0044101c501aa0000400c010004140305e06510302c9401030340120200c0c0b030001401804106480400903100301642228440d41e61a42070803030f403070240561103446564070789489590703800c4400703114042810070001089280c1d00d841004081038014444a001340d02e007181c00d800500f2034046550400c99604400d841c01c8201d0300030640590801d850343d8101910704584d4250200e005810f42038035070f01f00403880c02e00301e81c0314a5072440340e90a0302d65543c0640711440d05400900c83d8110101981c000440d0001d50141c00c500030030403146c020391042c008002585408031144207140a40f01c0801c500341000300781c0500c01d0b030203d01100d1051020140003601d5400240084038100c0607540a90700000041c06981814401150186640c500501205050400700c441c107009407811841c28410544086003503a10076001440203681d24400f0b01c0c0340c540c944228901a44c41282c614401506003901c0d02c2680440d003106c9021103203000e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 582540350 1250 582539100 582539143
    0x10e030405010f20070602120c060114010516120e10021c0509090c041719020906040f0203090d141e160816020405150906090a0e010207110a0503 64
    0x4010b4525011003d180e50070440460300508800ca55125008806440500289000352030312030000c0c03800f041c1190541d502041400340c0d03d0006400101c040c103444a50481d407001540a0004030740d240585007418041230642044c0340d0074048651040901480c0c00d54807c04000e212400303200b00465a010310302c005034041c1768003a1030140c41c1d10b0b098850684500e4460303e04402c880024a0220301599070260700540020108000c040e064003101111a108000e481280300c140b07046030030920a504040d00034066080003a540c1d40e036603070040da1311203241c0c0001c64403070800d04034290751041c4002c00e4802059181c00103107401a1483c09403080800c05001202d240c2080c0c51044506030000c00c07850444a9070103965800041a01d0080c10500c01d04106602c44e10030b003401004142d0300c01900f22003110f447c031000d000c1d039a2078401e1401d500c007505035508582074070b0f005031000050100358035040300742d4404154081003003441400c40e200e0359412900580180c0e124410142c9810b030290300003503510240c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 582541600 1250 582540350 582540359
    0x6040b0603160b0703110f030a120605011119020411040603200309030405060c071518050a0e0f040507051c03080a0513030c06090210090314010603121107030f0302030304050d02010e0304 82
    0xb4012058040105000c7d15602c2c00c41c1d00e042440c54000200b01030120355140850030300ea42040c0300d000300070a02407900c1551002211540750300d032000e00201813006030070040340400b90f4071390750040100041740f01a5242c2d22650780d04000d0040c4031030f01e81190385400380203d01c4254018072041e40e005001080140d03291918003002c000c0b01d40e00440c844185c0c1c2c000c0e407600003060300c01054403489800c84c42e110800c1d4010501c1e04101e04200399080342d481082504d00c1070012020f41c80a83d5030119112900e003015489500380285070010b04e60007258052050060721007c0300d144504003090511944880000d034440365400b40940381c04846540070205281c0c0c914001c41e202c1c81c43c1448490160200182c05107058010070411f220b4440444041803c0400070810043c4d41c0b4181c800d05800e42c40200300341c606613984c042a14039014a0f9004200c3c0c0c03040c04070000b007414400d2400469210104009464281c0b502a4a940044609862a00603440c0d643c14290040c050a410000b16902942c80d16091 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 582542850 1250 582541600 582541607
    0x16080711070b0d0606090b070302100c0e040606020c030c011706090408040f300b0103032304080a02090601090f0905070e030f010e010c140304020402090f0306040b0603160b0703 78
    0x356508a0010700c240100000d5000450b802405202225035000c00c0303a50030140090480b188940c0000740a0001308850b4022981c0424403a00d42050390901140140025504031004458625026481850090f0005420744c00150003d484202a02601c0e40c41c05503000640702d560b088401ca01861840a000401030b241c0407402a41c018820fa081508041e161481e61100d41c0c00e076004038100d02210001a94200b000d80c5461001c0e40000301e0007176404941c3d0303503559420308042c8401000c0c030200007030804145031405020500c0c0c500360103c494031559207130b0150380d55420801050740901c8103071000c0354565110324600d106a03001c24032144041460700284c50010300d8010420b001b0050390103807501c05a0741c20f012302055201041e001050340d49070390460a0866a030040300c2000d006a88503007045075040581501e50240d01243d0060701d40307410700d0120b841d00b1031008101d40d060241c503042004001203000d070507005910031f80c200d0f500040c0d424000b800c0d1150078020041426001d100040001e0721 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 582544100 1250 582542850 582542867
    0xf120b0f0f062802330721020d061a0a08040f020d0f050d050c120d14070809010c020109081603110709020c01141e1f12050105160807 59
    0x2000d8a00c52400e42c0034624100030610f54004000c3c0c051003402d10b4a40c5a60400c45083d503000183c1c0081103c0102804001030044154020030040c038440f0000760107240900481d2561001112008020450303083c0d48000951008007151000d5143c50408500400203152040144240c000800d241c400400000d076070f2200300a004480301c01900788800c1c01601c4503024414410303c01c280c20380590b04039240c907500301045011518108a000c0c4118400d0b0304000500b50900a406441255200c3c070340148440501208203000003c04010001c1c03001880d4441c3d000c0d40300743c510200800001d001e85904a007070326411400034180000031300c10902c0841c002d0081034040b46c86814040403490410404604145040d4071070401c480c4e0125170703200d00c80801c0c040d882d107050b910100c81e07075589000b00d00319040d001e00c15814a0b052640000141c074041c9801d402c003034001d00c20200091802c0d550a08000f803070b03410a80458580d402d000104080050003519140c24002546413503140d942e030004211030424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 582545350 1250 582544100 582544129
    0x60c040807050904140715081e0c1b030c0616020106030506270f061008060105100c08120112060b041814030d0f020403020a0501050f0d0b0a150f120b0f 67
    0xc505e10300c104041d40400102c40241203090303400200b00100751020f0050200206040a4007040039122003030144850780490303201000030142d580305e078203821805060380b19075902c0c030b029031100190500c0c4c001c1c000030300c4d10b07c20441a40144089281c1c10002c900340c0b08180f00050043e84110302094004284c80042040e40d115501c480304201e0001414a1030940c7c6007900c0710346a00103c090145130350f0101815405890b4050080c0025490130300802c1c06030301034464400800c00c0004813003040045810841c1d03444128050b80d15550750b107905104001940c04681282d209150a0020800342402d000d404183c6110f10210310082c441d586a8451384920b04c5060181804200000942d80101d0b100340c402c10a031504005843d58214811300545100c0c070341006c0d0601070300b0301c008408034803404212081c40d0084403002c2609055000443c0b1607544075001000440003d5511002c3c1582c01711101049404640c1c0303a0800001503d460301c2245c8450002d5034010f449894580301d2070501d60343d44071000e0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 582546600 1250 582545350 582545363
    0x905101e120e12040b03130210120609181202070f14040c050906160609021c0c05041a040b0a0f12030f0305060105040e06030726060c040807050904 65
    0x51584854100c20058886000c50103902110710720280c984a4200c000c86420018500d000c1199100c1c4210300603481841c0e0f00c44400000183c22506000d008184654003504161981c0e616060140c5250511500005840c1c40c204002901219a005180561011002c00f0350800c008c0c4d22491402c40080075800254440e480c0001500503081003420010700d1f500c44203c000380e07003103402c0009030361499000740c0802006000074800340d40e4a000721880160340900240d042280707403904802400e2680c1e00658032024103041094040d001052460085200b90005e0354205c0e16141084100c1b040c007581001c0545100320f10304080e0416a00929001000510f43c0f0713146651041001c07000e03551078004010344074041d40600e04040e00854841c242d80da00d804c0c24800d624100e00000d16a021318031802170801141c0c008900302d52018400040075100c4c0340c1404480783c51101214400e1420f00c062056144281ca00003124828084165030541d00180b0180c410b10703140c0340130000311103805070091b0380780d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 582547850 1250 582546600 582546617
    0x10f031a0126010e060c070317010e13050a05030d05070e0109030809060d060e072c010c060b0f12011b05070f080306030708070f03021309050d050a1223010b0a090510 73
    0x2065800c05c04244101d100c6040b50b42d8a40e40340c40c005100c210415001141c0104050041c0b01440451400d107501004207040000c94030002e00f811880c00001e210058807901001034000510034071504100d00c1547c0030348542e0741680c5403400448841b07d05100252003110140000b00c0649031400082010a208680110f140c0f03449091600340740d801503810b400480c0c0c0d60207180f500e00c3d4100020400142e200c1e04000c4441030b92800280c4544640c0b80006e160300c0ea02c114807011740e41d400030400030707245015160507691010603d0780c9000700038000519001b01180d21540302400e20400848042070b51004c41d003842425039544010194002405550b4503020b415800b061254081015400824050348112071030340c91401030012024074002003091080c20800303031201044000a02c003001c4005803500741d1341d038600008102c4040d4000306160164500300400d00e5907900c944e480300089441d114a00360102e0740d0702d00da1068203101d04203119000c80d513042002c101c83d00c1c280d04800355000c42814900038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 582549100 1250 582547850 582547871
    0x50a03060f081011040f060c030c05012c010c0212030a0908030f040312050c1c06051201050910050426040302040504120806010e060913020c0105010f031a012601 71
    0x55607032a0014401907000001e030005188080c015140c031416415030451505040401c1840545c09501848060040c02e80001c1d04151243e100d107042e09030070800030440c001410040c5100b52664070000304440c0c0304044404614a410710442c2030448407030300103126960316084a5002904021300d001e009594030140c1c0804900303101d005501c1441c90030464007180c50b2528015013031105401001c400540b0302010407109642c88402c4a04000715681e900b1203000e00c2c0c0714810301a00d0182c105641040180c0c0e8200212601504014080c4560320709692104070343e900c0d110200c44003200d0252000310040ca46100b49881c011040d030314207000340345c024a425181c0d00403c060341c000340e40c102e4205000408004040760700c00c058a4201000740ba1542c22480311500040d040d008098140d485100312400b03001545400c0ea0403a540780c550003000b40020342e91140c001c04501c0040c441078030700408040000d481440c01d074000754141d03010030301941801d44200c41720380c075841105032a018503503507a481c400c4e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 582550350 1250 582549100 582549119
    0xe07020309210a05060403110c0a030206032809030813020108064c230f0408010e010209012d050f0d0e0715030905340303020a03110606090403050a0306 67
    0x464038013840040c812400c00d8903004201c140485113400941e0030040c0b415082c0d9503929502000c03241c040761466100c0d26898102008006000c42c0004103c402c08d0303045030f44000c02e40003240c08900076240d18a0b1a6103d001c095241e00d07881e60000d0001d012640081c506203401005003080102055510501742d281c00d10b80000002031450824260f554900c891140702c6003010317512030043c2185440040c0210782c1c0b4218162130525500c820403079101180b030759503070b11965090758001c0282000a0040200c82c8480038000e602c41500342d03000404010000c0380200c0c0080ca03075410b030840c2080201002c172124108882540040d0092030a079801040480f118440902400b01d00c81c04140180c88200e2400b85411800e00000180e60145414950103001080c03000c9800d41403182812603000c0c41d11955603400000f1440c0711054204a02c81d99000300516030b0001e46040d000b07111340c81c1c000120856650300b0b81d03a0401220441c0c0e0042c0d11000040009100340050b0040150909010070415180e41668 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 582551600 1250 582550350 582550363
    0x60609081e1207060f0b0607110103020a14190801150918060306020c06070306060c020f1c02030303070302090102060a0605030d0309140a030c06050c0c0a141c0e03070e0702030921 79
    0xb42e1303005445001024500f0786610801800c640c04940d8185094056510999045000c80d10117041c940d002c0f40c9408042c1c00750024178400c00100c10070b00c1da5111011070159082030f440500340000307100c00b1b001081025100501e1500404c541d2142c843c114a400205022603160030300b00541191103980000020b03232640044e220012694020b001e403454880320090445089a00800c20010801840009600c40400140c01003000391000040300b242515500e0142d81c0c0e80782c00130b406210000c01c0001840d4503038003800c4060f90913800d0726a0394448002640a40702107008850f899041408000d180a000381e110750348051240c44032840d084030788418607007020300580707060300402e10002d4090204086440780d99801011940b69500b820030414400b542e0309103201000f040845103540482c0705090400007034100c1c0078860b2140c16500c0b45000d0080c0b45d140ca05000900911a40b0340100389190b580800c41d200d812a540114200650b04040100111043c13584a08a8483c1040400074040c1803080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 582552850 1250 582551600 582551603
    0x1104090e060708010b0f030903310f0f0b03100503010f0b2e050a021204060e0306070f0815010c08070606031415070f0203130f0603060609081e1207 65
    0x296080c4a0104a400c00301d000701100304100180700144140d10540042d150f00301d180040e025101e0b684c424a00d890751080c550a0091603d4042c241a05c8041204d0440c2410000b4501c18060b60380d00c2181d8030645800d8081d031740100741c152809019034941e00010b035500c001311a40300c880290755000400c0c04c6440715240c01c003039a80c95018668450502243c0e6600000078040c1078038000c002d40301400800c04040104408100c3c00080e4280c0c4c051080144040c40009035405a541d107a84101c040e102c2029283c1c1c40d1301078000c039030000c0c4c0d2440c0640f10801d44520303aa1151450390303442d40702e00c000e04880010614103000c2a03402103c04900c51601611300f062168400084950841c18105c60380145c030280641103905c0381603021500903c00c05c19903003041c0f0608020903140045e01069085000c9c1e02d0004203405220500090b1610400100f4800c40d03030582c40411146071928402c880c11001c0d4090003046a20100c480b50038880f540b10b140010540b070000381c4d582011401c010003a2603010940 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 582553956 1106 582552850 582552869
    0xc0203030d0501290307080f070507150c090b0a0504030b060409050f0c040c0c0317040f05060108030d0b0109060806150f0f130503120415031104 64
    0x340c5502000900d4144010340e160520645130800340103c09405283c800101034501100304100c07030049080340d4450f105984e80b800c06400c001d034050a40810424200800000b0520410041943c82441a8007107190380400c503005140c0d600d030f9001070b0014007080001000c416000741c1110700b100d9211482c1405d80e55400000350080800c000050300c90300960002c0d05203502c000c500d807120410215010460f1880c990000c507061505128002c01113050070340c032510800700ca94041c0d94407521801513051100110358860382460400c1c2d0050301c1c50390000ca01c400740a1400d01910f030030b0440a107000008246481f00040080d140039040c3e501640d1000c3d000604000942c08950484500c0000f6075601d001051860986511034070030400d0310f1484044c0400c0516002c200342e403c5550140e55141814100440b4105140749540f90009240d9510555107400020b00040d0009001d10407 = true := by decide +kernel

theorem cover : BRFrame.Cov 582374100 582553956 := by
  have h0 := BRFrame.cov_init 582374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 582374100 ≤ n) (h2 : n < 582553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
