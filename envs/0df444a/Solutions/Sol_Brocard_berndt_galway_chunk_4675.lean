-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4675
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:22:28.540974+00:00
-- url     : https://prove2.me/submissions/cfff47f5-0c02-447d-92e4-58cf59dfbbac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 840647482 ≤ n < 840827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 840648732 1250 840647482 840647537
    0x1a09040f05060c04050301200415091d0f0f040816060b270f10090c030b04060b04080708030309190201090306020d06050112021e0d0608061006270312 66
    0x60348940c0341505041c29900f124600c1c000701c40952a02540c030041110594003070303440ac0e0b01c440000307500380388090301c001c2016040307400784054000e04d10801208030482d107481204000080c0b02aa07c0396070941c1203048081e1401081c3d82c409114030852040d19070008883c0c58040c0001041c40c3c540c000224005007180b5420158034107406840d2009020454410360304000c441c1c1000fa0b00f407505a0704000260102d00941060035200d8400805080c42500001c0484400810401107955580900c00895102c1d10812034503015180d000940040044240c9100c2e03291440900007405c1c0314040c01c0c14030308042c4000c0341032040e1000c003c130100704148054100700e07034202000103450b4103050002d8403071003a1101c0403030514010408a8480a41c1e80c20f8400c842454aa485480383c001608090140620b0b0b00680c8051084101b084050541c4201c4181180e07010b4a41003008c40424580000da809054031010010543c51030420010b8140b00078501c8140d120301d041540390092195140744401c1d40074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 840649982 1250 840648732 840648751
    0x5040609020705011503050327120708060c0a05031801060e07080105180103021e01020709020a1d090f010b07080904021207080f010f0605030a0608071e091a09040f0506 74
    0xc000b820002c0034812085e03000c2607401c084513101d16503503a8070760700c0c030841c00b55100402d1034060345034003007510110042440d20002c003028640c11740684069950030b0288660441c5101d00404205078400d400300b240c2d000700c40c07503a800345141d6540440c0700d40d0400500c03072a2001c4d03584410010707508400500e0310b402044e90b5516150709516081c01c21580000070407200e0030320040c010040006a1360001c045007280300d5a56121544001e0100513814680c1a43c440c401460001400c0c6030a15400b4420b2840003410807408281d5240d0b82d17040c41440c0c081110700382e800f41c10800050141d9a0000c0182145034407624071680b4021120f0b0108050740c10000d00304139045505014801540d800000259000702004d200d241d0961404030000b500400c248901e030b0500000001080ca2104240c1001001e06400300440d04000e545604a460000c40c0345c0407d2480390150030f021030360010b00e00443c890140c00c1412a07204000c1101084103108000d001111900303111400c0400040701446650b10400740130703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 840651232 1250 840649982 840649987
    0xe100305010605031219020705130c08090c150310030f06230601050a18050604060e09090c13180501050a06051306050a15020a050f0105060a05031603110a0504060902 73
    0x40c6086401c0d03030403a800c4103201e50804100300026000f0b12040c0e440400c65185a081980300c05c0741300f0703418205142c0000d5041440c144104105c90810703041449000d80c140d031420500d0b07030394010035912003690b048255170203100b8001000d82c6205840c081e641003451032044a62a6980c0d55030041c0441c8080002c451998079200d180204d200203074040e80100f6903440e0384100e03c0c07418400003445031150007144030074070503080d11103040d0341080500e54015110140c6190340d115181e0b640034104801c4c00d10707510702c100c11201c001401c004010800c0034100304068040102e008291518a0160490500c400380903041103040381e01080007402424000d125030100003400c10300340014440518581d80c412100d039428960300b00b0960b2603070031450b17041b01d041007040082652100400ca09104c01c11070041c002c2c0c46840c250080c034600651006000d000c00701c808104407540c880074551180b0b1400010030180e20400c000700003080302e0020a8009504c014540c843c642e40381c41c0018200c8809410000c8a568013 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 840652482 1250 840651232 840651239
    0x4030e0906010804020d02090a0b0315091e1507120c0f0f030b060f0708070c0e01050a050411160501111215040219030903050415020d0f031e020705070e10 68
    0x180094001a003840c3c049000c2c540f80d00401c9078520f1000009001d03c04201c005101803110341d2042c02d06410007000d0740c582c03803544030103a0004c140688003020030740624004226110203644003005003070300030301c060180152186842444a04014201010300c4000640320803090040e1080e0514900107071540080e400301500c004122500942d820014140f400748080d0095450000b50303045090030300c44c807070741e113091600d054009801003c1d0020080d0040040114180d20704884050503070300c00390344007800242c1d12402c21094070411003540031402000c001c100058126001c078404480e000381c002007200c220f20f00101b00d95a100c800ea1140b1072891074180403003265459004c1120b08001c0394154100051115400301c03c007100a540c40515565a40e80c90401d070060017510000c046404030f60b10400180b01010752106803c90203030340011070b82c080c4401c86500911680751850f40c980c03201c0f04c1d003006582a15009501c001015036081c410014005141c03c03921007003e100c0c041004900811925 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 840653732 1250 840652482 840652489
    0x2b0c060f08060303160209190908030405120a091e0302090a2009010905060a030f02070804032108070e0a08070b042306271002010203271c021504030e 66
    0x3000303801688660010080c2d4170910358002040580943c046404013180e49440c90395601000c0700b80c0b49034901c07030b080c24603045c203003c1700d0720207144100e0240e800d913400804543c2e040348403882034908a0021500554041c4a81401022400d61109000310115403183d12a0000344a0301c104403140991143c8600d40021000509000c070f4440500c4088060700301200708001901040391401618010440802c5a03142a40b0031b400c201c2c51100c20020465071010b860601c0c2c1032581c80740c041a6004a9150070201050900c1d071240300841d60340345e41c0c1c041c0c030342c481e0002144e10012000321658031a40c10980801d0100741441010002c1000008250703881b4a425104151003414000300f01c034100007911550744c5601e450003150491284142d038012802400c0716138850441c80300ca036940d00081d004200a030410740560045010344000500c200100c0b91007c00384844c410328080c0200c1a4106402c121000040e408202a0318512401a610071580124401c2c0c6426421034080e00044ea049040c0441401d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 840654982 1250 840653732 840653747
    0x6051504061212140d0e03190509130e0313121202030a09091805011803031b1b0c0824180a0f020f03011e05090a022b0c060f 55
    0x30b80000782a00007001600e40d4808030f081c8452000601403030910042d00c4583c03500c201d924480041c0300c204074896886c0d558603902c0c0c224150002c210048240388503e07082c0a5410f490710110014043d03411400b0070310141c0050300a0f224007090b0343c8018440c0201d1100c4460098000c0e100552035840c0d0941c003801c26030141064401c0200035034000300103041080381e0100800c0140d807040c80011071501c092410118004035800b1029045502c0c080f81510106008040c90b4246400b994060100c03d1204c140c0c20075001e1034821207008203410b03400c140550f0806400e8400c81342c7c080e0524644060340d40244d18200b07100508011010b41100000c204444034002c0140c0e006400003c01806460500c2052580c81045a40190842c003641da00d020441da207000c80103050b10300142c001d00c010700c246444a4210950314001c0c0c96154141000100d1500b000600318000b1600140450008668034800780d24242071100c001d43c044142031a80004140a2206a80207080c140c3d1403035034010350380d44020401c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 840656232 1250 840654982 840654989
    0xa14040f02030f042a09050a061a0d1107020a030c170a1211010e0706090609090216080304080c0601120b0f090319200a03080c0901050315030a0605150406 68
    0xd8418414410511030507600c80c1d41c06940b20317160856140b6180030410b045149030002c40e0750045004800306420300c4903080580a0303a5804c50a1020644031001039000d2442d501d01d07101c0900087c07200201127803403030300518403800244104030301d020b400d40c01280307949103181c100796080b1403011002c03c07408003002e654425140358840600499900ca503164802001c0c81c8000000f081f58112549550341402e5000300030f8081d20740d044443c220b07600c400140c500c100a126400c0402c60860000440907a2030080f244014501400b82c180204c055a441e030994001402c1aaaa030074103002c1c2c0122581c2c10010503020300000a01e44d8202c61b1185007000d54003500a010041e50b0200030180b003042c3d04000280c1d03c101081e507404480c0e903854004125284803448441c442109041d0b600300c11841800707e104000c56000780da44090303030759401c10014510f100b02c401641c0060800c000044650900300d102d013105540c018251040c1c0340d007a07100c00090f0f60069031018036041080c00052118546071040703800a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 840657482 1250 840656232 840656261
    0x150402130615120b040c08191a150d0c09031103030702010801050616170a14190e04090b1008061005011403040309081f0507110c0f0402090a1404 64
    0x40d04003041e00034000c4510030681c041c0030b41440004103d01c0290840005a503014104111220a906005150b40c400b40c420180500b18034410491a50f00b41c0039001140116000b00566030b03852006010000ca1030840c400308084041c002a90000864014045400d04558404041c1811410141a9565003803401740c1300b5801000300000503600710035202c0c1140d004848075510790401006400400240c06001441d03001c10510f00f10054410340c02911685070560341d00c0c1d00700d82152400014a100e0075050102c941c00204940f004540700383d44c4140fa0460181004ca00c0310240d80c0c901010034003c0e908454451101c2005000d201e808005485c0c0c00011440c001000328a00000a4110107075031a41103800d40c4000005428507006103540c8006042d034104481d480e411900901d04189181d0b1003813101d035801d003030204403840d00c54142d9a4401071003074060002d0700001c6081040624040c4241a001038003400050342c00d039074030801c40c401010360f03050340c4c2100d284041c2081304803002d030202250f1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 840658732 1250 840657482 840657491
    0x31302011e1107240e0f04020a1713021e13020d1b020d0c08030408040b0301031203060806040b0106050a1205070e0405060a1406071104020a05040302040e0f120a05070515040213 78
    0x41070508072401304007201c0030304140013100314800210344180350716000980c00071b000144c3e202c0a140c0c001c00d520350300c2d00c0c1070342c80c4110382c2c992421980480304c0c2910041c0d4000304409440d032242d0a40c2c000c500c00050010040b1880c10302c4980820142e820442040b202207076900a040705035900300e41c9154010f01c00b4405802900d1a01c0d201600d540d10510000d0041000800060200103c00c41100c0103020b40098407a182d6030f43c0d140080e240000840010002401d2410000d568840040c00030f005640c441d00607401e5a0820340101c1e8541c00c903070711100c100820242c0d9268103d41c944070300c43c001d82d00342c0c0d50580d4178980c1c1c01c01c1c801a00c1c07001d401e07140261542e01c0d0410141e07100310b02d06d00c4805d00445060340c4d114002d0070700c003240c900c4401d10540e102c4d10001d0440425034110000b001200e10944091040076062440c0304d0326070b06103810f01d0a00344c104822903050310080300000d0803000154184181030800a4030b4051801c200066808590700049042c0401d51400640910403614041c01c21710 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 840659982 1250 840658732 840658769
    0x60e010509101a09030a0c0b0318061006210606081b1303020d03050c031606060e090c120109140304030b011703092205040b04020103061a031302011e1107 68
    0x240e4003035180603c509841c0204651100e6035042c485000c1035904550012042d6442d0410014680c2c01a100c164030500f5449200544800105406200e80400d11034400420304c0d25074190b4400d00240036041030300c0b24081c00401806820302c40c2c0f8020345541d80c1c54484914081149521102c0c520f044410441021711040e90010640e000290581e607040d6002107050190f4581034506018100a24609010100340d801c141c0f80c9242c18250f4071805000240720307650b076450080e2448901600c40c03802c0c9400c00440080d40c1d04042d08680082000b107400001c0e40c031a151a840c501851003200c90300642c2001804000b8428400225800b40c84001d000031505154109403503540d22840c900f41b8000d000c1000d420031070240e8448010a4015002d01c00d2069180c030b440c0c40d000b070302c008680890101e4900340000c500c100c03602007407030b904801801009103140c69403044070400352040e0004a040090305000e940c0b48c40507100c4104c042e44400d445000d0002541c1000b2800c103101500b003c07188084102108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 840661232 1250 840659982 840659999
    0xe070914060a111002031f050603130804050d060b0a170d081036020301051804060204170d14070b041202100204060e1e090115050d060e01050910 64
    0x58a205412a2a69a111074141041d10f28101d8140c00e400d80d8095607600b0a80c04286800840c03141404207454180007850520003042c10351103000701d542102013400010240784412100310350641c024049503052965650024585080112003124056203858100740681040544140070344404070282821034490400b255492241600e51010000c2030801304101500c51440c6401404044003002d909414408842800b5280b480c0307282d011100e040703000008506148250ba041e01d13001400c2c50702001600e034001910a801501c2610b14542c00c01001610351041c140d2000050444e2015080c5542d06140241c07201c49030301c0100705100300c200005e070001a103c0c2c0341c240c5c0c0190b0119500c110150030394400c03031070990010a940002d5100003404aa0141c100600d9101180102c1e2020404480b0803141c040801c118140250000e48000040c402901c0d00b24088500405600d4003e040c000201c010b4401d0f24096445001c0f00b1046500500903810b04003590703544540c02406030b90300145080a071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 840662482 1250 840661232 840661259
    0x6130501032901120b1005280509191203030603120503010b0a050307110d050c072907031b1a010603020a0804140a05060f0f10180b120f01060e0709 65
    0x416042118001c140081440c13954808042148040d001e0140350201c0c40d40641958400b00e10310b02c651100d42d5510b000307540000d0400307400d00165542e042c100b00c903000610030880e460300c881c0750621454078000f140c18801752500d240c140e0b00039500030503580e2850404800084c03c650102003080303010801031024207910070845442240500d070165482d51800c00440d04507030045c4d50701c1210700a00c107034680b5070350707108024043c105010000d40310384645d1240141c040c906074500040120015440ca50104070013040502030366802400c04010070b000c5c40c2040c03580da41ca8524100c03404e420003030420f90610080304e60030b03000d040141030451134690a090003801044005000074071440e01121a0007200006105c0e1188a5900c03034122a602d0601c601400003044044076644c0e500e07101c4000003075840071200020011280888403044d80c4d18140400f86000e403c40914640c1c01258003202e201c0282c00030050380c1210410507000099440c20000f0001250350060251001c02505070024071012003003961 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 840663732 1250 840662482 840662561
    0x5010e0d170f150612041a0610020a02210709140a0b06071b0b070f0525090506010912030e010924050c100c0903121d0f0406050613050103 61
    0x441d40807881a0070b00141007417148000d0b05900182032014041001801805044094407070b031501142a13403102c0c240030303e0300c000ba003a034001071780240c0004000d42040d2840013460741224414400141199081915003c180e520100c07800340e403008500b0305810181403154221a101805004100c10135001400d64080c1e0007001d00a60340980803000c00c89036040c170150083c00e001a501d5102c2d4240c2c04d00700440e90715080103454500170030300c0d03400240d070410960000301070640320300c1d650703050038203034400014440200b215051001c40400402c4840c034050083c90302e1407003076136041c0b1503848560004142031296417029214403409110701c0d5442180780d81e21700380000d4910f0f0807034845181722501c91401405040c010200c904e00004c0025251b440342c1c1c0c40d0103a0b03028003507112030720a591404890700031910010801c0ca01d040c050b424042c1c0340000f02000990002440856120346a20004a07030341e0184510300300741c1202d40800c20465825009003c05c0180f96612402004c030050002ca81964100c074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 840664982 1250 840663732 840663751
    0x70e010e010f09090c110c030309030d0828020a030f1a060f040320031e2805070f05190e040209040206070605070806041d0a14030705010e0d170f 64
    0x385076510b948200e1050009000c200c1040c000a00100f10282440c4c0d404a00d0082030b0080301c0d0301111500340003003266000e4030050000c104080012070102e80d07201c07024100c1c2c109000f003401020b03103998902c0300032000c2192503039006940d10041040942154680a142c220003030402070b00c685614000c45d85103041d01d10544000365a040e10103812403c81c8100e420003007100606000315039800c100c074071100620090640840e81a6012000b2000e0741c3e401501c8044640d910000d40c0c0507144c03100c025030200e1841d59624041040c165503841c130f802d0452a07000040c004946030010001707403400d8204150a604512840c1010310b04050076900d000c50010400f0b8020342c0e90f00c02040842d214030b41262800c0d03401c140108914240150000c00c070400c2031f13400d144502e043c08000061030006094a0042082e680001c0c102e5528507a00e000319114000e0504c2002d010601040010030303028040c2c0e000d12003000c00a07060040704403501410300c0c9510202040728290080c200243c032040300200507005100038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 840666232 1250 840664982 840664997
    0x2030c010311041e0501030e12030a02130803030f100522051b0705010e010606050414091b13031209180f1e1d010c02030901080c0c060f0f070e010e01 66
    0x20102128035110b10743c49180c5404010310301281c40e581c421a132006440e401d0364180082d46040c0030041d40e805068070350580b1888104042201565154003c2001c50705600c80e0000e20360307641c0c080b1811900119a14006002a0790401183c9102490358002508007140c1c41602c500c01c500000b28a18501c40401103000e95950100e40ca081003000701c440c1d0311a072050a03590b691400c0c50500c1c045d084294003104c5942c2040c00114001d4001c034103641c26580301c14507a010104881c000c00140440180650305801c4001d80040400240c150050619800f900212003010340385107400c001c0800318500000801c01c040105200d1221007846103c0315814101c408604e0b00940c03c0004018541c1c41da07401008601040b1181ca140e805410688030358280325100c2d61064640600d140c281c4070002c07020350043c0c008209114181d070085076256002501c00480300d0410b4001c002c164540081550b0001c02c10900c07004000c541c45021400541c40f0703015103025010302e8802d0002804500038032a5950620016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 840667482 1250 840666232 840666251
    0x30405011d03250c1e0812070201050d060504020c0f24060907090518190603030503190f02280306050108010308160605010b1c091505180f0309010e030a02030c0103 72
    0x70300c012444401e80010004034070b45d03528405040300600794890308070a6800c06200140d80c5801003141060076008014a6281409031743c011140b90340100201000d0316510000414a5103032407003d0000c020051000303006064800c1d4600e440c0c07106142d03e0044058005a11540035200354565a0700300c00282d5101c42c10707841e03548054503a0308641e0415a0081e40003111000311400c85022907015081c800520084084566444410b40d405404082c0105204001003001800e40c0e004505020007143d00004643c0407200c0c0b4001680d2104d480314102c220042002002e4410740b41400004400500702001791130710308000030381314600c14030000e0301505021400380d41c045811400768010b0b40d1300a030304100560311180d40400c1c0343c00407900007464002903008003440c20958031034a01a6900440c2c203660341c052510b444030240000401e0341900a21801d60300300d07861401c0140c110601c01c20006540c6641e003940c0010210001e00010a100341d02240585001d62004110034002150a2802095240c00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 840668732 1250 840667482 840667537
    0x20c0f151312030507020405070c030c030509120a0c05210613081b15060316120503160b1b0f1602120f0c040e031e1c090305030405011d03 61
    0x750b0340c04240340d280350300c004000b0103621800030980d4600c02c80d020455030b26416030440d18400340341001004910140b1755400424010303006000503c03c01010840e44c1400c2e010024148502240204c40c0380e41701040034403152400c1c03c3c000e01850000143c400c02955042581540c414001d0710341d00c003904209148000384092a030840c4c182100d03030740d54030900807803246000c0e40c0d034004d100c40903c0d00b1220f000030600c40c2c600827071000100d00001158407a000d060000a40040307011a1048891b84820000f4102405d400c41034104c11f5400f0300404e41f024a01102902c40e44000c560300c80c0b19843d4200f02d24a84200307240b003541c00500b103003180da6112200038800300d036903a480554103008521420300c40b001c94840008403085998001e40d0f00b444848007980c1c030719640340101c140c0c03e14400d2188200345903200c6c64101034140d61032608501c010241004401c83c044800e442016030020304004100002d0040074042c00014540d070310480100c100602400b180c0340d0041c05186c04150800805c0300c002c150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 840669982 1250 840668732 840668767
    0x6080118020f220e0906160f050a03150306090b100f0e0115030e0102030a0608010e01020307200a1b0305010b0d0c21050f0f060106080601140c01020c07090c020c0f15 73
    0x184c490100e9003500f40604602d1782ca00088840c520180410303d030a40d49107205404103085a075450f10b5003404c00c44168001c0d00034120f100c0240303c0485e280c600000c040341d42402340200340c1d0b008a0341d0103000d090459860130902600d0b0092455014540b004104842c44045102e044402d2250103411048200000f10003a10034040c68074500d60000c4248454100203078050b0040700c922400800201048a103d5800c0c0c3c0022544000800c080d000880031a03c06600c600884140107816510004002d550780c04c000c8080c5828058281d01d840018400c0100c24812044810303821983d1000c825860b80c2e0322000700380365003d421000d44041001045144082e01c0c49000984c0c00002c0c2c40880c034141d0039507507640350030b0099044d02c1d214031000040d07407601a201d030394080c03001a55416015002c1c20b404030700562005500100c01c1d90700b080b600c1074070101400b14a0203410344200210380024007540081c905810550b410b1310480554007804002e6a81140000b8030010300c404190311515070055525000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 840671232 1250 840669982 840669989
    0x61713140a0c0b180d110103020912010f1a0301090c0603022104050c18090606060306060c0a1104150605041809020a0e040b0a09020603062806080118020f22 69
    0x620145804030b03c0c45900f002900f220006550020500240c000c1040341c0c0118402c006004401c55100c007414a5100703030020702c41504080c001050b0480e041ca4528211391160340400d200c1a51080701200070f00e40612040b4101004400034400c4000c0c584404450308040c0c0304000505500160720304030b080c410250141e00300740221201e8018503141c01c00d0360702c410000100622984414990480790704041d40682d004035034446c010070b00c5507a2a014060540d002901c6117038040020310040320501000c001c0e1034003a600c1811080b1150340c60342d05100568004c0c081c844402d222410050005551060589080f00c0c40d8540c2d0b1200382076426140c03801130144001c060b400401075070000c1070701625a41d0181c0194891074150340070ba56002011f030122400e8940082d8405400c00203d2000d16100303508002d00c1104001740007480200e40b00359900c045c450b51142000c55a41001009820404a207040345c6115035513042d450480840310800301403141c10800d0b074007112880010404a85401c0c081c4016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 840672482 1250 840671232 840671243
    0x3220f030311010f020f12100504020706140603060618061201020a080907060504050117041a090c0307050301050103210e0402040b070210140f0f09030115061713140a 73
    0x9854903800d000b40a1203020588490725070070000e80d000506a10310880e040700f1a2080954289841843c154440d14805820a9880c07140703020f0208407176442c1c1c801454009d108401c0000c0400c4120080004604010103180c40b0390000401c2014a4a450002c0ca840e90310310607000d44daa543d540700081c0c0030002c5107003011582d880400c1ca01241038001521501070341110301101c00c4555190030450b01c40c402ea0060f0b900084842c10708490261162103800c1d041445007115403c8840c145824228401040b01e20380d0455000c00360420b610305060050304007601060740207022540c1161205100f5080216508100e041c08459143c0c005200c3c0c40007108040f00184203642e0f440d910064080399400450007070740301d0540030380811344581c02403a0a803034600a10f000107041a20318014220a50000100c0c0000c101041080c141595070a115041c10036040003c6508842c4c20440300500d4403100480c602e142216002c18031a621840e000e07040e00b0550700c030074801d00120a12400e241040703100a8010f0030f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 840673732 1250 840672482 840672509
    0x10c08120601120c17070201021e03011a0708190507140c01030c08070804140a0209011d10030302030d090201031d06010303120b0d060902010e150c07090e0322 70
    0x10400003146400c0d0060707500340e841050092204000780d04903100311041201283c518a01da00c84440c0304103010b07034031400f00e000040c10481308948415401030241c40b903d540726000030060124010030400c441802c0c0950700500d05040e0680d5035a40d0601c2a0a05d468840b00d5940c0d5501c0c85600c41c404903444039a00a065000044409038a82e580b1100382511501217030400366071107500c40c890b49019101d07000d42d554001d2280c44648031740d0103649171200b40f10002e0092030542c00160b1592110341e4001d2121000c55030700c0e0300d1084880c1912800141c00d00c2141c42243c90100081b076400015220306440a0b803000030040004d05c0107800900b01e0300d21020411a4070100c199001a021030082d040324000c0d00e5142009599000c003804490f880c00d1003d50007022401e00301d000c03888690090b10400e1040c100804030344201d400191583d1071780d125124004400054200c0302600c184907201c007d0560000600442205800b03541d224000c0e00181c1820000405103a0484000c1c1903c0304005d0121401250 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 840674982 1250 840673732 840673747
    0x2030606070c03060506100e0d030c171810090503031b0102070b01030813090b030a060e0102090a18060e0f0a0f0b060307020102090102011d120c120d050f33010c08 72
    0xc0141c001112202e01c1030550f10007e0340e01500524100030755001c01082401d18004a56094034492102c503000d40d101c075080441150780d00824402400360a03540f25500c410345680c04100001a042c07059050200405d00b0320030025a2000000e4900d19103034280b26404582d0085640f6009019890016002c9010040000203002c03500009110b02e0722a40301c1010425140e00800d001c1d503850800c2d043d05940801d103114081092640049130084510001610b003c445100044200c022504210000035070400302240c600460311881009002d62245d502c240c8c50010390030740c4808002850712140c55100c00320010100200d500902200900412043c1c681c100010000e0003500a1036100340590b05c0c105040e450055210b885004102ca040d0013880725045400483c100f80e08105e603d90f07018420724003c03121080914002e40400110f102c0001158a4001c215502400024203036401d84141640c01140340c2d03d2007040b407400d40704143c000d01850640c0e400103c4d12000103140227001d018000ca00413 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 840676232 1250 840674982 840674993
    0x20607030302090423180304080d080702060108010c050d0b130603060b1c1e0212071818020d060c0c061505090c13050d03110a060501060206010603021c02030606070c03 74
    0x400c580c84003a036080100e091003005c10042200c2d1090300300303140d851110000e41051a0810150b50014420040d40e0805544008403440e00b20100d00c01400312f040c000c01c00c01c48036410041c00380182012002805903802258001e8a01d22460031518215600c800a1010f10703100d1810b13101c2400304500040100d45d81d0f0b820100003c26650131240e100700c2900511151600ca06514401c1c501e0300481c800740c904090416032411400f18480481c0c0184020840c016803000501080c1e00034030404c003c4a018603901e501a02c100c0708155012050109581d0030000903072141c3c011102c84943c04000081d035910b8141d0140d905443c0440700800c141d0070920b06007040c0172050303850030440e0703003e403811800d580724170340e030580c2ca401076428410300c0b0b00e02001704008514005070300c003000038003a04144405807900c500741420240750440a40b055502c40c40108079071541000058018607061500b103040c2203142404219001c075281c02c00e40c080782c021002c20703950359641088030841c03540b00c100c0d01107940e540d00d0103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 840677482 1250 840676232 840676237
    0x140307020c0f01020703051213080712030e040908031303140406050c0606031212100b2a0f0d0e2704110402030411010c030314130c0815060d030c020607030302 70
    0x14000d0b02d803910a00c40c030354000548a030130f0701d03840800303000011505d464884070303a000310100903420000c2441c001020034040c888040a00f00d4460484010360140c240600740140405c2c815005526009490010408040689400c9a5031a16851024487c1d040468540004812880c0c403a0070010340000c940750040f0040c1005002c1c01c00356405e654030b2001f01605d0340e0112030344020040d020407007501c3c5c480e40d01055960082c40c10280c1b9041c40d449000381c8030a9040300c081620701a103803041d80302e08001c100100d408440315a00040540d98403a000c8242c64025120a490510442d081d891290b641c90b0030401055114180358070f4540c403032024100311280001c0d1420340c2d105001498043d41030030940200c03440ba47d00078604011084c0c00e00c0046030301d0403c001e03040c1c00301543d500f900403003400b000c0340141c046c1d083d074071082c038040026041290030000154492501684400e90260030811045c02da9540198119410440140170f41001d4440340c101c80d0000354845030008400c4205605a400b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 840678732 1250 840677482 840677503
    0xe030705060a1b2007230307230418030207061d010207212001090e040b01150207030c080303010e160c0602030a060504020417012a050a14030702 64
    0x7211081d84400541c40b04644000d500380c0c400410101400c0c1146001c1c40760080c0c81885400b000702a501c000a81c1070074808135421000070454092100e06800000282c3c12000c003d0880c05044120325001a00c248041c0340f8500b202c80800000783d0702e00594803603000d07120950110030345000c001200e01d0300075140c815a01454002c0341115401007001c0300f20400c203446602068006120642c21f00034008404011001c50640ca20001010b800016000351012808420881c400f514444100000500b01c5045504100100c01c0140204008100320b801c05030f044644a840144001d10a18802c9040c0b80443e0006812000d19080016242c04000000d50489161003041c86075511000d50000c040700d030f006018800143d17402812004241281e000b1070f001241c00c200060341540c1c4c0c002040c10f83c0c01a0f4803800d061450750804009118007030145150201c0b110800700030001402081e01340010840e400001041004a2201036450084004105288040007650384030b142c01c41000303588051004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 840679982 1250 840678732 840678743
    0x3606091109041404330c0e010e060a12020a092c011202031f02041505040f060503011a0306182a0c19050a061803080f010509010b09040f0e0307 63
    0x4a0300202080685030725014580c031004090400040e51005200380b00c0d540401c0074400c0a0b41d0040b0810745180c8116000c46c2e100351510304100c0711100c00940341440ca0b03038003140a507204101120f03105910403000c103078a0000700707401170b00d400c0a420102c85403640c9410241b1342d11a4200c2e030100002e8203007031820004081c4810744401d681c0307408401441212030040207405a1010440541812501e00000c041001c40500181001d035500c014841b480000941e11010030070004041c03210b61098807010307000e8046420424070b95407608460146040408041c4100a200807011230020b42da51140741d110b50050700042540e50401c04820500c0307052070201084800308100a2012404407070042d1400300c440c0d42c000c0c040380413414500300c4c00800b010381c003200c240c005e4882c1500001c1d207500c01d800c141c000d40c00415540ca84189800380c54003201034128204080d00c4001008035541c4e0504442c107440d0342c108043d0b250140c0074049400341c154034801156142c1400c41c0492000700002c0540260790151 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 840681232 1250 840679982 840679991
    0xd06030c080f07211a130302060906040201090e070c060203160e040b030303061207031a0106121a04020d02160b07030c0c05071a0706061e360609110904 67
    0x1144000d644a000c4e00c55070641010030107401c2c40902000d42110b1009008821000920f021030326107845a0b00116801c0708035100403030390401850b50401540d903200610710300a06290529070000780900001d4400c039107840d04620000381ca0307244946550341c441540120127640341e007090b18421800310f2039180310000241c016801c0c5035062600b03002e56030117054007501640c955200d010500c0910195500d07840218030441e503000000031481c5030144814a641449242c655060510051000103040403055140d8103001840c989145c00048445400c01c2c11075005958441e00f04c15600039010750040c040d54154050114024040c2d060840da1281513aa9020411003880c06401c0d40da0140a91014016604c0400c090000b80e0001e20780f060750072440610141008402d80d6a8826508150084402507000340c1c4808203903207030011020050301060280300b600d6201004201070030f0805240c000c0c1343c10360100c00c0307081c000060307880000640344004081c4111500d030407140a0560080c8546400303180741 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 840682482 1250 840681232 840681253
    0x42d0b090105070836060403030c090e16110d020609100608060402040b040228080717150a0b0708070b06030a03090308130906180c090612110d06030c08 67
    0x1807003500d1180d031031602d4100c0b15407264456485c0c0c0c05600c4036001982c0c12002c4e5000041e500302c0b149078010a07903c0004003c580381903c0c00600fa00c03440e1000748140003221000b0300528180c007220a502c00500b0845400c1d00701c0c211000c981008944401640b140101080000c00f1381d07011900f203109007030329812541001840c1808404441e01c0d845101070640241c000301e001443c0580101101e940020005030030807000d4401c4505c40200c444254404c2608144410000340e042888198007081c5c604104c41590300c2c17100c514110910080c180983c0d0745a01c100c41c006550b45007104400b800000c407401d0b850b1400c82c50003410980c0103d0040d5a10050280014030924001a80d80c03d43c99040c0c0c2c074080c1c25451555083d0b0035800090820b400b050a0071000300c1e69480034442d00d03004102d06160810701e0b071012104c03802161010b012440405c20400f506000d1550071044001151491041c00611182511849240d90084182c0b400072542000800030a01401202540a9803009800c0c3e0305280321 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 840683732 1250 840682482 840682501
    0xc18100e06060a030f0f020313030201050a18060c1116050301050a0605061204080f070c0e090a170d06091d0f0303010f03022101090501020a09050f0901050603042d0b 73
    0x2400c5500c0e07a0b11240c10444010154803c2d00300c014808900b0601056044441c14100103a0304100d0f0300100301c11141801c0320505609010f240e4100d03481352400c00c561469140071040200b02440c0160050303031104100761403d4811580d00796034981542c140ea00303aa450880600055400d4030880707109600340740114a800ca050f21411007203401c0142464900700a17a282c1c0420200014816160702038180021454000783c14001d15005100329401c0e9009824100402800c1d407028003030801d03a6201d4003400000440341c2c140386070b843d16911a01500e844d00c601041001d40b105422110b07115003004c0300c4000c103c10400030340d1130300d90300790080d42c08080d90711581c0c0782c1e83d00091248101003030b10b48004002506041c00d0543c6450340b450b00c45032070f40c900224080c6c2502e14480c2d084900b41e50001d00d40c81803692200405020f03090444680801c2c0c1c503c0ca0014075901c0040c0200751040748000003117800c000609214140d4118000c00c203411001095002c03407112038020b5070a5440113018400550304c0070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 840684982 1250 840683732 840683759
    0x15101508010b07030e220b10030e1506210f0c0118090902040228030614030304090c0216061e050306010f03150f0306050a0b0108010b0d0b01020c1810 66
    0xc0ca052410b604100d502d07182168400c110200d0190090301c40e88098034881c08041c0c0d10801010307646408038850b2056424003100d201c0411201c0d04061030402c0791402d4440100e20b5130a03e003d079080850240d212800020f0b116503800120200c40c0421a211800c160030110751102100703040c4098400e0099001c006458240131410f002d1503900e07007043c00340001c5c04d1a070b01c030030420390000d0f000605219100c407811031000c41c1660786000000c089070442009641c9405060b014110002d050742865403a40003280e66402680680309159440700d4024075002d10070800c1c21084449000c0840c0087c0c0d40d80400f40200004510081c8500082060580a280280102d902604041e9190300019614980c124024070152454400706841c4040008005112081c0400518001c80000a450a101e074081c001c4801104d4001d0600007003000401041d40740d042990030302000d400003c00c4103441700c40100d040541041031554052620400c0c4901700004465039480383c40400c084000700c9460751000000d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 840686232 1250 840684982 840684989
    0x20d02120604051635090c030601230108060d02030d0801092a0528091403070305031c021e03090c01141b01060b04030623100905091510150801 63
    0x11540d0580024030f001d194098085030701c5c0000050500e150f010142c20b2004025981581644e225040c03029103442c0c01d2000600401110440c0340303032915102c01e528110080c1002d901e040c0480c07100010b2261b16075600d8103600560040503180082c1c10920050020802030043c80b985500d40f201d481008203d041d201d141c2c1003500e0220841035801004203c1e09580407115030115141d241c020000c1142201240d005030f00c2d0241c079a040128100035614000091003400c251203940301110030804074001104544d510850038a0200c48400a03092450182c480c40c8402241c0e40d800c0404203452159210196006500003000c0d19541e10540004440503d41031400c40c03c11542081070000000030203007024a40001940003041495031032503101115041307135000740c034816120b46042003600b921800c0340810003450f2060304103d003410300307a502a510b603038001c08140540d40c0000c281e9584041121000511900c040400305142c486000c0100369664819507a10441900c5040c0c2120301032240c86041c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 840687482 1250 840686232 840686237
    0x3080304030f1b0f1b080601170102030f16050c03160b090c1e040603062a02061b1605030d060317090d0204150308070f0b0a0c0e0d06020d021206040516 67
    0x3030900c0703840e0004c000402c41d204541481c2c40c0002e2004003c6110800b900610702c910250100d0f41c940303a00300b488140b03800040c210592040007000015540360402c20317000070b10383e03014001a011160b01a034117442401030f079020310b00c408076031103045150400c003141d44240701720031301c076020303250b14014039506c1104607500c550065a03103022003030784020159800c080c414000c202103040ad65940756002101e40c2aa00e03c9004e0300c0200304180f103544040c1107000804401e1004000f07500e00607549600090070310782008005a4006600c4180100041c900c0c1041500032041d40e82c6c0d01a507803070708401440e091204840100c5075440300d4800344c00d80740c1515041e042c042c0c1041030202c025805c000040c20248541a4100d040d10740220104031800d001d041700a218011031207803040715060580000d840140398500c000d08298a8401095003c19a40c1880e8401d4820300c080b0300140c60408040c0c0580c250b640419440480c1003401e100740c0105040c0688003e9074208415111003910854082c0150211400b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 840688732 1250 840687482 840687527
    0x6020310140d0b1012050708060c0c0a15141f0911040509040501060803041d10060c1b0b1c0629030709050303030f0603010e0a051c090f03080304030f 66
    0x412540098194003035089450100c04c1501c0d114076281c1030070510016a050b0340090414001220100701c001c1c0c210103d11580350400c0500188541d0301c1c1c56444008110090b81805846150021b400445e04151031508400b51458001c140481a410b03c8040300280d0071001c10015040d1aa84100384a00036200e41540c540b506003018410500000b501c1224190340c0c80b00005462103003030002d000901030403a00c400b284400d1844c951a841c0c000f5025400401403020200b1038650032288266140b41d00400c4075030a1742812070240d500d000c0d00d9101843d10f020005802000c21840700b04000440f400150803c40151502c01040c8981c0c1d4231065541400c0b0300310125401071025401841e031000b65171030450b2a881c0c40d980424195001941c040c01200354000c180140740c07800f80280c0c181e01008030000c1171801299103c207681c3c1c031000c5103100ba06203003010a03c03454501c02c0700800041c050300c5c3e4100408e036680703240c8400141d00031181600003440f0454101030702845540c420716440c50007440c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 840689982 1250 840688732 840688759
    0x90b04090213150302032508070c0614040320070b04030305090307090906020904060602010c0c06021b2406100504030308060f04090c080607020a08040e060a0b070602031014 76
    0x14002d40c804080b003540e0390301e454000140200c500b400b03500759045070b94026071282022944154024107000c042803e010084180888640d400400070b644035100c0d14103c03509419a0070a00010105120381c0c4210050000410042c075402c64510b8404664100401c0d882620b46c042c80c6032502d1090040d8414a002008208080ae1040c4090084000c0040640d034031182e503042068110341c03450400300c40c6a5000b185054443c5840e00c1064028030030340c0000e103d00e10400c400140500d5054a004010590100c2c82d0804006010180b0380350300000421114415450040c0d4030031541420400b0700300c206c00400058141c1099486040e1854481c0c59540c101411230360242d03080b500042c18107800400c4002c1c11503299650b80580c1d64502d0003090051142c5003030044960401c03074020480c0040d90f002c807d8040c005042042110304481c0d070400c46541c1134032800c0001303400142030f43c80b0801600000c95003806020043d80114080c2d000c04000c40f03850743e5251420880001102600c4c0c1d80411041c8499 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 840691232 1250 840689982 840689999
    0x9030c120106320a032604090e060f100612050901270c05091509181c020106060e06030106080a1d010606170c2703060a05040210090b04 60
    0x840800c404032002080140e10342d0240340201034620007200c0c0c1035949444480400e003548a0001c03240c0c80a40d008510a400d41c0c0701e10485440e41c60740c9155040302c00790b1500745401200d0954014089441042c8203011124002a07510300086e00c2c0384010303404c00008a4003100b01211000200c80d0326440381c40e03c14100320074240003004000c110447c155240e1038045101da400140000340302485c552079144006850900c4500c414440d00200d0050010750184181e9800403071001070303068030031140d0800329a141c186c40300314000550001d005900c100022803000858103c054000f4048a50081003140d03904c95040700d030245c0201110303401c40c40800061108610030601241d002c0740c49070300881e0b00306038010000c805103019050080c640e503450741c0030b1007010361101010110f113019151981e80b42c20b0100b40b8094610404440d001402500f40441d12404859802440b20b100c000302a900d49103450080e003c00b034802201c0480c070800030300340c840c501e0702e0240c0405425180080a05400c150501005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 840692482 1250 840691232 840691249
    0x909050606090c300a050f0a020a110304030812160c0308180d05040810020702031905070f0315050a02120a0b0f0a0f060e060a050a080c0d050403020c1509030c 70
    0x440e04005402c1049800c81c11141d40a82c11403c401d541003e9440c1038103032181324101000e040324505504280600031510420a040c5801c03103008440141d4605015106480b01d508a6034520f586c2e000115000050018030406000241e03681c000c00d0402c1d40e148000802101d5142800d1000300700c9a13001040828840c0c54850b0b8071a00c0a522060f1a00e400b2100c1491b100310381a007480051700007e818031400905000020000622450542c02c102659000a807070360301d203449440c80c07091034030b0b8808107011007082000c0040c843d1035800d9441d551a030408044449031a503100d41002e062201041d029002071088600f0000301e003518001c90b44401031544094075917a1650f66100380f03417940031901d5960380c9070301000074640d07040c2d26507190b413401e07802515107506a0392a6104607001e0101041c42504801110840c4145103417002640e6101c10070907940e07000d824540c44080e480c2c401044200f580026201480c14412650b031440070406480c040d1891044800e05078045d0407140081e0040e0909099 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 840693732 1250 840692482 840692491
    0x10051008280203040b061c0c0b03040c0e07032423060c010c110114040c0b09031f050f250c230714190b030925060801090905060609 58
    0x200c18507210900542100360b81094406881d148985424400c245c508200007043c5094800e1681c908207440352200c80c8100746602c60f10500450020003e000c12080c50398041c00303000000d041e078440f41040c8030003c0c01428020400c480c09010024888641404042048119006018105d02c0ca800340c100e4000c090200382403c5070043c60510603804003020038091201300020a944084c0e04034880d5030303031509440101003e2107a5200003810b200214446042207016600c406035800d94034003511000c240360841400346c80d40c950006c01102140542d454000e14014030290001001944910a800600b44402c0351390500600306880804040d0340500c050b02c5440d401210000103042004c04003200883c4104500b1001340c00c040070500a8030788801840c6841ca80c240d03105c0703412844071101c190b00c000359401740c0000d10001000052002c1810000c2154004d01450040ca40031040c1c0034240b00f2400500400c03002c6102c00001040c041124841c030031030b1a8002e0001c0c09161640400c5c0300301c0181c00350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 840694982 1250 840693732 840693781
    0x5131701092003010b090c0f0703020705030307061a1021020706051e01080102070b010306092108070905060c0d0c03050f030705091539060f10051008 66
    0x31200003148101c01074000401c854070010803040c0702c0070101030840700c0802c02d4a100d0542c2e002400884008213007640c90811610f21a656140c0d401e0406924101380d80d4003860303161200080c00420400180c010000650300354030044002e0080904126011001d41c00c542c002035001c420480500d42c05885240c03a100442800510744a62912032405075241100c40558488004540e8444a948207982600500d0214000c60400406a82d03000c040841880b000e8442501d4403202818046266002c10005244115944a10185000180c40114103c0e80c0d0400306030071b6503000401e401c1080858080c00c2c0c03240090981200109001e5443c010180300076000c0201c184142c522444244c0001c5000c0c1c4680d440d6182c07034074200703410400c0d03030f40b03812890102240f030510450101503000c01001158035a010030a03c1c0719011059842c8007003025410340c8101d07124a0040c00032604021000030700403850000015816a03c0e2010b00c0000c144035554400040c400d000080c0308100c422a1a040000b500c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 840696232 1250 840694982 840694991
    0x210050c040b0c0c09010f0e060603060a0801050f0106020607020c03030429160501050c09100309150c08011701200915031509160203040b0f0706110408070605131701 73
    0x15595010b86800000940d5066448041c01070760914010350401d0041c1459885034000508080c10500b0200c8003500715801007001002041040c0d403441c0c0403101070000e45008100c00d1404451038240c0072020f00c6481f000d4003039400418160383c804640e011040d2400b03002985851705d040000f003051201d1809011501825108842481c20746100402d846620802d004440d0203090074807900711080075040c00600e6504100254007501c2d0f003010986050400c2c00c0c002282811424558581c1c00801281031905251000c0015215001861141a00e10f8656450b1134540340c3d4194601700d0700d00104103060140c402000c01480d180300e01c000c040c80040681400c0030f41c0100d04251006404c2640c031060b0003140140d9900c054200000400c1d4400a102c0200c091100411301c069202e210341d01a0f80b5541f44c0000c1c45055100c40700c0201d5040c1e540c00f46040150782c3d90031103180301541240c0900403c5000b4a94002602c80c411010b45140703a50018408201e540350171503003000c20707078005d041c0c12065484 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 840697482 1250 840696232 840696239
    0x307020a080921162c060d02131a150909150603040c06020607020a1223040308071401050615030a0f1104150311040e090a0b0412030e0d0210050c04 65
    0x410702c0581c3c00c0403410020400a08a00c0034072201140f00d401201030b8005400081c43c4c0d4000d0120484c01980708514000c00a803a03a002007151441b9060700a03400008102044d14401d650f503102c8100411154044842c40203038a0401240011040d00021601d405001403d46803902012003900070b1a204032400010441001142a0340c00031141039507603072110101000000c1d0144561079000754540302034034040340e1690312840c4030900881c08004001c95003548501071319801c0500f01d02100c0c858000780c0c0321036503407070546d1a690240e0000c1300c0300d0003080d00144110205001d480d00401c0002c0c007065007000d47c2c0c0110f26981d00000c184c140b4017900c0b001d000c00807c80510400d01505841d046a5079900e01f4180c540f4051444c1961100c1054030708004607a21440b10015107087d600ea00061840c151182d44080789010701d00280609a40d0648040c081000465905083c0300c1b101a20305010094074030080359280c0c00301c06440000360f0410510603860071107540c440d41d03012000f8205076007070545 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 840698732 1250 840697482 840697519
    0x70303020d181d19050a020304140c03150c13140102070e09030a0f030207141b061315090e01120c05180601030f200310090537051f0b0307020a0809 65
    0x1700ba244041c20f030354000b00b8442440b5030302c01100c1512606c203000741441c14000c00400d0f40c840e0f025440000c04002540416078803030f0b1240c211203d5403420002103804a45402d00d842c1c041000d540520f02611581800242044403030760720f58420407114000d1400c1242c140340540d4001442d8078401e0030907a080106c1d00c0003458074040b41c07070440009001450b0322a0030b42140a40d00d40c0d01c0d1525445140c0c18005250041048400203065485020750400c2ea001421810f031180346282e00b00b401c2c842c100c00700115000c160b0030300c5e090b0300303e0080802001150342d800c180411000210400c1e00c480c2c03002c0d0001480307540a5041800301c20b1103400700280344c4030b034406201104580e150a24810352800070520210700d05a10088000d010340e05003c0286081c11b5850136440342c10b240c000e1001c0560300100526251111101e070380d03a51918502880140f40141454076501500c0c00e1046c2c018800d03c1c0007281d103100b400c05503403040383c858005041c402010f48a6a0044c0c20a400040d0702880a19504220340e5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 840699982 1250 840698732 840698741
    0x7030609060f0e010e210702090711190f060b130e010c27050904060608070605031e07120e010902060d05090d140307050a02010b03070303020d181d19 66
    0x74090711001640010440c0000191810300b6500c0b01203a052003c100720006010039132252084e0080e40d900403c20340e10080703007628040d001e0040d510000000400c00980c2d0880d000940304001c6600b991490440810602c2204901404c0070780610a401c26040020300c5651001030480c100030802d0400464034003801060b51038540c41c1c46403130394564044001c1c180e0070840d680c06850307a8032166881c101c071501032000e01c07244520071541705100140204090011903400768010302601c0d001d5441454480002810a50040e1100c2d8151019990408007002c10890640d0180c00207550343c0c0000785e2030900d00300c007500c0c103030001542c19581e441e8944016a1000000c01c444000c081000c2110724202101074140b01c00035030304006008c4900c0b210700e00148240304403a1302036100d0a21036148c601e009822401041c01c8004d00d034051080f60800b0060540004814a994010f5681c0e20090381540095004400c820701c01e05074462104403a20030800301c1e50601a40c80300100b2818031140c2c01c100e500345c5c02e48 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 840701232 1250 840699982 840700001
    0xb07031b021b0a120b04080705161505120a020a171302041103250314130501110c0c1005070f0804050414060607200628020a0c030f05070306 62
    0x41e07100c8080d0848545140b61a900300c0c0c0001c480c0309440301d2403d90506050484010f00030901000440020200140b510540b100b0ba078000085031010141030917004100b211f01c0c000c18030b0040009020301e4200e07220b08215820030400e2100204103441c0d001051002c0d4000000c4607090200c0844000840380204a905104142c2013101d0840d014043c01400111021008885455002081000b0880c1044125001082005000560001c0ea0460120005c01c07113407a40c501c501c2c1c966000e010700c001100344e800c08414003500c000c10080344d05081408040c464542e007050945c00880d00c5500c1ca2030301c040410031600960414038544400d80c0e0b1010340012140c0307030071102d201d0040303001d12081c101403083d40c181d920001c2c12404903062480c00100d560050700340045c5aa00c500c00520002300720090b41003d5440e010300580d80b207034803817070b40c01e90100c9810a0400d00c0b103a00840080301310741700184281855420101402d030603815908d5554004003038203016207161149080010028502d441883d002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 840702482 1250 840701232 840701237
    0x90f030a030f0501050d03050316030f022a010204080c1203190c03090f031e050c03030d020a170105100c08121905160815040b0d0c050a0b070f0b07031b 67
    0xc0c00c1060301500100c81060b081700e80100d0fa03c0c420340002a4011080b030f03400810701083d010716010100f0f004c501500610b100c1a4000d40007060702034001c002c9952042c02124803401440001c2e103000e112500700c0c09248103407802603101034030751256424a03c03140c01900d03065400303580c40d01d00f83c03200050405030400d000d08009044a81844241035112036404c0c0601036200241c0d6100e851616425017032084580c01c80815a50025070404100b42001110784007032001d0140da03102d50100780303414000e411050220000c00c00a1017844038408010302e5050580714020400c0d22040c200c51411241c1c1e00001c04211200e01040000f0003003101c41e144410f101da080400c44643c83c110010811054840140c41c4020000452180304052608922a640e0102e00712206001580c013000c0010052303c4804000c54103e6408a855801d0080681d0640196a01a0b41301d610940d5103031618401d9108030480030f4980141e40002c08001542e4840d500d420000743d10f00440e0010408508640c28200c8800c800003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 840703732 1250 840702482 840702491
    0x50c0c03250e01181e0f020306040b190e1e0108060414010209010c060c0203040f0306060e010602070e060d060b030f0a0b1f030206030c041a03091e15090f030a03 71
    0x100410740d8951076001d00161141c0b5140c5501d4111140280306a151294206607181c81d646000d004014038000545803000f20280f01490711001000000d510a8803994022418052401c1c0b050800b031420020070690036442200d150319021a280701c220011b07003100c0a0381045142c0d244900428003800d070180030711801400c0c06050078075022442c00080440d10300307164010b01c05021383c0da822401400b50940c01c43d1022035045808441207055101d0380e007155202c00e003514004014007949a1000301512100f00d9078103030031b07600e03200140d950389030901c20310444c428020005002400d04980d5180b64901c9568046503040d14140000d040000e08841c41146902c001032201c10720254140c01340d0003048094880c0240c0404c07141c24114002c0d40e02001c3e000d03c5000001c116491084d4003290001c20195089202115001d40d504025600584002104d1f114240844102e900c8001e9080c0c40080c1d00f2000707021074030449656443c120381c003c0045001c0c5c00703422080070321400c060004080d001c1c515600080d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 840704982 1250 840703732 840703783
    0x1103030421081e041401061211030102040b0a0e0d1208160809070302010c05151303080903091e01020c03010e030a02120301050a03140a060f0e1912050c0c03 69
    0x50700d22030052010800c020402040c083e025628141035505242c120000c04420707504d600b800390a10411300b2003102e8540c41c01d20000340c044011004002c09030311409152001000c404105402c2c0d0081d4026840d5403541048803035503050007142c00350140780010b014022501c01e0350b100d101c07086a61080240c0419061800c010f0410816201c4002030003981c10210079600b050484140e4070351032400700a040c80010003640d0301740842045900c800025105002e0b60610301940055aa25452001100492104c40c007041c8060760101c02e0324480c0c6c4001e07180d115000000b48030400920168008581580200000360304030361400e0068000043d408401140e0710b000840c802031074441016049400b008042c1700510059035001d1080c001c0f0f0340c01502c2c0030500f6403144260f505254025800908240c923203600320030039001031f402a070040c02c0490140c59948200d00180e81c460880c0c40401030000300c0c0c1c1e0452010046c05140a00384840003081110423866401010030715040e01c1716000e0404c03010105409 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 840706232 1250 840704982 840705023
    0x10110a030807081602060705071e030c030f02030408060402100c060609021801080c090d0c17100c030515091b07050703170c0a060b0f03030a080f0912091011030304 72
    0x16000850f54401402d880a1400006c0d2a0f11001e0300940030400300283c0c400c02d200380d04004c6204100314000040012006107005082d5909111084021452012040b00750303500100984003141c9090b000381490f69500c3d400c21a072851440b20b44024072503c00c00311408500c4500c541c001501c28107000503620340c02032080750715088503e110103041041c0001086004039440c403d451140a060b2225034101c4440d00e0103c481101c40c1d00101104041428001258000000e00500004030000d0400410030710030740490036500c084805100c5514544884041da04143c0c1d0304680c44100d0500802c1c0c540b0300c0305004030240d8030424060303c0c950f00c0f007072003030041c000c4414282c400640d03002980d80c13400344072030000c1e034840c03885040c040c02c01951075001203c03075110100e03148221007000342a66503440032004090401c0708141c400c0c4c4490145a0b000521030350380000c01000145540c60b5150400b0200410040c60003c900c100108000c59144094890801000a07500441c41240000b24500680850307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 840707482 1250 840706232 840706247
    0x605030705150d020d0603050f030a0305071d09180a060603110d0213050603031209010c0e0102032110030c080a0308100302090a050a09020307091e02040e0610110a030807 75
    0x180c0700b4040d072400030022a0640088450b0150303e6100543c50388001640c0c07130000c140c2940050541d0146100c3d640c4540390210081401040343e84040005880304601124007202c0030429007801510140c05a02603e0071150f490343c403c1541d0882c019003003002c0703642400c0038500c510031030725240c4a201c01d0007000001e5401d610b4010094806d5031150030140c00203002c06103a20450628544d1380c4001c911b25481c10300407100e400c0b40e89030030500e0908080c0100b500a004003a21080010b0600c840060035600c04012580c010b011215400380c040103001d24145004c030060034404103654400400400503481c10030b500300402110001d011012a203003006002c0c80c0004021015505090781c0900c01680c480c042c040d0800345650000072160303201c081200041843d4400650b16108840c00002c86640580110b48144019140c3c000c2d060b9841074808180d0140e406250b0038220480001070b040e0074440c4588028982c6442c114002e5002c000440e4186000d00c10203a000a0340381c0100710070107400154 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 840708732 1250 840707482 840707489
    0x10e030c030115062006070f1b0b01141e040f2705060f010f0315020919050307050102030310150210050411010f0507030f14090411030105011e020c0d080f0d06050307 73
    0x442d10200b13003044500354980100403d1f110500c41c0d03003400f240003c0c1c414004c404a540583c114611090800c1c200b000603620b0034400c64610960802c0800b05030300f00112a1180c602c000001e2a070711040e980c00b000041d0043c20400d101e215680d02d620004001c100b506250840c2e5807070102019004a82411410080000c20040c8407101e050010000d9030480141c2d2070403079810042801c40c02003003070712840291040b40c1c1000d51125134080000710060070380c4915421180d003103040b54070081e03403240103988900003182c005032005000c220400c0945c403405207640c990b07142031064540b00814400c0e001300f1104280c0c1c041d68255501c6500100035604106001c100d82c2e928101942071488543d0000d0508004500000402c031110b50f03041509000c500c20341d840b0190051007070200390109096005030707030000d100711030002c4c032400b501d0307600f0000c00a44001c0343c07000b650142108134960001d018500324185003c4580e00c508201d070100203103084000e0590041d03c0480801c401e4038000400d450300c2c24540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 840709982 1250 840708732 840708767
    0xb0708010803030106080711030a021006080a0308060f031207060903030b011715010e060a0804260a0f020a02060c0604032d03050a060b0403050a060e0c010905010e030c03011506 78
    0x100502941d5800010369044030f030b5600e45218035a07240802202c0c001c82014103102d2a110104001c1c070120380200710005a40d0080504005180e59414880e55450040f00301401296001010842038101960010081c1c030019013200d090b014034045080207a485a44107490003941c0b00c8a043c1011f0303150003850190703902440d2110b00d140b4148244075655a0140103407007403400c8182c2580603640100122011030400404854a0300d014a1010340003400c111811a00d5480c42e11070001442044440003001030601c60400d800c002200c0070540301414281907900a610074407118034010794403100100410b0b0451009002581098500034002401e5080f54980c07004480743e1401060101d480c80d01503d64252401088540312010f06900030b1035590810000c00d180090003000340140000d204e400f030f13441802c0410a43c00c5050310f00d501c403260f0550351400140111010060341d0b102c0c82c0c1da0b9150110003030039256480d1200c0d00180c00c44e00c407940484401220300f80708001007900310000c00451003044c2c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 840711232 1250 840709982 840709997
    0x7061b0512070e220e100207172a070f030609060b01030c1b020109080105070509010818100f0212010f08010b0604030f0b09160e15040912140702031002070b07 70
    0x2000201d405142c10122503030701842c1301d0351950b08969904440b001035000c805a403515001c062910000c0d5101030419100708071000f15176626181071a044916400c0014440703202a0441e4440781d803203034400c00250f819803140703d038080b41c8541000c0c0e400f00103612407040000d025200f0304e451016212032880590515141035605d07140c094000401010841c04412001c80c40c101c07910043e100e9019581141c0400d40c80c000401003043d030040002c2000b00740989485d0015520002d68009501c003085104100c0d030803802c0da04090f100070741c0084101811440d405070604a8100a80d003500909a20004000001d24030400002c8401c0c0b060741c0220509460240c50b10303045840c0e0480c0303a11040c10040c080c00400c0d00044800400748001e44016000c40449182e00340d482441c2c2411000a236440c525403030248610006c00d1403d403088441e1590312103015007403140c035000c0503122610a40c0d00021400070400400300180d0302030001d40555020320100607210407260600750729554004101e0400e00c82c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 840712482 1250 840711232 840711257
    0x90c03090c030210200607080112030507060c140c1c090e04111206010306240e130326010e01090b030304090902010e0a0617070e10030207061b051207 66
    0x101c0490019a41c055610f6100c0c202010011540700203441408421030000605a880211010802d00c0c02000c0d6940e600c8082d0741c1307512044414108c12100200411030812140c0001100e40d0400c0211450500781072480051800070351141b680140102d04035a0480f1035007440300300385100c054031000340302c0c80c12a08650514155500315039010700041c00c8982a0302c81c1c020385d65101b07543c1040f119121001d403242c550b0740e80340c2000500786c0781001c148004216520548440c003450800802c4a800c4902410103407a1a01207100704403a250064040100c542c8600040b51340c50218178a003403800d10743ca100c4075807401d486501145010f80000070010304041c4030307560555001050b24280e85441e800010071030800d00c0143c540350881104182c21803641728001426a030000b07148124030580c051103010943c0c6008045408002d0040c0055100151010b4480c44500c6030f0b0107010f055200c3d4000050b2003000c41c00c85a09501c11030554000180001601c40b0040ca0030050103400601d1401c240c3c40441c070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 840713732 1250 840712482 840712493
    0xa15110d09051008040813030f1e0f20041505031216080307090509070c020301150608011a1201080717120306010503150a03030e0f0306010b0d2c010204090c0309 71
    0x200b00f0621810018980046401c0c0b00c4900c049600500c00340303c030854031550301d2900c002444800101918030200018030a09090f182182c3d01d03100d142d00c02d1145203044007036907a102d01c500c020201100c910b11101c4800340390b511588103181c142d1205c4844110b000b403404003094038240d141064811221424000d00e2011180c540b4804403082d801b06100d900d03560f401d801200c1d50f10840d0702c016801100741e800d100740560402e2040031420300a40081c4a002008500c2d1900585548036035000150701500401803521501004095800c2e000700302e910f0701140410b1600400401c1e0069640c640104a08100300300040c2001700440c221040500045106607a00004038000240107a062000c008005942540707614a6440c80f0a0000c26000c40c2e1616401c000300729444a0a0303041c05204103080c0131845180029270780d4100d50b1076002c0383c0e1034170640c0d0a010000c1c01240e10040c50202c442d0942e180485003807103081004003802c000040c0c03203e217801c1104080e111155000f40c2898502042c1e20b01140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 840714982 1250 840713732 840713749
    0x9070519060503180a1b24260a0b0f030607120207080403020613030c08030c03031303020a0203070605070b0f01050108073024050607110a15110d0905 66
    0x1c405040a41d240c1e9600f0005510001c03c8014000c40d6003d142c0f64201000904804c800e000c039414900e900103240c807900c095569800b11214038a603140140450b04856124101402c1c0100c1d6020401d0380400b40d60740342a0781031209840e00b100b015240c080801d11400c05840340e050070102240181030342c0c14140006040c94420a40058140fa00044c0c1c1c00140039816084070010f40d4003602056580c843d8031107501c44190207000840d013880c0c5030000050a001d0000583c6c80c00c0b407102d400f55103582c40300c2810300c510041c400012030960042d00c3c80400035035428482d440040a4544555540d083d0b50f192054800c40010103021a86007558014031059a000700d900b944a04c0c80d04010352080c052903480c0c50501030407200542404ac4000c084e110449058205103095400c400700c070f80161381c0c0c5239101148603030203004e0705800c1802441244042640e5a0b28000c41502c0031740302c001400d845030050b0b51400b258071074050210381800e030940b2605a0801c0341070804445131520045140c00c00d0b0000341c01d107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 840716232 1250 840714982 840714989
    0x1020d0e0f010f092312040306140105010306050307060e040e15090105131e02010903170705070b03040b07122a0f0e0a1a0f070c03020907170c03090f010f020309070519 74
    0x11001900e003216000300300106e010061107111070f480d140c1c1c074580788003d4640b17403603840701e1f2a40c140000601e65000b4060788041d101c00401034504103003012000c1f91410fa035540e2259000e80c03540c41e86103504c0801e00c545043d03262002038031001840c0c901007503802d45001900040c0707403816281005000c5491201e02152902540c12404a9032005000480350703540d603500f02034441100004400d12810380c04e0020966503100d142598002070b56642100403600044401900c04140100011072540c46660015034085400200017420400c030881129480d03810321290b0003a84070724101007545a00010126040d88083c60400d01140254020401c8402144128442c8000d800c85045c91100410305035501c0480c56900342c0d845519604106140c0a0f03c0d1100780c0c000e4003201c0120300a0b51062280b4000601100a0405103490b030800c542459070006000d05040d00a40070701c0c40034040b080c0141e841402a40e00090386901f0300c090b1143c14401c1e2a070102e032007000185841007580c6042c2c02860700f01d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 840717482 1250 840716232 840716273
    0x70903051203090a1b0518100e100e09060f0c03150f04140c040f061403070507060b13050405010c0512340201050702010c080121030201020d0e0f010f09 67
    0x320f89030f85903003034a0929903000041c418110840c0340032030411004280e0045440449211000302c48507031030039007030500585100300340500c403480500c03d0300e650161b01d1b83c0010581c603039000700c1552002c05d0650030350180c80701d06440d02b051091040b10001c0300851500400119112491410800e0300e90380c02510303202025001d08008865824a50350360f0340006003100e414030f08a0070034079140a40c079000c4d5005004400400c0201d14004c2034451103182200940018080014950340b203080341070b2603e402c07461003280e000c1d4070f920900784642c60b400c018010a265964002c03c1078102450700300e09558221a9441c02c0105c2406030004100d9030b8500960054200f09121020120700c240d001003000003041c0a103003000b000724100118690561110b0311038006940200300c06440402d0480d441300c1c0a108070b8607200150007296021884900d010710702c0c00d1081c0001441c1002c43c1d4801016210b9245481c8050f421485490b04420001c0c05403060b5296101410071544038aa9540490320030340f082c01211 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 840718732 1250 840717482 840717487
    0xb04110304172205030f161202061c0f0b06130501030b040e010203131e03050306060a180b0a020106050603040803010b0c030d0f0207030f0e03100b0406050a09090b0709030512 77
    0x307801d66084210307120010030340c010f03035484480980c020702072020912486000b0320400c00e1455844001285084409001c0300c4448202c41c5854084051504040c3c030580c0d000e1810440600d6000c2c800b4003448000700c0704d81000c1180c807600118203044681d4505194082c0c0401c1004034072000414149800f80d40b024240001d4890903100810003c00940161901540c80042403184803030002854811551145d030726003e044140c044150300070041c1c03d800901141c0d00303202048051810070090550b5801c4d80c0b80680c912803260040062000c0340d5031001407290000110000050390a000e12406081d0a42d2203c6c61420140d807031031300503c0705120f99100c084001c0799000400d40300340201e41c80404810402c2c00040e50611000000394000321049010807501c01400c600140101c20b044202c1500038042c3c40000700d0101410003078003171784000795401a951000803610b40c2e17581c190000900500030001450040d0762400d0303403910740082d00d41e0061041f404400c000085000400360304810002c1030668 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 840719982 1250 840718732 840718763
    0x513060305071703070b0720070501051806090414060a1e031115040f091d0604060510030807050d18080304030f17180102060610050415020304051201050a0b04110304 73
    0x18151701409000605210201050040382a4040c0b0410480c180b26100a01c400c1000701c05990307110036502c03032580031a034184842c0c1d208010080d658580068098040c620b400310040004088440c0c0e81c000c820104a2441817104030f0406040d0300d8003412001400400381403142142c00d16407407081c8002800d04e1900c0c403000707519850ba03400811446160b07800c01c5440310b884660740003425803036000f011340b12481d251541c0180c248140d070701022600345c034001d0030b4a0b4a45482d00d0300507160040400801c0c0c0620840000040c80301401003841a010324061720708084029801002104070070b07404030070300c44912000e005058011084504407a84541121480c0520380b820501400c0700b16900107003204041942200c001c0d8050325800c0c000300c00d80c265455983e8040401129106844c2c00780d00054052009100c82c881800030700305001c14500459080694a02c005250014142a044100c0c2d448100348102c0441501aa844d03001c41201c081c040c2c2d4400007152613030f40c00f0003400600b01a841c4e540c405d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 840721232 1250 840719982 840720029
    0x303020c190f080706030c03090f02091b07052404020102120304030e060a020a060605190306020c0703050d021006060f081611032d030f1b091009051306030507 70
    0x1480180030307080301c420314650f65601840c4c80b60614821070001c2030070000c5400d6207a200340b084203101c591104c0b51031442d0030541c003407245001004001c162a5080210314070307102c950010140201c0d81c440c50041030007454074180b0841700035608410b06004c6507403806200050380c01040c644000f01c00c0002c62600d0ba40c03181012120030029008280e00700c0f40025042080c280d010426100b2940603180a1081542c3c80c41440184887d1003040c1c2201240d2080c14030000d50690005d200c0325201c00202c07100c02e034490f110141451245075042c000743e400003a101100c1140c90049400074415420314024500c82e8a0b0701070100c04004000f00702c00e2101c6004d075084079004a94a407010801d030401c4944946000c00c00e1001d50800003071101c00b4443c00c2080c3d50104140c441200e01c140910010000c054079402601c00c034202880c43e01450f00001409004000d80b2406c0c6218680d10155446000e4180f800042c00b40c0b0040900501195604101c0c1c1030010600008050f011159aa40b040c407240c0074402c4c0340c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 840722482 1250 840721232 840721279
    0x602060c0d0204051e0925030e03070c0b1b010506060f0a022407090e15010c05120309010f05090c010f140904060305160b16031b0b09060109150303020c 67
    0x1030f0341e01104080343c41c5954500c01152400317052066665a285032541d00c9100100b9000c4c0540040c24070174a0a00d4424510a4011070404045002180e061410700d9603542185110764016201c00741d404500b40b00100c42d800d0491240500c0800200500e04101000c600144907100071030185e03407800110032600e14030802c441d550500f80c0101e585480071080c0100c0e14000000d56410002035842074000c26032058482d00c8501070044980d8450302405190019500401e00c2d21050340c41d4001d44804803a80d02c042d10055100d10480000005c4241d000341d90f55088420140000800d030f0b10005007172408d43d8100c540504510a01c0c10905c0000890050004540c4a02c489003600309041c480004208400004c000401c902c1c040c01202c00552a001d400f0450b010b4120740c4201d0081120040c03000c070780200c2c0404100f0b054003e000482c0003080c0c503000c520801c15030315599561720031401048821810712410916002e444c540042191035600d0095071000e0b031a42403881020852a0302178209000301a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 840723732 1250 840722482 840722489
    0x20a05182a0a02060a0e01060b1603110d020703020307120f060f020919090c020303060604030611130b070b07032904090b091b010804150b19080106170303010602060c0d0204 76
    0x82070703645429000c02500c1300d03015107101c0385941c00c1901c8202080418022395054030500e415403401c003105504801d0500203002400d4040c00100c1c4005501d04505200110f020386542d0010b0545a185206162802082d40d001c2180795401c546410000b605091005118540002c80442e0440b221011031000b03104046440b076001034004038102c00c40f220110400d0407150050020460354084150581e2a8401103a0860748550b040000b400045e406078030401049014000890030a01085813540350001c40d50010802e9980210302c00b403c100e2985611944407003145001e00922040d80e2510900481c59103000303900e0b440c407110050b8640c80d20b5114a215603081584907900381045000c00da21080b190107041d0f0546804011b5003c04e500401c11607000396440700a2007a003400c40206c03400201030880410b03601058110511800c064030540c0c48010b41011800050703202c3c601042c40eaa10040080c0c220840c0e0400d00041080380d8000c0381007503101000e103038665a10394882d00b044009104582 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 840724982 1250 840723732 840723811
    0x80606130e0109091407052b020a0b0304120e060f0a2109030801060c020108070305130b04080d0f091e0813030b0a050702030304020d02060a121107020a0518 69
    0x54201d0081d0804219130b4003640d602440c154400a00b562511030600841d60012490f1800851405414480d0113141c1c1c10070304036007071841d890740c001454a003280d4401c5108403804000c0c00240b0000c4c81e1038405c910000c1c01d01c00205110b040200e4410701a19440c10004d000101e2803191880c00703040000b4075071003500030854040040812080013040a140143c001a0f00900042a1540100408030f41c0540584030b00310581d5030b802084024040041000c09501406041c40c0c00094003004424007540c13040441d192200580700d5258111403410801902c580e00b00041000494255004401117200208005d001d8132003e05001210780710f45102540e000245e154000280502c1250960290326a001c043c852a29007031070880c3d49000c00c1c1c4000c2d40c80841314103000e00515081000784600350183c2404070000012010070411948108501e52a002001031024218a4940b1039800585400c840d400c100c01c80800100d0685e201c01032080e440003040c00814031403a110b41048403440e4142c1c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 840726232 1250 840724982 840725009
    0xf0e03060a06030606080601120b07090e07091403120d020325080402090f090d030b01030f0603050714030604051e1e1e01020414060319090f1406010608060613 70
    0xe01848020702c02031000799002403800740040707041200407804038100d42107c2c00784102c0805940750201d107024058605814024507040005421024400c01882040b03547c4609201c0c45c80c21185c09c00c19803a01480500c02c6d04480001100b40c00c443c3c042c0c0c3d10000d03c140e001030f10383d5140032003000c1c60a034603003e10404841c0c07844074292551b4010395244c400c510030345840c6400d464020315442618015945000c2ca6000702c40c002d60300e10320950215a1200c014580820305100e0141c001084400c0c580003914540c00074007050040700082803800d4414041900145207502d4540ca07100d80382e0801040f504482c00f1600d00e01c0c04601001c116504080700e522007520240c4240d0b41070315554400003680881c0365034032802e90070341407035041c802e5908448002100c6c100481c0302c6010880c2139403004015503d0b60310301411021084441c0d10400c1c0d8024444c81c640c00f000d49480c100346190804094000301c0e154840001840440c1d170124003550828000c0d94569180c00420140300c41c05003254010380c207007402d134 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 840727482 1250 840726232 840726241
    0xe040b12100e0d052205040501080a02040e060c0a0f093c05061603110714120604030903021203070512040f06030603080a081b0a030f060501021605010f0e0306 70
    0x11440c1c074045a00c40008010ba4100022407503160381d100b61619010807010b0002803090702c1d00c4010800e05078034201055008640f82c03400501210b0b02070b00071442582c00b640d0031104605051241c0e54610a80d58000d10351441e1041c207104540c0326004401d42005417984c1e03008400c0380600610005015240c86802d50204100e112440c138902100e000d5000741c100401e0313041c181d455403040d10255140508410324200c440c2c0960081e402c0c140400700c040190940101d2659030040c40894058010100b00c4c22242c41079100b0003510b4860a466030038680c000c50180b2001a03001150f83c0d0841c5d40c15203c140243c1c54005140341940907508003e45503000c2c03c400400d403074003240010702c00c0d03442d001070000780c0c5601c40400702c04541141c04020801d000030030200c003100f8003030085254880c0100035042d035050801c8403030b0300080d048205220301103034486014200031400d80c003a00e00034100a2004005100c0000243c3d020140c80c1d21819050141c090050441c6900c15202030a1400c0c0180c104c0e901800e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 840728732 1250 840727482 840727519
    0x40e0712080a171b0901090512060f06182d1008060c0c0627030703051201050405190906320708010b0403110f10030b0a08010c050a0e040b 61
    0x442106907001800c0c030440c3e10841c000c0309002601800300c000c54800880200f4910750521740c80441054148a050000011541e48410541480301c02050240c880b6007041410082c2c540f4000c1d01c0c05100e0f4142107645084414000509a404400420405051031080c1d0300d800c0096007000f40407140072a07450820189180700c070200304c02c49030110301302c41203a80c683d5091040ca000d120031844054101c01c1c040781d4001024039685200c004480c14034486250183c00d100c1c80c1d5448044110040795010030700c0f8200700e0b42d20800c640103040030f0701e0a11452603c0641c2006403181c000da03070428283d81d03c054a00340403556016881d0100d1141c106209106a107840740900444007070341820810101000519103886200c00c0c6040301c0002c9100c0e0708040c2907945129045001060440c0c101d62801034220f001e9a940f600c5c2c1a09981039280082e100c4681014032445601540040c0348581c107120024030301c0351b0b0013421951400300c0b5181c04000c0018440010303001d81003540c825680002500750700d01d6001d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 840729982 1250 840728732 840728737
    0x12152102030c04150e06130228031107031b080a0c0b06031501050d0501090803070509040b0d03020c040b15033346090b0f0a05040e071208 61
    0x3402101100d150070348510420054401040f06080b05008001c0100454501d41c1c1842d6000100102284024090043c3c84400c81c4c0150f40045550580f80a1068000110380902908481e4078075007400a401000f40c1c612851041c003500070308105015020b001140705200b01001402d900a5900c1da0f6060700740c000400b0344401440c21344180c01c004c0b0204015182c0059142022040c00c05034040c6c1c0da2030030003000403001c0c10000a5480d03540343c0c054900007800000003180310f04410b84416448401d250180401ca4842f045042d01518648034104003103034000039003c0b42d061f030807a004903402107e00701142c6801e0340d03c1610f0795411404024480c5402c00300309400c0c1c2401e8028400725401d440e00f490100321040e02d40341e003a000507410309a03c024441130680c603000c0c090031390018003030021400c0c00e0b2114880c01d2018809140c040c040c040c42078060b103001d0792055200885180c01c1450501c0b0014417107060a10500f4440c96a82c070090f4128130080c001c110041c2000581c0c04c1880d00301e070601d0351503035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 840731232 1250 840729982 840730049
    0x10506040f0204080d051c0e0d201c032003041b03212d021b06030a020705010b0a030c1a0a020303061e060d090b06030606011215 57
    0x201d0810050003414000340c0309031003c03550050018200b02c000c81d001900c007680f080c1d000709201c5929080a4103400400d00480800001e1100201640303c2c000d100180070109042040c030041c148203088280740c07200080d00001303900386040f2100002e02107410540081040c02e1820100d0304072801c0f540c0b0320000f82c0b405035100d140180544d8105840803030300c0000700010350000038030703240503543c43c0b44051046503961080003140c1e00f03111300d041841804031107031100110040d008203901c558602a1244c0c0c10302242c1c50000100c0041c1429a141d00300045050000820205002d50301060100520009400c450303211360780948074002241d01c9003030000400032140290542021110480401c0c400e540c030403108114010740c00b9505540b0b0390f40801c404011182242804030090b08030750600340c1d6590000348000c4c0445403002406164524000304038250060110744290000f00800c50240d0b002824080710125855000590b560f1107400c004600c60a5080b4540c420300d00400d510801c10002c4400c803c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 840732482 1250 840731232 840731239
    0x40209152d041503110607060216050d1b110619022103130206031b0a1706030703030c12120f1e090c0b0714100209210714041d010506 59
    0x90404041404141d0303420780e0520715541080f15040012030010010030f000d88000802c941d00c0d10060f0744540050744c01000441e02c441d04012424020061704029041118641e8181041901851110717001500384401300078102c01da600a0030700f00d81da1050125047d890807412044941c01210340001c1d030b905c00c00440030702528604481c7e60740302a050002d41e8810a624030711410509095401e1109030340010344a096101d0003203090380e20b400c00040140c03245041683d5200b0b00c09200107000841800080c005502a8005000510100340c0c0b0108064125403c019004c4480d41c0c0c000c0300f203803100150112080650710300725802110580e1383c5c000b445146280110071068044000150044801100000b00707481d5901c6010003449260501412149001c0c2c403000c49c04940c08103640307003440d221180b40c3e8402d660001d85440c10b40303441424207030200007030f100c1806180160914282c0d103640c030b801040e0302154902c90720441e039075aa800001da421400a01400880c0c544a4a680a000c1c01e1303426510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 840733732 1250 840732482 840732559
    0x501120309060903080d0b0d0b040602130e0f010e04080d050702030403120302131e080313080613080a030209041e150b0901051c20191704020915 64
    0x801d02e00c212030f441c0540382c014051a1410303840542c400000d100030002c8540098800f00d440002c51499004c99204038003502001d65180c4c00c0c9801090506483c1c1c00178000b12007840d0501001401441406056801c005803e01d0991030f00e01380580c00b8069400c0e00c502c40c5040c03404100140c0e5011014208172841544d218164140940003501070b80100f40710b10342d403078010481c10880ca101c041c0000b820305c402c4ca580c2400b0292216840e03030559004401c99140b902000d801041208010005194440b1b2040307000c00500103180da54803094070600c043c03001010f4000c2240c020725911548001101d600700f0750303801c1c215102d030317454640a89040ca0702010301c0c045034400001c01007a0300c8119000b00605a407101e00d002c910480d040d402d6201c0e171900d40049513480003d0744202c0c134100c8005101082c0d81d50810b88454061801c0141809280c00040400a46003118a818502800b04542240c0d0445021301c03d80e58103220710141084201e14985d01480000c0c040d001141d20300016160005980784164 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 840734982 1250 840733732 840733739
    0xc1306170a150c30140613050105012111071b05010f090b0d15030c030611090f1212030c09090610050a14161110080402091b09040501120309 62
    0xe00b190080c070f083d100800e2903020394541040001d00f40c0005002d508038005100e508a100540454a0000c1d8414440309800180a402e250041c042074200c1d003a8801408158102070008001d0944010400c481011100700d4086000e050b03088250413804100300c00740c8500c1282020184c40101400c02e20105155100201c0d4951040d03040d40ca0050468543c00c00f128648031450b040c65105001d5403400039a149110903005804c0d41e41003000b103000300c40c80c03000e280c00d50a008040703980904400c0e0001c01d00308103e2901c2d84500c084100e10141c00c40e01c1d828010300d1106014240612410101c1c50060000104214a1a50700190815040030b403083c207041d580b60ba040c4040f0401220a05000c12018800c105600e441a00e001040c0105505031900705100c090990403a05400d40003243e071100b08001018590420001401e000314403813070300c1c85260234141c01003000e460340a0005980302100d185000040c940c000d04442c20080081c00030025580e5805080703016034840d980c21030000b50340c2107001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 840736232 1250 840734982 840735023
    0xc08030a080a1503170a120e030901080f1036020d0c020105040f060525020a062f0906090a140a05120706230309070f15020c1306170a 59
    0x2a059070783c0060301541070a41c18584081c160004045c1b00104090083c10500c8600030b4040e041102800b40019a1501c4080c000540b040c4d5004080a910180243c100442c0c0c03001c0610030700440346070001c1015480f40341c2d064034909451100451010a007020701071014071400c0d40c001c04c00c84020017802c200d02409042c04030309071903055801403c41181103a110380481c1d020341c891a08241140c0d6048140110b040c40740e04000c0349400c4080140c0c100020070b070240801c500421428092a032807040c3c000388602e11b24601040150800281c0080c003080c140d840d522450211507280c00c000340b41003c203da850300400c5500007032004850003009140310000f1f040c140b487e44a40040c40344005054820b0420404841090486111041420208032090b0600b010b1070002c40c0100d0700d04c00035000300e50030040300c400c0d281540d900c0601850100c1e980310404039070204d490b44074484110341d4164160001c620100c040c00c0c042d040b0b10b14038904601150604c42d000600b04080c184200e40c650120000455003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 840737482 1250 840736232 840736271
    0x1003020a090629070b01090e0601050a0b07030809011e0e0f0303061c0507030f12030b0303041215020427061a0708073002060a0c09060c0c08030a080a 66
    0x140303c0300c1c0f000c07440030850b08041401e00b42401e400c0311400608100c15500c41c4001d500e03086c1d0113800341c59614030110817441c04c240141c0b400360100341e94441c4c0f003074982125401340384160f60000d01086440c00c0132a034080002e41280075403042c401c00d98517000004900380c500609102010329124171501c6000305c8240c50103c2900d00c20000100001584090261600e886000b0103200b1101030084444c04400178138001e400505550151140740c000d03022044000e000c030394000e81417038800e0b8010700040180b0105100c1c50000207601264100d4050321000b02d41c0b010b1301a94100c0c8156424085a003240100c2e000d010b07000321046428284806507030349010000c4522089030110181100b00b00143c0412581001480d285e803080c80d45130204000903400c10320203003a2403502d03100d100d030074102091603a604002050704000071341010860340030003281c00340040e2214451602070024208a80081c005002c0b5200c0c010f240c0d00080e65584d0300c0c9240000d10b400c1c4111200203050303203050710600500119501 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 840738732 1250 840737482 840737489
    0x10f11013e041206020d020f03040b0a050408030c280225080a0b281a030c030a02090403090e0a02041a0705300c0c030616140706141003020a0906 64
    0x1c82850503003051540520066558001d44482c1e408010012043da143e100401060f10104d101c80e450303052501d0080c0b5070b0103018001c951118241b100380000316101404a81c0c03c0150841080d9552004080f0f1050210610054451502c4a80041100d07550041030600c02c10025031002900c942d001500000882c1c03540c044c6082c2c980c40104002c002134081c0e0919038206020a0820300707019070b524408bd5030400d19074010b03003d103615411030910080c2000340260b504d50003140500710065070172011035603032049544c01912610012012900707145c0907200420241140000401c450714081c68180003030f620512410004540c01208085d03000c0c00c044c141c46201d44d200025040d000e03195410b0202015450318002e1041801415566610790008000c0588480c0c01d0080c0840351450002c05080042c0240256113040c01a62140035059000c00e50a818005117094603450340900d0404d18020a01881c05031303505074a42040c4406254004c8071035040340d02c2100e00c586035503155441e102c145d508522 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 840739982 1250 840738732 840738851
    0xf03160207060e0103110c1606020d0207061b02150d061d0601120b041e09020306130b010306020a05090d0b1b041a0706230109050603070302060405010f1101 69
    0x1022503e158440d4001c14542d040318039070b090800c00010016410300d103105080115519111b035007000030f1501402041d41608080c009400114603200002d4031028011702c48100b192440c50f021801c5607a03440006070071000302c1c2c0c9095145c40c0100c10400081590b07001e108607181441d5801240c400e080d004641c030481040e9078201c54407035040030746009812080411a0f01984545940ea08500d2100f03100c2200440c404000c541840603005140c280030018001c202040e6442c50038102046582000070304403030788030340c00607919201e1110494443c002d00c2c100742d038803c1e03000d80711506204403540214060b500b00c8160664a4031100317000c002c68491841040b4042c5a4800840c980382419005415940d01031040410401034180d001d61a25003402003500314010a44010300a10f10f05119180d8490340940081000904680014046004030b110b41410031184250907080c161050b404101807a108200a100300300c42c072919200a035408140c0c5420040250580041d0036690880c04005d103841e24 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 840741232 1250 840739982 840739997
    0x20703050912010608030316171b0f04090516020c18011208041703041a040e0109021b01050403050a021018110a0b03100311090403021b03010f020f0316020706 70
    0x28400d1007800c0420060ba0607181d540c6200016200740d0520080d48a080c1140040c0800290800c0c0581181d00c00c9401c011121583c0302040103012141850840203254800140d0316100020546501440f564003c008400c2c1084140700c01813801d6510107002ca5800d80075501b0200c4100c081c04600390b125050203803440c0840c0010400c54200000c40d040182c0270710741c0c5a1516841e040f003044007080c0802009015480001c0401030402c6070760318642c0781d042c003c4500c0e181034a40b42e0402c10510040c00741442d005c1c3d0001c0d040b040310034980d0b120030303c041c0c0c8000203102601e81414081c140f6040075680c6000350040c040c18a81803180c1e032258040c0b804503c02540300e4100c07642c4440b020102500440c07504642d032000081550145100510f11841c101d00b0702001707107070442c504415250003c068190280007803609000020350085800480070048458125214082d20300290251030400d0501120920018409600c55080c80045102c0e152800d5a85882501490100da441e00725110300310010300348 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 840742482 1250 840741232 840741247
    0x303081501090b1e0711100207030302030304110d0f050a0606050f0607060507031103090d170412080601021e031809040201021903091502060a0606021b0d0f050a080403140102070305 80
    0x7010300240c0c150a10b484141e18100a4103050a9014060507034021001b649036403c1450070b00807000400c0031620160006138510f5801035603034000540018102c41d0345810520481e250219255585034000e05003072400001350a00c0703078943e8084841940c219007460808034003801c050f00c0001039000040c001610748a081c0d01c841000704006009081090340701c42c0c407200100b6104010794001e098100c0a00301e07829038060054003036060340498100740f040d8601000046144101032040d4100c032801c00c035085940c0c0c000101e00340400c050241c0e07140714000001c2c1e1505580000507080154448144e04200314170b0008000c58a030b030841e0000d0040c1d1080004032840080d04008000d124842d042c0300c4902ca0302c1c2d8400010701104003c5950040e4060720401c00c02291501660004041d0780c000f4100501341048603c0380340f8151200140641e0103410715004005101d44252040764000068464500381450600015802844155402c0c2124503080422620600c00c03079018940c59101c0c149401c41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 840743732 1250 840742482 840742499
    0x209060f070503040306110c010e120405040c210e0c030a171c0212060102150103020a15090b0f030912040f0e090a0204050705031f0e01030b0925030308150109 70
    0x1d0208554901090100100140c1c55014840008021620458440d994448224210380d885040c00005600c6500c0c05020b000c03500040f24165074040c4c40100707612590310f0b803c0e5240c0071700c0d112040e40400c02d280840c00c1c050301680441010320384001645c2c01d00410030304041c4d84a0f2281e03809812202d5400100010781003000003002c10b21801018100c01c02c11005030701c402ca07000f01460191000250301000019070b4144880c00180c2000d4801c0400c40d415a004500c2d401d1050040d501c0c201d441192a03494035000710780510042041015051303603419641ea0403c8070350016580404648504901401e81c0b0b0a0740302958243c46403440440c01007450030000140304440034100c00d07142d000e070018000140e00c1d903010300c074869003203510781560ba81801c2e080b0380b00e0802800a00119680c1c482e00a1120b0310040d5074640c1181e82007080115582c81e9540558248040307202c3d0405641140703154400c08000115030300c0200c0740640c40700035099840030400170310080064206030001c0d581240c00d000280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 840744982 1250 840743732 840743737
    0x2f0f0f0d2001020c1c08040510020a0513140a0b0414040f0b0306101a0a080105040b1f02071802040e04020409030e030714030f0d0f030c0e06031f050102010209060f 72
    0x4509003800100314001d4004908903840104501401c0c3c00c284032041e40303200c2c40720407800c0c91a001e10b003c03a55468983ca800f6168280004000e180035000542ea1407001c0c030030002d940903803d100301141c0d40c0d81d507030702001c00f40082c2038180240141d101c11000520b2411030703402e450441d0090560200095108010400240101c08070511010756900303d40104d03483c10802d092007888071b541c0c070b011a00d0070b154000e5a0903071600c0300c200c1c4070762003000b113405001e500c015250304540741582e0104681c4000c200003030850f031403a4000d0b940d82c5940c41c4050016503000881608071440d042c1c0e14408001c0072905001a44103c2c080d80d0801c150900201d030050405602441180b030107860090001c030510800242801b890f0380c009000080b04100ba21200d00d0f0611455051510500040c008501036207006400800a0410f8006041d690f0b40b580150a000302052480c070000208000ea036031030030441740301041018104021180704030305008502940140300321030b02494001e0a090404003d10503e2001741d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 840746232 1250 840744982 840745007
    0x110904110910020d080f0912040e0f0c0f1e0c0d020312060d020d02121608010e1603020319062a120501210c050d110907020303070e0f012f0f0f0d 64
    0x24820603641e00288400d023005000600901840c1d8009170900155401031200c0c040c2443c45420f0703003002814106400803046030b2440401800d83c01129211154031042406680083d041074040d85849040d841c0d80400241146641c400d00f4107030329101c250611950742e40303c910003074100c054400018050310389075503110440c145032000c6480042d680751070b1072030030744056204810720f07910f4030610f25202d00140112408501340400c0030f8145490364000a40c3c03080203c03001202c90380765000c883e09120312500042c215041800c1014005041c001498040855028520001541c02070003284c19076071034050181250440d4107601488941c02046440b04a51044115880c0c00035a000103525103c80b108c60603a0345c0614540001220b505c410f100007904028880b000b1900708100308074440b0b402044482c5881030070313640c01c81014105001a0380c3e000003010041680301c1e110110303920540b90444d42c034403220819001d850280032000039107551415010b4048483d82c11503040c042e4081d105e1181c1c500300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 840747482 1250 840746232 840746251
    0x7141915030b1c060c0e091005060703111903031821020c0d14252106180c0504020405010804021207030804170d050c10110904110910020d080f 63
    0x300440c440c84150f40d19811408132020382d140e26080140540007509000d1911003070f24100702070b1500f0103d21640024600826220b082c01080c100c090600c500400142c81c0907900482d80c00b03c0c03030f440d003544a1107240441100040d0912224080d054841071a038010140c0c4044107040c1c0d42d5001c6d01c100c0c0c80f241d4038401881144146a0b6000c081e560b0105d101c01c28a026120010407a040e0144050a01c100000c0c02160500c000c0c011703501721481b00f01140e04884c1440c0c0c80481d120118208108912203528028014a050000b6025a82d1041d103a0104540c800c000002c1095901d1050000b86d000303a10808ac08101c0010014015044c501000308335210304000340c0358410744990703e403002c0383c0094208051450365801002922642080b0340c600c21009070500f03d080114810344c3d0782e0740d034a20241051110b601d03440e01c4441d03140c1c1441500d02110005005005200a40003407851076040300300c0b81480380c08500e282e149510700201d80303010385000380d0340e07100600d541e40000d250b05c120025110110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 840748732 1250 840747482 840747499
    0x906071101120f09050c0103060518340e09010501020c060705010f1b080702010614060c120a030c1b02010c020d0f020301020315010e030c0604230307141915030b 71
    0x2400100b5100d10380200912030380001d000d03c2c0700d04049241600300c42040d4181441c110040c480d555600070f0071200070080740d0341c2c420300d5900c2c048240690300c00700100380c003a1070614085200010703102d046082404019500e01d04580c0c507403000c01004c03403420301c10103001d1303013011071000c80d1804c044004120141c0240004120400141d011a0843e25034482281c00c6001d404408000b040d031290403140c2148561000b41b001c94108503500030b0880611488030312880e400078911240d403c041c00000c0e858843d0425180d1142e10a10018010700240c41001c1c0000700d8094800f032661a414096030342503a0107954110240c2060760a0080d850720441c0705550004030710019030010385c0e00340021481100c1c450041c44400c415000050030f803e05d10100148207401030601004161100400d031402c486107000c0041c058001d00d00b041c4503007444042625014010941e020074204206012220000d10542d00c409000300010444820022140a84124a201c4601d81d01c04184203030000d03c1c10403070040c0042e8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 840749982 1250 840748732 840748757
    0xc021c150903021e0106051c0203070506032a0d060f1202040e100f090209070206040512130b0309030705060f041703071202030a06080d03140f070e060c010e010b060906071101 77
    0xc001340361406030b81d1112402d100c28100000484075850417050b083c8144840d07680000d854504500415000d0a8080005284a10425901750b00000d0440710440c100407481c00d4401554088119210100e007010780001c2ea042c4166550002c440702d501c40000b03481100d80c02c1002070600002d02c000d03140b05007020f407040200e4520454940c0c82e00300a0001d05000307140306201141c44006d05031400c5d50042400c1001040c0003241c404407003024514007581c0e900428540310303e4800e02c4d80000072414408001c002642c6000401441014010720840c0c120b0707030b101d0082504005003240c00401e185a0754001c2c0c004202d01c0b0b00034503040340705402d008404500074183c4100f241c000b156a10207450301c540c402c00c800170060040f400b08903010b241c21300ae110407882028508a0016000d040c00c10310001c001403c0d540314210610b8000b274002d2085903240000c0c9482d80c082c2c14190807042c0c0c04d504e4101501100d1030040c00b200c20007003024205d0340c00c249031078a800c40e0f448881710381c0301d051182941181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 840751232 1250 840749982 840750013
    0xe1503070309211e0f080a1104030b15040c120f020d0f0b120d050702090a020c0f0d0906090303090b03090f010c090f0b030c04150e0607030c021c15090302 68
    0xc0c01d480c003d120300030b5100301d41031000401c900c0c3c0286414001c04401070002d444580d21000e44c90444c602d40c1444041502c54001380f03001849515a08580020045004010011580c41440c050100c100e5500b42411400041104903401c4c6000f04000c1400c1c504030008100f15500702c041030041ca90001800d224403030068105451403403403000c1c911940c9000340300041c50540c00020303181c0a02c00003031a0039083c502020b810741c0f0503004061700c214000000581e010010760102c4554001c0c10003901c240281c51401c00d59500c0e520312020f030204001800100300c0f1880ba410f2041202d07019a217a0900034504500d41c8955800905424828000c42c4072610f20403400b4010b0b588090000e42d541e082d414a003001c0c40010348055000f03850f00450800038001c50354400026501680c00c04e80701c442440360b2910b001e0301e0a12141144c0c580001c0c02082c4102415001510040c070301c1c3c0265812864201504150210031203811070060031300c0003504542d000c84110f0b070b101148481c403900403106c904030f01e103018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 840752482 1250 840751232 840751253
    0x200304050a23030604032d080c091212040807172a0d0302030310080a020d03051303061416020d0917030903010204080601081c0801050409020f101e0e1503070309 71
    0x95021520040b052800c04c100705450052140b2144000307e40040010350081c12800c01809031200140c0100d04040d140c0d45e0103200d130b00d941880c882200d08040c007520a559689e0000d01c0360f81158003942c00d0001b40d106008080e1034000704024042e045a4444400d035a2030340c0c030004400c2d9054401400013080039203681c010001418020b40096407130385000c0000100d001c0da1a08014402c0c0c01400c60301c0c3c0161942000b00c94480d901d420690f03281d4003010b1005860b8100c0fa4406071406042442d400e081c4502411a00e0003015110301c40c403170134a0702c2202669035405000e2058000b800d109001c101000d580180e6007801459482078034a80000100003d081ea0401d03000600349806c004010040b000041110702008404114180c030451110f03400540701c03402c14801c1c9401140c55a000c5e20841d6948038011210036001480c1c80c3e0100c2d02440002d0020703c0845840c580402c80380004130444d4014600ca6101190040c5010046d4021981c0c01010780c0028000b41d003859201c4440d40c00040c0842135 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 840753732 1250 840752482 840752491
    0x5030a060b16020901050a03030e0603250302190503041e0602041a0c010501080a0309060e01120f23100b0d020c0d180636090507200304050a230306 65
    0x35400b20078007500401c618540181c3c0094441d00c6078110410009401101003100100700301e40054881d560307540f00010180680a42c04001170800345080c5006d905580a090f03002001c0f4054074660401c5102030718144800d440103481c0321740210054244100712816032440030712620b0f0140c1840d5031240c04440b000609011404000b602188021002c0c030300344521390060074101c0040c0901174031520b0180c25403d8a0241c1c07000c00800c0424000700c0d0f4066441c0b0700c1d012034046010020300c0c3e03084804200500130f440070b00f07055246020199070074019000a06008a00015485005a01d08a07010040da0301c00c01c03002060503001e2207d16071724003080c8858076060b0a1500d907a07550240340316814860945a030000001c0c0264800a50071200360141140303528900110714062080400784003640c4441d182d4414640d00c1e00340410480c4c400e51016203124400002081d031240304241d9074100341c44c0d0103580983c0e500110b100d0010418549206c1c0c041d83c0d25051003d200100300c40348404203080820454 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 840754982 1250 840753732 840753757
    0x120510050a1d010603170304050106180c0e010305060a060509150315010807110c040b240903011a030c10050c0f010207020906190b03180714010e0d0c030305030a060b 73
    0x40c2024200e80c503482c409020080c2401c000c02c00c5506640d58510808250051079101c0540840081c0401009501c608060006035801d030781c0311100c14940348064a002c80030707480000c51002c14607000e94003d0007918091600203000b242d0349414a1811155a0030010354550700014a003801107440311140003c0d40038030000740c90066030240d10300016100c49805411001007101c100307496803140c1c0c0d0200c2c44040c602c00403200480c400700c401c00018014a12080f880070400c5a25100103a8501503100031f094541e4190000d004406260b00100c040b42c03c400c0d100780d0140c00c4403282486601e40150f00c040d4200031401c24500780000402181d02e0040b00f0348850070269070026420055151050145903c01c50407582da4640c400c0f01d0244100d0903401d403141403d88800440030400780102c0c0d05411420389800c0702142d00b0075a43e8524041d0101440101d640842c1c5400301c00381e10342c00e040c504510340a030400c02442e00380d4507550303003100c0c5a40000d01e100411135444034086192030b80e03c401000c1c07259144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 840756232 1250 840754982 840754991
    0x60d03120f06171221060a0302270c041a03060103060b07030c02010207050405010302182e0e0a0903081f0f0b1b03030910090807060c0206040b010605090109120510050a 74
    0x150400b0f14110240b10f0003030140b081032001700e840c000c8198031880a41aa290021110341b2003101040100300d42c3c0d0002540304000c081c0d00c60107030000e00340e0b141512135100f15851f1151944228540144128002d609001c1900880800206100d200031a000700041c03400285442d56400410446e80010030210002824808404290340e410481da50282504a50030059545503a0015585604c01290705104000d0080081d04c03c040d2aa4400450340c0c0d0156450064441100d1080040109003c5c1a151501800c0490002c24052007250800e9500d51601ea030182ca580c0305804c0346985803e048039400c10244004076488071a280000e004005405040d83c40c0c403164000a0400803141c0e64100c1a540705004200e621000000c2d215107004110b2000545d03240070303040c0085140318005014201d0360400c80c1c10384030343d6400208984160700032010b455080e43c07180d000700e40d10300c540c4000340e001031045030040c428403c02e541d007410308510903011184100442d40383c1d8000d03580c044901007105a81c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 840757482 1250 840756232 840756269
    0x2030307020f030307091509180f0e030a0e12030904061403010b0d03090909020f0402040e24030a03050a020f0717070f0b0427050a150e060d03120f06 66
    0x10800082e110b90403030091419440e000030b0082c5041c01901c1901e800000310714136041e00500460441020f07000095030780c100408400b8159029049140c07210540c10710304512040a010040241c40e481c00c1030785c0d40d14842803280400c0203210b09010b42025510f000c100b1025410b9a10f6204000050000300d080062580c8590201070840d216100071034096800a0140d00010340e000d0302d02400d540c10048000b6140c0c003240041060007240f101641d030060320015000c2014103148807113611410b0381002440b6224034055aa07030105c5020101d60f60154410006000060702a202405d20380c41c29104844031290b070a0b107800c0c42c110300d607030111420b01644244400300c0002032020030050714100c074020701c00323900d040c034034613860b214078881c800200b811008401000c0b0700c00003040012119000090010703050814402c0010405039107000b614508071a00010380c9008008298032809004003000054805a201580d5107240355035804000340d60b1303041c0d03e1000c00c15441200301511540d0647c0700401c84 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 840758732 1250 840757482 840757487
    0xd020604140c01080a0c02032709061507290a0b030d090b03010e070c021009140904032c031212010602030c07120503040b0d1514010c0b040f1202030307 67
    0x41d40303260355409401011141c10035981090b00e040e00b0035a550760000302c0300e803c40012411801409071406101c02225440160f40307c140810303840184044030b6511042e02d402007000b0004880d4001004402018060200800c07060401605c04000200c40341e05c5c030508a212010040500311901e240c516501c81445126007000c0120f40341042050501800342c0e0f081215207100703030005100300072614640d14000355040d48074400800f92198041c00c040c8801c0402e12000e0245c050034051520507013082450000f452a08000c04e500907501600d071184006800b199000908242004616001c4411308200d03901d91002c010303526003200581c3d40305460300344c2108008100101039004030115402071155160024001c40c0d01c1088400c0915440c03001d00c0c41d417500b1800e5004030b5008070b10001e800300c1e2a600c06c1426401c956100402c06152030102d60301c8100d0b01c0c618001c00d21040b400100100e05840001d10384100940d0414042c0c2c2d04646504155941d00d180d0342d048615440c0180c02c0481808078a54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 840759982 1250 840758732 840758753
    0x61b030c0c0108071b1106031608100303050304030c1703190b030a03090b0a031103010b0d2306011d030a08070210090302420405010e010e0f0f120d020604 68
    0xc00d03c0c25204900f030040c8000c0141031400707454200a051032030340383d0420a04202017000000040e054580301c1c030b04846a441b419202d0303800d0401190ad010005404036808501d028280c0364191685e43c1542c5490314116801c0e180c070360044400f210b04a410b0f440b0601044043d510600e003c020f80052800707050407079401d40c0d0b1030780700300c90081d0b02411072440003079080b031284c00a42e0801c600103529081e05c403204502600031810020f590b00030010001c108005050000c1c0b15800d900c140910003094241c1441c00101c2031001c1a1003000101c1d0041011580700d07a8000e401c4805101c0b943c05080d0020740041d0528001c00d008075010840011640c0c11403c0922030760405442c80c0c10f20441040c40c507004652065210805003001c841900514000003040d4403409210780e031031890008140345000c0b20060300d03620502659001c55031420512002d50b1060818145100c405071100c4d525200e000203000c0304c003480e44410b81e8400303401940122910405c02101c401c4030a01e500814060406041c24101310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 840761232 1250 840759982 840760003
    0x2090a0306050925051012020d1a18070315090e06070915051603050c01050f0a1104080705040b03011803230406080f101508040b0601090501120209061b030c 69
    0x10031380e5520094580c08000000070031640240c550300a000c5650804450b00c80c19403466040881c404103203048030b40b00a17440904609510103442074403400c04820040b070140c210407160b0070101c1c0b140000c2c04040c400d403ca0720104041d1003400e50120303161403540c41524880e40d0801001c0c2d1010301004141640300d4000c600502c008400251034184840009201d407140030140710b20f0500c810f040000301403195007110074080000c03000304154200020160030500c801c0da0540810350038202094403203150141214100d491000040050500d44018800a0300352400056415540c036904c04c0249180f040c0b801206030700c03e507513149000115002e44010a9200d80d4024000e180621050142c0750b002052250054100300c0034007902d50343e000c5090520f02c01504403002b0680c0055070166215048041a070050307104400005883d9600c40046074070a520384203850029040d00c2000319400c0741da07401008040b10140215180910406000d2118060f0308000f410603800003a82000f400001d00038010034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 840762482 1250 840761232 840761263
    0x30f0105010302090d030e0f040c0f080f06010938031801060b090402070627111507030f0e0915100311091009180203070219210302090a03060509 64
    0x1c207801e04e40400c1600304600d1005040c06580c003c0584242d4443c0303070003200c0c1540200280301d401400100241aa210b0680700404034640e100452008840140414403076401a034a4071a80d038645450b0114014040703140c60503020724807400901034a40550242c007101c052a10050303980c100160031001800205000c00e80c56403400c1d00070302180350b020f0200e903008501144e01507220340307031810200f0007800a5034071030581010000a4140406010030100101c500036944d02900c00750580a005079107034035a01c002c152100070090040041d0040100c008401150b18102c842c45940b0408110031300000d0752840050170601e00c040ca21031030100003100714850540f5043c0301ca07000c500507409045c014030402c107102c0c2c4a090084441c0c181700b80e000e01e004128000c0740c401c038580e41c200c4500003944140c41980060085141c0342210f064a03808034500c0e181c7c03001c0d02c0c402814000c509000d40c0c1c50004558010140c081080e0515540d5041c6a0000b86000e4000003480b800c04a0920b4a0006900285402c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 840763732 1250 840762482 840762487
    0x6010219050303070c020319030e1e030c01110f12040f0819240609020d0e060f04081303150c020d0903030215090c0a08151b0a030e030c070803030f0105010302 70
    0x40780482525041103090074034a00c4003001c4e00c00039050520201000b1142c0e5001e034048418142d0241c407100c048201600d04000000c410850051400103c0d160701c0d406034004021038005501c0740020403480429041920040200000700500782400302c0c6000000c140080380c180418810305c5c06a00041400200610007c41100607454144a000da80035146d01c074003401c9804080000107401c0302400e08404100001034071038030394000070341001c00d51011081c5003e45c59110004000741c0c1c07a004444250f8105c3ca603941f41d40e5402091303448507946a4824044507000400220320300448100040320000c0030440080300d84000b40740c1204003d4070003c10079410000c0000c01c0d00402c024111040d6413423405240c0d42c1d2041150324103045000c0c3c5d103801142d910710010f001c20f400302e0107a00e02c41110401000da900c034001d60442d400e03030100d02c0f0f52003503104000598200d0700942c001100131108000360fa081c0718180040c01c0c1031030f410358025601c43d00000200f041d15210844054058582407c0450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 840764982 1250 840763732 840763783
    0x1050702030712021c120e03070b0406260105030709050a02190f031b0f0804050708030a170a050103081204050709110c060c0307050301031707170409051e0a1e050f060102 75
    0x710241b0140300900404c0404003c8545042c414000501840c154240d590b40c2d443d48000d1680007501d05507014030178445131140308d164401c0c1614ac121030000340104129420b00b4042002460040c03c1204401d6080128a0700e4280300300400d420719625880d4180320700040140a011740740b0010b01160403000c000e6506c4a42a0048240c0b4038410b414640101c42e0790b81c43c907080e4a4140d8030382000741c00d4403002c580c000030f050740100381c00380e0102c0801c0d0541ca16201d40e411070041c0d03503080c0801080c41c0014441c1e03809c6085000c1c01c003984540100129026540c1c2c81d0600411200c03003a00c458145800011b031100d01810801030640c0111410801a1840ca00460700605500042c00000d01c188034102070480004a40000c0d1003a29130000c0414a50788010092001c1541c0180300e50071080f800c0900003002d00c50801181100c013400f1a00801c03203540c41d90519030040040e50104171b40c5d02e4441d010082c05898070312406e071161141e913441c1d4040d410701c0d50000e031420310741c030310619842421042ca90 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 840766232 1250 840764982 840764993
    0x51608090c220f051015020105331005031806010b25050f0a030e030f0d0503060d0c1d01051906182c010b07020a050f01050702030712021c 61
    0x5105035018041e00500305a030030302c2810050121400d200c0c0d80c1d9810031080c0070001002500b10000c641c14400d21500c1c0071070040090b0300741c0e0821180c1ca0819400d82d0000c58902c080c0d8065101c4000301c404070480d001c1ea85c10b00040e141c1c003c08031a0701c0019400300400c96129508100030120425610043c04207603d4a50744085500c545984000c0301400d0318458100c14001c40032103644d0981c07010903075001e260303500811681d8241c80c134000c0d0001102031407804100d08011445000c048030420180040754110b11045e80d0b16417014003020b170401f44410411020454550355a001790580e2074400e0103e0580074441014040c068100c5c900c64910002450301c9406010401c03401c842c100e050a014110180702002c20350341c259840041c1101e800e10101c000c2c0344000418100042000340039004a98803200714000a01840303078000d40180210100307000d01d107031a44000c171104005150a40c41e10000d0f50101c1d00703080f0164048242900d404091070110f00d8032041046001d02c2a0b441a03640036916100d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 840767482 1250 840766232 840766249
    0xf110702090105130e030c01090210030b310603050312010902040b031503150903090910350d08070e06070f0204020a030f0606110705040c08010e0a020403020301051608090c 76
    0x603c0e10030240c21952074240071340d54001d00040094981960f4a500202002d00d0107010400022417198070001c412584003030213032050101480015248107aa55100c5609800034406041a00b2605c030122040b0301c0c10240d0360003148007a510910146440d60f41d40050304840c8041a00483c0810b4014042804085041001d1301d0b40040381e002c004101e41007180220341454485100755100b074110008004136080e00000078800900c007030ba00300751140d03551030b03140301515090b00649040d010b8206944121240ca420b800b0040c605e10911840d016481c0b161041c42c10145514050100f000c040400c600760b0f403c41d60b03005115030262104e924102032941c50312102e030080c010013445150f021a184000600c039a00101c0749511010003009030030b07150480a4101c002d491080000381c89070010124283c14540038102503124551a05481c590a0400044d90307407800410070800650700703010010159a09010b501e002d003010104200c112041090003d240201c020308060590f808101c0c01c0d20070344c640141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840768732 1250 840767482 840767489
    0x503060118030b040308010512071401050a03060e0a0603031709100e15010b0301050a051e0f01020a080d0605040e0102120703020307050d29030f0a0b0613020d0f1107020901 76
    0x1d00d4458a03044000c0801140519000940600041d0042004240e08008000c3c1039650885100c102801d40f01c1c01c0680d9054107010351440810000c01145e41035003d42e000c1e14402ca80c50038007240050f16040040b134000f1040303e148001d035072140700800c103140d00701481480c0201402000c0c9080e291160b4001e985400c0d165640089e155034455814034803105203c01e111f1910213004400311969500d1550302150401c0c060305115682e942400102458258958040364425003c030040300303120b02c0d040118071030711020352034107600400480400045c0c0d03800041004065403240040c05a00346404d000850b95024250680b0342e1040001e84400c0e43d400c2030f1240d111401c0d240250342c0384c0d200c600c121400d00928190300784190810541c607218400041b0b0380304110385651002004413101400b01a40d9001001c0461026001038180402017800d610b8059840700d40603010521000c50095500c00300d0340003105410305075035101c8084600740014000d460004000d4086103040554130b40004958220622 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 840769982 1250 840768732 840768737
    0xc08010602190809030a12020607020a111c150501030b060f06191e05040e132f062107051317070b130303030509060f0a05090a02101106150105030601 66
    0x10030100800c0f0500003104d140c4140071341a02c40d181014544400303102c4445a494025010b00d1001458840c40052a0390501d0303080034000c503a03284000c061001d0b80340200c030f0002110040051400c0440c0c0785412082c0700c102d90b4800003681d98914189019050409070000e4411128015030000a654032025945801c64003e0402c03104034800070240c418402c511803411010242e00304100105030171802500450740d10000c80425540d0740f8012020244102000410391581108400e80c40d2803007040c40c0e580500c040101c0f1001c102d400000600a422180031440d000c5000e88032442301d0002c29176959040203070350400d503080142221414500030110301628501c0d1000700750403001c403203041050310010070460042c19592850781c0c43e50441261140000e030003290910020640081000072814441c141c0d01d0014501c03911500602c1018000103001134043e440780320648405652620414450318249486000403c4100103c041c00c00e10005e041d400646050b00c0d180311166004000c5a500ca0401d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 840771232 1250 840769982 840770023
    0x609040206033c100303020a0b2d01171b011d0a08010b0a0f05010c0b04022101021e0403021804050a0b0a0209010905330706050c0a030c08010602 64
    0x1460800c900c00382c03048040ba0070901040b0f0a5008900100000f040703401e010a2094030790350380000c049075000900c0010016400620140d0100d072600311815008400140034040c0498440010180c41850907140d18a0741540e00041102e420081159010142c0000180402c0700705400e260312000d14510310a41403219107507800c0006a44030111038650310000380264030aa4845c47c0b0360f030003841543c030b405004804d0350744007040c200b8003078000404465050351211300e403030020781e140c0581010182041341c0150f44c24047c2c0340c1441c0c02c5601e41107000303108400103031180502c07000c0d01041c9265480003a42580108403c0c400350310b600c11007501030320440940100c191a00d10740a0710380302d05404060140320700d035800e21020711215002401d0b410400d0382c4540070151a101001144145510f40c00003951855400c40e8801a48044030700040c4460000346040807034640b9210241c403011901c0e60785038a130000300030701c00329014440c210394141c1600e007203950b03036040c413801a55a0745105502080c12804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 840772482 1250 840771232 840771241
    0x1410080a0b0f030316030813080d0c0309061a01030c09030f060207051207060c0801050105030106081503010f0207061e091502030603030405041a040f1a06070503040914011a03060904020603 83
    0x451000305481e000241c11039031703a5038003141607601d0115240c404600046050f4086400c040c694000b0810440d001034000c1e140051100070003008100300c59441042c15220440308000c00c102c1e2242d04080070310b043c0c0908020b11486e00040071100d560f4041c2c020b001d0322000c24400710340c5007400b03220241d500079801039555034a81809480c1081384a4641c0b15008000389070001c002942d0030854000c203482d29598141c2e40c803440152100e002c240038603c0080c00810004182c0c1007d800b41c418000d4005d000001c0030413030403003000240e0307201e81b1003540d05a440c0d103d140804c81410000e001d041c4840d480401591603650745483c0c1c440004a402007100d0780102c0800c1542d501401154000d0000078010000f006080d40224804180c40c50550b104600d00351405245440c0c50103041c4200c1010038812030902920020031000d03410219050f203252000380300110b020001881880185000c210407208107600d01800300c030310301905101d40b03c2201410f1050000755115111065041541114001e4480d41c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 840773732 1250 840772482 840772489
    0x18070603020c191b0f06030b0306150d1104051810020703020a1515030b1f24020102190c14010c0e04050405190318050d050c060a050f0304030203041410080a0b 70
    0x1441030000c0500b007034004c8000703040040c81507407804a50340c0d91002e00803040c800040544410080364600e0b1000307100c84464801c0e281041e101000f07a0300c42c1c1c00401c104960400490111035084615610b440c50355200d8034440402044600035210303a15074198a000311660b0300944518010070010007007202c15000c2400c0c0380c1190404102900301e094610035650340c2e401c0c00060f81e9026242d40e03c807442d40d9007802a4001a510282099030109040d008818400c0b690fa5008000c01d1540001155400d10011b500190303d040d82c007803843e2080d5521410704c1018102601d01000c4209a401568540f007411400b49801440381116028100d40000e2280d0311410b080c0d05000316944150110301240c2203280c2015004800300e032a000404c620f14071402d80310000d020f005800090041c020b036000550551031841e01c0e20040060441c18600b031403c02d00c0b032a124841503041550211f015810110b01070000815510306910401c00468210540f081c26641c0900b107200082d2a507640c2c0307070b21085c141c08141c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 840774982 1250 840773732 840773753
    0x120c01061223032b1a150c031209010c020f1b210a06060e09120d0504050c0a0303110d0503060645120705010f0c03090e18070603020c19 60
    0x2c03e82d0b80c0c0d00124100c002d540300003041c20b0142c418907a900e4402d54421744032405910700b02c9410050b01880103e2144807100e060342c1c01c4544e07203051034407081008200606281400c43d015400520001c00e46100c54038019091000f18184010503074407880c0808201c0d40b203843d0090395030758280c42d81916400c0d058116440c084404042404900c5142c50138410040c03ea4456011204070048a4000340c441e100d01c00d441d103600d100e041000580520600e00e40c035036140e01094204d44210202e80000c007450021030110744585c0d1003940420030b03a012000300c0000a000e2051417244500e0018036500c1d10300000785030390054007405030326030700e220040001d101841151031003007488040594080600c0000c1c1d9804520b10580141c0c0a0710300065095200e03034000513450141c49050b151028000194a0112680903211700c0079020045c105d00002810001c2c50800c9015903070804070f01b0728071050400d00c145840e586a014400305803041000c030040c01004200c3d403080703103003420b00e00d07440320b04900b8103a2500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 840776232 1250 840774982 840774997
    0x61204020d0b010311010207150c080d06080717010c05121501020106090f02090a09050402030d0825050c0c0d020a091e050106020a0b0903070f1112120c0106122303 72
    0xc0c2c9220004014441003116100c4010b02c00d908880138252100700701d10288480c0303060340e00414040907803000002c85240182c20121803a400000d1519a1031600602c3c02960380c1c01351401000e2100d010071020003c1c01032400109050600a2030051000201c0b1841d41c4001e210070384200316260620310300d03807007901f00341e0080185101c00e00c141200c10148000a40c00080b05501c21108000300058402c413600030320340f2450f002005403846082c0d0785000e03a5070f41402000200c44078000c41076a4000c0c01844540c00c80500d45940d22070300c803960b072540e070381c07420104c43c080c140f040320025690030050b500c074141e400030307510b554030041900303801050415590280e401f5408080c50404001007140d5a002071565192402035007002e4998a4014480d0b440713100d0440302811150900e00d4034004a4004200c403440300e03034058000188a502140400d00340284c2210040c4031040002e02030041d8042400f0f84e90241c081c60b00c00799261509036440c0102d040b040e980b203c02000b500042d00a03038420910584050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 840777482 1250 840776232 840776243
    0x30702010c0f140d02070e0108070e130f0804090f050603070501050c031213030f05031302041e02030f041101020d080423070b0c070b190c02031906020301081002030402061204020d 79
    0x40000c202500d0303454164072134070140180704100000460303006002001e81201c1800c03020f05001418102c8800113454014103c10080306031840d035a00054078042d510400d9401186816103440c201981c0e507041d64080c442c5000702506003c10304c21569004142e050480303109007042503449412000c1d40e821030103410703004135a000b03002d01041914901001d000d0301b5140b099a0340c1503145001e1106541900056851068409540641e1401403c0c00e600c0341c010500d1112030000000d0703203500b00005907801100c02c0c200700100c003018082040050701c400401248240080d2042c100c4484c4010107070704000700081e00155140364200050f140d0100d6082c04502d015040d54007098a40702602c510f030f07100e118100c1d403074491400300207008003082081c0d4001e09190710340c1c820502c0c0101011901042007050999050040300c0c00b80c0c0440d55010b00c0041050b01c034040250f1a50726114055060604d92007440c85424010410480113907581000c8882c0300700c0201d5548219221381c0003080c2d000340d41c184001d20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 840778732 1250 840777482 840777503
    0x5100f170606011812020d0b01060c1709010e090c0d06240c0308010e0a1e060e01050a03020607080c0a0f031d0114190201020903161d09030702010c0f 66
    0x11582100c141444000600d0030031208a0b440320001100e140002e0365080c0141510780c1800e014041d4000c010242e014001045401000d00503103407040300c0b002c2a449103010400354019882000303144101d40c080d1205e40740030303981040c01400c0043c1c05458580c140da442a2415000212505495825034903c1e01864004104503502c0d0011120070181c40400410203103d0b1203600380c00141f2903190244016419500c2243c00c0c3d280200100800030040c00703920360319864082c04148103801010703403400c00340c400c00b0129449140c060910300060040c0c11403401184004010300160f20349000701c0300342c00d910400041e6200234034600ca07410042901e00061460f4440c804407014140c1c00b20300c0311001d0408902c5240c1ca40c025500666aa01420807031443d0b200041c001030078140140c10b10040024514000036142c41505800281450805442c0c411040c6408405200e030003081020480030030780f480c1111810381011009140c1d24000c0031070013410400c40f03102610401c030b411b112402010703910100122 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 840779982 1250 840778732 840778739
    0x70b1c021b1005360d03390c030309020d080d0609141f0806071d0301050403390b07030506010c05070e040303060e0a0f0515011e05070506040c080c0f1305100f 70
    0x1e0107446914805a1000102c401d10101842c7c1c03c05031500441d001182c840706584e10700e10503158081090415000c1c10355402c003c002607140c0103c0c0109981c0719108040c0d5071070064000704201e4800360081e440061030300d449801224403184806801108003401c0d17035001704080041050700c401d1900310788003070300510042c09100c50b0001c442d100b114101407180405029402c003030500b01c034400c07600076000a4440460388a105021802c0c0d01ca06000140956024240050080105002c060f41200c2908526040008141c0e161003060380000c0246420071003030070b0300d464513961040c45025450a4070840e001040c20140070b54440c1009081c1003035100e01905e05003e18900900f4a0181c0036400c504142c00920500b4003c01c1000c0c862505840e010034202d0b03815964282d42c0c080305c06240c01d014040018101280b0200070082c8641d00c10745c4007150150400c1300b01814240101c06141c0105060340402990b5511280220070684940c00c0c0010301e640d910407403002603105075001100b007486101021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 840781232 1250 840779982 840779987
    0x30111040e0408030c0c07290a0f21060303020c030616050409050a060e01060201090c050604180f06050d050303090114070f03020d060302042912070b1c021b1005360d 73
    0x101c0c07003648420741c100c0c001107602c446c0542900c0340809c0d4800184090501e904103e00500c50141c0040c1403103e120700b81006d04400004031042900181e015a2009071412103a2038104070650717005846031100c0045002600018001e0700450068840481c0c5690000308200125407110340140015a074841c15540e40780006402800c3c4120103841100c034150f004a041e052039001ca070116500264101e442208107c40234000700006040e200540f03031583d80010300c50359000355401c0300e180120003555482c03c00302c05c1e40d800c648802c218242454a04e1080040782c0341c0207041e42c02408610b01303002d6581c624480b01304006000d540c01c025441490180e0f00d88e0007000c460101c28140152b074a900c1c428207060010800881c44000c44101c8591001d402441811043c2004c0e0941000040d80660351007840384030750040e070f0007440c0e98402e035122400c0052031030070f0104101210600c0642d800c0005040180c42801c0c0420380302001116541c0e0001c01405032001c8651801081d8200703003d0724003142c0c03481da00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 840782482 1250 840781232 840781259
    0xd0b031b1c0c03230607210615030b060904060b190f05070201030b0f030d030c0f0908100e03160807030306060e0f010e030a050105010e01080607090e0402040902060909040f02030111040e0408030c0c07 88
    0xe1441e00340003070003025400170030382c4541c0c01942c47c903027450043d0030402c0104070301401ca00d41c400d0b500a0030600070010319403158018080a014880880c6441daa0000c144000da1250300d4450b40070060003a01240c000c40e04641103415040d028680130449400f400c0200b105910340c980448e4041c414400b000450070742c5a03110302d0f01c864080d590500e00320002082120110700302c4c02009801e801c0001d009990000c903621040034100c000c400e603814a10005c20350011041124402e0300c182c04001299010564180308802c0078103094102500304542c3c0b034010a80900e190410b41c1c0c1400380e160b07a04403c907070f01040a00340c82c6500800a200329a194001e0203000582885280d4851007100086008a806910841c09540309101081520b1f9500c0c3c08000140028182c166002502041100c0c80c6881d0050554440c41c01030211030040ca4143c0706050845106040520300000700380028010640016400ca030065000595507032652541c030f9400005105801c5038800ba441408000103060700003040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 840783732 1250 840782482 840782507
    0xb130305060f0411010309081b1f0c03060518150604120f020406051203031f05060703020a0b0a11040e461b050d0b031b1c0c03230607 59
    0xf02c98110040104c010344c00d40c0d00c00c983c000d140c054140304030741a0b2910020590705800c4d1f05005c0300d00428031002c800380602ca03520320221130552101002c6000a426000d210000c2c030303007603540011460001203801066040039142c0081601c0900d40d500b92a5586403d5a014182100ca03000b040105841c0c03140742102d01c0c213400c03800b842c10000001a070b4035007086290b260300500000341d03103560784141710380c010141036901e006030100200202060359220180074202e280c0c07280e0010110b08105040100c4540c200410f10b0701d89a080a00c6103280c4440d01c1c0580d800c440d0204200d035680c1c3c413254146403aa1500880044d031140c454441c0301c01c14003840d88045040c0f03403401503859184001a608409403401044408040411004034408103845900102070030000c44030f000481d00803030000682042882c0c00e6015082422805c401550314012402c10241155007001840802a83e0b0b91090280041e01c03016028811700018801030307040d5a19a07940302c400c2c0c20196191860400c0e0082e168503420304 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 840784982 1250 840783732 840783743
    0x6091824040e1213030807060c020f06150d0f06090609170306063406050a1a090a02030c0c0703050304090c080601020a0b0606040f080105071103030106090b130305060f04 75
    0xa004200301d040c248208540d20002e0000303800c645a0031a44030321150300c0112540a803413080500040400ca6030005018400e00c142808074001154140c0286010480800c000b120b070030400c10f209000e601880703e144152000c0d5014003950034542008182402c02b038001829107400c000c02c0a04200c500c1c0e008030700c554031420141090f0000c49080f06514002200e00541041007000700042008001007050200f03800700d83e26500a202da40e0000300c1c88403600c10200d410756242d40c01d0001078002030042c041550032406a40e108850407000003941c00d1009445882003603400000b040a4082c46411a101400758804560401765a031038401d549a000e4440c16410500c0c01c4aa1861244111000e03401160168020140052691525084004007500c03055204108210000300350080c0101c0c5e00041c030800d0300001d4185050400a0104a0001d5603a0b130745800810040c8905600445842c042c1c502800c4015212071203070314240890201030300041c2c81c611134501003245030302002d94071600c11445032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 840786232 1250 840784982 840785041
    0x1050a06150801120f08090303070302070e0c09090c130b18031005010e0a050c1909030b0a0903082a030c0306010e0604121401090605040803010314060106050405060918 74
    0x484040b2200c1c5003c2c020102c8120148a510002c1403410703a0011105000f0080c0303506e003448050001c3d18591004108402603005001e080200c0190500b8055001d680e00007824602044080003415012000340b80e42c0b0070388400f180d580100001c60a9038006000415a4243c2e00c030302d051745080c518048070f9070661003441812490000340d41c0a0080314121400d420402a2a4682001c00d07800341c403005004504c10340041c4460035048034001a00780034103a40741c036004003035411070600440c90200202022445400c000e81580004d9004030600d62000d03035450301c0842214801c1809000404c0100c4140d400d440100620885041c541d0045002c0c01090301d8400748503d4100034485a409944140203282e030060746000c6c04507000d00c40c0507802e00c5a005c0005000b401d03586d2400c044400c1030304c2c252000403021005004000002c050302111051000040a1940c94000024410721813801080e00410011032003104540b58039040f44a60311130f2950b400c1d10361415640e0a4881110312407070f0a5209180c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 840787482 1250 840786232 840786269
    0x60a0e0a0305160201020111030a06030c0515190c02030303161d030607260a0903020610152d0305101d150a1d06090f072c0301050a06 59
    0x14400591a07142d01c03000d00744008810880c00d001d80d43e110a90665480709003071070088581741c00851242c0000c01001800f5829802c00c103240c007841c1d4000500402e6a076801c007a0400d4140d095038003458000d1b858040f06c6169002c210f420701300e8400000d4051201000384405c10400c004450300895440c2d44a844581401140c6c40c54000460361181d0180c2254010514051164141000e40c1d0301240500900344021096002403c2c01224074000307517550395103168109a41031118541001c88415240e50a60604030230503540c0e0b9400c1800d40500650b4550402c40e0750411564449020b00720100c4a51807030361080c00b8001d401c089620300e031120800e050119400c460440d01c080e00362100c02d403414042d581c140e50540101422804168040100c0394002205c500c100040365074059455152180c030701b4080c060010007400601011943d02101d410002d02903403100411082243c1c0d00c1040c2c080006550b0206260806011800d4155080104100070040590000811100304a03001d00c50b2101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 840788732 1250 840787482 840787511
    0x8100219020d08010e060301020408070b0301030c0e010b0301090c030e060f070906030c08130c0b030c22050d02090a1808190f020d0521040f0b0609010b0f03040c1205060a 75
    0x42d04240b0b07000c20210401841070492910300c00e0340c003501c040c000515060302c4200007450031105601c48005040000014020061407224550040c00c0c001d04506255052814215030340c041402000c154a41d5400c0315900c140c07082d000203100710000d8041d0b64180c248030a4281440034110707500d81c003203444007200141c80e078480e102c0c1e038010b42030551310a0b506846062544c55002c485201c140e64030030342c1c1d020129184402c600214041c261008110b0340d01d188070401420440303006503e400d0409440d40c010031087c0c5a0b602042e9583e9070403211400140da4407546000181030070060000314000300107070001080b55a900074400402c07002041d04041e048441e04464140044202c24016004100700c40c201038007640c00741c0415003035035034440001d031140a46c01c0401c5078212000d1714400040c00d407900c01d0011043c2d52903080036055403ea0215030402017805800d00c100c1401900c0103100200150600a00382e140303801800c0c1c010714514a210780d034100350b9503501080d01c3c5101103500d00201c00301040ba = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 840789982 1250 840788732 840788743
    0xd1a0901030f0b0c09030709200406080108070506070c030f0204090803010602010b091003110d060f0c050d0b092419030803040515040507270504051b01020102040506031f0810021902 80
    0x520040080030200c1c2423001035406041a2511002e44690f400981030142031104041c1014160070341c0c901c001580b4003030203d483c02f4030faa40002d0085c2e00400050001c1000007118400f907070b402c80c2c490b01101d00103102050060800c0140034103001404000420306e9175041d0010300c0505801c4903a803031036840d000e04000f0644010710009054440c1e440e540c11303003803c101d010600342c103010307010000c4c440380015451400d41d21300003c81d4002500000c0d11403c030000c0ba01c94640c5601040d00c0e8920245403154210f0a001c81804502c00c00d103400c40c0405400355940480319004000440c0800c07030f03c99030b038a841d4800390802c2c0c1d0111124003a59201d6034a5460f46000188119081002424098901900d04000c451800e00300f001400f408011a0070740c04050141c0340c0030b0351103000141180d2841c7c08861a0102c4042810390441e40104010029680c8480a603500096501221840c14040c00d0540e44082d00c60342c401c1450340550040c101100e507096004d0100d4441c00008000602000c0f0b60490301d94 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 840791232 1250 840789982 840789997
    0xb490c080f0a051b0d09020a0905040302100209040e1603060e030f0a0c031e023004031217070504050a050109060f0809280c090b060d1a0901030f0b0c 66
    0x407850900020072101c203680103282c0081d0400c120150504c190304441c10710340c4c4550300c0b40342c4454440d18039000710f04149919a005042007801000076003400d81d0b000307403a01c40c83c1344018440ba802244101f000e544503441006031a80c8003088882c010b010259140814440d403005941c01440c040324941d000c1030200807503c542e248038015600d45170010900b07a41180f070000d030a60410000c080084026442c2100e5411700c85541d07001064814142d45c00c135034161703145c1003030100502da40035000740c00d850191041c2c4017a03aa010005003035001910804840d4002610b444128024002061080080d08440180b080d10303410307912031802c01c1d203410040d58a0340c007612400001031004030b80040b180380f08118075500401e616090315484423892038416604c020403105128110b00a170f611000b00404040842d0042c4403008051101c00184d1002600b10302648280090a580b6008014035064410046603900c0c00000e00d01c5806584a05042401038442407048920200c200049131001e80c00d42d0503225031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 840792482 1250 840791232 840791251
    0xf17180f01051204031b0602031510090f030807051213030501060e06151303140d110a0c0323070311041a1c080d021b070f0b490c08 58
    0x40d0f04c903581c0c21500d000501803928680030100c194a0700203000c83c0019809421003070050782c000001202000041101e00305004188800350b101003102d0140003104100303d98000310040c4d103400543c10441d040284d1003c0e20740c1c03920700c00640d451030b290b0b2160300002981c2c040c1d0001c00941c0d40342c03c49851059025152168404100c1c1c40441c01c0280002c000c01d100300070040b80c0120150303660b840d03070400d0051a100b902c1c180c0260610120242c1c4c4024490a80e480700f41c0244030034a0b517a1641c803162841c170700001c0c2c4002c0c4400064801d030b03181200c4c81105040c01e241110700c00c5560707080410440740030a000074400d03800d1000e004a0b10401c0c004130400c1010081a0020000c13186070443d458511701c4d10101c481c907400b44249010754400b440500b00b0b02c99038600c0e80502c2c4019201484c140b460710b400610f50301d080b018050180700100003c2c1c51078580020145483c039013190720716410070740b24000c00003001180c003001080940103098180100040900c014001444070719070039075882c1c00888200c00e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 840793732 1250 840792482 840792517
    0x120c06060d05011b031a22092105030a0e0328110105010b090f1e010305130f20040e12090d0c0807062a0f17180f0105 52
    0xe9480c0c0300d000d09985034402c1c400000c80c034007145100603425820071443c0d400b00396244900c2c1900c104c4841c0050656108403a190070b0085840d000000910031410170b58a039a039a1003400c03041184141448400c6c1074420521034180c000d0701c00081141d44221b0325403d0300c604095032091048000400d503840c4042398030101d4084822000c148d0305401407207644600b00f26554404000310300007841254013809015402c1603441505806018481c000141c4890090001c0f42c2081c190951003240116034010034038001c1104d849200c4849010007035600050300b542036000c141001c01c08080c1c90107808070720400e40264555141c01c100004c580c000a8107880f02c0d000f25451400a0a0314001014407040082c002140f0040302d03180c2c031411983c550007001803540550418000d840e000384200b0502c01000f050290800c075060041c001c00c41c14110000e104580d089207600070403510140300080d610b0541015900c4000302a405c44015a65080b1107010741085003050209500c00c00403561b030304d1041e149904 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 840794982 1250 840793732 840793741
    0x12050702090f1b04170106050307030317040c0302040f05100501081009020706020d0e0a0c151704060f0c020c0406050303120f0703020d1a0424230607050708120c06 72
    0x42c80c140000c040c03800d520484902c100141c03090b04050400340107441c60320081c03d0300d0710a074142102d10940010703100e603018000410000e90311035445c0d10807910f50f4100c003105803140d15002c0101c0718a81c100070360090524056420500169024a12820381c8080792408032380e0354001034030400d1050715100621140303554140000240e580041c1403a43c4a00300052512680190000032103201c10080ea02a4011000001c24003140382002c8010b0520010a0f14944803200005040b09560440b0281c2da0403181c4002000e110861784162105910400c05000e0b0415000f0000c5d10b0f80d050050641c030072460120081060b090000503205404d20b0628a0162511480b41d86420f00318011b1984042580811517151040110b01a018241c98800425184584100b04010a90b1030900f480f000b650091902000c008a0420020045503540c4602181c43c20740c03228000d81c0d5031412031649801041c00514031081200000b2000d00300c860401c20341e5010010309420880ca07200f0340010005903400b000119 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 840796232 1250 840794982 840795001
    0x11060f04210905041806060e01030c0b0c0606040e160906080d08090a02010302090a030c0e010f050603060109030b0c0702190801060e0408030412091502150604020f0414040902031204031205070209 86
    0x44440040c584603064401002d555060187e541c03e4000c050f180044400400070441d880c104800502a02e541d610b05100783d130090156961002810180300f42e0326201d907149144400d220380c0c0c0300ca03c3d61001c007800807520340302c420b40940454400e511a42c404c854040e1880ca04c40c03c81280200307244005821140b50540045000c1d40010300c1071540446500340002c0000e8407104040001d021110041010398540602224150030f036600403400740c0c0c0708100b002010783e44500701d9001d903a4401604000c0b5141e40b605000a4041c0d00310007034002e18051803080451a10261000403608100c00900940d629080c889901d07032003d9400400080d03041c404900058118040c100c1101040c2c03400c814410b0b5150a45080740030320040c268007581001c0e122900e1381110380c0041b40c0c0301a041d03405601e40040140a000c041c4560b100750a86103c10216400c22661a0303007118004540040c1110700c00d8208c4501c51225034403506c8120b0301118903041d1188540c0c043c1c8103440c5140e0700101002d060742e4514545 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 840797482 1250 840796232 840796241
    0x118060207021c0302060a0606110c010f050c0d032a140d1424010e030a06050c0c0a080a02160b0a03020703031e06050a0f0f060f11060f0421090504 65
    0x2c03a0f00030001c4040e0f0044200c40d4864215090113076000707201504240030090121801340c2c01550030041c2d1048041e054000c002001130311410286007820754902e5400d4210341038050905020080c2c043c48924031041607240c0c118089600420842603250241043c41440e2000764401d880d0210703807600c001208a10324a005020000401040440c000306038111761500742004680480c41e03100c146007103007000240400310f0b2507241001e0a058000b9061070740000d580b869410001001681c031a400038035444418030599003038000c08022100404481d2400c034005402141c10351006204801021610b502e40003401030444000c00c6120f0300d45640250304902944c0101025030030300d03031078a40a000c101300071140c3c031600001c140c4000542604050170041c0c000d107240c0c00940c01c006056010700200c07441042c00b000f107451a0408985882015400b5200c8400140f0b20b00e001d805080b0400054404c8039059a200324400d41d05801000c0c4088880b46422403010810f4002406050b820300107420300d50311 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 840798732 1250 840797482 840797497
    0x6090a1515210f0303021b07050609100c0f0804081506102708010c1d0303090f1503010e07030509011815291c170a0302040902160c050301180602 64
    0x21000b84045240c0b00c10040480900040f80041c0d4002154107140303604007079201c0c000e03080e8009010140d16100018489005240c0750510601415105490050256800c0d210103075108542030340d10364441c1002c010980051040188030701a071202490005440c0350414841c680c0100307291110525003400300c900a885030580b03103000e4071007980110b2501d4a1081031008100480010403150745558008010107112010002c1800005400401c50341d804002e68000d92030a0b9481c421709a01100003e8200c11f85500c148a410750010001c03810079507100d000e600c1955262400c0c0902d440d0984140d00b207421400300528210440c001c2c041c00294804140360b0300265800000c201d5901c0721070001d040c00c42c1c4c40040840d54004618140300d40c200041c3c410040c880c50b00d0011400c0650381c0790115100300c152040d100c250b000090100201d13005c0d50580303010303005002d0b04548501044001c01000d0062102c190b0781980040c0c000a03e51805006101c0500249082900084029078440b00a90407421 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 840799982 1250 840798732 840798779
    0xf0b0907030c23120c01021213030206030c090d030c2d2a0f03050601242109060b13020307091211030f030d0e3c06090a1515 55
    0x406100d010390b6003604071002c80c00b10b10044d240b074419020007e0b24040301d400c1c000c12800c1051184a4060340714003292021250180c510959940e074420703220419124442e60150302c560000d85000616600816070000103214980702c010020a2996040c0400030a0524207180c40460101d040001c80f14910880301102d00e0524a0751401c82006a8500c0102c40c0c1112001a942000c20002c0c00020051140149102e454100e4007980c641d400070340c03c0054070060000d001441c0c0c80403400b01e491001101e600744103240c080261030803602e03041004c0c000601300350f4442c01c51074480146c06016442107d004002d00d0b200e4442c614039050458043d08c002d62001c0e00c0040082186241e151800c0c008080d100c420300c4050340c0d441d030201240500315100e4400d440c0e0140d0029500541c1c1d0803a0807041412080b01c2400c00750000c03443d0360602c9005000c0340a03856580640301c14000030440000d80c450303246210344800204003603040d000074102c8190b5a00f8908099032503030108040a00c060740400035003d004c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 840801232 1250 840799982 840800039
    0x402120a020603090114010f081e0c0a14040c0234051f1e0507060929061203120103020904020102120a0c0c050f10081f030f0b0907030c 60
    0x381c0028645030801c0301c2d1502d03140d44400301034104441030000389000d808080104c8050700e08017604140d0320720040b00040220400c2401c602050703d010050745040b10b00080c0400c0318203880f100f28440308903c03c5866806142481030390f81705540045045540d4102d440c010304400750002c08000b00c20090740b03000007902e241000020038140c644070034030b843c040c2c484519002041e5141000400400300321000f86401480d40700c2d00719003250701000300d400e401d410410104244035282803c4140c1d000c504a04000c0d05c10003030040d0f455009038107609200e002c0480740c1c40e64080002d0741940d160b2141d600c43c02d80c0c0304030b6036005100529010304d46641282c010720480f8220107500c1d407011181da000c0000728011420a0340d4a5080110f15103803c8080c000c1512004201d81104000c00d2600380501000003e1100d064000f48003c59840102c103100003048004c440519620709003003048031f2400000f61440440307100041c104000025500045940c48480564018030b000c2840f0610702c0050400c00080340300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 840802482 1250 840801232 840801253
    0xe04080a121a060a0318120f05070b04060f02091e010e0d050601230307030302070515071e030302130e0604110306090703020901030f060621050127060b0307110c09010e040212 77
    0x141c0c07900422941f09045034200c0c9004045c003d4089a18007091104100c020441600041e15058102c1d80041d4840c4e4003250b007944504188019019488106401440c0300000c14030002d66000d013010400020380b80c0c100312250306403d01610361010b540241196210100410084584074800c1e18902d1841c00480b521580382400241402075507072084d070050340710940a010b940740461036480b40190150303010745401040e585c2c2e989402c217810194030300103007190200b20615000c0e40449600390114405e0032540c688614a01c50a440306940c1a4015031415501035600b14490048a024060040041641d642d55038000c40284d48000301e154100340e12801012100072071070003010050115910340606614000d01c001900e050340000d4070b4155400c003801000b43c07103803010440742200002c0140000c0324030104000c102418490b40814624a0000104540550300c501c5c0c500502c00464140d0308044980803c201c0d4850080c02840345c1422104041401071810805440314110340c1020703150030402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 840803732 1250 840802482 840802511
    0x251d03070518040203032511010512040605090f01060b0c061806040813120c030302240115050f120709091506030b0d05060114040c0c0c090e070e04080a121a060a03 72
    0x200e40074080d1801c4210403140308000f80c0c00f6902348110004c2c6040350510b00301404a451055010b0801340440c0d0790744c008202445014044801900781c0c42d070084c0102580c41c04000461707400003210004d540a00008986903031440d61080828902c250001c0040f52201d4941084a620100020f00c0115081030000303042100d0300c06003000c0d240078004203008549942406410101e0100d25441c50141550007102d41180c03c198070360549400b0110755030b004801c810182c1b43c40c4603d0702500d10040700420610003032001d02c020544501c10550758240c80c10740e1000402e01f9980300030781840500040c204140480c1d8404d6008400004008043c02e601d40000d1325034034249038082e00100303204004a08510380c181001c1c06150320304ca4041c41c111b1920311080c1c69007500c8030703c28010240c06580341d80c0d04507002041001800007900001042c6034060030306150100c50b0b544420707208404500c1900420311008001c0c49891981c0e441c4403995005140c84400300301895110038a804245540c0d01262040d110707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 840804982 1250 840803732 840803767
    0x30a230f0706081f09050c070203070807080c030d0f0c0305070803040f02120c0d06050a09021804020306070509010507020f04200318060105030a060203251d0307051804020303 77
    0x42440001d4000316042c010010640c1c00b00900340b41c0c0038104540b590390b45504628800e01152a1281e00080b541c980340b0725a100d030f10a484d0060360520030a032020504000c00300d110001c6503000c208551018005106040e141c0000c014510041604030319074440c05070107100d00720482482860f00c9440c045155841c1d1207180c0081e035007540d03490110100d10085040c074100403103001240000600b20100e9480c0040c464010000f001815992600081050001070380c205030045c0380d008000d448072030440c2044d56044034045030300764420300c174000214841c03a000340c2c120f41c85104180e4403645010751903024412110111a095500a5034499620714940c800001401c550340f04840816906e040c9030358040c4600b44100125007941e04840e00411055034002401a20300741c0c80303035000d40c980e5200440010880101e0b0340804000b641d802c8441080350342720041d000099034030102c041171000c2240526079112254041c0d590003681c0e28102e2070f03184c80d4652550364844d100034222071400c0d500c03040340803041d0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 840806232 1250 840804982 840805003
    0x507030e03030405130b010f020f33010803190903030801050907090b03010f140303040b03060111010e01020f0a0824010309061107060b09010e100b0f0c010e160501020309030a23 78
    0xb60791240c07811555a4059281c20608c40c0a00c01805501c0c80c841020751241800b51442200f422210540c0410840ca080300001c42c81a16440869a41e500e000c4070b61240d010030555903203500018054814075002c2c2403180309482e01070ba2605601d130300380424041c416a016105000703000d0784040000c0c01c80700003002036000e800f644040e40c00080c81c094141c1c488407180c0502511941040c07005000d00040e00054070750211702480d00120100c46400c00600515110091030b009500005860b070960007000000c01e5268200c1da14090030b603589d181c0e03440301c640322070003120b01d1038880d141211451741c071a401108149000d101c0000c0d00100c403240c81035040d44042401c6811781e4031410140e241c0d1602c2007000c0d00401741c41401e0480c903d031443d10700d00c8030f034402c3c002c034880841c0128a448080d440c0c5001d80b1200e01400000b001000310003030206550b5111101086034555a05030085965480482076034101a4080c00a243c217030700b1940c5510b660400040d1a002058800e100c02d41c102d0020030412038035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 840807482 1250 840806232 840806269
    0xc0201020a14070807090207080f1c09060501030209160c020f01180f091407020303060114070204020d20040621090c0308070c090b1c05010b120c0a060f0507030e03030405 75
    0x840c2c0c80d2640e81341c10405181d01003003005205002d04404101d00c4800c0300c4840c4101008030b9030300c0040500c9200800407400a002c0961320700040641005240d40c0400d040c4c034022100101030707558a03450f01071b840007152241000600d03842030f00301c0142051403a490210b201410711000102c000482e0f030740101c3c000e0b4801200071441c40000c202c1c0d8512841038010b59400f1403603600e401d00c1c013000702942d284000703031505040003000d8484940484852041d40c203610750041003559030b242c0703220564020304504003e005039004801d2801e14070004450488045800c0c036240c0c10040200d500c0d80c48043c0c880900c811340c07a980c50b0504040041c50090002c40558801c804094450f1828104501c854486411030070b82d440c07501100e078030503503555200401003421031180342c2c2c002c80c0d90b407030814050103044500359045074800310003542e014000301d4141c2c00300c0e5007a510107070707030690b24001100c0042010441401054080296034003080c8140c1c1c0d108070603c0c0103411607140964450104a0316800000345584 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 840808732 1250 840807482 840807493
    0xd0203041b06080f0901091e02040c050313020607020d210305010614030a020c011116201c0602091005030702060609060109171c0507032601060c0201020a14 69
    0x400c100c41d07000c000800000500500410708007040a03211010107820790f880400d81c10001050074001750015815164086020100414174007155414103949100481c8614140141052018450016a03102e6282c015075046980d96540038422140d01c0490181d0b008500c014018000c6900d0380c0e02c424039400169242042c0c00130180c0d009040b030b04103800000820034100000860b10044105403504451150b00c011707562600744080d640140141c00d40c181c20110040b80d00d421000b10342c1c2c01042d209000e42d1555441901d004010310209541d041c601e6448080b49038021700441e0b0465003104568898200140b51a07103034000a82d90602c410504400030b1400010820100e42c10701000360000020b8419500e071b4242800060452840d90213481c0c100c01100e2800f00703101c541080200c88010b80e200c04000c200c0c00107000101640d210f10007e42c04641da8803215050000000200b1420181d00e0300640c656900f41301007101c04403c00d0700241d0440c420b4100f541c0c0411060080040d001482400506 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 840809982 1250 840808732 840808741
    0x90602070c0f0f03050c1c0b010b0316140301060c0309081203061f140a0e0a0e0106020115030503040e0a02071a04201f1103070c21260c030d0203 64
    0x10002c03aa0758006601e1011422810000280c00041400030312208880300601c01d006040501130440042201400c14980d0000005008405500440c0142400061054245201402564241080c00e2176056403c01000104402440b516450351400d100b40313804d4150940e03030f074001490081c0c00c4103500111040001440624604441c4002d4100b0320304880c0400030003090406401c40d0344081e00d600c4480c10008954111500c030f114441d03102ca6005010001d05511405080d4446900740104400342d0705e0000060b80080500409000b207036840760086103010300306051250360100180900e0a000d40a10080b00010038510528180c1d10050011900c9481c01e03041c80031304001c02c03250240e40b1485005c07108016807200341041041800410810188100d4640210707200c9218101c04145804049074050410800300510000c5a18030040c641086a80142d0402034480c5548014203041216403000400f9086000030380041d403044540d1402c15a40002e8281954040219007203865400810803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 840811232 1250 840809982 840809999
    0x21c081e03160807320d0e0105090105190c0201020d020c03120705040b34080d0c0509130b040603060204060f0909090203031209100c0921110112090602070c 69
    0x70066010b180c5031011003400e00d40000344c00b00d102100c1c100da40601e007102c2c01c20350f03040384003001daa2810207151140e034600e080e40c1c4d0440100340b1a4055030a950812020502c2d00005000b554019404040e03100b95070302d00805407130000d1800400c86400d654082c420b0702d50304d03e5940b020302a00c2140030003460b6915980354031144c50b450300a14500a02c1410702050003109040c0003900c0080c80c110542c0c0b410f8000c01890f108504030100054500b40c007404100001f0050208094241c1a503942c4041c081650741c19415100d0303008480c0002c1c3c0055021164485048690f000880d0410001c2d00c009100d5840391941c0b004d90744190007120200784800350340c080099000d03a01d40010004500d0420805c40780d0780c00a42c0b02d04c03820345205404560740380810901c1c1400c0c0440c0e41c3c0c814500c00308001d15000c1c004090848038181c40385440700100c1d10240d0003d1030741301080040241d84461950001c000c01d40040d0b480080240750400d17034598541116000600e0fa100030590726000b8108860a1803612910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 840812482 1250 840811232 840811261
    0xb0a1401030c140910111912050a020c010f110a031d010206090a060e07171b03030a02060a0507020a0c0905060406080307050703030c0f020d141603021c081e03 70
    0x2c00c2c1c10028078411040700c0300e01c1401580c0d110707601260015000d90980c441150b400041c0600e41060b400744241350109440c000192005d05440b5000100e0b140402c100150741d107004e008107010260b0456020210298428441000c012009080c004141c01d82104076a1070041e580104034040703040e0503605011009107040100c5810400d10040ca200c4c5821000607465540c41c42c801841d0715250724450038204810302100024148403800003800c40c48102d44070f03a59401c003221136104904c0e1224088050f0801004858040f84540c00908094907190f001078000c050040c00142107000340309440b0002003030106c20200a00001901040b941000381c200030448003541c5c0704c401d0700d03402001141c0014401240501c1201d405041001c020300e105e040c40600c101482034000e6000e01a02402800c2141f50165a101c04014804440709070103d010310b400115050b001c00f03903000c4104071035a1424041003803003c24241c441d1003000d050105072103031001f03101100c1c001c0c030280000100c1008200b04a0224 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 840813732 1250 840812482 840812501
    0x11010e040605030c04020a090803030a0222060e12011b081012030f08060109210605010906080a150e0a21020a03080118200417030c0c0d060b0a140103 66
    0x1000c00641e45004000380d135075003540c0011400b840d008214800814028014180101001015251360b0300d00105580d0095104031481042044064404040007202680c6041039401396220855001c8540342082a803101e0702c0380d250282d6407114002c11030030100d00c00c000013400302e030f0701c0b800d4040c00c04245601d5a41e4142d000962055214610301004c03941c040d41d4280c0321009403c060380c845e01d400d001200e8006c003d4001020841940c0e5421886900e250032034885e09020308802c0082d640c0b594600000d070f460510074020143d0080c0344000c045008528070b20512003040c01e00048117440300c130820b030508240c4202598480301c801f02a45810355a80b103481030080300e42c8040e0140c40c02765640902680e2060240c482c60030f6007442c20445003001d95104001c00f001c402122085034205010104807a4071602541c00c40521401410031460000410b4410740b200c0c24014110f0196401b0501041c1ca503002001d88455442d682d600c00305880b4a0350035809481c4960482e17024032079820024090741c98048 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 840814982 1250 840813732 840813739
    0x30111030c0a0f03060b031305010513020a060e01020309120a0311010c1d06160606050102070911090913060603060c031b021e121603110a03021005100b0711010e 71
    0x7006a0110601d040340e00400d11070a00d01e00d140c2c94140120700801054003c50301620340002849a408002d8a4040b100d500c540300031f11180c0c3e100c40d08036a9008420800035088800d900050024501030000c0c140c403004184128bd081840300c0c1c0c002520b0240041654002c1c0e04180401d03014184d1000a0705042160070000344100289400f004000101007410300c1d40f45002c007030642c01156280000c8400c0d50a4080d01c03901da01e800c90410030014280d038030800340503115050002407408041e01034010420703403030301c200c030301304010b0701c0500c00804002080c001501d02c0c8501400c00040442c03003810301840c0200c4000405c50181100036007150f100344203103d0000e544980000d012030b400104d40b0003141340d5030380c0729980b030360811012480d00c4420300280240c01404200b082d203090340c0c08080312005009607a01400325000401c0d480d00d8142c075160260044c2c00101a15207200040e401c01c942291450301003002a50740c4807004402e83c6c004102c00c80e02070358481050512503a0004402c119824103c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 840816232 1250 840814982 840814987
    0x2121803060c030c07060203040303180b07030608150406020a021e011b03020c0a0210020c06070303050f0708010e010603050601091208070c050441010e040302060c03070909090c08010614030111 85
    0x20804c0f0b0482d4020305000801594001002404040c4640c11040400360b0b90001d03000d00d104031385000c0401c0ca070110f9090002915101c00024a1040003030031310b818034442a074821490310780c0e40f158400b81d8050100c0764103601c44c0b020078402d498420140c07002c1c4020304200004851009804034041200d202402104040c01805000034481022030310041280d81110303c00c4251150113400e80c10441014040c5a100c000400ca01080c990143c01a92103140c08a020314807955410000b550800c0080c050300707124480d540c0040c8941d82c029030081e070304524141010078070700b951403002c82d00384080354104843c440c402044400c20440d07a040c0c110b024240490f818052000080b00b41c4100c07034510200204003405000014102d1109038520007140a800c0a04000c6983c5440c00c01c1c040d114142d0f8100c00502c03c000010ba1161051016240204100d42d200c940580c5858040c4016150409041e10003012040000856250910032840141a0342c51000b242c28034210406084030541c80700c006903802e08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 840817482 1250 840816232 840816241
    0x60904051f08030c0d230a09170f100e0705090c0903030f09040b0d0510020904110c010501050117010f0303080a0e0d081803070803040816060203240f010f080702121803060c03 77
    0x4131009803100c8010800515100c1810503400c45098102d640000b00101c1c0300c030040806080d006c101801004c0d405000c8414bc2e1107180d40103000c03944050302c2d15040381c01c5604180706a01c0c06001340d40d00f24480c0342055080281800c0000e086a210607142c001d46040010a10040e0900340a50300000104035003180a8040d15100c1c41d41382c42e0382603245004954006042482c5942e0b46c5e01800c13005000c00400307510b6061841d0b4042c0289803e02071035000c90082601c0891494044054905a030581e02401d40d100c0d00d942e50554098902401500382c0c6621207060740c0c98904100000303809240d40780e0b10701c0601c0c10050905010154000c0c254020768004025000105220000301c07a005580b203d9219541c00201300c10b0a1100550075008100301e00000502c42c0c00003165042c140344d115442d007090b00c07601c2a1070800c07426142d0390f800da41c042403a55160324a020b004181d901d80c041c00c50300541350300910021071071805a0110f1003540e1401054156140581403c105c00c07a0b00014062032a07296042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 840818732 1250 840817482 840817517
    0x801060e0a06140d0603060e010b091302040903122301060504080c0609191e0e07170a0f150e0106030e0601092313051b060904051f08030c0d 62
    0xa46006001c00c3c030012074400a2000018000c80f030801a01c05001c100c85074a074034041380500110086a0b1841d07007002c200000e1881c10303540c25406103100e8825540c0d41010396080c070010303250800c025000c2c06078010180d007880c0c04078050101140d209480c80000714404460009440d941178000500b040720910003802603402c001f83d5410215030480d00315445d030007007000203011002400b01c481c012118024000503482c03107100c3c0000c120030000d462f0130f0003980c56040d0641d54903011100d80300020380e01c13111503005030880390700550002405000840d040daa0b0b44000d00540c0e2202c006d0740048400350104015554003d00c0c04c034007400c0ca900d014002c101c0340b076000d40c1d035071030301030060360119a5100c02d40d0501210b12103140880c0e80003d20541c07003a2038081c03c60308000300d8a9400b902c0f0743c050140c100040c043c03078074030780010f5140041400341010002420310005000c001e0800781c0800440001085200c045402c21009000940c0115955113401204a042c015881d00c480c0601c1616618a6401c11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 840819982 1250 840818732 840818749
    0x311030727050a0e011406090916030e03030c0d14090a030f02150703020a1b021c080d02160c08120d2315010914180702072102010801060e 61
    0x50038000358104690546a180c1d050400aa011540c080f00851000480c44c0d11005024100e90044c0282074903c0d5080341445200e1044044090b400b40b000c400003648185d0407041f401041503185030009008c01945242c515542c4140c5099584110116404018450500030a409240f0300c58109560703003402030f81070f0fa072640d184c0740c01410b03c0182d400c0750036402d1017003180e0340142603294815038141c01d0240010340207600802a80d00040d410541c1c00041c00a200e415920380da0303000d40180c5000135000c2e07070320766811010700084401000401050304400414005402d1014002108528507802da2405550b0306010f580040f074180c00891011480107502000d5401c1c0100d4408045206240d82007450f0603400c0c284c6491811003160310901001c6101c503007442e0340c804003e8030380300b203000e03151680d40a0200c0c030020000d074000d1218408054004081640d50b4210f072070760040398096501c481444006104030303894020182c902c120350b1025503034801d2025004107801e0806034140f00042001c1000613 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 840821232 1250 840819982 840820007
    0xc2802010f2301031113020301091a03030c071401050c0102030109062409030605131202100501140a03020d050c03030307111605010e090601140c0f070611030706150e0112020103110307 81
    0x351048082d017910380e151221140800d903600c610443d601d44e1221000c0300103002c4440c44150501054180107010309000045808134581100241801c42c0f40101d840606020304e5402410060144602004004240003640c040d14482002054840c1040c5070200c0005181c107545030600c141d44213061903107400003c0310064030b400c1603012819555400341510f0407500503100400e405c40650b1800061036010500c003110b4800d01c9028081c59981c0c0c000c1c42203148010401c1544203045610800c014038110211703005140c403960545030304000c02c00c006419500103c800101107500800c3c4c0011211050000304203444000081e501c4481c140700000344004203028240d03003c1d25241d00851286d0f0b0081120b040c003030729210301290fa1100c2c00d2401c940c40f28582e0100764990700c183d60022401e03034015a50001b03480226170040d42425481c0e280c0d903001d0100300401c140d14170380c0010045090052a00158080c203850046c0c4180c0c9825440010125134124000380741d80f4070f0610500964070390100041020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 840822482 1250 840821232 840821243
    0x909070f0308090402070f060507110309030c09090a05011803120204030c29040b12010807030f171c0606170f011a040810050619060203030c2802010f230103 69
    0xf5940420003050091041c00d0020b80b240045408220400c60182c120910408480d070b28106803000c40c4440380e540e4001c0540d080d170f26030846245510542031003807204c0c0d071045881040b952882c16544455086801c0c500e100c09208140e0038141c010706801241c0801c1d0050102d108614040c5540c03540c01c01848107010714010742e980c0005c0c003940000440d19a04441c19182203080e52180d07140b1407840723258468400e5929204089000046241c2d000c034031101120b4100010743d043c0c0c402c4d40c1c0c5d0f00307810000750103d8452058050208001a20820b5082c44010342045800243c1504200010305880e402c0307411140403401c4031041010600c43c000130716046a07114a039419182215144148160080743c02c2400726101d1541c0070f442d142499081203008000c00d40b1400c0c1030441c11442185122824040d00340541e20420104441c0c1d00c0d00001068801c582d89800c3e001a69218480d0030031400000c40040142c0d150303200040320072014450032410181d1201d460f04001c00b0440ea0030310340e00e814407000c2c0c80d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 840823732 1250 840822482 840822487
    0xc0206180601141018140a0b0403150c1b1514090a060f20070b0603030c250312020d030c0c0309030204050a0207080c060a0605010311031512100b0909070f0308 70
    0x41380d6010f03d4100000c2245c00c013550f08100d449261520f1600084220948610102600020400a014110b4066903000b4281c0c40754044001c440d0700141054050983c108002e4401e04000443c100c61540d4115105032401d1084d00b5a4043d20010342e05508a402d0540100700140030260394005001c5203419805100851030340041007604000f0a0000d1409045030260308021002001541c000c0884038403807110081c950710740b1028103a6901919030a41d0460703000104004850b241011400320020740682c180d1001e9403030380c0d2945840300c070241c43c1e0320140e032241100c00c5841c0e070140185888a645803403d212000406e071030007807065030148000381c02583e680c0007003228880d15130104d649403a004600c150f40d54200d6644140d0f604012101c003a5114070f0080081007540c400d0180c0516003242001c1e15003562186100d00342d0304910090602c0d4400c100312040840e01c03e040c09890311070b10b00108005540303040c030400c0c042c50000c0200010b01e50380040e181031101050000441007969008010180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 840824982 1250 840823732 840823759
    0xf06070f0f0f020708160305010e071a28110106060e0d02090a0e030c030a0e1c060e212a030f0309010f09080c0114010e06060c0a02040c020618060114 66
    0x2403d04c4080d400951080c0502c0b604000e80c0c0071203031082e004483c410f500810492400d40c2082d601d6000714003e420342d90003070b45540f00960651001500300710300e040c2100700b0302030700e0b04aa503807400b080b201510011517001808810801401e10800c0c2c000e10150518181408914001844002c0341100c000d00c0341100c02c01051164040b64080000412140c04407642c5a404c420130319902c0d0044044800060124040c6802c1400c0510010080042c51030403600040f6041c0e0760100034003680014592a0b1040781d83c0900c141d040c209404918240420f2000c0d5941d182c40d10b00202c1103050350590b00b04200f9500d00009000d400002c4943d100002c5203202d480340c460110382409000181494019182806862018408410300070900f116000000704031103a00c1040860550304240715614404028500144890400c0f00041100300d003440103451130b03002c070380c0c3c0060b00f105d071071050505c0164015401c21450040c10800400b4a84009004040c40e40c036203103a00d90700310300902010707010790220310310007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 840826232 1250 840824982 840824987
    0xe031b0106091109030f030a020d03090203250f06140307051b03030c0310091a040e01110c060103062306011d041a0306060d0b040b180d020f06070f0f0f 67
    0x180992500900000921400f0460710f50850021303184030380529100d07030a480744000100c6900b06065005450b0350100800244d0042002c06401e81e014010f10b030b90302c21701d40c8541e01c0c08020541e41d4a0140b00142c208140e0a49803a0389812a50900c040085521480c040c000d080d0780d03026041c0e140c00c582e184640d2107030119403042111462150310001c02844a010191005184140b4190308124403483d81e4a8018090307507104001701107180700c4d01d40d04869074101900a2000b80c00c03540008030780e01e40d03009070000455010f001007412640201b03006000b0030400e8024000e0b108000b80e40081c008120a40c000c0c50100d001c7c0000d8140514519a42680d00e441c041d628185040184100080751001218084000030413109a2003070140d040042d001c2e00d003841200458682000e40c1c600c4940c0c50b07980f82c408050014108901d01c030711112992441d000c00300802c1c0e48040603a8003901032030864030000c518000c0040c0c1064284041903030f40b541101d501545441c410301451606280d00181402c09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 840827338 1106 840826232 840826241
    0x315040507051909051915020d140a0c140313080706020a060b0301090f0f0314120a0b040b0a060c0b09070b120901060b03130b06040e031b01 62
    0x345140c40c8201078002d1501d8102d091a2a2680d261703c0012030355420300e00d0310114580904000c0c0080d501003c0a2000c100e0300380002c0c24040000350029003006a1030008203664580400c002052030710425040c003805803c2401c5800b00da1200400c143c40e83e11000704807441c410540c000042074040000da101c102c6803541c3c06800b60b11039603540c48010303200d820b0015a1543d00c3e8801d003000700d00d1580e214900940b20380b49030120f0f4055440d0103045800001504105407006024030310006510340506a80510320340b2000a820100500180050110080f00f42d0171460000010039215042108061201e00a08000c6420350700c45240564a202c2030080090303400c0207210890302395484502d11a000325115001045d241d4480b6070f8a4125041211020300803112445801c00780000500169040802540d06210080c03d0710f50f916900d1089d84c1c2d058688040110000e42100030a601 = true := by decide +kernel

theorem cover : BRFrame.Cov 840647482 840827338 := by
  have h0 := BRFrame.cov_init 840647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 840647482 ≤ n) (h2 : n < 840827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
