-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0295
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:02:15.18824+00:00
-- url     : https://prove2.me/submissions/f4567001-2cf6-4e94-8962-919f499565e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 52877701 ≤ n < 53057557 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 52878951 1250 52877701 52877717
    0x30c1203160c09090c1508060a0308070201030e030c0106260d050c0f010203040b041506060504150512010603060618060e040911030a05070f240e0a0305010204080604060f0203060907 80
    0x11820079000003040d4403c008850402528004102008080b07400f5a00c030312984044c0c00e070b011141122010010344940c5c0d0444581c000c00d0003c203828400a221079070041c1404a442c0c120101d42074035507401070030740045070b0359202414072420403134a40c0040d810000e280b004c46081c80900156494100040040080c8000041c1590406006015621501001100840d2646014141200074030422101100c8000c038080c1d02c01e00c0c500315441007000b540c0182c0d4465040900b80b0800c0869102ea090520f000c1c0541805025051044c81008070301800e640d40c1c0101c0c000d4900036026120102011081c074203500d091406202c41c2d5480103250b0700c100002c89011981181ea41058218042c92164480d01400350007403030380501c5000190641115081d01010001590f54038032405565072a0600024000445024802e4140700310384e444250900108501d465695950b965400ca0f84540d10030320a40d00203104000611440313110704450302c00e0b007540039403a40c604900061145800242540117010f030320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 52880201 1250 52878951 52878953
    0x619110c1f030213170709050105100804030e01030b2101060e0112080a0302070f03080411061c0b120a05010c02010c050a0c06090503041703071401150303111c0e030c120316 76
    0x181504900070400340c144007030310a840c2d01c0c2046e110607003409003440321401e040000945091148106201220942e5035100544840d0b07801c0b039031410004002ca0415481e2400800d40d43c0d1010040105443e031403081c4900700e881b0300011400d44072150300c4041c0038038100c00104140200c440c0b8041009a1020660307a480c80102c009800900070b18030040d0080c0c0c205507401c000c01d6000110240210300a0b00c8001c8088030050402000d481031004070120310001001d804040e41d5550403225040d10020071402400d11074880c00e610700790428000359100c1c1c2d1990030020050b034084c410b6410050b0307581362140c45c1c41d290f8040a010301c2005000180050b0345c2d91040c9081c04010700941d009001000d05d4990901440d20395182e90744c00c01c00e41a9aa4a81c081d043c25818205104600100801c0020008080c0c990388099038000b4030005016024002c1c8405c0351002d0f0b420702100d000001150b00c0700001101d100f018940b03444258440355015800a16160625140020683d260300c074650f20b0b80e840c51065 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 52881451 1250 52880201 52880227
    0x30403050d170c032d04060e01110904090206090312070b07030c0923040507020309030c03030304110904061b03090303050603061b16020d050106050102060f04020d02040b0619110c1f0302 82
    0x10340c5c02011800c04220641940e008a201900340118012078041c404c2200c1c0d1800207080b01c0301c0c0802c604100004101800150609401450165000500ec0c3d07040061803070100c5d040c14100414400d820f0400502c00d01080354450710300350400d91510b01003000c103030002406010141c1d1070003814500e0b140001d000f44100480310014001400c0500240702c40c0c103200c00042d540390810200c592003800341c000d00442500b000070a80303104a400c0002494440c00c00c40511110305809041518011b0716614000c5542c1082208541c41c1090359170005910005414014215600641070900c60b40003a418006031391072600f540001c4d5501001c12030360798400b501e50f800c504419010021f402c94a000c0d04141404410740c00181180c001382c081c1c6000c2e0343c55820a135240b43c41150700075404407a03510b40a004d4207241d84480d40000014288620701424080300007014820000704030700082070101c800303a00500500c80d860700d00a090715140f01c440c8101a442d000c0721f0b2240c89520230580d002c52050303002c0f14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 52882701 1250 52881451 52881481
    0xf010f0302010203090f2107060f0219060b01120204030c05040c030c080403050a0e03062d22060b06070501090210020102070302070e04031b0809010906110c0d08040512030403050d170c03 82
    0x987d02101801203520b20002c983c03103284d82e108403408100b141d05407022907400424440c000000c6502a080d1000313003641c8081c0140801610f0604110380d10025550f10302d00703840108051070140b07103501c22452828040105032a6900d130b48408040c03d0100c5404506d4015020315001541400e03c1600d0b03005005c000c950b400c2450942d6541445414140426003104401c21800b02507204440004070404d002c0c0703401d07411400c0d80d00f0b265680384548103c60342c41b628200344d80b03507921609000c00c044543c84000ba1103074005035001c0e40c0503551180010218504402c14590f030406500003541400650b0720003039100d000601c1245000700307401c4001010180729140b100d02e902014a000204402c032401c5c2800c990704a50780c201d000c51072460002c203500e80034091140d144400e440040281010410511216801e0008212669102400080380e0f03555440142c2200f825204005d5480300c0c51403c0861820044042d041c0a1254490800303c547e0502d000440e40405402595a41c0380c07100c40d00e420901ea = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 52883951 1250 52882701 52882729
    0xe22110d060b030318030601050d05070303050c0c040507020f010506091306020d091403070b060f100513050a0b0706150b03041e0203010903030b03060a1a040e07120503030f010f0302010203090f 85
    0x10000161360740042c01c48035204140502c0c16402c480c91603813074002b841a403103120a0301409035400603504000103403050700280450388602003912611601c410105c0d054a9050b01c2c6000941c210030030307588a20070240724a83c1e100c401200c04d0640c505101d04000c1e2381c5102d40390302500841e00041d81c50792803c065003240c665181c3c82440480020362060700581c603030f04880c20440314a881040412600e2610700d160000c0494010a42490f441e80003006468540c051540e40c40745440350680050982d656803d01002860741945590343ea015600e00701044814480c0c6a00e04e10034000c2c000c0c040049401d084c0c981c0305510a50441c01c01410f0142200550b010b00c80082d45582401d0885007015450703081f481c0e414078150110b40c842e4403406081401d031900003030031341c40c0e9180c001c0c01e0660500c3c01350003e40401914000b5036922940707a40705001404030604081c0d966a1000040c45000040403201500519452020000c00c42c19a40003d403a0700c0b4544a841c4121068000e01c0c005650b900030f0b80d0445 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 52885201 1250 52883951 52883953
    0x90f02090f01080d0c032f0a0501020d0605040213121713090c030b010f180503030309010c18080309010518090702100b01020708190812010e22110d060b03 68
    0xa00e000950405906003d01908400740145460328000d5400749145c401c8842e8940c881102c1c0301ca805c102103003040c5058000140e092140a00007440b41e6080c060030500c140164005685e460365101840250b601690140e8001c520401c000960700c5140c24251303007038580f08003100c140c0d40158101742d2841d82890444480c0c01300005080e038907500315042d0f86000c4810200082c00700c290130140c04e90403200203010490104141c0000c0d01030b002d110f0014103402c0c00c08801c80b03001e10358036800802d24541045480e01c034581c1d960b084080000d0380001ca40c920036450601283c0f000d030706110707010f902c1b1301813082200d042c0180420f005003103c03000d03030b4100c5a0400140644210346031002c1d000b5650420400f10410a6250a400c640507500c003043c84c0c4141c5035440014211481d5200103500c580044078803d071784c00541030100501c010707516050030780244410341261406080252044140440480f20390340c0c6060301020070b0380055501d045001403076804954055060f8800c0c1040c80c05030401d1030580d1740c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 52886451 1250 52885201 52885219
    0xf161b0525050103060f0b0d0506010210181109060303040303110102040504090305090406060e030c0607060b06030916080105010e07050c0705030304120314040e0f04030309020301090b060310060501090504090f02 93
    0x15050603401c0300d000c0b80c00136602409110360b00d29144a410003e40500008001c0403c07039100400030f580c00860308008180704072100340c6141e000c004200d134020850b0303040500101c0102002d0100100840101d12400c1b038051020b4181b20001136540d1280348802401d0140a0002d88924902135040c2c40041c28040c2060042c5266403a00801c1c6522809104c0e105503d444000300b01c403482050301d0400070a0240042c6400b039842020403031180c1064004031040c640362540086180c44150155001d800b0140050901400d20384c4042001b001c4c030303007001400d0380c50f01c001000b1034080190a10f81003592400d045560383c10340c0d481503040040320f4208a415120009000413161200c6030500c10782380c041e59604440002c00e04c070301c00c3e05100301d1141000a06075034002c600b5550900c00c0858000d80301c0d090001301d4003034607404a400d442165100340c0300a10100100542070400307210100d030941c01b8640401002d400e00c0c002a001000324000e140c001c60352580c1400c00c0148484810305450380050071292 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 52887701 1250 52886451 52886503
    0x11512060513140a05040503180d0c0b04031e020d0f031716030c020f06010b03061f02010605090f04020901030b0c0c03040b03060f09010807030f020604090903080f161b05 75
    0x500320f0300e07503102140c00301d100005200c00c4103442128000c6612070051032501d0484149401c01d440003094480d48645158040000103000003042401440c1240d1000e86892540c1030441040e80e03200304600555824442c2c0b0801aa15a0700070a02d685e401640004610ba00b41030855001d00c4045218560707900802c14000c040035844924100d951440d60300f44401c80000700200d031203405001250756103511138001401258500c0c0c1c06940d11800141256545005101101403c0079100c2d80703040142c3d541d02014012030400d5035416a1000322000d20000d2400c0560219648810500c006055070b400c0350b011a582e601c904c012a0300c0104410700b02e07600c0799241e0440f00b126600070384410f0b02c1400c601500041a0901138001812904040041c102c03e0740380d0744804190381a003020481e03108200704001310320109940704400c10360f8060380c4d881d4280c0c5800070b007410100801801410241d02d25141100d10079910040c1900740b0701e0ba01e041c10314800202d00e0032614143d0701ca082401040c0e80450201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 52888951 1250 52887701 52887739
    0x504060603020307060e06030f071407030807120b0f0108070e0d0b06090a0618020d060b030a020a0e040e0c04090c031a0405060109021206120c06030c0d050f0115120605 74
    0x181a070b8021020344a0159590105840d00c080000080b50403010500000b09101c5a01204591003042070a2002007241080c01c204d400f0762000a040340410405018040d000d507106101210f0007040c00c0c810000b140202c400203068029240d0094100204d07940000c0d69903103e8002e51030407004c06004210a6a06481c001c16000402c03a01c01340101d610500048003a19240501d2080701e0040520608140c80841200003075888104000c0f10b16031180070004641d80080003c51060b20580c1d0010780307982244500600c1d09030b400c0d6a140c490750501d00380401107070020984071381d03006c3e00b02d600041c01e1705a0f01e03140700d11b1415544050000086100f003498440c81b1045424452807240040d01d041e603886010705002c03800707210780817140441c1c0030300001c6180c00d15403071000c401c00d0750400b1241c1100361000006c4031603004441134540d885010400300500c4d641401000c1d04a4150b59400d20907605107050b003203c103201d400c00d107402c1002c90030800308078182a5028078060030002d01088010090f1420703407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 52890201 1250 52888951 52888961
    0x50901020702011101090206031b04050607060c08130b2a040b0c0d090e0408030403051318151401080c07050f0102120108010b09010608090c090a0e1507270801050406 73
    0x41c1d001c03400c0d0301c6056144c000103114148025900400440c01c58503207000c040c41c0440c18446080310150108004a03e95486802030120700384198000f2400c055411801010040080c0034481c0d84480985207a00040541144561000000c0341d20264409000540050b00e5520042101840340025011403150b0071030005150402044040f43d0303482c5034190040344c201d803ca1003050f41001c8000c0c0031800203070048004540150091511a023800c042d01020403120301c6582c00021100000100140d0300280f50264200007004000560819881d02202c40300300c40c003030128541045050400641011210429501034940040456004040700c0311264001d5205440d00014000079600000b2612014040c10a040502130500710b0305e0b0340380c100103480410700a451400ca03801851304254240d190001b0140c41034079603000204000a20606a6003404c4c1300008500e580d0040800700302a29170449141600c51840c450700c54072a1062028010541190350040150744d4200b40621040c00b65035040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 52891451 1250 52890201 52890203
    0xc180324021c14010803070303020304020105070b130203071d1501021f02090103050c0f0901030f021e09122802030a0c06050c011427070b070f030801050907050414030c040509010207 80
    0x7000f580c11003040d01c200c4a202449009516070082116500007440ba80185801900c1030400314248100c99581d4004107800b10f61151320111090185820351404005440c01480141001d184210044400c110312407030040000041c0480140c8451141e4400c200d000741c8501c0200624816101240981c2c000c4c2d40300005c118002410030000c62082966102150070380071500180718900f401c600019800380000b0f03210020101d50901c055000181c2c400e0702c0c09010b040d8821800da95045040030014803400d48500e2009627804184d030450076803550484a15030030300803020141e0140c2079100103031401204140c0280361604103000000c1e02da810002515841c070840000f800007505d03004209840000460744a01440c580c4082e048196070a4101c0b44e8400c029241030b501515100c02002d070080d0b010580c2142d144042700805401e056200381d0460160600301c440c00e002d41840d51008100380154020864400e6070114032080d5a40c00700301262541c0300150040c4002d00d01010f210b8003c1d001194 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 52892701 1250 52891451 52891507
    0x3010305030315061305040f0e030f1c06081e010e0706080106031a030606060d0902090f040c0801110f0c033c070c0e07020a05060411040c18032402 65
    0x1020081c0c504013080c1d46031045981c94102d0814031b03000410015110b1308000d0b5601c81c0d41c4100e80d500c203d4060005004003003c410116545840250303822400c1051010304844144c94524240407402d408504002d1903c0c1c98503c80106a03203583c3c4060041045100c910032604c9094000900302e40c008040d00e0481d10a902c0803c0205000c00740e00207052a9084410342c9604440c1c00107049141c440e010700704100c6a138400080401e1943e001c02e00202060b207606000807408001c000c1000040400c04020300760f020001d110500f0709010000641c082d03125901506c00010075507032403400f4100300340c0350003041c4850b07000f510419240400f207903d080c00071000d10800307080d00d81e050038101100840320310b1580b00ca0049101441c14a00c5001c40030041d05071411030094038114004070303d0801440340203502820703000d004130584108020441d100700c0c030030a00b844038183c0c46445091640510303804403900020000c403c046d14510090007c41900040400e451000c11106070701016444d080c0702d0511406 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 52893951 1250 52892701 52892731
    0xc02031222050303071a131502090405130305040e0a09060518060a02090a1719200a0302090406150f03050601080714060406030908040b0304060e01061a04030308090a0503030103050303 81
    0x50074182c5900c114100074002517002d000b03800d07140082c0a03140760300c81d81c0810500d1829419a0b23892403580d5803202503c2c03075660041201001c62800c0e02c5056040b0460ba40540e8002240e44d5003d400c40c0614803420004000c20400100940910342204c1d2095501600130452803601074140e804d884000e44044400c0e01c80d60000407244040e07482140c7c24003400a04051069207022907074151100c0c0058805064050040c1400c50101c2c62203d0800b124856030b41d030000c000300d8074988a40aa036444d0382c2d9200f0514040100056141d15845070f400a4119001040c4030800000481107003190f90300492040000020000c1444404110385069038034a1042d1840c039a568901912084004500e89070700c010b00f00001c02046010390300c40c12589201e628080c4c14555034401c900b1a6800440f41660745c1e503204c50780b440d42d2503420b12403a409001100460b421365403208401c4081c80c051408020180512000841c544642c10048da40c5d40c030f40e0002c1129903e603102e1a01585076042a60f00e100384610038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 52895201 1250 52893951 52893959
    0x60703020109060b040e120304060f020f04080c19142d0102060108010b150711040f14090d1209050f0303040303020406020f0613030305061906030204061202040b09010c02031222 78
    0x240140d1b6050803018004000c0100e840030f41c00c0a0784d001510403505145e50300502c400328039040c00646420404006040c1d241d500d000f070000c0c2414009a05544241c801d44061280c0d1141303601c004003131302c000e9500303400c5062074a0045014581880c1403160032096150041074281260030208400c1c3d603080c0c0c280c55503a603031001224265950f9003401648129486400180062150043e00c1030034003803001c11541030b02c404041011258156884c0e41c1064558885019200c5a40642900110807800600b0507000e8000001c10350340b290b200c210b6046484c4c2d40c0100c240f28007040100a00b8000400741c03680c80c2000d10703000d802544680b151030054003541c0c03d521804000425824800c40100c0e9110b4200c1d581507604030000c10000b4511903002000c0c950407500030294411103030103001d5544005a81c0c034105480a025034001d07a0a03401180e004000030301101410105442c0d17484400e082c805010005440001d00b04030a0a0303210462000c0402c0d10b1900c101d911044201608018003140d1001e511 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 52896451 1250 52895201 52895209
    0x901110c0a05060c0a140a030f020c01140a030209040609090203010b010f0806010f0903081c050105030706020a0b09011103040b040218060616080417010e01150501270302060703020109060b 83
    0x40014450740302070403210801c25401c0c90b8009000e034031420b00540c1c81031041d550b02c050440c00800781591481c1e02c80072010b0101034002d03100201050b090f0009200c2da007440b4000902c00a080b482c01041c0200104001c400d41d07000c1d40640c0d0000100070010700803540c07100e4209004104885050b48a5801d10700c2191282d4012001406c0c606410fa4a02c1c4041e640c070f83c01510402c0980c42c250b0200940c14000002040e801c0014105815000e1014482d0900804000c82900c606810003407003074000f01002c012003030300041c1c7d4840c443d0f8454400c0d04070b56182104d1600400642e50a140d440400104210410041d2a400c0b072056208039007a07000c0c22024070701960708810440d110341d082a010800024145501c07400f8625091144083c5468141c550311500905954803400c112a603459144202100c1000c1c05090030038500c6100c42e107507c07442c20000800034040340c0010340c40001c1c1c048500130540000001017000c0c54019210036500c1d0303900d1400900a01041606442040c40c00244994a02e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 52897701 1250 52896451 52896463
    0x27060e0a0f0333020f03070306051905041a030105070f0807090303120f0603080a0c050618071701020705010603030e0915031c0c050d0309020a09050c0a0c06090507030602090111 78
    0x1401111105076122500403008104182100030b03032040b0081c00f2100b01c0c400f402d00007081440703220703141552603003419035020f01924115009540716030034059400b2150061100518100c84040b540468907240000e0001070900d4044076840d059400c0804026442d07400030f044c1c00c180680d03a519450a6565008100c03900035290000a000400601c0c90040680450b04402e5031012900c0300040c60642da80c0e1101410380c458544140460048a10300c002e1220030300ca0207a0085424091039001d40c2041c000a0311408213005800401d41d864138500360b50072007541510451940403008100c1b1a07240e06000d440c0210602c1a580f03c3c2403440001806003805d803039451100c0e0009001130942c491003807100c0d003446003010004000c00030000902c10104504206600552400382c6000844240344d00600420194942141c203040e403c0800340100c459000c0c044035840c2e0309a10b000c2c6a00b1000786080c0000c1c080c0008040c1c01c6214050010081c06101c0d4000c050004003625100301c040500441103848034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 52898951 1250 52897701 52897703
    0x10507060905030d1401091409030304080c0f16090608010b010906050a0e0d15050702030307050a08060f0405160e0f030705100302040b160302010c0e030d27060e0a0f03 74
    0x51424011000090800d0300300c850481c2c411000d80b403c004802c8030800c1100c011011400400b1000c07401003050340c03183c0c400c01d03c2d8440e46c015018964505407150607905d12000d40001c2c41030b0b0000501d120780c82c00521076941e828800300155001c0c14200d64400044628030300640b54100d03d041740000f02020305200d1004440010707184c0c1145103103404400c0c0c0703d03038104613000c0043c00307074001502d0301c0e0f565204000c560b0203200d980800b14113884002e03080101c1c3d100822000540d03104000340000c0c0ba41001c203462440c5244d140002c85035035000080b40d0104030001d0320a401c241460144547c0160320615445d00024641d0b40d0b4504030940750030400e810020506040c1c00da007000800348400e051000e000640c0b842c09040c05803a1540d01c510100d101e50207160303170010580065111343c0400d54280900100d12000b45400c40d1840403800c00a07442c0c1c4500e60754a030521014003d415a11045040c182a06405485903102983c0ea1441301401d4990758004084c03084003514004a01d050040403180150307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 52900201 1250 52898951 52898957
    0xc0606010305061008040507052e02120313060603060903170f010b071b050616060c0503040b01050904030e0a0807082a060c0a051006090e0601060203030a0f0603142a01 74
    0x4d20500301c0c081c3d6405002800550303c1c1c0c0110320010502e80c0701c000351842c0386c0222400218211020341607480040038181d9500c421504090000d10250600000341da070440e20b12015040a0710151502d00020884d581c001072210303044c949803205050b0404040b9800304020610840340b07503602100c50600c05ca0034050501941c5051006201140c0c0488105400d5a5211140d81307403d13440340c001075074a0300702c40318007503000e038941502408000d458000c5000c0c0e0841c03800c04030705604081e5580800703842d050003010b0191030824005020f0601c070703d600041410b4050040380c17440ba1074814a54441301140112005072142d03001c0c42c201c0b803500390420010400900c080c103485401303410410140390b0240021014030700c180c13890003012910600c074020440e14040701c0041e411303282018400950745070f60511101900900010042c0075000300490b9844100b0750300005910310700c41940c00040100d03800250801c2d5400140703602c90a800503c04190b0b400100c10590038000e00003c0036010030343ca40000d800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 52901451 1250 52900201 52900219
    0x120c02100e010c0203100c120501060c080a0201180501050601020706050c060406090c0e0a061a13030b0a09080c03070209180a0b07050c060a091203060302180a021b01020c060601030506 81
    0x384500c2401071038800141490410b86168541d0000792825945e03881c001c40c0325550b040040011904005220f90083d411003050181c0d43c9000806011100b488130702400a01001803803203104d038030070340c05111504280346404140c1d482a0409500070101240d599001d846009800700d00a40604140c60a03480c80a0091050b075846039526009440690760071500e0b00444e14002c10000c107282e544620440c61b0082c001032103440d000813084503210812800d1000c201c1000740c611141c82d41032502064940040c20002aa211440180020a0261000f510080d80400e80040300c1002100a143c40c44c0201c41c008856241c490b04078100d07240708503141d90140c3c0000280c100140c2d65011659010029052103820400c81d40001d40c01e19004035040c10a69036940c0291081092060302c069509180f8501000580e0450b4049140820000c281502d030001c1e200014002440540484904122504c091080e00c590700300c0681c041d4101c02d14a011034022080090f8281d403280c490b15200b0003005247c645 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 52902701 1250 52901451 52901479
    0xb0109020d02040302030f01050f060108060d03030510090c08010302030606090610030c020309090115020f030307020d030905030f071a061c0206030a1b0f09090606050703050c150c0304120c02 84
    0x3503100c800c4001016400f0302002016a40610204100140201c0041410304c1c102d1514000328170020181c9052000850902c00b890700e901c074140c124560725040024640d1900b030a61043e02a0552042000c14142800c14800d01d500082080c100d91007642194415150030007040740e81c20382210b01c147c114043d00600050345109403c51000340c44c240c01a02c0c03528007010f02241c4888000d030040e12809050710f41041419030b041141a00205106002d14118204000000e45403290502551308040e01ca1000900f80321307040c800c40710792043c2d003d0203a694800302c1c80c00e4510035158100c481d51494808002034400d04150824096503607400c0003502c00005541d0070400c65400c013074401d03104907a40e01213016006d00d0f425040c00c040b00302030f124520341c252085001002c00300c0c65044900c0041c1040c0040150982000c150381543da41030a2407902c8a10343c1d8801e600c1c01c0500d0314010181c034401e0b400d21090001040003107020b90300400307042c13000b02c120748401d6070001e4003100000c1d04041070300c64443c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 52903951 1250 52902701 52902719
    0x30608070504181709090a02070506280b190602010c021b060406051b0a03051e090d020603040f15020a0f020309010801050112090812090c1f03020a0908030313030e0a030b01 76
    0x1c1c00c103003801c81550300301503044002c150a06c0088808108403580040c00c0404e1100401400f948403a039920441040c00071520100c80c408a50f0704044099912262a24004e66a07400480052465021149410b40ea00d0348003e002e03003407041003440075005003c40d0113100c245415070300c1460b01c0c000e401c55217000c2c41d050040302d0359406a04e20082d0b04010b00a040740e4054144904101107003e5601d403911110201d54103c08401200c08032102c1c182e04001004007603c42501180c441c540464080303850b960b49041515123000c2907880101047d10f854040000302041768007900266550303995a1010403400b0a040e07a403880b40115040c04510f030200104503642c0308010a03105e22135817800202c2d00c40040d50716802c16030130003043d40041c9261700c010003d0300380707040029080c03142044542840c020458104044040d84241703d40041640000c3c030404080e001d04031f0030004003504400c5954a140c0364030b081c901c020310306000301c0001d0403440355201c0c075181c6010040c007582d4001c98801c00c0c40e443c00c4640 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 52905201 1250 52903951 52903973
    0xb071101030e0d0905010206010f030b0f04060207050f150a050103030509090702030f0a03020306041104120602180a0312180b0f070501091707060605010c12030509070b040603060807050418 83
    0x20504160700c6211815250800340190302d1590002d40b58111454240800079080c03002c1600704070f40002c90441c040000ca20120051504802407201100c02900c0301d040c9840a0702c5400303000740c0980300b0321900d03014005000a251614280940d070402c01c503201c3d00500000c0c1c0c0c41c00c0c400640012000e01116a45107485140d158006c0c40e60300480e45030910380030344410035030495400600800d601008200c61410603006504040740d50038110751a2500303200d0036144e20402c455000d4100e550102c1c184481a080f50525880c084005084005440c0d0328a85040d51908810580700000e81450950074440c59441903a020344414a0f10582012042d403c418141d811843e8150380c9076484120000100d099070842c40e14070607102c101c07150b450a483c1025400d95030700b0b40c005410000034440c19004910088131080c02c000b020325000c10307952200c091172840c040c141d400020190f20009000035540f0340642c403040c100e5844c1026a0040b503a03440400c4119007214050007072003150000c0b5040010070203090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 52906451 1250 52905201 52905233
    0x807091a210f1f0e0307020913030c0803010e0a0b09040c1505040b0a1e02030c0d0c0809130e011515050c120301030510050a02070218090a0203010f090201090608010b07 74
    0x110344030b80d145407118500e0140030050085030000d0082c4007a00e1480c144c021040c4039110100114a40b40b120b6001c1401654000d1482240b958555203000401d44904031100189800404041c0c0707958690100c1440d001c0140c1d0010100c1d89440141e507409d0030007051040c410358000c860b00f0031440c40c1c089004046000080c1036800c100c81000041049407901d005400005095954503243c4414960034855014001c000c070b00940d4014000302580880c001000d030704800300762501c0380c80c2039141e14000300240500c075903c6911001c1e981800c1c0a0030b05982c005032801006000038000c01c4680e20f0072104080b014000d20060015480c0b141140c903001c0c0000382265852401110a200c10040714003103150820f0f08106da00350030080100400218074040e0780d0304000352050440c98030300307168002181e810480b580031081c10085c0c00001d4030709005118100c49550050000d104a5078104400c1e0010003c040003240400d40e0030101003017036885002924180c501480b541881c0907210b4980003400d64030300301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 52907701 1250 52906451 52906453
    0x312052a1216050312010602060603061b090a0b03090a06110a08040813051207090c030e031602040e0d030e0601060c0312050406060f120311061504051b040807091a21 73
    0x20300c0200083c0100010540d40c419170051400c3c40d41080d01c002c0c14604044c0c07109110b5030041091000100c2424102c0d10601c80e03a003400c0e9654020007000c60321205440e800300f010600040108000510b011481c0c4400c0c510690b000c0041c3e9290741208480c50098209690009000000040004110750028400c4040c0b0040c1c0e02021580e820000c1c513400b12400000080703802c2110100003d1000b0f0240704070356540e60800b40304041c00c2043c0d4558074015607605410a680407501c000542d12141d03c030600102016040d51410002c5540c041c01520720b2110222070743c0300d4203000045c43c5100b0043c0e190613690685c0c2d0341070320002d81c00010700540b0000d0f0040d204140d40d0b440000e10f05804441c0500141400e6008000d10f8a46090151003000301e60360b4085950000010020544145c0080d600b80190440b40000c43d038640501d01070503000420442234101c9400038011410307000c00240d03102141d0541c5001d00c0502d00d0601480351141c403240105030843e28240000048400400f4041c6082d80b0041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 52908951 1250 52907701 52907737
    0x40302030a0317060a14010f110d050403020118030302060408030a0e03070b07020625030c111006030209010801140402060906090d0305030105031509250312052a12 72
    0x5000282401c80d9040200c0200b9003c405803040c00030202070042e441081214188580780c5440182d00c000d07000c1a02c82410800d41400344401540a494042000c1ea80d80c0e0490342d00e0300204401a115070b01600059000c202400d0761490b102d0b5400a40300c041d6030349603000c0c100340c0c0c40b00d64a68080b60009442020b03516201e0f480c0c200341d07000820140a000c1e0180c0c41000701420700c0c01000c0d04007903014102c0d540003800c02000b080795036105600594050a0762030b000413001340a0f00c0490344020074064040c164050b0101001d5400b01075048501524000ca17540040e0782d1361064407508172030800000c2d006030001c11001901501e8120041d0404a5019143e1490f0503900c0000448003441c81c002240490004401408a41410480c02460014010542406d42000c2140c00da4850b441c0800e01110041c83c1d44c0c4000d8442c1401c1c0c4940150340c880e01c0c1c04195240d1a1000d803058000d04040044061100710a001010340300c1d100034050700391803000d4500210101804061507014036084490b0340051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 52910201 1250 52908951 52908953
    0x40807060302132706080f06070e01030e070308070201030608031303020f0111010c1110020c0316020a0b0304060c030c03091509020a1701020705060609060105030708060118060201050906060102120901140403 91
    0x70703413030b144d00031115502c4191a0700441d1600811118182c0001643d036100d03400503008a4000075440350402c0060038602680032241c80120043e000c1c1d10b510401c01d001e0000004108061000a00f141324402d803030510180d03840b8040a5a02e008410036060114041d1108001500b04000652020401890400401e04140000c00d00f5681a0300d03100001842007040405948000d006107001c020380c8540075031500200c0b0301043d9590041c0c59029009a4081542104564aa240b000f008101941d95991a403410b410188000c0c99400282800b003802d240c2c500303195038440c1c490310081503405600c460035070070010446001051040822038110038590400308400c0003a09100c040c80001c1c10016941d0307600e602e020b03800e0640290450340101e4000083c401d003a03800005a0707621194500e445c000540d44e480040320050a10407013120401d100c01400314840c5d50640042d441210703104212015910740500482c0c1e40c11500700e401c02810828003001c9955803289480e1000401600807250070320740c403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 52911451 1250 52910201 52910219
    0x30c08071707031e0e01030b0d05010c0206090f01050c0f030a0e1b030c060403020109050607081603111b03061f091406031002070218060103140403031e0204080706030213 75
    0x7025080c050403800840d1440406a0044003604e141503483c1a0300c035090380c20b490140c02a43c0e0f00b07800ba410306464142d0700815407103024090000c7d0390090020701c82f00d41070a41c080d4550006840301100c41c01a2080080100014001c050254140b49581031828040391407071039154201801c1e0940142c1c0310903000c2d60000e000c0000603a8020505a03500c11100712004152809001e20b41c00360041506000400240c1c2e0060031080c2283c00994105688402030718010fa001c0c0b06440f0f540d4000c0f965218030f0410300d640081e46062141c800003c0fa40030010b8000c10b841c1c045960740740c40d41e259003ca40060801501121650035003040300e460100c000c2d4890f903030340341036030783c8001507440003103044042105a260801c9101001c9000000031450315407160049048502c5070024031048401c01004107803507034483e80c060030702801c0c402e802e0541d5081510740100986542000c3c02c40143e4088072404100e5820302c00ca604480b0644000c08000d860050203030081e41011840d08040030000c9000141d10107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 52912701 1250 52911451 52911473
    0x9070c02010e0907180614220b0403030302030a0509010506030a060e2409010c09060e04020307050d0212010302090c1303140a020a0b0301050a060c030c0b0c09030d020c13050402010c030c0807 84
    0x515407100c49002c00885d05a40705080c56520032800c01035585000803403000c80c0000c4500e0b0001b16441900800c0c20b815003400400c1080c1e2050304c00f1a8000340000c245540759001d1400340c2122041800591aa1111942600d4085d00c00300c0c0c1c503030040f00050000643d070742d100e50004e40b8030200707a03890300311f44100300c1c15500c29402d0501c105040c5078041011184081c4903188500c0c1e9113040501c401c6040000c000c0408a42c12180d501855000000c1440b15004100703039104e01584110039540c403031812644e440d00c40c000317100c01c4340545041004100607024103130603644141140007600e0703102071031a22506008241e25100c1605030140517824005030b00c03803650b0880901125800b16643c0c0d4940418084601d00f00d500030020009005200400a0740c010b0410a0046d0014086603580d110400c0d00210b9200c3c20821640c94403400b0b40c1e018640e074009c40c1030f040c1c038281141c1140f0322501300e0840c0001e031030701100d0003400501100d1103400002d014016054400d400740501c1c1d810700d40c1e1640c40d00b501d28 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 52913951 1250 52912701 52912711
    0x31002092d0a1202100315061202040909050f060106050301050d02090a0902091003030f050a08070f110709200f030f0a0b060d0b13060f0506070602070501090609020901090b09070c02010e09 83
    0x591000d0f0a065091245100c1032220031490300704054600041c403445480100e0241c0c0b020485130000d80190184641c06a030082e09420301c003042407903030500d8156a190b4500280c0c0720b10707000d402c00004010b80a02c0c2624103d0384054882c07080a511a0708001e89100e0007040e00704040e684881c1c00c800350711901c01c8507200d0344404410031580350a5090240c581040c0c0040c040812070208038004060703922420254010440d4104160400f04d503100aa52161080504400c00d01ca010400610013045810500984000c1d10402d4550710000c240154075100728181c004a207142000803031100d01c020540142d000e9200c6000150802c101030000d0240e600a810211400340c580700401c5035468148500300d81400c110504002e00c502c1c00400d500140d90600c9110b00c1150046815005c0c0020b98048645a80c2c2c440007c0003107161515181009180a200690107562142c0010801c2e288070300c100004d05000074a88610b6545006048551080750384003241089200d0b8a108029154004400e00034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 52915201 1250 52913951 52913969
    0x7050d03051c06180b01140c190309060306060905030a020927030a0801080115050405090c040608060f06060c060a02090a09050a0605040507030209150903120a02010b031002092d0a 79
    0x44c640094803108440040e11190b001c0d143c00000c2d80c00d6a00522402d4419a00f075025544401c407485a190800c4c1014076403022003145d040c2002d0070180d0124004064442c1d50710300700000303030f15080c1c1200c5009050280340e4160b80201800005840c1c0003100e0341c0d200346142e8510038030350b8204c02c208402c4a6402a206100d03440170a03030019081d0402032035409009400c00800c407950062000340b42d009802d1003064084d0b5503e40104401c45008d0110304491500a0b00a008231569413007529030b2580226061054442450040380892610700120f840900044005106030b8445030318070002076109903584da074410305207130000412174494080d462051441c840c4c0052282e2800342480146c8500800c100c4c20548100004140340c0d541c0094013440080b40103030140c4940885010a1602d483d0f04900b0800c400042034800c03034907070305400c065407142c02a030030341d0800c181000d800020ba000e0340300403542c03050300180c000340b0600c50b04460518000b640740400d01c00d0104072000c03404110064000d2008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 52916451 1250 52915201 52915211
    0x2d060509010f2f010204080d080105040b0306090a1506120602030403120e070b0306040b06130f0f0312030b0f0a06090303080c0703200319050307110f07050d03051c 72
    0x15540c0c00142c0b60040e86510b0401184890242291051100a14003200104245681c009075501425030545002d000351030221505800400720242c01c140007440f031180b01c0da0038480d181c1c0c510309010584502031000c03e0014a445042a9503441849410144492103255142c0d40040c0322420b01700640603e42c010f100040c0c0d01d043c0307414010201004c0c4805000e440d828100f070084403c40008800c4c3c112541001d2082d265291640010007909000c6032841d4072a01c0451494242540d80c103040049403220414640341d96981c1e581009412038501c03028080421003580b1200e150302a40101c200c10b0001003d200110911200240c3c500000e42c1104000072104a8144105600701c10480e030402200b45907141014582e41c0c0003009011190300d01c1480301a01c907010000d100c000c10039100c103094000e144040c03030200c1c440010300c613400c1164400001465490208040340d80860110b9a4100c000043e05040c1e00705418032081d070750716010880400908001007511000c00f003034030482c3c0480d680b42c0400c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 52917701 1250 52916451 52916467
    0x80720060403050d14091c18080102190c05030301060f050909091605220b060403060501030503090906060703020601050111030d020d1505060c0d0e0d05010e01091e020306012d0605 79
    0x2c05ca42040b03681154802c4c1e100700f40040642d0000d062055a05110300d000002c00d281c6e90100d80e40203898011040007861000042410711064005c1c00042c0703500c1100b002603a03c4c480c0212a03c2101d1000640b440c0c10402c01400610320a81c80c0003004801410180d15000011000c2000400708644051098000c0b403042c0c80c01c070b040842c0d8000200740890b090700c409500303030210140039a041103140031441d5503030a00701540d07101c20040c1c030300940d04040c1c100001c1d03950f8105a41c403580401c8540e8810101c96000070384501c0d203803040e1007a45401d64028209030f802c000c011350354044149408203540c40700780880740c0a80914001454000b4450b00301040d1b00001002c00d00c0015140c0d0010751081b501170252034010701c000500a407104c61035151154400003404040f800f1420f104401034140e50030807460071101001500051903462248403007a00440351050400318248808100a5160b00007000400442800f614810f0320860031030b818851030b450300c22802020344501da018101051000c5a005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 52918951 1250 52917701 52917727
    0x303030507090303120c182304020f180f040f1d15151306030605040c0e0c0412020a050406030c030605010b030f041b080706030621020108072006040305 67
    0x1a0445482c1c18151121801e655019086003d212680780d43d203a0f503088940d444900ca81e41a99440202000e16028152560035000c1640c0c146003802036205c5180c100e0f601300d400c2900c200c60402446210701404c0184c04000b2581d008600c0b1103042d0300c0004001c6210465540740b00311046a80900400907150b000b1a00180c0c60369030080600c0f40c6c1da00140e21802c4c8802e6103482c801d91011840101a00025100c400038400c80c050215a00100c2d00c0e221021003040715a0303002c24061030140d40a10803d45e41d8011083c810300084030100744101c0288401c0080f01e02040c07101b000e16100500607421a0f07216804101141e080e58816aa400600c0d6010401e000c100e20810f4003510040c6040c42c694544800d11455a07070b00038000510055035445013004a02d801c5682d50080c094010503645040d65030007000300a45864080ca18000e070641800d03c4d00704802c083e440f000168103868000c0c40340e9407010161808010028801c2708214201a0080780403002e01401e44154441c0e11000d844a0f1710381c10350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 52920201 1250 52918951 52918961
    0x40f02040f090902030d0c03020703171c06060f0c02040b03030304030903120807090501050901020f07090e011515030504080f07050102070b070804050a060f0b091003111806040504230601030303 85
    0x11240c0b0900d81520300300580c50120315908400402d040c0006068090f10341240341442340e500260175003400701150700d03912250700300030700480000303100d00203000344c29040003000c17100c1c0380c81914045441c07241141d0409004107082d03c0d4050008000280300c0300f18501107400c1d6441101c04900244c80f628050041040b0b400d07407602890014a403040c560303d4884409025003000b8040c0905118000c41c1c200204c1c0e10070003122482498003000da444181d520781d141c00c040c12515100801c075500704000c11030341c0011402246c040321040382d051403030703c584c0c0001500186405041598405000c1204c0890b130b4524800609195205000060341d648d40c0c1e0400a02004028110b44204850941888082400001c071840b54907000f0388009100c1d07a030f00c200440100135400003613801202c02c0b001c00101031601481c40d400ca902070740254071a260040100b0105008c108e0007501c008034400e007c1a154205548038951183c801c0080075407100c0280304049900ca02440e1034425544030b90010f02c10181c5c54050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 52921451 1250 52920201 52920209
    0x20c060115090e010501120e0d0e12010c050d11040b03010303020c010e090106050306040f18030509310b15070b040204060602060705160c1d0a05090a0c05120a02040f02040f 76
    0x11100356803c2411040c060941071040ca0f040161a49921000c0030321a4042002d10000b00125014219012000380c40c600307a00c040240700b003d41c11600ba40d582018028510f200240344e980074542041001207030014000c400c0144c00700d001c103200224007120001d000318041c5019030001e01180781c44000040106445203001401020401c00401c4043e41100a1765000b410485000c903103410004030510003400b0b00070800c610140400c0e092001c2c181c020008040560054a100d0401c078030000b0881d03034900c02000f902006008103011000404040d0f400400880c4ac01012400c0c051010f8084a019402a110030b640c0030360854144021440c10780714203c000d2a03a1b0000d0011403030010401b03403960003126240e011070080c3c14003074010416030760800000303081d254440300484481c84640304200728084440030007003441e05001c60000000041d106c3c00056000140700c4d625810042030019504141c10404064490560364400503075640c064144900340501c40140c84528018101c102c40400d540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 52922701 1250 52921451 52921457
    0x60105030304120b06040b0a090c1b0c0501050a09030c0605031e01030b0c0705100c0e010809070e010302062505030a021908070206030403090305010203040b1608060102060f0606040306020c060115 86
    0x30410f010100c0c2042c400c040d08040042c80b1130b591400031a001c0c0000b109140d41c000c070690400b00c1c1c1c20308164810034000316160b5a4100c020700c01031035190320442841c0f02601103217901c04c040045600c0342c4024030803a210303841c1070320500d0365030390f0765500202240d040b0201040008c01008002c00142103070340711041030b5007120121945552545200d40b400509020b00343c190003d002d400f44201003040c04140d5003948010401e8042d9120020205528202c0050005416202054800200080b03000558400005401300c507440c0d6801c0020b241d11540e1a1b078485c3c4910400f04182e0140808506901070040d0080c4da5640d280c03000082c10318402d9501c17102085d0412b25040081030746402520311696042c0c600076039a03103031800c040e00c0b081170560004001d036000001b0442004103443e038107401208c040e050080704208013441a502444111200c0b40141d1200000811141e80c00f012290000c801a0500c1d03d0103440b5211801640e010304040b4403943e00c02d0300108a8142d031440c0341c0b8843c2c5e1040c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 52923951 1250 52922701 52922707
    0x60102030a0e0907020c060c070e0108070f06120e1902010807020f192d061b05030f04030e060a1d011806031a04050f0601020d0806010c020405040807050f0f0601050303 74
    0x710282c10350040c400301d140219100000509107500030032040040300c20042c0b9080c1c8a40e0700702244e5030b42d07001a006101699460b4000041c8040740000c41e5000c0d120241d110240013820b01301d0440d031000d0445000d080350f5841d200e14400181c800e1107a42c0c80c040c0c6181700300704580154000034001000181c180e42c11540040003044d02d20001140c00090701c00d100d425909035121504041c100342ca00000409460300d0175201410142c00b01030030811203644200c10510429044040d0751154401c5441d03208080355040002641c840e4011002c16442407180c10003e03007410202d8086489904034000d02004036140802c51440500c0d4082c850002903024039002003000c03144924204420110700ca01014140c580b03a900040d81d010f8004100320b1480908101f010b803422040003003902c1800e44019015000d131025507c000303403086000c244500c00c1a1145503c100040d400c1c0700c01408020010303200800b007840313000c0c0041e206000000c07140090000820b00e401c1c0310080790341030800c10303071010f03200398410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 52925201 1250 52923951 52923967
    0x309050c06030615030907030507080601080d030203060f060306120102041203080f28020c1605040b090609010b0a0201060b07030804021c050d080a0905070801021312080922020c010c0806010203 85
    0x280155400804c0102d1400351640c94041040e4600011500014400d00580c0d80224911000080c00c90403140d01000701c8141004001c0150704030300c8241c4985400044480485101d81480c1005540001000d40b24065000032a20b6590881c2c000b50425418075021001303441c14540c2c0040b5060b00b00383e0310b01c541c3c005401c02c0d002d03100606101042140c08540d4800c3e03200203020684e81a14241c90b100310540b0301035036a000c1050136403062801441d01c50361a0151b40030340d41c01d20703e0000348902409062210985d00380300d100308160b04000489c804664a0340e40c00f155240e80d40000e004d00c07038480d40315114542860301c10030160080c5400c9068883d0720701010748002c5200003a149000240d80d0804807015154500b4035009480c5540d0081c1481c0300740d04000402c03203c1580140400d8102c000001a41515584642d40d03130300842da80038140540c203011034411491701c3d00c182c040030344a0340340584030303c3d0780301c1c0081003079070000d02c00240c0c16550340c0b818403e0142c012865075400202440a14504202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 52926451 1250 52925201 52925209
    0x9040b0f09070c0318060e09090105070c060e0709091415041205091f0804051c120f0204030c120519080d1d1b0f0d050304060e040207020a060309050c060306 69
    0xa00c400d04000d0a43c14540505024a42131420b0341103002034602d0321a11010060800e0140c2c0d45e46c0c50007038845400041824034103104150040340c181d0381d168211600c87e01c0301d00150120005145580c0035074035002a507200c05200343c5009a20404002a0a0161205d5542041441041d03038007140c0b86c20040000180203441011042042410000e840701e140e5000f0644044c002c0554000c80910481c0000d001070b00006440d20407482041154075100d0742c0450f1a11041c08152400c021480c80e407020050b4260b00d82200d600300e003110300c00500b03140d502d8031529007403481c50b401411210134140300c100900809100c900031044242210311391600e41d075960f0045500c1001c0b07280002d40d6840c8405440ac0b60010240c01c900c140103012140a281803101e011419050003c5c02d91140711110025222424113a141d0740404c0e40141c0a94101454050f00351900e40300302441a03130059080214100694820301200090401541d00050f422101d1a20300c2c0f90211002d28188070f441c042c0204901642c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 52927701 1250 52926451 52926469
    0x12060e10080d050d0e120a11160605070303051503010203040309080c0a0b040312020a0501050a0f06050f010503160e030d08160305040b0c0d020c190b0106080403091203120e0309040b0f 81
    0x700c000400500503c290703051a08200004411000c101c000003000820b00741d0010f882c40070036030708005503100c4404031107101b1700c112440c1c42b0300004242d043c0580c901090080d4032aa83c01843c810001d150305134044000303401c99004aa0450101d403c401d410300a08a040000c0440500203890400d16103083c103003507107258095444010200c0c1c1c000d48489080b284203000709010281e1041c000d0082e810030941c030034003030150381a220351081d1038404001103601c0c002d252400030301c9041e1602d40c85e588956202c0106c89401c1e020b80d206010402540300ca054508001d50089042540d03120451418510f081a062b5040e085840c0700b0581850b083c031001c50052216a9000265076071840c0ea254003d801c2030000c0e01a040000c407160041201044512950f81b003a020018440c040c1d0785550f80c0c96200644081c0350980300a400550004414021100d0040c8840e6035035009003400c0c0c000c01c454861542c00e840c5d0100c222100d64001046a4095081600415110324402c42c0c56000c1e2010a4000c588108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 52928951 1250 52927701 52927717
    0x405100b0108011202040f0510050f01030203010b03041e0c0f1505070c0e100e041401050702060c04031b030203010e010c11070302060f0a0302130602030405090f0108060402010f12060e10080d05 85
    0x130f11143e90200c210743d142d5104401895442206103c503107465103007001400a03d1084034010107042c904400b5641c8203100f2203050fa1002c410843c2141c64a440d80420624800d0780051050142c4070344002040042c1321020003071414146021a0600f450351485a607444901c1e98000d2010030b00c114000203511100e4881640c1c84031840c4040350b6140010100300b04017642c010200201804140014812100340004150314000000d001f56112021b08130790300c040880f02024030000601c8103000080e1540407141c0c0070310340240d001000c1900d90b00043c0c2166006101c0d03000aa54610030490003540145080040d00d600b9405486610b1441e0081000b520640d0b019500c50400042c4918095000f50b055810b40f0090201e480200740d00d5083c042e641b54080d00801d0700c02d41c403010024000d00d907890b8036641a01c1c2d074130010301010b0326158010b50b03030301000080c2001800082540c110041c401842010300402d00d004080304036007031075501140700b001e04e6000000d180e00602c11844101d0f40201c1150194 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52930201 1250 52928951 52928969
    0x10060801080a061a060c07051c0c090c02120309030909150a0b03060a170607021005040807110d060f1d0a050706050d060321030509010605150c0304120b0405100b010801 74
    0x91441840741040c0001000ca41503441800440c10303032186c510009013a41030311400e486114103038994100f0600d05140c5981e0040208011900c10300c8100c200b1340024a0a1125004030f4955850030640101903403c00c0700c2030205a400864850400e1404803d12500004091221a00c601022020481001c801c3c054603480282c00000300d445a1107443c12a0010502140351000a0312080e800c1a00d841064940740011f104122050500040c24230485005d603500640340d40c0341c4030003956801889032480140d00da005291100da00c000c01c5241c0030345c80c1419401e07000007511420303950744204856000ca40100a59000c1c8541c0030014000042c040c007518640d00b00b55803584481e040990160690703810040100800398402e01c0005040a40202c0002c1d50752028030442d070785c2c5440c0e5400c0b41c1903849944d900410000b003402034044000e0041c18400c1011040ea45015100c0000b154492011041250b000c1030050402040c004288141007040ca84540184600031001c00001e01480041c020081d02c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 52931451 1250 52930201 52930211
    0x117013b1504050307030f0e010e0d051e070614030c0403141002070302010506040f180213060f03050304080d050a0903080a0c140601050a0501050901020a08071a0103060510060801080a06 82
    0x110080000c0307545001c201d6503501040c030782850b01036101d4001034000c0340403c6841905a040038001e03003031001c1140c0c06950b5004600b0181d0300f0400c081191002c1541c00d03008104000e030012803503020501d08100904028051035141c210010040010382c08100e11911302403003408143e4015404450440f6004407070f1001c03c0d1500e40880b424484003041d8000c01520002c1c1c000c08054042d040b8070b2141c3c80880d01041804500008401a10402c0840481c02c0f81002501c00040c0740c1101410001a0100340004d0096203818148814a42036001650540d0000c5020090740108100c1440c41d60300d6444c0081c181b00851201070086255804024500c01000c64405e08c0c10788110386061403150010300d803111041000424903200e80c0b0130f026040c050003102da0045080e50150048800040e0107900400a440140d1100b00780354110b800101c1d240e010305414480740039000100a03010314001c9100003014108200c00300c5086201da4010810302415900402c000701002c600be08045402400104d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 52932701 1250 52931451 52931561
    0xd020105041415070309030b06010c21020f0a05030403021005040e010e07030b06041509061d09040501090204050103030203120105040603030e0616061113091b0f0302090405011701 79
    0x40c0021040389020f6807018082683d030300341540f06c508541202d0242c048080aa1580300c0110307103507005940040c00214041d2455081b580c1aa2038400c0954641c0c8141c810b804644a0320358200382400e1001cde0340c039500101d800d10540c941382e24840e03042c40b45402d01c0f41c030701440c00e030060805600c14424800c0030080e11001514680c044c1e0045176503110001d0069560b103490321640400b054440d00c2d02e500240302c10001040341402005000c00e100b44c40d0104144158103802044200d0400400403180c3e5502c600c3c1c1c2c880180c803140185400303144682c000e0742d2101000150701c038403604143c0c4018420f0703007003080410201c2d0f080034000c00a1002540c820740e480d0310030351000c9450380000c42c0041c61146004044c0da14142138030040c000c50b07103007400c4500c0c03026030396840102034801e000740ca082c1800c3c0281c0111049030040e212030f40c090036141005400d0184010004040350300c03d0b0300808945140524107203402070284208080401c1d03010100d00c04901480c0c0061642d0003004c0508010300d40c100b0804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 52933951 1250 52932701 52932709
    0xc02070308130b0301030602071101020f03041202010908060901050601020607020715030c051605030901020c031b0108130c090906061514030c09150a170c07020103050a0b0d0615050d0201050414 85
    0x4000e0310f8582c1080d950303075a491030700314000d6104003030580d4001c041c214a0301c02d640c80030580c20041c0c0400700c01036003001c0c10880c140071040c9200600301d0500c90140400180c0c00814419140306d240d00900004503860b190001a0401038001d106508642016005010000c2d4a20380070240c800c1074500001c9520140c64103992a11a400d50000c00c1c200c40030381c0d101048000002001c404900780c0c01c1d104405084810305030b540d4040d161900d602d80090891541c1544a20704591f84001a01c410b0354445030640c80e039018201940e002591415120865903003404101c1c00b44038004c0408880c580b0082250050007040070b00b000001031011100040460ba16107402010740d1801200144110240000c00000d900c1c1980440380c6400801c810001d0080b617080701c034007514410520380f01c0b464541100c1e41e0046004000c01005400315566428080c10903403140340c000d00c00b07240b2601001910400d0070600070b50410703840c1e00c444d1141c201d101c44080180da0200585040320b8503042214040e2038040006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 52935201 1250 52933951 52933987
    0xf071e050402070b0402010909020f19170a0b0f0114090f03010f0606090f0e010302030322030f05030901031109031f06030203030f1309020a0c030c110a060201060305060a0c02070308 80
    0x4154898000f25a000c1070090420b03900e40228403d80f15144030903038400c2e0300360507402000081032040000348400f0012048488122024505034a04030ba209950407a1401c2c1401d029910b08208507615902c04150b420a4251608018000d09142000d905104400382d4248641000640500040819100561000d42141400140340d041c188892911803400074925400341c401c01c0200004080001019001c034582ca90580e07401402461400140ea14072110041c4d0241072032803081c011140c0000403408660b0325800c441d200d00091580c3d9050b000c001400d80d05428a081503100e010854580c540e50006210b20391343c41000c10381004107213286c440400520150748040e4250000044203070560700e0170001840030341224411108000d803140100b500324003c0c090b0100101d07043c400d4010100c1d0154800c2c110303040c030508090081c00c00f0400894a1081c15500c8240541e4640c0e50600422070140003055202d418648101707c44180300074003d40d01d00582c40040d1640c9400529000079100071a54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 52936451 1250 52935201 52935209
    0x7080919030209010603021309020c1c090b040e0117060f1801021e090315010602060103020f030a06060e060301060806100509180307030c020f040c0c081c0f0204080706020f071e 78
    0xf10400c0750b94a038000350295004c04405204e094105402080c04d01c3c0310320a54000013000002070030200390044c1d00d00c441d40d902082c1101840003441c0c1c00034520340d0800003000540020800b030400b651401c84040804402582c0000e01600700204000c420034a0317280d03155000c21b0910386411540c01d0340e9140c030b00a03c1400017200c3c5890300e03148800c20400300c800040c07002c0e40c019011144030140010000d501c640d02070140d800160000d0004002600d008010f00032a03c60013000d0b42c0c035105240c0e80705411200c00f0f5002025151002e400c10115207400e220300e20045c101e000c00780c01c003807518000c8898840d906006030391180644001141028456030710030580d084034401102d03038a250394180540504d45241d022403088140b0814202c403400e00d40100300300e440041c0c8441408080f180d0342c404854010b403440f010b500a0030002d601840800780502e0b10602c5400c00c0c01607480e4200b43d0000e082c04480e402c01d00540d884003002030343c1000b00090890840c0d01950441c0c40502a11344448140e0b40c0e11781c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 52937701 1250 52936451 52936459
    0x300b040207081305090705030403050307030504060e10050f10030213090302010e0f0f060c091309081309060e0109060605030f130f03020d0207080d0905010c0f0c0315050606070809190302 82
    0x26501034441c0da080f8101c419180c044a40307140c0b40e44d403010101c80c50711003224020000f95050010640d02030281e0011900184200303804101403841200ba585010444403580400540320390602c8110356010048907040301c500302000c200c041c00c58021907488070500e4800c81900e592440c5203c28580700394400e052107034520050f5031a161411009035540c0600a4600e54940540c802081030032410717108031180d0500c0a814030b90510260400c031001020044e8040d07a80100411035103c01d44e50050300319018100071007000503102c1c1001040e10912505070490160b2070720b41042030060039007003400e5a9005908004000556039074603d4412101d00e80c10b4000c10342010094280201341d004591701403a404075908655482d5560721540769140300101125000c140320800034040380d4801c00ea000c5105000754800a140803450340ca000200c04103a205403501c1810505502c48040307a805036030f030010800c07601d5505140f00e07516509280c0c03058100d1140705101d08101040340c1e05034001c40c0001150010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 52938951 1250 52937701 52937707
    0x150602071a1605060c04032001080106320a0207091a1903060609051509060a0603020c010b0901060c030801090c0504090506130f050901060f0317130b07030201020901300b04020708 79
    0xf6400d171a04d40007130204030b801c541030304800c5103000f800b20109000504141c0d191809c50f40390800c00d07501c0d078410007046012300320494048215114000c2c0100318816801d10810f680e504008002820205203030003142055081c807255206030150000b038040c218000300c035541400340c3d034240d0402c49825140d10080c07119040c207200040ea403060f944110712540a810000464218180030014003210403035400307504c030a56280900c0118401d078058080c000007600001800a01040011400300302640454001045402004101580000d1403801000c0c1e04000340b02451808201030054080c40c001c3c03804542d03480c40026040c0e6100b0b60240f219040c040000c12100c04200701080c050b1508607040002503090040c009846804d1340c8500b411a6080f81140b031840034400d8004200d98403050b12445d28031810f00c004201e4046030002003890900c40d03000140d550a4400026140240b000100c16800640002440360800c00d56110707044000c0c05a00080e100500d0030008009004500000e0400c517004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 52940201 1250 52938951 52938961
    0x1031d0f03090f270903040909080901090b0450030d0e0f0f0f090702060a0b060f0703080c0d060b0408150405071211060a0201150602071a160506 64
    0x100082804442c1a261054181e03600000d00052026040102c1907116007100655800c920b20180a604192100c040e24a007540d6030600c01e0a889141505031907803400010400c0030741d0380151011004000c04200b0314180741c0b0705007101070212403121a86643c2881c0440c4c48508150541c8000c624a003020b240708c00000304490411070920b2044240ca003e8460605200c010600550401000c05001000c0040c00b5030010140301010548190322030304000c001c65400c02a40d2128081c1c0d00ca41210741c001c1ca072616111190005640c0341a541a01424003040b00b0146025000111043c00c4e4050401c021162100d07039030070083e84120350002c03903094078080300801c0003c0940010300071520274000b181c8004804043c0030f2100c0c1002c0d20b005201d5841844100405041910080c52032402081011005c20101e03000c155a07601c030448980050b50341e464009903d0301c0c01203810f070203070086d88010070030142050301c22240c080c6600010019081c000c01d50451102003003002c0b0005a51050030b4400c41c0c01c20b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 52941451 1250 52940201 52940203
    0x310b160c08010b030f12040b090301180b070f0804020607060e070b0301150206010503030906040e09030412080706140f011a1309020403201804050a140f0c040e03030601031d0f 77
    0x4241403144240100048108600340000352202d480d154001900c7c980352901c010040503602101001d50155203c0c64102c0d440d800070700103460907038018041c400d014034114500425074030001c1c5100043c8464075050101503243c0c58240c9418a500c07080000d425038110808a141201a0741700300d0031a000080003042c0300c0c0d035031406495805100d80880321240d03214410035860340103201143e900020207000400580d800520f0007900987c4803803d40c1d1809841d4000c001022a40304002e0303d01a0000401c00d040045511034010406590071210301903082c41002c2107800e0070184640e0708203100d0075107001c0c0d01208450840d4541c600c0280b11286150340d84590601a412500c002c0d039048072591800540c1401d200b0f054071170030400608590000100d9502c0c0900101c0241043d1064172810450034006882d006140e400d2026400082056510500c400b03440d15200c40702c0d4600460a21201c0ca154180000940c0d4105600b400c0c041801c101e00790f40003008404d001802c0096208816051b490094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 52942701 1250 52941451 52941461
    0x10c0501051f0b0f07020d02060403080a18081b01080a2d0c09031a1302040e010f0501080d080103060e03090a06080a0b01050a020a0308071b0305310b160c0801 70
    0x22844000c40600b942c0c3c2c50148840f400b842c508403040850030403d0a005250483d10490200d2004105608054891301ea00600703410403400301d00030030900b258003d442400400e44000404424000706902080da2110000c0302900e01e600c40d06000c0d5000104521410603040400340e495121044040129206202c10b4041c1c14200e600004600d00101d84101034031130b02d40740d8107889d0031404203000ca60100700040224a0000e02011401030134542c90001643d1718014100c20001d298004902d501c001c00c20740d070881e0310690168000c3ea010061400d011600500e603241141c0d00400000f0700e102d9030360f01c442d05610410000a034803070185600130404a400120a5000e10081581002440c40c40401520140320311000900940e204a8022001904c210300903940900d40d454210383c510356494032a8a00f202d0306c84203c0205e040444d003210301c003074030031003202615014180e00b0b0000c0803a1284d4800020181c025140100c8000903d085403451240000012950043c0b600c40c1031580c0e0050503001705 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 52943951 1250 52942701 52942741
    0x110405100305040209070c0b16090909110907080112060e030909090706020d020304060804060b030703080f0a1d0904080309010e100608210414010c051b01170103080a0e010c050105 79
    0x1444200820180380c4a60087d030501903211a42c2c0c00f1713903100c6070241d401200000300b000e8104400800c7c08600c0145c1800380685952007803500b815070030900810002010f8000305144100320f08040104042991511000e036000d801c414000344c498807443d40340b030a52081800090b0402040c8042c80703180b100004041003225459803c0d90310003803002c1c1c0100d840340304521030640002c818501090114040d5030249403203031001012203030b0343d50341d941e100d8802d0b40100181c02c0304030710046501e0030f0305a0440c100810728007134280c40c8803200c81e00c04002411000003030005800d481000c00042c001d103600b5405210300c400303640120303404140c500381080c01030f0440d800f45480038040e04464501c00034061240f84e5500c44200d98a5082600f42101080d09000c12004e0030b040003001100301c00407860510070040c03440c085004441c1700d03400c51400980112066803505080d60b0540f0010008203502c0000d652440303241e131914041042c10f03007004071110019108040c01c154a018240aa001c10950f6100002c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 52945201 1250 52943951 52943959
    0x90906020c1914010b0603150d020d03020102041503020f120c0708040f0303030608010216020114120406060504181119051804020103271502121003030e0405010501050d1104051003050402 82
    0x20300d2800c3d41040c01e80f4000c4000b107401503401d20105020061039000b8101e40c00000d001000000b0310340e000100d40c21940300c000c0d03001d80d500103014001c6606074000307806445030a003410362801081c04604400d91003954034900b280c825440c0440c00e07054601085802c04d0b500405542e48440c0c4a541da072076099014841100403070300d050b030005420b00041c02030725211032400d86200d05100480e001500d0592901510101e400c0d002c000440d0354021400026018502031840094a28100300501c0103c0b60680002c5000440600c0c40d0b00c0001c540000108080d9001ccc2c1d40021a691048492486988141c000ca5401100c44c089c0710b080014900314213109600036a014080c09051030610412105000401c2400e00589043c0002040916805c2c0c1102011070000500d096241c0800e00e000078005e840f14034038902c03509010414943d001103100c425290032036080100d94500340010301188581561812a1621020303840d10000c5c082060310010302c0060600302801c12240002401480112001c902c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 52946451 1250 52945201 52945223
    0x30204020a0516030e3a0c0819110a08031e070f03050304060f06050f04020c0f011d0606030d050901030b12010509010617010b060403021c170d1a0901090906020c19 72
    0x28040709410951955485004404544c1040c1801065540c6c1400c20a48900c0c0203070000044c0b8440c10002d032540c50000040ca0b07013028940d85400072005442512191007800f040c10705220704440441180c062000a48065007000107020440d00c05d401a504003500452401c4c14140a258001c4015031140b0703c2488200302e540b080d104a83c04481e524000e05400400000d65a0380604060f8000d01ca10a440d0044902d569414152942034503500301c400c0280780503140ca00c0c03140120410981d074202c1d0040f405044c01080d1454000c3c0325014580044d030405413104078024094039008912000e22050000a202d02c0c81d240845601803c0103110708040d0400f010340e070b00b50941c0c1c107205070361113070800400b5285003038075503000c216080d05440207080000300320001c01000140c1c0c00521400500c1e00c1c82d54541c0ba0305003000a40d0440e82040741c20709841c5a00e8034a0600b542e134004800341502d02c05c00d40040c80d01283c0c10044000e0061040341151381c41060a241201c4050800c0440070718400d07010200f07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 52947701 1250 52946451 52946479
    0x11030307030504151b03020f07060f141617060d0203060a020c0f070311010305041506060e011202090a0501050d0618050103020307051e24030f19090309030204020a0516030e 76
    0x10880e0030440641000400080034072120600c2074005100300310080d4009270034036246031140c60407100c2020002034600d0ba1070f41d80c0000c0110420070241c0c003860480265480002c0d078540038102c3d00c0c1101c61500c2c411110000510f10380d94201c42c2d1710700a50050304644052401c400960000c1d070080903104190f12034400007110350100001c812058a9202c6000881c1100c0200150080c2c10042d10031103210101810215001046101d0140140207544e1200c1c0680030050025102c010501c880d42007440c0100810ba65644803020104201e5200b841c140c0e5681c14290400e41c02812103030004448507800207041820242e0507044103040e41e0080341600d040d2a81e07041003050042c1d43c1c4885819030301d40c5014200040c500041a25000080311019032810303950304801500a41c0121800440552040144035a007851580d02500781100048100031020b03040d10080d0648070340d444000c5c462500000d080da1014490005d8826149035a40c0000c140a1a860090241e50040544501510882602c95 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 52948951 1250 52947701 52947743
    0x905030a0f0b06030c150406090e040807030e04020d06030f0b0f010806010e071403090604060b03010e1e03070512040305010e0106050609010507110a1d010f03050c01050a11030307030504 82
    0x3a85640e40150040744040040c1d4a00c100080b00814140d818051000c913154651240f100701c04a00348118051565903080c01000707824102181c00800e4403c0081003000002240358040b90106505414500040707400c2c0340004000c0e20804002070f000c2c0381411000010010300d58504030110707108400101c00d40d0740314040c1e032140d00002d1140911503801440100150150107840640089075460000c0102502c2008010561710540d00440198022001c020500c1100e00c80c0c0440e10500728000d0010b90055180b03255258440205456a0741070920500c006c100204120b450701540070041e00e031141c0e105d044014058000d844252525424401c82c52800e020600c0fa0000382c036001800c207814040d0300c2c0011191601f04ca8000c40f2100022101c1c0300300b641c0d401c4030071002041e0a0200001040031a0200048120103901c809012440039806000041000c61390494a0388280307022074803042007200448140c400c1c500c904521f4000081030041e0a58160000f034890780c064a5800683c2690101d15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 52950201 1250 52948951 52948963
    0x10020703050301030b150301091208130209060f0a0e0702060403080a0203040203070e040201051309060503160506030601031e060803030601031a030606090a020d05010902120105063a020a080106090503 88
    0x50024800308011310000303048800e10794215016402d040e003540344000c042401c44d044103006442d9440d604510000a1343d024072030340e0707100844020300b0051900c8c036400700d01c2c0d100c0044d02c05807040800030185040b640f00c42c00344100a02001c0e002d41480c2c10203400194a0303150954095000406010024040000a000300c9025550143c024625a4a486940b40c02e803e000740c800c80c1001000c00c00300c850048604c9456020b040034201c00203802d40390808161408644030074285c2d0759002028208410f5a9060940b03500002c28240400d01000b81e406001c16070615400980b11145415800f03d40c902c40040514480c040a0302c02308080c25505d200c41c4c4440c141c421405506500070000074090f410b21600c0c094202001410140c1098021086401034900903007000b410698042460016680d01c0006680100001d4981d21b00c0c00c0c1d105284d00b4484000a043c80c640300409c080100300110318041004403405607194115202c0d006404001c00c185028483e001c00a180103101283c0c0d49008194 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 52951451 1250 52950201 52950203
    0x20606190504020a031d01060e01050a0608180a05030408070501140f1801020c0d030c0b0f0702071215060e04020a0501020133030c030507080d0804020a03060b1909020408100207 78
    0x84108039854007003000040c0d03000500314400c044e1621100d12200311403142c032502d41a031032000410351509041d21a5040310050380603900c6040c100c4405c0111940094200303400c0700302e444101e010102c00c602e5880c41e200c94500020154407001900050041e804298034003940c10176a903181c86c404c0000d00c0b012090080000c80350a800c4e040012542658002c552030b0552003041c015500c000b803c8200040800115200076804142900190420405454001640110450340380540b6007048000295100c11501580d1a071150905004040c04078080030307050602c10a8000f4881503480d80742051a103002594101d0041c880e0309808940e560043c055198407110325201c0301c90340711882007484610780d0f0141884825041c2d0500110100c0c0b00700034810007a50092008104032440c0000d06441c0c528030807110020040120103000050750786c020075200312a000200464418503041c0020200f800584c6e40a001c0341d82c4020004845a890f000340044810078000c3d115458595203020081e841a408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 52952701 1250 52951451 52951489
    0x151701060e0f1c03030f061d07050f0f0d0b04090203030d150306050a02090a0801110d23010609080d030203150603071202030403050415110d0f180e040201020606 71
    0x100502515108031002100010000d0000c50580c5080c0d002c185810111960841210192000071040c036416000b44141c1d000b401c50304000592030294017050382c07140080f200c000703080703501301082446200f0723030a4070780d000042d130711840e650031030b000501449602c8042c00182032420305c00d039403c027841c20344501031071590094080c5207040000005080200345824083c291000c0c0104040003060b01845158489d0158540c0145e0310109a003c1201c11040c0d0790000f4080e80c10005001b00b05007070380e0256004020b647d40082000084441c1788549184142050300c100019000009030035030f030120700d0706c0403182c044060b5400c00d8181c54049040e07101c219001202402110001c07992810300783c00441d884059450143d4440650440460036680309540035800140040703800d11401c0c2c2d02c9980000d0f186c4a0f07080c00c02509a09103003654980403520b81b40030a02000d070090707030005401a121141c0c03c034414001c1400c42905c0e203914020025003647c00b07038010310a07040040d00f6410700403801c8018441000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 52953951 1250 52952701 52952747
    0x250c08060721020d02030109020301030b0c030702030f0901270e010602010605030a1103010902281d060d021c05010911090402150a1214040521070201030504050304081615 75
    0x148218502c000091a1111650030000c21034849428400b84d4040c1000450143e5a54074505058505007400340100c0f034540030810031f1200f001d800004486413455640102c6403070b0740c1150010707144180b0741c4000d2284d06290350b0710703146004a1040e1b064244c036a042c280c0302441e40c030b03040120b00f211014006c140e0036078032400100300031542d01940b20202100c004c0012a0072126540420303c43c80000d64626142c90760841e41e01e4551503911080800b4220042805120071907000740f0849541001d407001e0302481507030b403002080d916201d94901c0060102d4003820545001ca14003540246000402903d1012100c0c2400c246840c4c140c0c612409560010071000145000d048000c12507404510280203110720843c4951900c0802d00406c44c1c410f904c01e140c1da03014501400c0081c2040605450380740d42510303c68550200100e001c00b40c131091a0207280c0040d040c1d031149841c0d86180f086400641d0944180c90903410000d00c84d54a01d070680d0070700c2500741d5041407920341c00d07920441c02d40c41c1c1c040020644 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 52955201 1250 52953951 52953977
    0x3081b0408070b03060a0f060f020d0f0e01110a02100c0b060a0521010f06120501050703060b030c09060913050117070e0c0f070210182103050f250c080607 68
    0x180c40615004217000f80450f044554406416000c80c0503548104c001c1200441c68510700c903018444000c0055003401e28201e0340c50b04000081080081070300309410321407111000840008200701c1c0310b1560358060321114014100030301c084c02d1080d09220484600442d00300051003401c0c60320208084802c003a01c0c4141c4501c80b5107500100c211380c1c0041041541d42c404d58444504228000c0300010a12032200d26680c400c28200a0309682c1c000313001e1030030315040050030400f0405441c21030341d02085090035030351540b0300040010401d01c03d1204450f404807202400180214035a8000c90481351054242ca181001d0b80e40b03496122516440f4044c08901e40c400042c03502048000100013030400e64816a10303100690340003802c0e40c0701820101000407811a450783c808114090303c0d002405d82c520014080460f1010008a45050080020100140420034400400c0300c00180c070b0800800c2e03080c04450000d0384022404640d0382c00010303178210001e0180099043d40c0441c1c4240242d42a03035800c10040e0030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 52956451 1250 52955201 52955219
    0x504030201290f0d0b07141608070c08010506090c0903010b0303040e0f07020f0a0303050604060b070501060303030b0d210e0d24180b060312072f0102030301031101180303081b040807 80
    0x50244031f00040301040041145120080500d011594426500180c840034a0300b000c403002c601c19003041e40241c1c5400305008199552840301d03070f03210f01c20001940e80c40340004040b9000d0b04041841540605c00030a020a030380e1f50401e00706205803210040c407443c5941c0e414089070380e1403000e441904190850703070003440464441d803c030070380c091001351000c51b1f250794441001d141940040307800c2d5000c0e50f49001c14020180d05009010a0102c103c0f03410340f049509481e000403440b40c000c80026a08451810000b1141c002d06c810031064100a04182a100701070900c400c9188888035141c4002c03042610600c01100107208210342c0c1d109140f101210010255580f503240c54020341099407522690703503420303911490b4600400003d48200001086404c104450300c1200049440e03c071600c0c0a6040c501d0072507640003003664116504403c81e401a4140d00d4010384405106071107000040001030302c00300a240e0008140b40c02100c0d450304a0030340c145010b4031105503014a0180c2c0c8515007000d1410080c1d00a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 52957701 1250 52956451 52956467
    0x40902031e0408030708010806150d11030a05210f030105040e010608010507120509070501140307030608010603030f020607081506071103030406020f070b030412030504030201290f0d0b07 82
    0x1410582100107001401030a04061011070301200c50100001c10000c8090713028441b640140260030061805040440603c40080f2480c842c0900031900d20440d8024805032130400f411417000a401d8400710141803d08948400f0300c921100401c0140803007403c28807004804564003c2c0c61002d03020300f16400c080401c0085c0c0140042e940f40d0307641f110310115043c0320a1140900030801a184d5440c1c1d007a000304000240c03800100341c035400d6002444100b0051340c101035044030300300e0381c034003155a6a603c2c40000c3e4001d000a07005440f19610f801004020150844102c4100c41c00c1602180c40d40d5076412001c866103013040743c1c00c1141c540010546070f050705250005c2c10800c0d10555441e20300b0b40c00e00700400d245800691100005a2284450024601c4144540300160400b0151245140351944800c054081601c20000c20566541d00040915200f9404075440c0d15110b84500d1200c0030301d440740d207181e110041100d0300c02c80310046030503c0c41c03400800c007090041d40560302c3c10441e40c400304180c0f01d0403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 52958951 1250 52957701 52957711
    0xb09030607032310230d0303020918011211060a0903060203090a08070b1b07030929070b0f0a020a02071a071502030103060f050105011b02031c02030702031009030504090203 76
    0x5848110701460380425190054031404802c009803c0c102d15120400521003c40341000e104283c003c08217014070b89401c40b8150003550117003009655490018042095024030110f43c2181004050000c120700d0003d01c10400030ba402540e0881d0702c03480400c02c000c881d00c00d1891040104003000010000955103401669100510348191822840740d500d46075942ea12000c0122504a0540100180303284901c08a031340390300c004c518460401f00a99009004064a030090b44150f14007403681a80b2503800589441c2e0140c5200039403030702c80b1110f01e801001c0d0b0005a1b010048800d403a0b000408148441c801d48900703081039401402c40e14900904921030f4495a02085203d55041208401043d8039000c203040e5440d40010040e901d6265041c810308464054003500803181c1801c3c010401c40c0c0c1e029114010001c0d072000d848400444c07074800280740881400c05c1e002982610360802d124180c01201a10500c2c1c0203505480c10022018035000498001d4030004010810510040c4031200c944c1d405141c8c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 52960201 1250 52958951 52958981
    0x5040b06160507170309030d020607080c030402040b120c0103050f07050703050903030d1509140c0702040b010e040c0e01020f07030b010e0c0f13090b09090601061202040e09160b0903060703 83
    0x154542d0403191304500f0802285249501c0080e000d45103050030886410f8600710b0340702078142c900300b10b03400405048002d00404050000130010405542d2160b204414a840040004450010584140d52600508250580031900d03180c00604948070301020700380300b101e6644d546807a2042c1640c0554443d004020311980603c82404003204c20300c0341d44922140280381e50210650f07a45000114000d1b2100c40d4035505100c0100300901400024403030980d0360740e07a4106c2b8080391030040400122600004007905036403203070400e052540d01c5900f0089000174142e082c1d09966001201001240d0394103480d20009015003600c1c001004202c0701e1400064005034840f00b0710740b4044031810039101c680c0204a07121140314071140104881c800900c9200001c40741540d240c8090315042081d0790311120144289810320000c1d001580c040078042d811038000d0000515014017505029186035a00c4810b0803035142c141601e04001710707405440105031680a00c00034024003840e615038404601a101c816a84449 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 52961451 1250 52960201 52960213
    0x703021c05070e0a020c06010909020105043605070e0108060f09100b030708010509220206030a0204030c0803040518040f11040e030a030c030c030204050d02060304080c030705011505040b061605 85
    0x890b0f0102060754002c4030243c602589030000e1085613410f154041c3c4c4004078852501d5130410050340c200c41070720304a5480034241e0110084c0401c513034082900f0201105141c0d0304e1906801d4201c041c5070f0013980184080e0755100303065081c100055452440c161034050b40a1150103c4101c2890411002f540c0034545c5410a6801e0b50741da41e007081c458006507215030200d00c8030300040c0f0490130706500c01d41d4003c4046c0d03000a00f15940034958100711000342c03000b138024000000081d0311400e05404840056602c40c16004219036100000c50702d83e0041e00500d48a1030364240309000441c61800000c0c012030b0002d104070140d600e40d540c5c1010100e241000d5036046a11043c010544580074400303440341020715140840c052030007d00040488403000d070003005040c0706100901403501c030030095074051039065400316500d8030380c2e0070021014014410400654480010003e081210642081c100915005071100c0000d807100c040100340c449210381250000c1c0140807031001c0d030411020141440c0c2c00b50049c0c0715 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 52962701 1250 52961451 52961459
    0xf0b01050a0f17031b060105010e0105070f12020304080a0623100e06030c090109091b0810020702030c0303070c0608061005030403200f03071406100605070311010624020703021c0507 80
    0x91700c03ca5403d008403036800c540010001941c000141b8005914246840d038982080c0c0c1c1d44003003001c1c0084401400715290804088201c80c000c00031500507080140031203224500924001e40070b058a541c01c0722200380390120249116809141550207a1100c1050403451810210796200194004010690510400d068000681c035041904d6010780341020000ca00140300b42030a600f890b110780780c01c0e8500e0001c18820400800081401c0a2200141c44c000d030b561101400000e14198040c207450f98980030006070001007221455042c4110740298a0308030455075054200245500364030318981c01b00e001000045e00281c03003100c04070103441d01100171002d0180410030742c52a0400c0d81c010300041d58000150b0f541400041c07504400802881e034014a200e1800d1350348004c1c51301c8244a4501404030118100003054003401c41c0510b162072100003002000d5a0380403544480e03110516070702440e8038480654503828804105e541c01ea0360041d08071450f00b11248104484500710300c4003545d081c015418003107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 52963951 1250 52962701 52962727
    0x306020304080403060b0306040809010f14130e0702010903050a0509010315090b040f020306030a0305090607080a030516050a0906110106051309020a05120a150605030a0f0b01050a0f1703 82
    0x50146000b08036107502c840c00c514052044034a1480824070a45c400c804000006400ba800c0f00e407009020b1800c12445940c4200175030341c2d25007015103003400540201e00090b00c009030001c0e020480d0107210303c5050300c0d2100d030400e90807288030320400380028204021980d00240202c2c002d0040b10f00601d40040c08185c4400a0144d44e006500044103842d16280580030f1031406008402101000d00021451800c0401c006136888842860040900c580800c0032411a079031501600d000700c0d001001e6560300c1c1c13841a4020001d00040341d40050388640b8081c1ca0041d9881801500d50060050b26128440c6080c00000c0d50318910b00414030744a076403542e06c04074083e10b480240b0742074070341007488c0810314018500c104040c803145038001c0c900403401c65030349031000c0c00b0010354100324070307080007085400313442c5100707008060210b45e0015505803180070581c038200584c0780d907217151a5015042290306662204c04024880c80c0520604e03e5060704c0c20f1080c00f00541425510540001c02c908a07494020380710291 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 52965201 1250 52963951 52963957
    0x1090909030e0306060a050a050909031207080f0106050403121404080109081305040902030a03080702030702040c0e0922021c02031509060108061e090708060a02130e010803120709030602 82
    0x1200001c81008800d4003c2c1010454950010b0f02220b4901c0340f18140404107840d0031051203164482d0150001042c102002881240c0000740c400c0000b10881c030b40528003402504040d10908080c0c40039100000e561803094003514162030b801490129402000e00c001c5407003401c240c4030f1124000d41013000088908091040d400810312624081e515019005003580c100c80883d40031601980c00c2220003401654081107203071206a042c10001c05946a2201c120301e180548600203402070314007019004495082043c03c600c9040480d024699503640800d000303214102d00e09000845102450144014506480031141042e0002c599500da0081c50300001c6c50f088800c201080f205e6808014046603010a0103000c3c090822000101480d04002614009416601d400304030400c0c01200401c80c0500140b01000040542e18126080c40c280b00e484c4200a520901c0c8540c0c5859a1440015503480000c0e0344030304039003040c4041e500788035080f410f21400141c010320280400511040c08030001d84c1e18030203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 52966451 1250 52965201 52965203
    0x216060207050f03070807060f0c050a0f1101020c010807140c010612020a0e09030a030b041b02010c030c230f16051014150f040b060c010e0c190b030601090909 70
    0xd0540e540b40400740504498900c2109000c1d400c04142405140e4000420314101c90303c915050380d0607000c0f20422070300d113503486c0340c0108140a83ca4000c800c1c4603c250b030580300240241d0409010340810001680d4541c01003072a40d0100d080100001c2c109405112540014584480c04030f142034950f840481c21101d20707403c14075101e24041011015030500c8603200700581000903582c40340f4188140c0d070075500e005000a07102010b0320349100d42020b840e1900b0074039404d01134000c0340d42c1d03002106c000a4043d104c2044c3d00000280b030303c7d850b85101c81c0f003030702c0402d01c80503210701100825050140c903080c6070380003075410030411384d00700514400541803000c22aa0540501d02a10210310442c000c18161100d8112a40513444081c051240c0c4e8001d86405001501c0c088810205403c0c0740f0340840d000e1f2000711030310355104c0c101090201c00c441d410340000d501e0b4003509041e41c144600301d50800c00c10000c0300c8003040b541c45c0400002d01ca400c2c0c1d10401550840014102540496510a154419141c0b5068 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 52967701 1250 52966451 52966453
    0x1020c160807061e11031603180f0b0f0c2523010309030210020d060510080106020307060b010309080a020102070510110706050c04031a04050606062802160602 70
    0x20001400d0900308040384040d040d00c2014242e80da01d0f16800420100d290340328452903903009200940201c0c02556048800c91040041d00c2d100c2060f603030183c4030514840c0781980030502c9020710309599070240c200081603591318000b656200e42000c1182000360410344c4407100142080110300450f000400c00b01651103640d2030340203204034500c181417500903a1584000c52081c035840403109804031042e0b0340c01041d6020300c0c0025030004030f4102249000f00d039003030030545507200003400c0d4990020354000c0416034409881800c20070071400030403a1510002d00c20140180c00500003107000446c15001402000814500440d01c1c1069480c1c1c444150300040c0c0400140c0e50003d100800c011040c800001c50440d407003410410766051000d04142c0f80f14210008214541c1e034800507915400344011780300615044840da400171500c0c8043c0c803290740d405407010381d014401c81001130813a01d842412101c07502c50310a400b144031288010600c8120550114600941c00703140c0581c8a040700c0e00300304000030255a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 52968951 1250 52967701 52967713
    0x3010207200303030f150a030615061404080a0f050a0c0b22180f020c0604030512090a02130902120f0606040606110616090f060206010f060512010b03060f0301020c 72
    0x2074140081c41015101280c000d400610400071141d40c04060554800c01c640c801184906012000078000119500020501440c10035214003030800220110240c403026220941d41c0001800001464000c9224151290380181c4040c800104469462070000c0c0c410f40c104d40760b41445030395030000c3c0001e80e00700d9681014041041b021941601000c040d8a0100104004030343c5c0c209502e20415120306003007107421030340f2095401040710033075046541e07280101082e00d40c14142854000d16560118480e10075076007044021030801c0101090620b042c550003003a500c0f00c1500905100b0150a52070000d82c1e100544842d200d0f129401030102c01ea038140000003405d03640c9069030811089400d90b410040400c5240d04400340d100b000040c03000e40000c502a1054403608440c0000c480400c03a5800820400100b41d100144660b000645117041e52202400412226210901210540104c403a01f404000c1c40710010800e9103800c40c020764000c4c07000707410410b2140c00c400101e400c2e40d00c800c8a04050364481 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 52970201 1250 52968951 52968983
    0x3030a0929010303030b0a030c03080723031c02090d0b06040507030c0e0409060b0307120c1202030a0303050a02040f030b01080c03030909070f0e090103140f010b061806070203010207 80
    0x15100d010305400c150715140c8140700a0905501008050000806040e81c0700d00300f5078181c1e0780018800041d54018041800542c40f0300e410f003002d412243e002c0f07032035808414101d01001128440040c140e03070300c10002c50403d1409415030210054040d00008071540c204540a0b40e51070b60401c50a105011302010207650030494240000c5641c010705a5042514100c0c1102c41d4079804508232080350021100810810300d0360800340001c0a031030040305d03403500c50300600295400c281004c07111550f00507014204019984c08429070303082500f000c002c0d03041c2c0001c001e440029000341d1101e074204031800001400c068030748a104a62860580003070b035100c1641c3e00104051501041101d5059505801a604040201c00415101c0e03801400c0309081c02421141d1720201c0344550341000706484010a010750550b5030303091128941c14020391018150258461050701080140a02850b0880c090315161070525401e80614102d1101d07030450741e00480401070030025aa0900151004901406201c0145040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 52971451 1250 52970201 52970213
    0x20d141201060e1504060e130f020c06100503240415020c030403020f06041a1c050403050307030525030b1309050c011701030c1512060f2c0114011103030a09 69
    0x9081a80402424108000d00c0b841e584007500001e1f207107044c0c0d40d81c01c2c0c021407200c01070b0150004032901c4004910200e4412892000029002d000708108005035a54079117070320a040d107a0700c00900c0c0401400801803000010096007c072203900c14055002d4804140c0840b403e401680c0c000800091591300100e818420351900002c0050441c03011a0340368a481e28000204030324501c41448804481c0c8040740255607040c0304d080082c4046002c00007002680342511740a0a9504240c0e1550006071904002803010350724100391000c468491003e00c081840b800100b01c0180c010407403c0364100030b140c0301d11034a44040b401038038843c03807086020b440460744080004003030400c1c001c098a03d0304509001000401e08036540307001a20301e90112405450b04011003070354801507100c200003600746030100000d0580383e90140c12003035070b020320342c0146094031354036481540300455842c1031540300c1007100410170510a050a031102c0320301030614002a0796998002c03411a0812107500300d81e00d031244505002c0000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 52972701 1250 52971451 52971469
    0x60c020321130303091b0902040f050103020a080a0216050609030304030201050f0c0909062205010305010e0d1e14030c090a051203030f0c090301020c010609150303020d141201060e 79
    0x1d00e0044114035241031803201161041c082c4024007810303a5a90325505010300421000c010714040785200e01c8003951140f00d42c000398403038400c0d940b18414005001c1810b611900031901d1880b07090755000d11035281c0c030103004002e40c031080c95942021141110721000a00902041b8402e603a0b581c05151a0310309828080d003134480040459940744400020041090003400580354120000d446071015541c5050101d8081c400f02d84004c0500060008007407031100a80c3c1009040e05c0c41031000780710f68885810380b07a80c0d030070408c000c050216040e032102c441051085804100803110a1034007881d00016800801586d50054600c8054001c0000300e03030318517081c1030400400900d020f03101d4007040c5c82c1c1c241515441c0d0002a04600d03070a59540c0c00b16855800d2881130312492107005008541c3e6060340103026008103414407492030941c1c1048862290480f5001c010401c49405402400001d014400d007255910010002085400003d003c0740586161110384980648503648a461030a40d0240800680312 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 52973951 1250 52972701 52972747
    0x41103010501030c1701020d180309080606060702150405120703030807090608010603020309010605031b010e040e0601050108040627020910031205180301020f0306090f07020705010507020d060c0203 87
    0x40c0c107180041002803680781804048174000b0100510148074458094007a105c0c1e00c82d0f144100381407542d0305084c101028091032001d446500c03903011680c1d40d14102038417910300329802a070160f0f040c00f8000140c00c00e105240c4d0710412040c43c10f4509a1540c001600d051074125a01c10154041202402019001681c594000c1c54905011700e5551034420001c00c0100c0500508080540100100f12010030941111014280080a039140001407407a030440f032800c03160b05540068030310384c45014a4206440341d003110044131009040790780c0c00d020041d220900058811100c280d038689418080050041d0101c400500c2442d000900d150706004108000300b000c1c08080c2213100c82c4008100044000380d4002241080741000b03600da00d52600d00310b4001c0c1d0364001c1203400d940000352050040784107000540c452101142da414641e2604401e00f40641e40484146000d82e0000d03000b445950f0150b40a091001e100901a49040040b03079100c0c001d48a0b5010030030f01580c0040b0703000c04000280f003513251000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 52975201 1250 52973951 52973953
    0x804080d1121030c0703030e060f0a06170a020d02010219120807030b01080a05060d0501050103080a030c050708030c130306020a020d0e03010b011d1203030f01090c0c02061b030c0f010203041103 85
    0x402d05a1081446612016000c00340340e0ba80024136008060084d0000c0364a4034460044c1d400702d18010b407010441c207008a030606005840c200d004501c9100d4400100c03070b00c001480c020122004640d0a010152964540980c1544960f245080c500b42e00421412032192082c104e5400000c8141d10140580c14003a0507103040c1810265041d1890364010142503224800d180c0100380ba44600001c6a1000d0f1319580142141d404c100010040c0b02c0c0d5080100200790030765404121441c401c000131642030180a000a100101c00c03c0441d44090b61034000d0449400c030300c600d04640c0c1d690b03560b81c0310890b07106050300c5000d80c1055101000d100d0f000a0640b24a103c168001d00c20b403035500c80000c0003694031641c1c06c04620f00021500c030b081c2d140c064003e04480b1600044235030781e0400100e0030302c20203000d1007502081c50070901c02c2a00c1c2c0e4414022607082c158007522050910041e651415070b03a0300068104015480103004001c1611410030014440701c0c111000169a4100350500d0841c001c031801c1142c0c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 52976451 1250 52975201 52975243
    0x9070801060c06050a2c06010803120403050d0209060c010f4502090103050703110102010c0e1201110a120b040e030a11030705060f0117010b01020c010302070804080d11 74
    0x1186401064030310310607602140006661750b443c2e08040003403106c0d28102c00b0040050189a51049030f01c00406600e03480142111010380e83d8040c21981e83c403508a414188491103008180020700600140040c0c0401d24000341c00c011681010851580100d00c2e1520561344442800d000030912b442880b46801240039145c020000309800c64680c00b1100c3c0d04907082e08060154031551028003070000c04020703401132900c541560341e07083c42e65603104c00b80010323100c414240c0c04400b81e0350300501c86c1c005881816180c120001c2004000c10460a079164010380641d520f441120b11030810b2140146103a00c083c3d120800c2206a240b00601100e156a01081c0501d2a08800201c0701d4000015a1021016031070300d00300345204442818118020407200410300d00c00d81040c42480700301e880700300d8142c03007024070400883d40507640d40a00380c840074540b05000d40c000010070300705541319400401c030340350080352100d107419501c15296140064055081c00003425110010400f4002480400859581c0314803180c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 52977701 1250 52976451 52976459
    0x81809090304050d020406050402130602060114030a20040509031e0c03040522180b150a031203090b01090b0111030708121302040504060c0206070306060e0d03020309060a0e09070801 80
    0x541ca200b5400746900c160740c15140c4a04543d1182c00c08005048041c1040d52a002070281308012403030140034000243c01200000f0420f80607e682904200364000d008005103071303003510384840b1207080c07484c02403001c0c8030145a18200d44450056a016026000045035968000410054560385481c04940c8182d81040030182c0402d00001381da00781d4004480f2010445040a458030780c032500f54040c50a103078141000501503014961603100c2c44c5000da210b2481e00d40d1b90700340000342030710700b4022107501c1050710009001140c0080310003201d6411038100001c0d40c21a5846174140030b202640150303071b0786480380c0c90443c495a00c00203040100d0319500096040c90055610b840190103442d11144801f070405002a02207606030084107611500038104221070305041c24030030040c002d00440c4202510071400071031181d41c807a210b103c0c02c64460f6600d45070840101400c010903002110340a070218401800b19081990300e4600416a405058841c00b2070510000d0a021410800600301002d1040c5400104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 52978951 1250 52977701 52977703
    0x80705150403110f1e0a060908060403081807080c10020a0b01121e06020901030501050603070c080d020702041407030609020a27090c050c06060f03030702061b0a08180909 75
    0x3900b62503118150391003000c2008040303600c83c203e104506a008001002201c2c00d421403003402d4000c58401e03039100503203540f1610181c03140c2900e4814420b95500800c000b4011a00c5034068a07001b07103081d50b403503c1c204043d082e45440c0c40c2c02038000301090b03041200090118030700045c00144800b0180081c00c0855902e13191918100014465100321540c90003c0302d080100c01da50500d001a01e5914051241516080c400000d402c0a0b1000b40805d2619001060510300842601d100b182c2035615007058164558400b140e030303080001e030303900031079000e000001c0180c1c0c80c0d001700c01010340b00940036807062034401e40c0101a90241d50000b03400f18030422101c048640c0c440b0701c80c103090f020607130710400c42d00c1c0c510222000201964040d000081c500008298101d40c000001d10301202c103c030458001da2210020000c152030030506281d4141e000308171140c0142410f8016019000303010030010100540c0300c591606145401a0444201900051603113400103e801c58010040d0265900000d6203460348200b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 52980201 1250 52978951 52978957
    0x1203070b07050f040e0906090718020702010e13020306010224010e0702031b16050901120b060a09140a0c031a04150b0c0d080601020d0909050c0408010504030908070515 74
    0x600100040d0001441c1d5074062030445010151881403960340f140d40f910341c480a40e00546084030036000f08808500e252000040d410705641440151100d44d00d00c03059140000d500c4018200e0503c03441c01090b103040d035110169059191a8000090307960300e8110002401d00040780120040200190080d081040c1e40040e00d6041d900c60500741d821907111170030b00342c3c42c60080e4500c0f000c1e42285040201020400442c5241c0360f03c00001e281828035440b0b2040142000090041c02c005c00681c0300200d01003408003100750f40001018100c141495200d54861040c0c4003250108040c1d003540c3c506008003040d21b0310401c0c082400c0341c5802c1080c8960300421001101d131040407107101e107444a20700d81c0b440a000348524010038003042c034256034091101c1c9403912042da000d03d9401044002000644d2940041411030100290343d0fa047e0340075040128000003000081c1c0701c2c0700412420b1001140010003442840c3c0610b0003600c41c03041d4545048142d030302c1e055041e0040d0b401104080514003d00c580c1e0740036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 52981451 1250 52980201 52980203
    0x510080c090a0b03010e0c010905180604090f020a0b12060405060f090429040b0703050115030228050d0c090b0a03230f01060306140f040911091006030b120307 70
    0x1e461525203001e900c010b8160712842c0c50389540381c030102288000c0c000441961002e404e0302c6010580d0340e203000b0003210f0178203e01d4050814118800080051619500c4411414840e40c1a5000d10490390080741400b9000d8120301084da40000341440e1054409184952111040750203121625008021a00c00504105d07100e01815050010038100203070300b4511003400070750705d4407016030a004400d99011403609440a8541ca000100030640c0c0310b200c2c1c001d0300d058800c801c03840c41001250650440080d400401241d240a4000000e0204260300c0c2c2217000c0709044507560030341c881c88204030300e00440303098561103824013603012802c1120f07050420580340c003111141800203100300034031000e1031500390820300c055190441c207040080724040c03c1e9a0034143c51255408015a54868a10500f11081420801c0e442500182686903a203881c0e00b000c551903210311508450841d1300c07c0030848c580006e6072410344003c000c403010700507240d0610030002d002c1011101d4500214149441586a1049040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 52982701 1250 52981451 52981459
    0xb100f120204020a0c06020f09090a0b03060423030a121505150c070302041d0609010b06121503010903020c0f0301050408090d0309080303090a03030b030a0203070603050a0e01060b0408010510080c 86
    0x2c0b0900f60b04c3c05845c1c0d4002c165000303c4255a0f420150220740346550102d50b21a101f100010f010030341418051050b00b01d55100600180640d8943e40c40749940c0300082c038601002c5010000d400c0064410610140c407410f041500c856481c02c800c0340110068038006030540c62031401060081000342d88800025803807000c0c400082c0c1d500c409003020181094003942001c0d4029062180350802000c550340600600c0c0758100589180391580e118003400d0f165078485256001c07006120710301c1c1d0045034070215608010003400217a8040d0081000c282900c400e0042540940c0120003500414102190030340c441c0314040b03000300100c0c646540c614404e030050480d024040c5000c403225004050180710310314050041c2c0d10499440c1d180030f40700207550f0103120700c0450019081c001d01010341e040004810000035802006040b04504000c4100c0003848010b08002d4510b48991009806c0c4a003072241c1c00c007030609000f14540d1207050070001402c2d503401405c01004840ad941003001800b10204054440084c111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 52983951 1250 52982701 52982707
    0x8010519050912030f0406060806040503070206030703020417070302030708030c120a0c0804090504060f020702090a09110a03060f0513050a0f0c180207020102010e190f020a030f0b100f12020402 85
    0xb40103a403404100a40351198080d00209116603c03500c941400c0c401c0384200340602c5503680702d600c1d80d91140b6080d0340c0100194403d024041c01850020080e60b0700c0842071070010701389a5101c9800103440901e002000e0b45400c402c0c400e0040d410140140c1c00601b0031280194600655800c0455580c200b08a402680c50301c0132440104282c070840c04408019008040e0b540ca1384d4aa2408034024030b000d503011a003051070550840c019982500a50303101c543c0040c40e90807940d84115450010b001240800c0301c40c0c070001d0245203400d0b5181ca85040c0030710b0041c0130002e040e0720f000300d1a2049610103840d000d82500d490100c24002100000c0c0e10343d0741a804003528102400d18500f19441c8031080d008650505d9042006407600c043d641e000c0c26a10703000b68000d01483c01c074012000d81343c0020841e401c60107507150f082040451031a020038844288068041c42e903156898880301468a60303000d041f030711070b0756610500803076000382c1600c0000740100c030b4441e6441501e4100700700c0c2a4002d00800a010390707008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 52985201 1250 52983951 52983961
    0x7061101020c151501020105010b0304020603040c03020301060902070317040c0501200607030c03050709050901050d0f1416080606090103171603020709150b03010303080c0f0c060106090801051905 86
    0xa4060380d800b020040c048440050340203450421000080310048007881c096040c400b0035601c140117260407a441001c1062658407a03400384031080d44000c0c03055a48a910070400801a20248076400c0140f00e0350400685403140e525004000903507500880c0290000001070001007100c40031110200c6c0d1090900322011450682c0005402c0d48182d0038480d6805114200001c150b0150046050b80d0165902013009645000003618000e107280101600104460014445404e0219003002e14601501c2030742d01070030135503071081c0303400002d1000c0902d1604501308403d02200c1240e102c01c013611010001d08403d180050116030400c205202c0078003a4079800190000c02e00c002c50464089000d071860011150865080103580c842c0c41c0c1c400c806541d854801680015030a03050714200380e8078040c3c0924a503074078648003114040f101a088050f0050100802c140401d5500000c000c50012103010340465803401328003030200170a6602103d1246d041c04c08100d41050405900c81d06044200400540f40e110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 52986451 1250 52985201 52985203
    0x601031a210a0c082d0601090b0301150f0806060102070b0703050702010c0506043009050607020109180c080112020306131e030503060306011703030406091113050601030b060c070611 80
    0xc140040d21032142210003003120302010420a18011070071281620105004501514405d04040d807100d030364200344010320840d030701508064040c0c90010008541140c809105011100e115070000402d034210385010403030714400340702290303201c07209001800d080351a24400140a105070b0400408006001030200211380c0552282901580c01c075088648a240c98170700360080d1409002c40c602c1a00001e0840e20409583c8218100f01c1c00303d039601c0c094080e10f030500b4002d075a00841422810310021840126500303d6280c41c4981e580060080420a00307403080c00907007441c42c1038021102142203045458050785001032141c1c7c1048801025600380d001904210030100002c155121020b00ea50f440d420515a100d00518040d4004070306a61060740d0300c4000c80c80e14200b85c0c1001c49a03800138800100401c003a42d10008007030b4040c130340383d81d10007010f02d00165402d000b50100d414115501d906111041d68548641c440c2840f090303d03030600d445200345c1120b0b0746010a1081004210b81c1c04034031451210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 52987701 1250 52986451 52986463
    0x51906020304030b0406060f090902030106090e0c0402130b1c0c02010203280609020c01140f0708010608070e03030406050a021506091501030b0d030207060f030203070512070203070c0308030601031a21 88
    0x8071085060508e1078982c46080c018043d04001a4031941c20301c1404210403810b4840d00d07818600403801080401c1d80c1e542807001a400081c0500544441550001124580d9030002c1c00324100058824001c000c080405d10111203207103c00c0c42c110381c030600030407055021043c04100030742d0701c0142449001404401d22000b0f44035580055031154004922081007500c15000025501112010840c1e590b50312807080f80d0301e18040351130000048103039004020f103501a10070b11703802a880d0b24040102d8030290000c07a01e181d01c40d42c0444001480021008407640d410b12080ba4020710461118826051a4001890034030024045038102e801143c080c0215a0103540088945000a03003009022030709810040e40381d508a00c9083c01107410301c00c51322149031191081b00d224a005845940c00c04040704184208080000d014000b580310400c40c4101141001c0348001c001c1d403140c1d003c5030341ca1400300001001d4400d481204240d455041483d82456540c40ca140d6140106c0d5001801e45c0c1d007003280300185001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 52988951 1250 52987701 52987709
    0x10c060b040902031227100309170a0513170a110d0b01090603020405071403011a2b0b01020102090d020d02010309020907091401080108060f042307051906020304030b040606 76
    0xc41042645d030780c1d07280d482026041c0c40c251046002481c020030482000c210320f101d07040c0c0c1d0b40012070f000341780c000d03901940c000080b5901030101500182c480f510903101c40d902c200303000404a1f6010510402d002d8007408410080d1180304192204a80c90303544e05565108000002000c3c0c01100348204404e40720840c540ac02c40341c1200d5582041c0d6036a2003030303500400d080e00042c0d00580c2802c000a204900954a141e000300000940514581c6050402d4461421240c1c01c481204d42c10040315080c07009131101c881145c100768040c014041001d42082c011500078040b81415a4018408078880d1354408595140b05a01516072008003103141c80101d008040444c030096110708074406020090380d000c61240103452202c2400c039614a0980010740703002c0b900744585825548800001040000000e20700703a00b1901c00e2900c6041d021303020640b0404020840c0801809070320880c0100540e1070108131007017045901400740098030381044002900c903c624000030b4441140341c0c001c5010000c595002d00010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 52990201 1250 52988951 52988953
    0x20309030d03020c060705040605041a04030b0901023103060b060c010204060c03080601080c0901050703140a030902090a0e07120c0308030a0b040e010e07051c020a17060c0405010c060b04090203 85
    0x500407014000c0c0003074002e5481003030a4807a11002413038040c0070300216816100a0346900f400d041c034041225900e09444012000001c1d414000080021100807180e4007404010b40056200c55100e08503003200c0c0012108106011000030005051800100800d820350741c000c0c1010030401c0030356011803418400c080040b04150300c000307030000e5160b910042c3c02d195140b10350784000aa03103681d401180c0d601019907032068141010000da6103558002d1000300b9040e80300e03042030b41e00c5920310190920580c11100e40c40012a85580b600411032402905165200c60711040411640c2c0040310034558901a50107210f8940407003274800c006102001c01c0d40b034000c552021a056491038100014409000062030f031500460514144500001042c01800c1c4401e562000401c540c6180604100070342c4144880d5410740308142c054107001d612500345040c0034005181c145000e2054a1003628680007000388140400e03003090200b84242da0303200c1c1801c001c0c2900a01e01040001055000800820040f0402545 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 52991451 1250 52990201 52990213
    0x90103090b0403030c0212090312090d140616050705070314030c01020310050f010e031209040e03131409010e040b06060d0513060e010204030206040506030a0207020d030201050a0b0d0f0b0702030903 87
    0x10154503800c100008082c0340d080d5605030f07031f08034a2020540a6603061951580007001c00e032011501d050081c1001d000010039805000006441d40c00403104025007010960300401c1c100502c00114103c1c10441c600c0d0b41c80e141d49814650303161741d920790f41d060000500b50095401c150101c42810801e40700106600c070002c569908101c515142c90400324800c86001d58081e146d02d4800d50b0040c1302c040985c0b00c002e4050404203075813150b20211380d40700d610f4665105036500411089030b0700c104060f002c0e242000d14030030521420500c00d00718200c0041c0d1030a1281c1401401889904084045031350016444002081d00c1c1c2c840e480011490302401803542c48640c41c050421485614107410003001e940541020400e085117148540d00f03030322540c00040d401c0501000100701ca8103090001f160301c902c1d60040141480065800240c0c40c00420b507003580180c1d100d006100440099200e540034103841101e4000c000c00710382d6182c4800d262000400307400041800c0008440c140240b0442e101941d00a0680d0f01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 52992701 1250 52991451 52991453
    0x171c02010207050c090601080a050711010e0102030109060b0c07090e0c09070215071d090402060d0e030301061704031202180a08070806010905070801150309060c03020306030f01051902090103090b04 87
    0xc000e402101003a075542c4251072442c000d500740b143c00c035401034006940b0560706560300d01c0720b0b5016090140c007060400424580414540c182845401400940c510016980c2c0d40340c070003c01c1c26509a9001711031054001c000d00c0801d090300081c184200e8501c140c020a126865110f00d50500d08822941c0c2c6d0024055400c014171141e0104032500b80300004210a2060381b2940012070f10840706040d1000d542250001051580c80c0090004e68018030003082c0c546451080c24201d0140d800c0d84022103507941c8040018052160070404203042441a12000000c0d4541600d005107240140c1c90640b1a181e4005000b4852105800710440a00d0b8042d0190503015550400c2c03580d81c041c3e078851800c0ca0f0103044008140003003503003c0c3c24040c00c00b83d91844c00e140d082000f50190901080a0700003490765900b2400000b550901500c1c18240003502d0040e100c0c50b00794145410324802030a00d48580e4035100412601c11603185100380302d80790312100162200d00c1000180c0c0141840d100162440901104002c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 52993951 1250 52992701 52992703
    0x12070b0907030c09140a090302030a0e1c06290109060309110d0b06120c0a05010e0d0506010e162c03030405030a0809190b030402040c03020405130e06090d0801171c02 73
    0xb01103680600c00c1214a5944034211411621f0101c0001c006800070080c0c5d005040c414190038801d420f00421032249440c1030706000000c58050501140c030951038906800b42c01d10b8034101045407036a409811541d00400800080c0701000381e0203070700181941c60b205082808010070340b040100310301405041800c505410100840c0504a454620a541036000c2d4442e100001c258110301c0f074409015a011582090019200c070b540e1120741c0754206040e809100d0210301e0820885008042841c80c040241c14121040d24000090500c140306205c0c103011034981d40e00c00517030010303000303002940860450311000300080d0662003140e00095051080f66040404d010268000749032844013100d001c080b10702c00c40314039103144c5075511401c01404070500008016040030b0f0060740c0140c0951800510b0144c65200061039801c808140c0c1119a540700e1600d4110142004450342010070070700107080c1004100c07001441010140108568121000900c0200d202c0c02c000c070000e0850710342c0e400308908070249002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 52995201 1250 52993951 52993961
    0xe06030d02063103021b0a0b030109020c0a050703140c1008150109080307150b04050606040b0304150c08090d140714010b0301090b0f071b020607050c061605010e12070b0907030c09 79
    0x2c1b641d955907031510400390345803035082c02049034030b11928a4111b030300e40180ea40094200f100c00f01142d0207040c11380d03400500d040c081c03000031b54800c20340c144d000c0c09400e80745441c0883d49810140075400d0000e00e2211603401401c070366840f10760541c4284203c440440104d130608181d03405002684808201c1208100030b00300400c1131200c1c1ca00007040481684401c1000303440040d02c9698021200704810b204045000c001140d1240c090a000c1d030019502007400401ca036400c00032400014010070511500d09001e1041c1c1c010b1460a03d010440680e940780c125949100e0104010310320041c00b00080c104000079040301c3c100c004024000c1041c00000d0405420781d503000c40c5c51205802c2c100740001c2165001c0e003503135203400c11450501459400c0a034240300e802d5002da50199101c1c810503002c501d680d40c4080041850345844405401d40017030510b40310b401c0d01c2082d00c60034955081005180c14504110041d00c0710b10b90400320155050311110400ca09089142c2c0010b17146c0610120301049205840d000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 52996451 1250 52995201 52995223
    0x108010c0305090106030b0106051b03040608061009050312070f080f0301030212011e0f1b0e0a0906030b0f190207050c1804020f060a050913060e06030d0206310302 72
    0x82c45142d07a02507186080f1485c074000107000d02c0c641c0f00148159031140014117081c030a003900041c22248005001451500207a00100c0020031300070820016041110450b50300d00038a062a4220908010000c1d84528030b40c0400f030854100810441c06029018145002d0290025242580daa209900c001048d90090009074007580100642e40800d81c414440c8050f0000b1460510610503942427242014101100d0f000801a4881242080d4180c40d44601107007034009459601c50282c85c441482003840b0103900407803480e0715013031041003c5905c880b503030b45d404515800c4503126540c401c181101e00d1034044000e088201d2011903440100031002405040010b41140d0820144c0011040080c0750901250001d402040703a42da510040d060600251440301c0903401c0c0281000405030204032410785440d001120181c440a04102041c100d180003034000c881540601203000070104007a594641c007600f07e4074130007540a10b00c024680e0112000300b201500905085661181d824029170b91036121039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 52997701 1250 52996451 52996457
    0x906040e010503120708040905071101020a08010317130308091c080403061506021b0f1003020304120e360903071406010522090215070c0b0a2a0503030108010c 70
    0xc0f88040401114245c42d081a40980030902d09403c01010324050100500078905020b50220104400c2c1001e001501c3c07507030103541e90520070358034500788602c0c00c0c031044041c2d031450181042541d244c2c05141d0101025281c02c40c00381030307072605180d0201c1c00d00340c2c500d000e01e060b118102c4c42c08810040d4040040003202d004803018000c0c1400040e03000c104545500c201c1002d81d04c207051028074490100ca403000c00240040c10902c50408a0001c902e840e5020310700c55001035800410002003182070352010740d0000b15464802d00d5100e401020400b81244101d50042c40a50b440c1082c0205020321002d81d864003444114000da800d02c091001d640b0380000700d0031a04030f4082d0034210524030300064114102e400c010241c9003802a020030f203842181781800c481e40f189460758014009600c400d440c0b0001c00c0c07110040d65130f803240c1c20305200080d00226000100780c4001008240c9030a5840300c961115030455000c41050b4004010426201c0714500700c00420f2800040300000346101c0c10b501800b42810aa1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 52998951 1250 52997701 52997713
    0x9090304060f0f09053003041d06030d05070510060b0901111203011806050604080c0a0e07080103080306060c01090c0f0e040213020f0d0915060e04020904021002030906040e010503 79
    0x2d801920f0b0000f01c036079648002042080104400d01d0a0401c0c910711020041c09142450080800b890403400c12008162043d0310010303041092a41030b1510100d19048100c10400310705110b0001b0b5100c1410b00300c031000300100421000705012040c030404240050607101044069070b1510122859089014450701003080d40c04608803030500800c0d140482e144409001d4074603801c0172001c208503110b1090914185c3d503290404100c2c2d0310707400c00900140c08071000601c0d586815808100c110190f94100e0480218042c0901100a4100c400d590540e0343c880411500c0784c2d038000c00f244203030042901d92181136081c10a81801d102607000c10800b600c0240316400d9002c1d450342c1e07802115150658009401c10850427803204801844d5000d00100c0e070340d40d030000b458000141d0158055940282003655000300c0301c030443c0c1c030b48041841000e004102440d001a01da250580001d9004000200064060015520803003502c074428002c40d0342284000f00115107072a2901520301d00e80e9070900400f80a44610 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 53000201 1250 52998951 52998977
    0x30605190504020d060213050a0b040e16020d1b06050f040213090512030601110d03020c0c0f030c0114090d1a0c070506070f020c0604030506150a0b040b13050909030406 74
    0x540941c601c03807500941902000303002a81c48070000d5000101c0210350301c2d80301d607000c00e01d41c3d20191050014864036200549550030202d0714412550050403900c8910b02d103c810200301a004200707040c14070046d08140c8490703124008012503146400000524151816081010f030000d200b010394080c5000799503c0c0718008245031544111010788601500b207600c502c400c51101ca05241c0110750201061401641640c100c10740c0c103140c654607924a00c0442d8001c2884115801c00308241240e9610885918801005484c00300fa11141000c0e08a810480d02c409400b118141c500200c131060710014001c0d2600b40c2c00d50909248503240c0081c2c0c2075270300d030044022860343c4404000781c2e0070003900724014240d152202401650462020003a440546c0a140083c100523580d80c0702800c011400307600982414640a407039581c0ba000a0f4941e14450b0381064428010754814109403015a402900c0d055501c0107445082000c4801542c4030503400b482c034800308028a1008070250040380c03140d4455078529142 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 53001451 1250 53000201 53000251
    0x504050f0d0e0906040b04061805060a0e0601051b070b0c010b030d1403190f09020907020d0203040918060207061b09050603040215120f061c050d0302071b030605 71
    0x401040360002c0d88450215001d4942502000d030425402000003800e04417280205095070380b580e10801d081c4400010200c1500e07070b240510303540848101c944103d11801d2480e1100b8151001d00030504019002c1002a440c01403041e030312400b404e4130400c442219030799450031205580560427002095007400c01404450400043c0c1134041038540c0c03282003207039400245e00c1040741c10040a04070003003134041d00c103140c55000348a0010f0740d4541a402045006190050140f4140041e01b0b80e001c6510286014410b10350210076982074270904580802c0365100c0000160241f011150003820903840010204104240381d0301c094496041c5640303200018048600236640708071584655030300b258040000034018644000001541e50030350302040c7c1049118000b695054a04440c1049170400b407a003400142d1520610850f202d400c00108920b0803c2942d4030036031101c08407003010702490340102d940c9003001352101111a4140c260100d901c1c106941c2d090080c0500030980711344005c032400203030000300108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 53002701 1250 53001451 53001463
    0x10e010e070f1d040206090d0c0609090b030a0201080f0a060b0c01020c0105010803041202011206030803180106090e0a060b0a0503030c0105070306150f0c0606050d06020405030606011e050a030f05010602010504050f 94
    0x585900343e10f04907134980d000c1c04115880b50103895404040d500c1ca400004a0b1038014901030503c0d40e0300d02c1545420150b0440c215050902000d02c81d5211242a60060781e015622a9104041d101c115007a130700c0d26003450001d800c168101c0002c07801c0102d004248481e05501034801800c54000903c1a80d03a103000e0a902e82c49a401045030114500281d6400365000e120f15111070105d05500242035a0380c0e48402055800a0300c85003a201840429400c080c1824080d207009401d8084041103011960454142d54500303603c40204090b8072001d40e01402d58903602d41e0002401d018081d00c0d561203810034154020300e805c0f40e154001c00d103000e9012403100c1180107689072484483d00d40c40307082545810280c5403c12002d90444405403905000b151075114506940102032017500c0258595080000f09030922000074100c50402155001c441800020311068690150003401d00642c0c0c0c925412048001d4403041d60f03c001000d0030f280000983e260f0550206115502a0003960205a600405942c40d49 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 53003951 1250 53002701 53002739
    0x40506010212030c042601150f051e040509030d200a1209050304171207170a032301060f08070806060a0309020a0311011205090307080705010e010e070f 67
    0x780c031405500a5620a0000440d044480c130512503040a0f03455101e0803481e0401d882d840e1600541e1103010745240740c24010103440f50340c0025440280c0c4d00b09103c076642260a442414450004081c0345074211400e45501e040d01d074070180c801d00c210b00d05805120303501c0d8001854050740525140c10302051850441c403038000388460414240c40c0903241c0c041124103152010244e000c1d959a29152400100c1c00c0004000511040159010300d1060701040b5003048540400740328605020410440000c055820000b00305a10030881a19003420040890080003062034100c038140320f000422119036102001241241e030181d5034020060406502203800344816a0a01d011600c5076002c035401c0c1c80d126001d01403d41640c0390001d104481c5800140542005500c15604034103003100c408029640714554440c3c503031030ba010920043c200300055542c4ca10403c000913042c56408114201089000c0d000400c1d610041c40090041d10740d046030032500d40070544103020189041c101f00003062162002414010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 53005201 1250 53003951 53003953
    0xb100f1202030309061b0706030c0e0901030c0e22050106052b02121609020d0c050f090103050402061b07140102012d110c0a1506080c0112020408010c05030907050405060102 76
    0x8900031301401925085000001104180d802d101c5c2c006400410000000700010740d03000c02c0c09400d040f00600305081940c160340c066600a00140003051949060300210f403004c0c0041d0420f03035601c41201c22042e641140815050400c3c08046d0244881500500182d034411981600d0416044054000c04200f40320310584501542c141000549010060032407004c0184003a03903503000c010000d0303200e45030950304042162030b408140380300d02603454810304800348528203000e440c1c001c8d100c0042c0e005003d0700d20001c2c10181c8a2002804644524003503031620104c8400303004410b80c1202e00341c0c0d201d03243c501032905252110302c01001507603c140100328a82030f10740c02d4201c030726001a00c213446004e440583ea07100c280d00ca00d200480c40c03174100003d0200b092071001600d640d00705403508070b070300075a0304802c180f00c141441d1b0144696072020500e69900d510900f88000250740300c5402c20068003903039102000c1546070001d5006090307001001944115890b50980b200e641e2590104011580103480c3d407401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 53006451 1250 53005201 53005207
    0x1b02010c06090201030b04110301090b030d0c06020906040b0a0309060f060f09090218130506060405010b04060e0a0509010b1308060f16090e0709030201020628020d02070b100f12020303 81
    0x4552070b81d100084407070062501003803000c0745071702060541d10b0043d00c108031001d0000041165204502c03808032101801c8024200e1070b00c0c0200010302c0c40c0070317548001d8601540003c440d0980d03940d4108a0380101001d0040c60b49800b80090040c0c02060980815903c04d41410707904401b445a03441010282c42519940403800303400c00c1918002030141040803a000300302130150369041144010454454000d5407400807180d25070b45026811b1201c0070b842140242d08081c0144005442241950b042d10300380c0ca0140c0094009100144020059902c0560000c8643d400441c44500703e200a01d090351851402403c1e8035074512885584080407103c201070703c240c000128140c9070106401911783c42da0752510a140b25100c54004010a4056440d40c01003603501104008650f0144981c9500008620100e040d42e465600341e00c103051115424040016030008613604414055811740d282c0e03d0300141e00c1c1c1c03ca07240a00c2095142a41405104050020400005180804c100d01e4548003035001e400303176003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 53007701 1250 53006451 53006453
    0x127062109080a1812080306100219030e0105070f320a02011404081f1803020a1209090609050a06151403040c0b0304030201050403090f050a0e040305040f0609061b02010c 75
    0x3460454024000c004d020741042c0000700040028018052980241505039883c28158100210b6400e0419000f0554206610320248051380d4400c5030603680d05818490103e50411004030b905100b0341000405004043c10101c0501001d100c2000c0d070100b0521100ea8200c003003402c4a50616a14459a240e96100f10b4a200040d48a40c440c08a0700b480d801c0c0f81810281c40e00400c40c10024000c0710f240c00301c83e039100300281518a6001c0c0c038420400303415980003800340c20f450007034807100e200340c0141000c40c4064048803c28880c041e81030090030344482c10002c0d15100c810590140c0001d07900c14110350b040c00000310f460744221000500035030507038850718090745000011400e5500010025510050f46d20400501c0e0704400c801548124420360000440b403619190107012200185c001403103010030f047c0f040c0900d4850100002c1514074a422484050340c9134602100c140c4140d42140000c480b03400c0c0001000c42d0041c01d024162040d07500d84000740690701603a00321010004074041d001404145150b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 53008951 1250 53007701 53007707
    0x71404090f090f0803060a0b0702030c041d160f0b0406080106030c0203070b090610080c0d06020c01020702030d02030a02012a1805100e0910080c0127062109080a 71
    0x2088801c0303040800316801c0000c0d280c0d8140c2202c0d81c00192041c0c140041007104502d040304c5a00080d010340e40590342040d680360080303541c520780741c0001401195507480101a01c2401c5110030b03412240d140444051000041c1d04408c0d001c280d1240746c60182d4191008031382e4105e10000d9509071500f65030bc001c0c803a840d060084000e06a640e101d40194082003089101295002c007802c0c1c4150301c650024440e50a0100180c02e0f0030754154006001500040d16140e6607a480e00e002040c07490b00088056151119488500e00a21500030006c1d0305201e02a00700000030380100282000081c150000c100101180f03820207e03c4805940c1240214000c460303003920180101c0e5008180e0740201200c03d9015195400f0070010300d94241d20300c003c02c2201101490038a8810f1350103070f02100801c031f100a1b0924140040742e44640921443c1c3c14000718030f2071001039002061035050810485036402c102966143d60207041d81448a640300486201000700754180c88032030007100740b42e940c0700b1030707451426140010071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 53010201 1250 53008951 53008961
    0xe0a120c1104050705030702100921050c07080a03140306010c0212010e0d050309010e03070203030301050f130f0b0a060809060714040509011d0907180c0e0d050c040507140409 77
    0x1c903084900050074068544440c403070244070303203403989605540b0708191070301920707204149a41071089030904070f0010014602000034501042d8032003401101c050611015a01c0d4040d60001c010a4801d120000848000000d5405c02e441d0082e1640680c0912203903289010740b00440d0520701040c120710300200141401c6242d819070004020000a140303441c11038540c28604050040350004402005000e0181028400c0c10354560980d03000f540750030b80301e42c003098881c0414400c0f148140e80c00403600069444807510b06250400da184200310900d0310303001e00b20040c45003904807400741c2e42e80080420303000c0c042e101850050131101c0060084e0b980b882000c03100160410040350150100b0b0000103402c0e228111524064590414101d1044040d02207900740c00c0d00c000c00000e690761121030100002d20302a451105400d013a6140030030344004468040c0c4126108242854000900a4292052000104408000440c200c800f44510b8440c80000c4600f8400d40703114105c50340381004208031100701d0b5449 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 53011451 1250 53010201 53010203
    0x20f0904050c0f0d060c020607020c0618090601020114010b03070801050d03080f06040f0612150b010804030e0a05090a0b0a140f1c05032101090501030c0e1003080414040e0a120c 78
    0x144e0030007600c50b81d9207a06540d560515074003da0301820034005001d03018007200b90544410781d0b400b81021104044d00c800744120740300c1c650051031a81c01050050340300b9041b40c2d03104000c1030b001c510a03580d2011011059801115a00001200304001103001e1078541c0225100301e8055580d211262101071109090400282c00a40e101c0c1e42d8611034104240203004135002081005480711540505003081d80c21140f80c079207110505440d00b400c030f000aa0700300f007101d900703e601490322098040e4824040341d0301000603088190700440300b804001c4080403a400146054000343c1d1600205aa60300e0411240130b1017007095030384400040241403241c203112010001c680c0e1410400201d0444603180c0a003941d0100314001803258500070a02120170261780c1403801011100010010317036256850301040341e00b040c0102212259112301240c1207906080c103080c0607540009115a4565031425400703244298003905502550600051075140080801e0a400743c0e5000f201d07032540f080c8900c0f0200e4008602c0c0c50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 53012701 1250 53011451 53011459
    0xa0e040b0307060309150203071704060f0f020301030311060108030904020c0c06031e010f030f02010507110406060e0f1806100c0812040209160f05090604080f01020304020f0904050c0f 81
    0x1210035656a080006600a040b25280021391000500384645a603000480d141700c910b0040042c020002d510040485840d8031441610510b40c64914045001e030414100c0e0702511070501c000030355203190301e600841c1220b2080d205c075010030030003080c0652122400d100d409840d401c10300515190b802c194008000442101065802c020b0141c2d0004556800c1035a150911066555a03900300d140e1003d4964050581202080360040c919500d44c8021b00c51600028104500810848100325030102008183d540c020401c0c001c5079202c5900804006190a00d1480b500200419401e24100843c030041000e04507454030640d5602c00c818401c2002000007008100280c02d101074010031044005000701c80032407000b1014609060040180d070303000c0601140e03c6510003c80c000307589a04445800c902c1c0c0c00c9410642d40701c4103a40e0000c4c1d9180202d03803141e1034074001c02d05a40c5030300300c042d0700942c882c5100f120760b0700340b006203003050143c0d03640c080b90001e1150307000c00f03100b0480349810f05070b802c04400014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 53013951 1250 53012701 53012711
    0xd0b011a04050d06020307030e03120115050c0d0806030106170a080f09031209190608070f02160803040305010e01020702100804080d090b0f061504090509030c06090d020c01050f0a0e04 81
    0x102080d0b600c0c144070f034261400781d808007d001c0340341e030306000d42140307682c0d2a00250b0418010341141c2c3e01108040c07103440c041c039400710005010b06008200b6a40c218007030360709550311400040c00140584404a0300e69100e0b5207000e0300410045650800410b86640c0c0c88020003026040780d58401040e485403480341c1049406001c01019035800300070a04003c1f103002e065544070381c00e01c400c3c00544079200841c946030681c9494180640b6074008456940983d103403506042140c000d000a030f062040030051003d44056541c1c0101c0d0741800000180200c13842500200101e41060100034200d02a218009502a160900390b00f034481c46040032a030043d0282400da071800c0c200114600c1141c140c9802220f00c60b507100200b1183d81c0e03403001c1155106406a4041c507016185043e0f001c0588a1401014035507581c5034003041525204209a07100310400e2011505c40c0d0401c080700a40e504180b512a000500c11542c3c0c054095104005440d072440d170501001d410050034a1068070f40c88905c545031074005980b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 53015201 1250 53013951 53013959
    0x6030106080a350403060b0306060603040803060d0c090905100b0306010302010503071205150f0a050109120507030b070503010503210d020307020a0609060501090c05090312160c090506010e0d0b011a04 88
    0x1030b4486480b81440c203080f5074030341c81c40c941b00090f01d8030000d40030b1003500000300300075550700c2d141b0481341d00561105402e640c0703641d50000514804c1d04004041d000e5400804046090382507075002800c414010000c40b490001105c25890981e00c1c1b420b842c9800d60480001000154025000346400c50881e00744290b000e0076440305042164000c81f00c070181c00b401400301c03c015052015049460714001c0e2990b80245040100280c02d09000c0c0c4078048441c04440110824000b0501c00c01000e0740c0e0140c50805a4200307198010300c00c0e0405e0060394460f000f555581000c403410040c039650309032800860542842200183d1000075000102200e0550003820000b00001d50588503644100d40f0030040040c15505028455040303500e00c1e402401404800c20032195240d03400503000d904503600000301a40c0d1000d81903803070740b078070501c610003012604207100100b503011300c94004610445003030340c0740805c141030201040400030b69204040d0815010200512401c2c0e1464405060000c0c80190549080e40d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 53016451 1250 53015201 53015273
    0x303080c07060e07030c0803090907050a1407060e0609060915042a0905070309030e1002150a0e060c0304120c021f08010806060301060b04090b04060b0a0201050f06030106080a 77
    0x480ca100c1c0880c0d001064207201700b01b0a02e21540207000d085008505102c603400206070f80e0800906001d040c4032020070000c0d00c191280900591000360303140000c0e2514803e1030028090f00c00c801c04a42203004000c001103d1300c1000032194415041d0750000c0402e81501080075192800280c01070750030504032604100d54481402d2610700f41015010a80c407001d2620a81204855001d08031500705403c04120001003a40400c404604080c100c40a0105a070826816450030580e0712000c020f107031181c810000c3d00412a440003181d05424800e5501c0c50b690740741e030a540d40c0320842c1c00400c84420080c405c0c910521600908a038a84054010415070b504400e2000c910001080d040340007680080040c800140c040c804c42e80c106005800a100d0310b410a4006880c0b80260b02800e60b030203039110610ba040e0750b00c60300541c0040220b4028180d81b070a030018001d0203040d0807203010f0301d480051700c0030a283c0d060520030700048036103403005041c1d40200c5659804011b41343c0c1501c569140d10840005103800a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 53017701 1250 53016451 53016461
    0x1104050903180907020c091008060c07060c0302090a0e040c03020303030c04170f0616020313030f1217070f0e030f070806010806070f0e0d05060702011e020403020a0303080c0706 78
    0xc2844010750325021405520b00b180000c1d107140758003842240c024040103a80028104d846c0500c1115014030341d50319003080300c181041980c000c82042c41404180841c0c03404050060a503103000e40c0003400301100c2420150240e2080c5281d840d004145800f00308005101c4903141c64020b0b02c1100030020050b503e40019107940c10039a1074405003000007500304050900d0b00b0300c50514504c08000f40298040350f4000645640b4001d00540e0000036001c502c4140e54424001c8549518000c1450304500b40c69040c52400c45040e200c0440d50310203498040c45085028040c0003074442000d0950350115950349400300c881c0d4030000d4590060155a444280e800c4d0340500002800700c0c684c1c0001e0040e14940541c083c90504180d1001690303400001c240010181e21140e01c1075480018140321007142d45910220301e02d056840030290103402a4030130301884941c10741100f400d81c8031415240900344460903542c0c040f0700ca6031000a60000000308200300183c040c05050307510150030003000c2e0425400341c80b180c060b41e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 53018951 1250 53017701 53017711
    0x72d0809030c0306010b0f130315060312030e0c01030f0609020403050c0a1d06040b061c141f0306050a110706020706050a0608150408130b030108010f09080a0c110405 73
    0x500081410320150074100501416040210024201c5500d4114180b00d40c0c40780880e102c032010800501c40301e84443d142251300046d5404981c0c280c8208200f0b103207500500c6e16000480d99079100244605255109008003c0710010130006007203140144801900240181e09420070840c1c0c807260000303840c000a1002d00019230080d4080c10310040603d08201c21004035070402c03800000b401000c0c180b0b110022205582c0140e040e01c1c00100141e0ac800040c01a0080580850b1900b0154407044142242d41d0090031000301c613481192801d0321100900d0501075a1420300f4514001546810800710300c41d9000650030120094000400303010050303003c1d1143c4d010722010303501030f83c000030028208192403081d140d00c001c80c4a82003104a080c201220b85400d044555203000307062101c042070500000a00f26201044890b4900c20855039643c903258445c2c00c2407094404552800c050003031480344a00581c40e04035030008443c2c0c6860342404054400010884007900c52030940d038000800c81d240c52041b40e002d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 53020201 1250 53018951 53018963
    0x31b121b030b100203070b010e04020109030212030703080601020609030703052203050604170f030c0919060c0c050d03020c061c0203190b0307081903170705070c0806010b072d 77
    0x882d0100900a0000c2e02c1240401158001c02100c404110740d40041e50540784102c2e07040d06240ca8500049950f8074075900f02942c0074482d0030043c040b5190000c000d00ca1a031080d25070100340e0740d40700016038844404544000a0360420401c1c0c03400603102e000104103240f108032001c0c503a1010304e0802010728103107810440d0558091010b21003840f00d94420070111410030031b40a407411042004080d810f0001400c54403442d14082040721081c0c1e2074021011501604a4044a409039940c400410012040030b040c0c8821040100c0440d290400e0b0440480c002c0e0990000c101454820b41070001d41d9010f0000c0d508032010300e10f910020440c04e80020340c026411300520329840c41e81841108210381d100c403441131095002c10b50401c02c00d007000c21001c12a085c82c41c24200102e54a0038141e0700041988582c0c0c0315841070a00704408107412002600825020b10b0a14120390340310428290744103c02e020345903081c04144800c100140d8001c1c046240420004018a04e0521448051007076404644089885c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 53021451 1250 53020201 53020211
    0x160f0503040b0a08130f120c061a0406090902031b0d062414010806010302030703020d05040f0b090f12030a02071b090b06070209040f060902030d020a0c0501031b121b03 74
    0x80c0d070750084d075560700146407180c05e01440c20140e03901c0b140104103030b400030140e03410501800c50140c010340c102c10740c4507000b80d020300615800542299421780488035141c4910b00d040c0c008180700300c462007034004c45903000d0010070055847c40341c2c20750140c900c02041584103000482050000c1c0b100d0140078000710207101c40030400c051440c03450340e070720305035402404456038451400c1e8156179000d031065401070800c0c00d00583d20380f10840d048010303102d02d0301c1036036181e402c001c241710800c1070f0302010f02c502601038402c802c0181c0710b00c40b80030707101c040c0801e840d10a584028007040342107070a1001540c201c45007200042c03510b02139503104460b08004a2580520101c00076040002e51424040c50500803000c0312100c0ca051903030780c0021310740e020260001c0c3c1114801c2480c1010880d0b03d52155000c01d070000d0868035242c0c04141c00a5032040d045004940302c9000120000f11540640181c0081c41c0e0780c01114901082c3d2600e08032103100d0031031180000b46490740301c800305000a9103120088141c03030b07640c0030074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 53022701 1250 53021451 53021467
    0x19060204080712030507060b0301020f04180c05030c070b060105090a0e18030301080709020319090c03110a0b030f0907091d0f06070203040b0705100f0501081011160f0503040b 77
    0x10030b080c03540c0e0040e12604007076000e540c0041e902404943c0c2481c1d000d580015203005050200c0d009001d52000c40a01c00d100040114020542c100320b00c015400c00e03203081c007403400b07500801c030340c0e9000545030003400700005e21a080004c0d48042c4440d60114041c50218100303100c04002450b00e03100d035800002501c000c02e041c002c14135050500c83c1064004c1100440ca5549405c00441c0e844038540700d400715880e0b0200218100700842c01c460008100d0708030f81800000c050b030130001c107030400500c01281d2110318803a0ba9582c13414003881c41002c90752032481482c1155914180d0203004070000304841c0326030203004c0c800308010303150344207903d0704040140480d4800b04803403940a1502c40d80387c09041881c0d02c0501044411680042204c00391001402c89944941003858042d141c24090000941d0707030350a00503504914822035100d207040383d040b00e00310f907500201c0540040444a4202514001000421001040c50706051060401d141f03d089401c91884d8a034880c4e41c1190040e0700600f140080c0052008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 53023951 1250 53022701 53022703
    0x70b1014010206060108060103090302030d020a080906070314270f0c041d0a12110303070f120b0102060103021e04020d020d0e1219141801030608150609091906020408 73
    0x40e4094420300050507030b42441000a04036050080130320341003503240d91020301054400e00a0380d507018840b0009540741d0617400c60241c001c01c004c07107a138440c0f88200c1001550042c824000c98400525076885007042c1e48030249240800c045280301e2260b07035070000d0742e01035407240c04001040000030a1380240c400074595204200603a0402c1d144a0491840c0d4200c100c002003020407180c0781d003a404000c0d1078081c49403d0b82a1800320b816281c6000300d002c0442088043e039008400c0400341012659221890619841c800040f64804000c00340140d00003001400182001c0740c01e8a440181c034100c402603004403000040070baa010410725414260007003500a2401340c5030092141c1c01000c10041c0c14405455102d0014a010720320140d200404840c8040c848503004000e00c07401c101d17090040036541c180b0f030160100c2132102100c0e402c4c0080d1819100061401000c2090110000c0c07c841c0c00010b074548004225000e040a0244025030140700c4440c8010035050b40100c0b5850b07c209000368070b40e46018501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 53025201 1250 53023951 53023979
    0x30c06050702090c090316030b100608010608270a0501230603150402130501080d1701270e060403080a0605060708094e01020c030406050c03070b10 65
    0x84018804248403140050341c5451182d6030000340d81400d682c0f0307000c0d02d10000b0718180c1146480c030310400c000c1c0008803d010321445860b100e070454240903c8150350b20a003c9440d05400d20842000034040400700300d44031011880310413602010104952000d215803201070810488800858003603565070203c0a0101c604c1000011044042000390418507001740802d03150b82c0900d001c1c18000c0000c000007800c5550f014100c0c01c1040b0000c00400540d0b84480c81c4036503c01c286544040810206003044c806e450120914606031040c0d40c0254403055036030401940110101810108015100c81e845401080e0410080c1c0c03040d8000d54450a5a04055002c442154555000b20f400303403104001d1200070421a004031601c14905444484d450f4200c403d0004000f500c401107140c503c00360440038150480085d403c0b516002081c000c0c0044c40c003010850300d080f84544000810660002d100070044180208042d00c000305540707090b03900d842c0842d55524038481d01101c0581c0c0e14106920103000c0b8403404294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 53026451 1250 53025201 53025209
    0x213020a0908071d010e180102040611010b04050610050703020703060f0c0f0219140309030d03050a0b0409050606040e030d050403030c03051e04080a05040306020f041d01030c0e2e030c 81
    0x300034440c102013150f181c0d80e940c14000c1d044e0400c1c05030702081c44100b0046440c100303081d28000854803141c940e100200001e245982c4c1c000b0642c00c0061455013031416200715401050024400001c0030701d526429103982d000030000785c0a60091032000030102d199409403186841047e030000a2185201c40090025880421002c045510055407007007101c819080c600111508441c441003210310345c001462541c415030210a401d4004c41c040c0002594058200c14080c6405100a00a03010040144411170303510b40d0340904030760b1050700840e40c1801c03c0d034010306800e501e680c00da80c58400300c3c101c120184c44003510110000303591454015441680351049580140010740188000719810400c00068580504040c0c181c3d80e0029414814034020411640203603400324082d1b40350001003099005c81c0c3c100c1d21076105e90300b140365a81da0500d40210700c1d090690340d00848221041d400c00100c440041c01c018007001d4801c50341a41c10002c0401d40c0907011002c10700c144000c3d02507045150075480d803070300c90b88 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 53027701 1250 53026451 53026469
    0x180b0f0717060d02060702060c010518010b06091002011d070306050a0605030a03030b0102010e0706030204080c0603060303071104061d0a0b06030c040909020f091f0e0402010504050108040213020a090807 89
    0x289103031101c014800c1194000104a48819240a907800000d88502c20707950002c0d03003c000083c1181034040d040d080f07688030b03503100c0c84030109800c00b8101c074600b40c9003082110390b0300c80e00410420380c881c0b0380700b1714140c00e818883c4000910320086003044048030810060805242c7e0006404004008140c0195a842002c83d80284803552400c80485e40c0e910385200010f09240e144c0c008044a640300358031a40d4490352031810ae401555686001400035405801749010f54014966030103014140403040300c1c05080c002d0000c5140c9409a211103c00307403500d40003d50700a0316503500042c7c803400c0d02c1607054504140c0d42e05040504184850034202d51149141d28083d260501c2004100c4040f0703000e4404440c480d0001048000d0300348002040c46e24105519588109170205105411420071130004001c1c148024800c01103440c1c5081c2d04d90714500711002400a4010401031042d54412840313a03030401d2010788407020000c1da010703492060b41c104038101d00000d1865102000f00c10003c0281e82c0007052050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 53028951 1250 53027701 53027717
    0x3050109051e24040203100524060301030f0201051e2a06060307060c050c040501080c12070b0f1602031506010e01080606040e09210702010305010e06030d0305070201180b0f07 77
    0x5815950f01000c000d20012036034500c480002c0a5460a0205104004106504029602e8a06801600e1011110440e080c0086403903454500d810b2841c102c03410789811000c01090010706500468555000013904c8000313500105201000c03010781c402a00c4441094920b104601603102c1c0010440d41000e102d40c0c4a42e03200101303018441d02c2c04130718181a01c07aa4134000710140424286503203403800e040780320350b0042c2c03030800001144400812000c03000281240c21070f5040c40c01000c40d0342c1d1a0154001c01120800c100180f0441c1000303040140300582c0c3c0c4221502d0601c806400180c20f054450100020842e40703602000043c0da0f00413244405039400b4240746a03182806000300340d95000c0c80c007a1001c0025114003140980e103040203c88a04941c0d600082004500d18007201855009101d080740071a04150001c030b00f010000707003d02d216090140060100f0781700701c0000c80180001400450a555071789034409a01080c610080d290107008000d182814101080803c00d170400040c01c1008001d182 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 53030201 1250 53028951 53028973
    0xa080105011e0906030b0a0f0e040b0f24010c02030607080f06040204061d010207080a0302070305010c0302030702031206061308010608060703020304030503011a0d020711030d031a060d0603050109051e 88
    0x203d074044054600d02e02d00010703014143d901003580e0790707916008800c49540210001030070410a88000b80b080344100b15003452503c0d15a500d101131441500c540b0400d210741d80c500480030307d070040f081202100502d40700c00e03445000d401107030a0000c185d41e504001208903041100c294260010190484800c1d0303411491f2a1404030020468502e85094004621015240384801da1003000420060712051040d150400d4081c40c006c2c2d9107261500c021a50b950900401c45d9140e8042d00c00e591041400c0e80245107407214806030030642c8070b00104a00d0b844042030009610002c03074420030001a04440d400001d0700750612841c81d01d024401131085081500410030000003a51040c00e5a04443c2c0400705080c0d0700760300403004245405074140484019101003920414030105c5000f89500c1d00c0c007070b001d45003000c034155021415210503862802c90300c2c085100141c040e05000d40240f00c2c0440c40e290014480352295105402d407401b00c02e054810394409481002c1c5035080b1030078181d10b204410001c000210305 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 53031451 1250 53030201 53030207
    0x6030114010b0d0e3a090513200d02070b010b1615090602070609030e010809030a0e040f09030207050a0f0503060c071b1e06111b060f0a080105011e 65
    0x1980b00c82c01c3d50f2902c6082e1aa60031008204c1c414101010600304209050300c80b00360f503450000607480003400403014101d00b034444d003c2c546450907104041c1c1003c0c10044c0802840c070107000c00c0c11000c010000b501005401180d2410b02500000b60544000750317071605142000c1580360010723007103a4403088040282d014410000e950030125680d01400c0e40341044412048040106107803100504054000104481081040d42c04a210144aa110300c0c200004e488011224007030125406c0000350301c10424150918081d01c55846100c0d0000d1000c0740d41c400b03240c2e8050950f180f0f5030048000da0701800087c001c601d45005940301602940c041318002a10b0040040c2d80d4074006486820300c048001603090034000c074880b000395500d18140104104c25640c15040d4661501035030383c0c000c40f843c85400440e440d881018409281d060303410084c040c070700c852010803801d031011303041a07076000f10708011480c9240045405054140503540b00d5032403661405c0c00140c1510500b200c902003140e084d009030b03803001d13070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 53032701 1250 53031451 53031457
    0x20606031213031e050313210506040b090f030d050109060509040305072d05070503060106020c0607120e090a0c03060906050303030a09020411040e180106031e05010f020301080606030114010b 84
    0x340100c0d5040d0320144c02c00a5504108184d440070304140000a0301c0801d140c040c482c00030460f4114612290031100480e950441d039803103028003e24a41208012401081d0750310011504040d054040c2c540829625400c14a140c1c00007564051745030b21240100810382030361050500070907003603440e02054030301581c0052080c4280400103012509440c1c0e1105101580c24008030b80c0c0c26907043e180707000e00705420901d59500071446210f110f4400c507800410cc1910101d9000312440e0301900060801d800ea664801d4070b900c54008a104014494002002540d41c5041e00b5000b00703001c0c14006045210b9007001400c0e100b01b0741040108600f48002041140c40010860f58086165100003503000560b20002c1c000e04521030034803042c42d030045404101d00e0401043ca5004034400c1d105c03800f503000c09040762420703a40c880c03101504030f4071044009481c1030380313650480e111180300700000540381d242041d540040382c000b80c0052a051380520100681410240b00786c58844132410071408007585000a0030780c03984 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 53033951 1250 53032701 53032703
    0x120601060f0e151206061303060f0f150905090636010f0c0207140603040803040809041b020c04110a0c02060403020a06020303040201120207020a0e0618040302060603121303 76
    0x20078541d81d080d22a100341c202c1e400382d500040c00709480e0300c0c0c00820500e05070451401407192007820b9010450f1032404400301e4109882c092401040f852960700d60700c1c01002001c032009585a181c105074440ca000d988030740c14103070450b0380801c00d08901384803101040740c9000381501c40652204041c001b0408030107074251941481c4010002d0034000c0041030840d00590555008095800c25420341c2c0701d40803e030400c00c2140d80e190f00f03d4050135030710409244001c481040d1281c200200300049001314452070300840d03010340101041c03854010400045001c5811a644400c0058101400104280c0d418484000c640c40126010b0044100c10107000113076204444426041c80361605042045440b2202030342d0040d03800401104485545d014080d460780c1c000c031400c90001c2d4494102c0701e07022025200b41c413813103500542600801802e103035444400340f502030700c607035444002081422003000c0b1101400d03200e0f0b0300c00da0180c0503070705013141410710341b0076100c500b03d0800707c00b84060140c03000406003d07c112 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 53035201 1250 53033951 53033957
    0x20403030c15020c060c0a260114030a0807030309020102031308060105010e0f0109090e0a1410050705070c090906021902070302010219020f0f010309080a09080d03140703050a0b030d0c0b0612060106 87
    0x42c528aa41503580d203950309023150002c954041140003400e00c0b4031042d8121510840d00d814400b070240c04142d15510196401041030f03a052010202091090b4044090248180110391802c481e2882089144086a00100d460350100c0014000c2d035900c4200d0002040381510141c481440000c006072010035140501c40c0342c02c0e035840703004284000800c1009403003500659003503540580018255114042c40100551860400380402d440c14403440c00c0b50a21504030203000c101e07500f801707000f20103400004026105907400303000c10080c1130803500c1440352102c0d8980081012518510000e400c06240b403a0002c8107101c40680300c000361319140c0450440c100c040761903606015500300140c00610210303e0181403080049422280160400610003c1d1a81070b07003141d51502c403400044060b5441c1c0d40051035144c06030070204100a020f90490f03a00302900e58000320b000c2c980d13078000c2860a141100c1003400241c2688203907090100282800350805800d560707840c04698406505a503a05061188a0070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 53036451 1250 53035201 53035207
    0x209130204110703020a20130e030f0c0303040209010603051306020f07060507020601081504030e010806150a090e01090606091809050601030f060c080603120f0c01020403030c15020c060c 82
    0x31507440303910200d5140740e5038541c00d4030350311581030003541c0b40d03091103040300c0e040c2c1c03050f00c80341a031014001c14482176500102840d02010500328080040c0c00340d01d082035010300c414802015031048980c080c07d20101038000854481c6080d00400003a208180e026509052400c800d00c0641c0c2048082c00503159002900940d0792407050320030200501c14100050300c0381c0c1c640002d10200d2a400f103070242c100c0300c84004480903041d503480400034880c81610300401050304029801915400782002d40d6000078010149500100072842c6112103134040204040020000030f800d00c01f94858041840c0980f010040400c0510b0502002500c2519a0302404c010f8040d1501c21a4400283c0d411128040b40c0c000169000c550b52032400f04000b0300794103000c84403a070810710300c0c00035603207ea071010344600c00040051081181320003907001142e100000000410204010842460809000600085100ea80d41140205850405000c1c8104d000c01e5280460300402c0f10a0700c4220009a00e40c1101c104004255 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 53037701 1250 53036451 53036453
    0x70302070e01080a0b01171513020405010906060207060302070203030708030c0c0106030809150a0914031018031e0f0e040b100e030609010e030d020309190606091107020913 76
    0x300e400441d40c001c1c1ea08480741400401d903000041803c0990912548005c001030362a00201d40202d0303010602c540780740d405140c2e40030242c01e0340d424468200c01c2640c5101d080c001180c0101d000d8510036000201040d0320383e00100849035040110000a0402d441d04500342941503000a40328824404064400345c00400421203034003060302114619502c1e035000b000044e03940d191050181c1c02a1202c0392127030b0b01243c6104c0c1008540001c840107040b482d0781d004403c90808072052240811050b507a50544560103100048008900c030385d0140f4403842106560555040c503004010030500c4001e0410810318144072014039070060180701c02d1001034100355141c06903032008140204107251480ba4840303e01c2c0b895941d00b41c0c10400c905c50012040d070130742340140d8404150324283c030181190910307540e001b08804415101345501458207c03d0090564164400400c5031005c410300044d0180c41d40c1d0741d56101000750303004500c03a4003001105c443c0080e0506840d500010750141c0000c11400142c804104024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 53038951 1250 53037701 53037703
    0x6071104020415020606010f0305060306070305090c0d0b0402150f12040206130315050108070b0f07050102070c0b030108070f0f05010f020f030a03200c2505030a1406060a060212070302 81
    0x10050140348140c00264240540c1c020750304d81041d22060f0110300500e25141062740710340207181c072034040540140a03903101c40c001100104401000030601740150303103940d40d407603503145855855240200132007a01800d02e40108581e5100c00203403021280f4040007100041c05e003d4054500650005a03030b141c0d16a21800419018420004188030007401c84c1c0002c02001a00481200c940c050280304000c50b03030300c41d0401a5200302d603000b40e880b4400144051013024401038004d1011601c207130009404e090641d59a0041c0141c1ca41107500c8100f008001888104400c11030700d07004044c0c1500351400c1c14039203040a407081c6020b01138181000b20160044a038140200102103c001d030320011240d0382d10018000030010804112055400340f07183d07401d410701e0041d0702c05880c1007102000140c803101e0120541d00a280341241c032542c226000700b200c002a103039401c0c08480086070040350b0b02c0c2d01103683d483c0c1c5541004d00c02400c981c800c0b502e108082c0041c65002900d5107032031705000141540c92085040903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 53040201 1250 53038951 53038957
    0x2010809070f09020307030c17130f0209070309140a030c02010e0d150b0102190818310c0f0c1211060405010b1002060103080304080703090e040501050f01140607110402 74
    0x10b4103403010040e2001400031126030040d8803c216a0f42c0070842502e17144011a68010300c588034605140c0304034003180e8041002080c4100941c0710341d10b0b000307103407505501140105c00102c83c80740c080b1355100049024842c0c20f4002c511002510005803103108201c2da0094003040e5038680180c1041130004289100c4d490340f5000381450343d00442000030061040300c000000e403400821007801402194040307080241c0c2e100c0d040c2601036000ca5030b80d007440d624040d070590100041c840c0741d5101c40c1d000d81c1715807030006082ca1102c0e801035482004000c00c201003080e00030f640e1300600110030400700b40045402c0c5035000441c010f80c258000c0c40550703071200345001207038500400256102e2034040c0405100400c01b055020100b00c2c681501e031135030000d0180005070f0300c40b102440043c00b841c40420015000036100c42c02008604d2090519a120b10340315500d0840081045a0861313080e9540c2050206011000080300c0c0180115100d03001160420700c04107825018081c002000c0d0214411046081c0d0b50700c0d016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 53041451 1250 53040201 53040209
    0xc0306110c2b050a05030a0f0204120501060e060d020102030324030d17010b031003060e100603081e160f05010b0603090307031e1b170408030409050109020c0601030201080907 77
    0x48a9031100301854020060300c41950303042c1c02e080d41e9082030718a9800f407802c2e1402c9010546a00707003035589060503000506918a142811142d0810021610030310044d070000f0114002d030000120581400c408110f0700101800551081600003002c400603030b800000c613503000c0900303004100c2a4294452032a06064604007556140c021041121b441507440644d0900301201c14607000c0705a40c5e071b620b40c4101440f0a951403012000007030780600c0403d08540141c202c6065800c2252000306042068108585d03240c4c0041320800e00c00201e00d80c0204075102d080541342800030388240303046001d8814204041c40300000070410070003035140d41d0500c4001c3d0700105030240c0c05080e0781c0e40d030f14102108507103990100f02c0440c0401c070002004192001045030305402c581c2d4640300d4042440041070502c4c100d814004088a42c80e040000c03841e10140c1920141008048030001035440300d00304180101500e038142c01c02041c5034414040c91101c0707000041c845044940a080c15541611140b0b0f110b0300340001504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 53042701 1250 53041451 53041453
    0x13030c050d03020706050a02090117040807051605030114010501050301090f0902060f0a08070809061b0d110d0b18010b07020a03060c02070e060603040507090b060405030a0b040302060606070c0306110c 88
    0x60792020b4041c3c00418220344202d80070011559188103140413401031500041c001a540c4c00c904155189052519070800e000f411000c3c1045000e980d21840d02101c400710342c140c0c0f0140282004079007000d0180500c00c0e440c0c0c041503803044d0304000c002000da000500c01d6141c0c07240c4600d0820030280740c0f40d1107000f02540242c689683c550841418640ca82e0056800b500010011400200054802c00c000d40c095406070014001545132f20354000340c07003040c1125644103404104030003d1a90bc04d4031415100780d42d001c540a8480210101d1681260404000c1500500f140c03956000c086a200c18002e041da9400c060301901d44015001249005240d07820040905207004d2102c1041a000242c2a080303070b800010003c015503030002400020300064800408070391143c0000d0190351a03603081000085005010542070541c1d90001030314040f007009042ea6008072070010300080c0341e81805083e03401a0281d400e1444c080381580d908030b210255110191040d80d4400402c241f0410310f20480302d00d445490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 53043951 1250 53042701 53042713
    0xb04060801141602030f0708040e070804030809011103130f021908060c09010c1104181a060307180b01030207140609060f060d02010309020a080303010303050301090608010b060313030c05 82
    0x903a51802891010801c8281039404000188410019080c03a00388200c03a5000e0f50811a011401025503004005c0803282c0000c184000704855030b0418403076200740717600d950b072151030300f0581400341803000040c004039200e074140420100d00d81001c0040340d1b000000b0304100d00824803c0e003000d00c408981054002d40c409a0b81403208070081e402044a07050303824803000c0e5200b07511100780d01140b41c841c106140e80400c10498051011a040440c650f1042801800c0464120b80030851062039010a03007003120021020320310303240c038080180c0780c00e03600440c00d800a06039a4100a1134070b0658841c060018140b6407928040701580c1d05c280c068496107075018020404d890b02c9106d000752118000c80e0500d01611a40001401010740d4090b0203005503009000e0703010a0a240d00114080c0019601c141d03003240b0b420f80c0020310010708000441c02940a03603500c60310b95060900c1001990907a070310090043e814980400c020703684140881380c000b61400c4021680d41520300d001c1c0c0329002c03440f074060401e010314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 53045201 1250 53043951 53043959
    0x3030f020a270e090604152702030a021201020a020105010905010501090b0a0302041e170d050d0e01090203060a060e1501020304062d05040510180302060714070603090b0603011a040f0b0406 83
    0x40d029018903c240c215980c41d0032070340701d40d804403490102e14508006414501a00c2303207108045c0f0021032070010382a83d01070100354000c108280d5450b544450181c0d40001c21400040d82031045a0141c800c0e07103070a01c80c41d4036150000301542124050305490620010b8040304030f50182c5c1c105d03401804c2402280306041e02c2c1040b2001c0090241c400c0c1a0300780441402c22052440100d20800d940200303446041c00c1100c241f0691004007240b030000d103200e6688100100140e9800c10543d03108184c01e400100c1d1980c20203c40c0d42003e080640445115403038015035464680c3c000c01620b050360307998905a88919881040c4403445240c400400d5022120398454843d200d50100090066800940e0f042c800300c60501003c8441e03008a0050211001c901d400610051502c60020514a402150701454403c9800c0300c1070700b080d643d540440c02003655141c0c0f101c1000503001d1445e500071001c900030060f006009141181c9600f1010126100e00d0383c0b0f01a0416030b0200f6400031201e294003810800140d521 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 53046451 1250 53045201 53045203
    0x60b0405010f030c0801140102101406120a0b06090a2301080d0207030302030d0213030c080c090a0203060609010c050f030d1406040c0906050f04031502030403030f020a270e09 77
    0x1a008103800507401d0982c400700c0ca400b034010800c0070030075540d851019070718040e82c941d6180c5124010030b0440c015075010386008200d50181011203402040310f4840c2c1d0911a082000e817010784118000d85401c40200040403a848001150380154181d800391901c2e80c0700fa203c1c0c0000c049004818a1044044035001425001c0d402d216045c2c2d0511402c46044c241c0c818000e0780d0358141440000d0050340100582a01c0d90540c0d00541440c16255001111032900c958074003c9840b01500302c1c510b40d520054556000d0724001c400e4a0700104401011407650501c600401c41610481c0041360500440d0f51801c0c080044c10807000d144001200c7c1565110086e01010b00d004d04100c06040e03d400c0c204001141c0308e450f00b8403410703c180c02c0c2500d664611626018064540750800e243c85480340307800340000000724000003e40705108103007450040c0d40740307868640641140c042c02180da0b02d1034410700c0290034040c0c0060041c08580c08000d2a804943c08045c0d01d041d190455421200640d540074040c40541d100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 53047701 1250 53046451 53046457
    0x3150901030f0606081b060c07152a15021b010e0d0806030c03030301210f0b04050d0c110418050a0b090d110304090c0221041d04050c040507050d060b 66
    0x11041078180034041d62918056680c0240003010846034056071580c039111710b0050001c103a65844403098270886595005000700703002450300402c0104600148102c07034040c41600d25001110390b122203101000e25621031006072039600007403070f00d910b48c0018548070075803896840e2043c0e210b80100034400c12400216154032800500c200101103042c80b0045805450b001c240444908c01c003400450440e80b1704034082018103112801c031a4400700b08607a1201080b640301c20b45100c0c40c007031180f1060728202031518610303001b0007040403c00c100c1e45002c090001890b800000d40c0c001e10465012800b9a200c0c1d40300004c640031500011300a2041c0042e1008100c04210035520030728484080d0b40502108100984401c00c007103201150b81c0d00104000d0207004920b0348941c40000003481120180c1c880c04074840d5040c0c0800f91051945180414200254103102e501c10025040b80000c4400030304040da10f1030350300c42503543d6452040751100b00017540d00d4440e10a48541c0d403801801441b0007a55001d09104583c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 53048951 1250 53047701 53047703
    0x4050a0e0c04050103020d1b120f1a04020a0504020c0709020c01091101020f0601300605060a050402070309030204090314040312020d030605030a020f1906022a03060a0203150901030f 80
    0xc00307403000801452074503129003412a60050010000031303015a440454541c21800d44190010200001045c845000c800d500c890314440d152225050006e130800d100951100c1000305806d01da0708007080f0060325260000021940181c8000d40c580d00303840d481e13030f0a211183c0c11503125241b0125902c2c0c2c00c0380054004040c1c06002e0751121080084040049880340c141c10b80b05440c40e0b021200421a002d00310000740c90740d08185140800c0c102034034010342182c150211080d80c80d9600c95040c4200c2d4038003002c241005240440d002c41c5001416a0003500c40d920328030010f48076035510030412003454015413110301a1480006074036070f201e440380342845a6490b01e81c031000042c07003200c0d099030360035009100c0c40b000d41d03200500500c0308800b2a42041986e0b44041041c603085072a50088000000045d20200c0240405802400440b12940c0040f1103186240c14030540c2001c80450101258a02045058100401c0e180140c1d40f5a601e44190355140801000f0941200c03040300004207101c80030145c0d04042e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 53050201 1250 53048951 53048953
    0x90405010504020313080307020a0f030f08010b090a031b0803041e0504050408042c070c050c0312040509180601030b04031808060a0c022b0f0203040602071406070204050a0e 76
    0xa0341c031201070000324001194054001041d000c5010041074400d405140e11070560301c1119200c0c0381e01d60300c00000d4150303040200c001c282c081d82c50000103504007500309d01500151528034101348110000601c401d030580f0024281e40907040d802c510180130b554022005d045940e0032a951241d40365083d00541003146040c0c0c100c0c407041007000c10f20346018018503000e99004814035003002d0404000c07660550030444c001150341c40d0800c1d546120151449060702c10100c42e281c020f110981c5051590501132400001840303600010303441031103948404292001c1c0c83c0d00f610041001d5456840c0701c50885608207030420746109100001080180103520b40d88500d01c82d0341c3c1c84400079030000800038030003214010031a01c0e8214800041c10801d542d8020305c410043d0744104d888290441e4200038140c90a501028074244030b01e407483c00441d07000401c95034240300920096162030314240c0025110701080c0105000707039265070b030508071954450040d140d0480d002081004203080501029000304000e40e941d02d85 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 53051451 1250 53050201 53050211
    0x90806040b1b041202220f0b010e0603040804030b0403300e0d020a03030c0e090c09040b010906020c06131e030c050a06020c060309011103040503090102100612120207080f01020904 79
    0x614030b600010b41d411980504c282d895122416420005108908480080b00094164100c500451079000c0c0c031040c03416080001951a00b40000108402c03114016240294420410300c000191018101ca007101e802820030041030320340b46002c80c0c0b0f150302146c13054400a2664080314101450022104100d62810f104101e1828860307881e0742c40b0b040000100d03000d070b0070040c56040824000d4010030380c0c0101e50318112912864a4000400b51201624410035201c0701052080d0241001d1149810502c424209440854038200001f95902e1440e44070798019440802c007e411600c035a061000076045150f0a61620510210800b002d139940d0f00c0b056990b0300c0c00490004103030030030400340002c0c3c4403258090600c00c0d01242c2404032560014089205940d070350f880e10488000900080c41c0a40c1c460f40196646030b5005d40028a010030807180d4900080c64150208102c1d906808408c07002a03101000c1111000046003d90514040c0d40c800c80c0c46009821800ba015030042d401080000360840301000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 53052701 1250 53051451 53051491
    0x105040b030903090a0f030f060b0402220311090906041e121805090c0a05070503040308040609090605090c18030a0203071707080613030c0f06020409020702030c01030e030a0f090806040b 82
    0x1a800310351f448058200d81ca0541c0440c040f0391150441054600c001c1c1c130261a1a0a0761090210840414041c8030340280111085c000c03c00030010b0104840c82c11518a540e42c20183c1e0160344400d0b02030001402c052031348030300850b500a01c0c4a00b0302815040100e00bc0280c82ca140c002c0c001d4070015001180c02560b500c030220381e0b4a4040d441c980114148410360b8244541180e040d5507603400b000c41500c091009000000008020100610151580b80d40300c407220348c80d124958050b5481600514030407a5640d08202101e4503510a85862110040c00c489042c120380000c2800c1100c00007000c0c2d09409007000100e42c2c60014441c144104d900d00045540d80ca41c1ca64145482c0d2400755480b0060040d03440068001c0303840707030b102111218010f40c803032413070240c0700d40e1032400300e91142d03011180e06134001c1525003d62605028440e0760384000c2c2010b00001001342081a160b00c0741c28080014000000645012a4420307801403024003540b500311031060405003062050135008640007103040400d800c5401c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 53053951 1250 53052701 53052719
    0x1d0a061d010305192d080301030303060e01090204080d03020a0509030d02011b05030609070c0c08010204080a0309060503040b06130f090b041103070617070329040606031404110105040b030903090a 86
    0x300c4181c3e0003075a040914100d4440010b60030b00c5005c0e40c000f035441d035a807011010400e03910040d4001d51082e200060b001d40703000000b01750f040b416800110f8061061004001c0d0290200d164034017044540340040c1e85008040007a29a40076500704e56800d8400d01a207c070049030150310001c410301b000207841c80d000c0d00280080f03c1500c4111451a00210b54001183e0703030728050002c12850750311607600c490f05140c84080c0355003240c100d5404101150f000003003090078150410a0710000d88110b00c1c0032482c5281c00c0d16000b600040243c13046000d40c50580c40c0842a0500d07900240702020420b806101c80401d03818103804020069600b5600a2140788100e68645000601e03101141e10075204c401d00030201407d5100301d44802800e240030300d519184002c4907140b41741c0e1082c803250341c4040c031045140001000d12048542c01c4c0c000f44141440c10004114494002070101d07030003540b000482000c1030894004032014042c0f40d22482e0300c0000031060041040d8080050b00700090161160346035103036144a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 53055201 1250 53053951 53053993
    0xa0f02070c06121a04020705030c06040f030e09010e06010807020313030b0a0f02030708011202030a0f03020d080f09070b0903100504081b0606011418060c01020a020f071d0a061d010305 81
    0x5010b030701d01c43c04d5501c00c0d08041c1c000d004914000c10030340e8180781d052405141890790880381200d80b00903844403074081641042d10981043d5080d284454658101800d40f40d2800300a88290305028900b4000b482e00c0b442001298141404072624000481e624a45410500310540b2180401810046030b45410340381803094900c00c88880d610128182d18000c4141e4101e0001c40060307805000b98200040031035920445079080fa84668020802103d03180d40003443c85030050646042d4100d120b0a100a050000a01405844605002903641c21821000918043c01021072814080c102402c0000b03001541020b4124103410b003030900d041c18107484509440b0b40d0111412400f10300c890202490507400c8070040c001c1c1c543c40100c00d03041e096000b0300250181d0080e140b14007107a9000254001d5007035052140111a5140c0c0d4024180c0d103042640c00410240e06841008181c21203500140c10f00c01540c001100401c824001244020582c0380180c1c001314090109480307a2203080398107004c8032066000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 53056451 1250 53055201 53055221
    0xd0605040b240d0203100501030c090e010501050c0312010b03040c0801090c0909060b0916030c090302090403080403051201030303021209031e030601030e1605040c140a080a0f02070c0612 82
    0x9103120000c02e189256a50300000c0260002e00350203000640075a0002d10043d4015420200c1c101081890480010b050711018801d80c410040305040820040c0c802505150669100f42005a115400d1031b910303601e9070040450b00924008000c000207140caa400e40294000c1d07014104000304641c4400d01d20b07003a0360b0341d01e0008040c1454541c0400241110b070340131170388592043e480802d000242c1400281500001c1d82c3ca100b1600740c08190481945e0188140d80541b100d40c2001464685560009122050010f0001d402d00c0601c2001400300741c42001102c852801d0440c0341c100c2561a402d000740250480c45620320403d00c204049202101700100b40c54040140b0224940b40e02c03616050091a90000382002d81416202c0035003041c0c000c014021058071a84004130140c2c0350b031034001000107541e03050300044140140c1a44403c48030200d501250100d00791404c11900035250800280001d0000b410101a41440030039082c2c100010000250704540503070703035400140d4400129510495030b001c0780e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 53057557 1106 53056451 53056459
    0xa090c030515040b01020606040b1206130c0e060916030b0d0b090d170c0304020a1503020c010605040203010f051306030b2805060a170c04020a02030d0605040b 70
    0x4001c10442200e044c0100904500040d45545028180500031074542c40c0c4c40e415070311049102c42c0900034803401c039001881d100c450031286d07181880089516030940c00c80059560340c1140064000e80000b802c0c180d0b59102c806440c1291003185092600b41501c41e64020000d03030762081a9a40355010b05210b00c0300345000c100c614100b280e0308506d01c05210000054200c0700700f40c8074040358800c03050851580c0c0c0b91254000a840c054041e882401070110140c0700c4210a41c0c107802074400c1c3e005240080c401e19459600b040140e0109014640000d05d05200c10007051a051480e140c95030602c202c00220141c883d150414000011100d040c104071840c40048640314611000010f07841070382c94100000d00300400010310012492007503c11660410104a0201000388141481064000c1c0308668640708400041d403240c01c0301079038070720340c0d441c00100195501f05402400c602d03400c000c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 52877701 53057557 := by
  have h0 := BRFrame.cov_init 52877701
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52877701 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 52877701 ≤ n) (h2 : n < 53057557) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
