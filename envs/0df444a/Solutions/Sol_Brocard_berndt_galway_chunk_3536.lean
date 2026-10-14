-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3536
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:56:40.490112+00:00
-- url     : https://prove2.me/submissions/cbf80b17-6920-471a-aab1-ea1c4f53d872

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 635791366 ≤ n < 635971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 635792616 1250 635791366 635791397
    0x15090708102f070609062007020a060f031d0304050306010e01060207060302070204020712090906120503090d03020a080301090c090b034006020c0d0201050f0a05060d02040e03030601 80
    0x941c0882001a10000b040d5510700d540288101481c8100c020448032510384a4580e85980171901508070890381c0c150b54244100307880704900d039141c41c0c2880c0b107800070b85410302c42e400094802103188290410064104000201c1e036110340c001300403142041110080019036403a41d26200c0e003103405414064440d2000000301d07030000e40f4029048814540140124505080044000c0e501c02802030f0b030842d408004c0807000625888240d000a4042e039168035000e81440c864500303075421036208501142c048800300010400200844036050310450701c580681c0e915140c16810040085030161a82030b0200001554034400c0e0443c0e6055802d55840c0e10360350b51a4070b2070520ba800103031039107100c410f180700d90809444052604c4405916030140803603e035540c0401a41405034103058200ea420f5008941354039215400c1048010303905042c002400a032806a0320300c0e03c110001841d0a0010f912000813034815250304c1c000011150300a00140300d559000002e856480d8402e480369400101c2c1c483d00381e541c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 635793866 1250 635792616 635792621
    0x203100902150a020c1801120b0604090c0e090706020c030714030a0501020a050d0e0106030f03030c09150512130b2409041a1312051c0f2003090c121509070810 70
    0x42e50b105000c08e0083c00f0641d124101250001811345400a6a4840c842c0c04202d0048240c1c1c02821410140345081c0307000751140307050001a9000d1000d640c4002110070140e5408038041e4161002e550100552211650000e46802d44502010f00701d0b510014110b08126448401460551110340d0180300c1070a00440c000e0032030f01a0301c40541154541404000040e1290300070103400310f9240707400c540c1c4545589407418282d50031200000414800111202081c11303c0e0841030b440354944010714880c010030340724001c12850003408030002040d2800b4402501c068104015003500020703010044a140510b06079000f445c880c0e00c110310000d140c000081da895000c102c02d01e85585e0110b0b4020a09000102c103540315044151071420940030820083c82080703171445a40080102c400740404d03881c02d087c02e840c0b407040e12a07000661901c1c0820030041580400154000c0701e6000b550592268010b0549007400c02242c1d00c04400314280c0301060144280c400100d100541d4a80d00070344000c2003252208408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 635795116 1250 635793866 635793869
    0x60e03031b040b12040213050c030a0f060f0603021308030301060c060f0b0d0b100e09070609080303070f0e06070b0f010911121311120102030106020610030203100902150a020c1801 79
    0x110010100101a0154001013407160000d20240c2840f00e4200b201d0f002c40103584088a41d2455108003208000280c101030142440250000358200f210f182407501110700b110541c000c220034140c0008080044e540088444401040c251041d40c0c5c0783d58640307000502c01c0400c6441621054284006210070142034454100b000c0001400c600405c8616903030510341c4640140700744e031500650100000c040d00007000c064803c0e0740070b40c0588216407e091010386500807980107081c480d442407003005030a54016000307900500c1281051040801c61900080446c458060000d0000020000740010f0007250316034181031340c0c07501c01d00780b058032211490304c441ca0282c900c1400340e01030748101084402c1c852008100d81c0502035101342c0c10040c0c1e0030700480c1844051050b42c00c2d8981d40040100310555050191941014107110101111813440e0002903645001c0c4400d546090341da40c1002d011541c07a495441c00b0103055180140d240da02c920310180d111a00641c1d205d0140c0442c203280040c0104440c5441d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 635796366 1250 635795116 635795129
    0x190612110f0324030a0515090105010501050d050a06090906020a03050105040b13050a0f0203040f0c05010206011508090a050d0c0b0a05090a0f030c0503030a0b12070e071b060e03031b04 81
    0x1d08541e103080c4050303d50180c03205000d400141503e050a241c0d10144410703607078030b8019070003030840380c038036250041800d14028540003d50345007400521403681d004080b91240c001c428004107047c2c4418184c10000c100f10344c04800064a00310080341003010540240906c098651010407040c0c0e6100700b840705884044419540c4140c03204115002d0480a6101680102d141440010220030046802c01240d00c1550f080d28409900c02c20359003000180e0040b200500301c20700c050440c651400c25242d120041c042a030030280407101000070342071102088141c9049400c00c0444040d0340d181040607018a903040301c20f4507107124250020b050080c40d4002d450184c609180101180300d568ac4030b049041030300d204101c0c104816543c068000c190200701860180840080008182c11458108101540043c0c1500484d812810041020000303c164450b0302030218140000c40e0102d51546851483c120300000745070516280d01000e12840c00030140d44199014281091802c0d880180c00d20703a801b5030301c40c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 635797616 1250 635796366 635796397
    0x120a2d0507110618030408011a0307060f02030a270906090f05060a030f170f04060906020115031211010203090c150c0601050d0201050708210a0212010b030619061211 73
    0x10305031343d81032003201c402c1c1000000342c0742001c1c2c650b100142500c03101a09444410710b4141481110b2a0030700c10100180010304240c401d04030101e001a481c1e000d081c40aa061040c600321034000001800200000d45406911a6600940b5004000c00074103050099203d40e61034484d06041d04d807030f140318203802008001c109159251540da2100d000c250b585034216512000c107049046440d0211700a8000c4100710f00781c43d901c1e241441001090701e00941c1c4400304680c1844100c48a00309800d601000b901e410900c181c52880200e030b0305031820080c50116003940c3d840001040300e04a400300f900203001008955500d0480070141c4001c0640c018009000d4141e000030004101c6c40c540800440ca50500c18107109044c100d0300d807110192500065042c0c19120f0f041301200e4a01c040c01402d10754041407428085060610203021a00004e405000700d0328010b60000100314180e4800c0640b880d4421490702441c400d070385441c401445110407400415410b81000c0381c103080104088141c60070b110f41d4103581e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 635798866 1250 635797616 635797621
    0x43806040b03091608010f0c0e09040f020109080d2a0c180b0a03050c03120c0c0603040609020d2a030321061a071406070203120a2d05071106 62
    0x40c1c8446a1014100c6440e07481940380c02ca40300010902c00400070300c07003000001451810900041c0c2907446c642c0f03010b0200140200e49906983d0340052058100d0707040310074a0702c0f02c00f5902c0180e80808250b002a00248140031001014540c0540d03100d181d500c0560016049411006600601d0715a0110040c101e0180e0b2500b40002100400100360044140c200130540c3c480050214140f0000394006940e160421040301d00c05042c00c0218031580000208850320b070010030340180f0340f506891011107205040000100c0c09000c4250800d128580c0c000b000441810b11074139050034101d4005035203021051212103900141600c0d404401e040f0781e00364031010a4000d2249480a444280001d212042590740743d01165400805030001c2c054010b003c0400c0d074a801c035080c140010040c11030685d000d50310100c00c00c06400e40c080244c40d044075407106410310545440281d1800340c0005605840b200034417032402c0f03184c0a5010346500114002160403c00c90315007640c12142c01c1e0044410b81d2583c1d100401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 635800116 1250 635798866 635798879
    0x7050f0108070c17070c060f0810090903180f0303081b0915070c08010b0307090209100503060d0b0c07030e0904020108040308090a0c0902090f012c06070204380604 72
    0x1e070603e0b054414101c0300a22991164458040d8002c080142d4070b0341d490b01824885280c0100003074200b00c40d141000c0320640380c0030781d040c00400300601620000720f84403d0302104041c0203000700c01141040200041d10f0360307115201129890704c10311083c0d0008a4560100310305001c240600e1a0600b41140428a484260700c01d10984548a14031310801403010048500480c005c9005107014216420001c604ca10306e0b00c2c00c05d807170405c0e0b41d00100503851041112401c1540d451034004140b80c00350800c0d07901c1e80d5402c8001804103416040c05449100c10b44200910b00714803100a1141d64841d442e511103101c542028010a0001110028046540d9801246c0401d000d00b0481d50312505900442e480700c602560307548403503425a4400c1e03420725004168035900e880e18100c104241c15083c80c02c8005401040a14051a5031400c0034074403000b00d2a000014544800048600840d0090030038000c00c210000c007000303480c50000d030844180c0302c0a1940d09084203410042e61801e02c00500d002d0800e03003000b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 635801366 1250 635800116 635800127
    0x1e0b0907050d110702060d0c1d030703150e070303020c010909051e1503191703091b030c0904110a090c0207090f140717090d1d0103090b13020307050f010807 69
    0x40c0303000a1020180304c0794005944a030014a618400d0043c0860541c0f0010307400b80004945007441c140d240385560900045417400580741040b079800500b6814400300700f440c1c600041c5031707070808024640524040031003031680010710040811740a90352100001c1c0e0700e1a90360212507040d11040d1405640400e00c0c20345002c861505a0010f503507151030f070194404503000a00c1c0520307201c5607105442d140c8801764184803194218210502488011901c0c41c43d142c2d01d000d417500e0444140e9007034008452200c2d43c290310100241c803425900a48507881500b014245003151804000b1503170b10074151910080740e5a02d0342d001d81ca0b0028040d800414601d41000c2656000c1c1129264070240b003a511704580000f4a000d4020502079600c60b00c405840c41101003062a420748000c0c18245184c0c070540a03408020781c083c990104010610b4040d0b2188402000101d002c0c3c514001c010340a078240c01c05204032001800c0c40c4034806442142254451903031941405008000c4203d098007207403c50002505407405031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 635802616 1250 635801366 635801381
    0x10e06090301060902030108280c0e0702070b18031647091c020916030f110a02010c02061326180a08010b03101e1e0b0907050d 56
    0xa00119800f0380313440315542260000d0f88100c0c141e070300410000780c2079600c241201181001c6202c00c805408680d0721950340d1600540b20340c0380700d2001c0d000000c213814401d1140304003a10145020f071b55501015421000e1241c01001618401c1c0682c8a050038200014207108048821140c0c17504c0d0707041d500d00030601d11241420710a1303240c418074802000402c0c1805548080c3d603441807030460340302c15482c414041100a04641104101004401203001d80d030745020460740400c0d142c2c101108140d6800c021000b4151006140800c14105490014110503003000b40108001a50003000440d00c6180704990f1081e042c3c65014003014002c0c402030200d080300d04042e540c140c0d11010b002103602c2c55050140740354040800821400d1401c3c3c00b000c1e040c500043d00340014001c2400a2050351005000251038104075084868003507a102c4000c0c0c00c94404240c08000c91400c94410816598080e482c6801a80e80011300340c44c843c9800c3c40702090745000880e45020f81480d590301ea040246d0801c0c55001051039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 635803866 1250 635802616 635802619
    0x2306220c110115090b06040f030204050406021b06060102060c0f0f0703090317030103020f090108100b03071203080a050901060e16020307080703030911150d051e250806010e0609 78
    0x4070250104000c0c00340501c090b150702032405107a90501d09180f080445000c01101889250104010840813038031004810590b07070100c074000b445890b00d16082c0300920403a0b11030701010349881c0401001070000314210384990380030b07004d4800c117664900c1c04603814400c04481c6e00c6112030910080d001d0344114070142000ba8441e0605a014584a07110300d401c44c04810300c181c810490010040c800c40c1042444044407440c1030f60400101e5040c2011a07440300c1d134050300300c4c81c02036580700070324840c1d40d040000c1801000b0208600100010a040040081c0001c9800b601050b050001040c0007031014492641140c0607020109003989420040e00a100d0894290500b10301c0309012240210702c2d60402811528171030344000900c000a450000c2c1c15244034041e452003521011045070600d1480011034070501c03d034050005140c0c0c0c2d40700720217203460f808031180c5258103c82c60800c84101c0002400b88420303446100281080c01c0602c0b003c030f074944011203806000408541c1074501c103090003409445132440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 635805116 1250 635803866 635803877
    0x18030307050711060f0c0d090b120a150b030c040302040e160605030a2c0d0e0a0627030308040309080a3c24020f0f0714012306220c 58
    0x594481c0c0c526001220382d411b540e0848020b00c584070f500041014001c00d4901c10742070814120740c9014401140007006052070304d803160b080744428034207403058002401a41000d16141d041660030311026403c680400c80c0611b18184103805200700020701c84d0072907407945080c01c0c002400c02c181101c5a80025107070900c0507031504e102915011000040c02c080b038a22082161a452462a2062074401c04007643c0c411300182c0e1000c00349507168807104009035001c90070000d00100c200c085210b40c030f28443d0b0000d141c800c0b031108003000301070303002c82013600a038002d0fa905904a0b80380c19040c3d03166580160002c05000c0403000c040081010b20111f20291078081c2810a2140182030015000000514003260754604488824111283c4540510007641c1180301c110b0405c1c0f01c010150760207102d461180c0014a03000704290342000011007000d00c0d0701303844500a00000d08100c00c02c040812000000e50b20b028250400240b11341040b00000641e0314071906aa903c40612044c004010002c105c080d404111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 635806366 1250 635805116 635805127
    0x7062a03050f0c1b06190809070302031b011403010602030304150f0527070e0105040f110409150b03070e090403030605030a0c0e0903031603050621061803030705071106 74
    0x440035800b0f440703c0441c07a0060301d01002419004d82600f100e4001282c0704100501410352240001032140220107002d0034403004d181c6900365503920b02070302940025810703c544611072058000c40c1c680100c618200f078880c5850740080308010361030341c0070074001c0800680c418000103002c104103118854805114142c00588030620215000688100f00c031462211070a208580108110700851050b42d255000050414079081946501ea001c1b0180701c0c0e01d101d141c1b1004035807c860b606038003015075124240350070340c2e50326611b80c3c0ca00c020742242401c08920030589040065801d002000301d074840c0000fa2381d803003028100b10b0304102c00e9000240c419400c140d95850701007580e07103041003001c0d04240505240302d0a14070305044c80a02010003040c050b0203810500600c4003410342007146c1050b901880c200880c1c0360752544085410000380c80356044280d160241c1880d91010045a10b5008840c42d40c0001280000794080c0780e034a120a540f200700250040010301c01180c5080c1110042a00082c079280c90711 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 635807616 1250 635806366 635806387
    0x120307050f030403081501020615090604020d05070207170606221b030e1608030f2101030609120c110f030109060c0906020f12040b0a031d06010807062a0305 69
    0x6400c1228104e01080450081c0700000780d07200210036000d50248020052490301c011445135002030b0540e40c0d4020003044000c5001076070390b03030160340c41b10113405030030040c91500c40402035450a96105d0b90903007070441110310003050300c041100d512580c1c1c05070841448100040503490611050041001c0329599240403a110f4040000e070b1b080912074559001c2800c050441c0e030b00d03041240020180381080203242e403c0000d19000b1065035401940541119120554240580201207141914407200c112101c004010801c02c3c0d80f0011143c2e00543c4000300e10040020141e0303024014010241c8104652404401545840c200e100445038000d4000f00708482e66540760b1081e00d80e0b94078100007054208605001060b030400c101000e00ca2818000c0203100024119105548a1401400c0680e040000c0e2181034030b0090b0800d402e01218403a1a40a2070b1040d0b9942d92119403c0c040d503015401220f80024140c1e02c200114044d000050603501c102a500b5008030300c50300741c101c00031824443d05003c24141c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 635808866 1250 635807616 635807647
    0xf06060306181915030b0103023319020c1f050d050c070210021c030b0a0b161101030b15070c2102011e0507030c050c040f060906050a05010212030705 66
    0x40c0032407282c0300000e410a2000481034555084c1020480c080d142820030105202d006920304494040d04e40c46d901ca03041070002d280141980902d5000340d6051010901c042440c4001407020101070301041c80c81181144040380c0b1044003110160340554001d80d4400b072001080c2d56401946418101036141c4800d0402900540302c04648050b000745000c14040c0560410090200304c01800e44041d1002e00c42002103400a0300c42400d207001059134452140020351145281e00003e0403d00c428951100060441d45180006080c400c0358804c031001422000c7d1350280c09054210f45009000441036260345800c0103039034114134000d076a092032103000012540603d0b01915a14501c24000d09140031060001400b0b800845c07210000d00f00e41002c900030b0043d071280540f0304e015032600d03000103a000c10341400c0d0b01e003001950542d90b0207480c0c4207071543d000003241d1010040b90210001403001c66034600410000c2907452164a015801c413119504004001030010340d440841030612034240304910701044070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 635810116 1250 635808866 635808871
    0x601030e12040f0501030b0607170d050405030c010b1903022b030f27050d0f0501110c01150803120c071502030603150907260f1c02060f0606030618 65
    0x880c0400242845aa254829030074050b20007806c0620074414610045245032262000c00341002e0800c2c419207000c0660001107440c4034007004000c2c441070a19080558076a4008041c0c40700542c0303411105002d070b0170000926081800318607a0803000910f1074080c0001e84040005940020120110100c2c105024609400c0c1180c0039035502e0310b0441d200c2001604125441155242d80ca0a402070316100d507082c0035811050715410b450342e0044116914200035024000b0034001c00c15401d2a02c10b000e010110744c040c2114082c0040280620b04410480705090280c50107038a40c142c104024203005a940362040c070f9080406002c2c40c500c0c0207070544480c214814a5509114659000800d1207403914040141c0c4801c0100c1803101c00140c00d0503e00c207952004103200300b55072800650b40c03801102070386003441e003182032110050703400d085010a80717980c886020b05002d29501c0c4400b290b80340791504c0012024814102c045910242e0345860042210580000b00300036403101036030560314aa00d4040c4402c60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 635811366 1250 635810116 635810143
    0x20a030209070c02090a110f0f0d1416080112020105030714040806010f0b270114040f0504181518050d020106061e0203070b0c130305030304061b02150601030e 70
    0x43c5903c10045803480203041074035598103214403e004000d007101200c10340c5442c00c015694451142c2204440c600440c0d00c0c4042041c904142c00c0341c1441c00c290b102d0311030a0140d11a607914082c88a0a603103016080c0501a8070610743c0c005a401540118011034011406082081143e0001003c0003115407080d0084030321504100700405c0380c00e050080d80b00181018025180c1402c0c1c600d03543c0c0d00702c0d41d21041e1401c0f0f92055003503200e00a900070380400c1c801d00f99190f141a6140e0b2a019100e040c078200e4800c03a13008915041c40b40d0394445140040c100c45991000b88040c4036014150520b001d007027850342c0d44a00075680500c140000f24200242001c601907500003203621490518040e0841c84801b041007645054280d0343d601040d40403088903a800c2d40a111412161158113101220380600d409803400801d005c1008400d2180002c043d41c41180f090105006918603413803020304a00c81662100c0140e4070038030b01e00001c01d003107a41140d404074040c03400141410103d1fa1603458604a0b000c2403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 635812616 1250 635811366 635811377
    0x18080904050c27010e10080610030b0a2d030b0a0903092d0509190509070b0a02070305010506010302120109050901090c0f050a17210910170a050c090d020a03020907 72
    0x1459540c001e0301c14040c0c480106c41001014141107000380c103d40d8001c209a00c20300d01c100354150081c0c001c1d407080152400c041c0285040e03a484202c0c0c1d072001c0d05c4000351016081c03220205000341c0580c040c5181d06882e84120030b40c040c1c3d1102440c200242510182c1142405405600840e001000e80081c44400c41d145540d480301c41501440d603002c0420b503800040c0514110b0b0204040303c07030b0803400091003d504200c0024150340f081c031102e06000c00307900803420062000400c0120305a0005001c81030742d010304020401a04d52a006404238072641d40c505264041c02c00041080400e03552089910405040020840c40000c3d50b89101840d820340220608118040702440581081c1059902034103058440d20400404444d1940d50b6021031a1903442000080700404100e10031182a6128200c02038801321005c403003650301800e510144841c015903041400c3c000350205100340075007400707886a0f240761440d1011303801c00d200329840e003007900782d0304a0300c8640b00100580f54840e20b50321440036903030358 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 635813866 1250 635812616 635812687
    0x31e1709191a160f0c15030c02120c2b0206090f0c04090201120f0e100203040206180114040603020405010305090d08060f040b03060c0306040c0f1b060608061005010318080904050c 79
    0x5011031b101104201e00d0403d85840b4a81c036550f030300002ca2030402c40d1121f409684405216507041c0ca4401c82d16400244100c5090043c2d0480000f04240c80200c078054080d280c096483c41001a42ca05004105410560041c80c41e0394103802c15a01036142180185809840d000e1084a0103095804800c0c1007503559a4403607858507400e00a2001c010410507200003540b0714180742c0c0008105014007861900004900c0c041c42c61143c0c040e05000000d14040b040442d1550795508024009401c28841c40d80840d0400380044c0201c000860603032214178440d210401c1e19202c0005008100d40d42441d1550002d82d5504441010341e01080214810980700d2186940c9103442c00510040c0ca001450380404d0105c01103040c640107030400104100c074000c140007250320307240500303001010b80700300da0201485005410078004428100003080003a103900b80c8ac240240c403032001d1140070501120718003401d0401c0600001c24149485d0b086650481d10780341c4c00c3c0f030800001d003921103001174005038800f4449140110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 635815116 1250 635813866 635813879
    0x1707050f03042d020427020f040b101e0c0206070b0c09180105030d08100e1906060f141809060303040503030c160f0f031e1709191a160f0c 61
    0x80314841078294110002d06481c100c54240380c0fa500c0d6100911511030020201220b403070366802040c00c20302c0102f42e8010000803400c0901039040b02008066801001003802e22214081c0782003042072940030f0800b61412a050711007120700c4d04060b040d2400d420041003860615a1000c40c00405070380d040031056030a501d0721007018605843e2040e101d040c441d0b0041005030f652800150740d4112061f07c151191349607614240003000b901040b200d0f40c01e10303142c1388021400c550b002c100e05401c2001038842001508170b0711081c1c94580101080d014210402c2c0c440164981010f00302240c1200c0d01808503810207459000003825900180c1c0d0a44c039661100c01d8034160840a00c103410028001110a00401403c01061600d07005280c0009040e45903402d420101c0c030220000d00042d1150000f07182615840d00078600c1c00c2a0f805505164400e0a08010300c41c07030079200c5030b40141220f0500914003a0b2098840c003900903034024000c000252031040c0108000314a80c1da100b230071824420304130241c5190503c007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 635816366 1250 635815116 635815121
    0x501050f0a3e010911060c0a021503062713050a05010603060b091b0711010509040f0501060311040503060105091b030a0501230a06031d010f020a1707050f03042d0204 73
    0x2c0c11070360707060070446000314900003449015810180d506075641c00c00306a1840c640100b6403802500a51460000501c00100c00091801180115045001304800103445501c501980b4016800b0b03810240c08034040a128a190014a92240701601e40070b42d40313a00e03401c0c216a101d40c001d507215511659a49801e241400000c1e41c45800400b6070b41e80401d590041e084140500c1070000d040003002c014422a980c0144159482c1c2d0200a0003840f6400c000240c40015180a205210103e0305040281c01900451401c1d181138803001703401461143e1070181049000d020141c00d6402e03031180d021451106181520045200b000f030881e001c40e01d545440d914150031200d64009880200440790040f0450f5144807003c0c0440c2c602d440c020501c103858446003000d14800c0000848690310f08102c841150000342c0242441446944546500324a4140c0010045d0740440d803400000d40304012040d0a4041d030f6025503040307401055101c0c20b51006525140a5164480e00043c8132000b880b400bc0461800d030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 635817616 1250 635816366 635816477
    0x3221406061017130f060615050906070b06180a1e050702100902030f010f0501051e030706030906060512030912071203051c09080c01150501050f0a 65
    0x1d8441034510058100c00511100e00126402c41c1c0a0105010884042c0c07584140d18090350048039245c40c010017880c00d880248014070643c0c1c0840f45141c02103400ba130082d0107880c1c0070300c3d010b00107502d03041241d80c4905800b07100905040e40030041a04503c40b10000c8030a02c0d00c6010306250008040700b104000404031f00d80c1d4141c4600450034407042000065010803c0074503100511004900d072802440000d007841142110b82030701d50701e000e80c2c1d070800d2016900590b0480e60240d40b052041d44030b0011a842c144089050140c040e44601e41c01c00240d0f10a0340842c000074001c940010351503482e14002800b03d81c605107100310780d600105a10380e062801e43c081c05e40440100c07008010340c518001400000c0d54400307101030240306010800141c440d01c0b15102c00441c0c6001c500c02c00402e4158540790500e03070440400300509620306201c0e01e1002105280030016528161901810035205507107da5880d4070031400d110412101d694a031230300040200041c030407800035081c880d68a1030006615450340411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 635818866 1250 635817616 635817619
    0x30112060e0d0504060f11030a0207050906060f070f0303060302040c0c030e0108071e020123090715090308160501050405100b0d0c03020103050903040803070305070b06010507030e060322140606 85
    0x400c01400b403280d0840100c40407100e40c1d081440642d511904162a807030399042da6008a40800910140c1c051343c081241c0050314002c640460481c1c444005109041c01044140450b00d40f08022100c0468039450f0344061031441313407402040c072940303940c08070f02942c20424402c8041380c4140c0b80b5008143d00880045a1400b0030310749030761a482d02540040c0744092401e4001c903450006e4050340708280c400c1d000034030580006c5030744250740741f0f01808000090b0001c03141c51406010343c18021a15401441581c80486820b0f60f4603d07040381140c41d83e14040d4000c2c94a04802e888a606c05000100c003030041a201e0b5000c0c002500c00c08180d9200c140580d2079070f401c0144140a200d039250001442c1c2e5404d042501d03020305c1c001515a850f001031510794482d84e00285070740e01c000f01c0e0340410183c2c454024252103103d0165040d054540318019a01d6010351000180464034092400c000d03400d20402450388401d408004405401c880608041c842540d18400c0d03c0e100300d80c6901c801da0400070030036030740c10400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 635820116 1250 635818866 635818873
    0x10203150d0f06020f0f130f0f08070509070314042012060406020703051e0a12050c1918060314060108010b03150301091514060103020c0307110a0b030112060e 70
    0x41d80c2d1101003065803518000c10f50795001c2884190b501843d03041d2a07105c2143c513419661100c0d101c0150b4106101c522603051101c0290402180d00050000b00c1e404907040c0c41c00500c812401c0004114202000400f04801c00d51348407840e1481813000030403140260f0141c0d00008603075860b0640c1503102112118658081c0706030340d159a4501200140702580640c100a00588036451403408648902c1005191310a81402d1030110480400c400f0040c40030491a454010795400080e11703404c1624400c0f44c0881c4008428031034000881001c0d103070247d02d080945490b103030300041e0041c100c22803c4a0f801540020399220804640c1a004142c0f064111009007401ca00751f41c134000c1c0903000381c8002081444c0200150440b200c00352001d41200084580c4168182e4150040103801ca0081014182a200d00f918050101c0c500b540240b080301c020f07840d21400b840c42c09105840d107021548255000b1908502040800a280b07125080070b94043d1008c21504292802e16041c008207855990024224030b80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 635821366 1250 635820116 635820139
    0x509010501061b0602031005210f0d08040f0203070b0408010c020c040b0907140706230703060803040611070b0c0c0a2c07020a02040906020309070f0b030708190e01020315 75
    0x840c0801e8610491382c804005a41c1e81d550090101c20701d0310075444242c001c1c50201c5488400d27205194912983d106d82c0c1b0849000c0030350a00d03820761314002911802c001ca030034240400c0101c0c203580805440a40007404035007134240e840544d008581c5c01076100e0340d460b0b5940c003440c005503035061203170a900c1d040c00c880c24000141c1c41030000f92002c00152402c014425003001070341c4132041e510141c81200390825800c11002151258100e4040d00c1854080c1660500303100103468140244a07003020345030300e40001c50403c1c0c10904183d9450541e40094074036486864000194210182c004041a640c90f0004c0c4c51061584001c0c8001e880594101005451700d4001408c60342070128660307034410a600000248507112000207174244010040007940081c20176640f40144030ba160001d500418444d800c0304c03c2c0c5c3c2c0e9100306400340c07009240550f07600d050080010170941c44c841c403003003500000c0c800104c0c1000c6010000b100e003218801400f010b8207940210400602005c032444452603403c3c155085122807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 635822616 1250 635821366 635821397
    0x14030a120302160605100905060303121f03021e03010c05032511030318060105040b15070c080d090608130201171f0305060a0b03010216110d020d06050901050106 71
    0x400c05036418101580811460541c52506118900b65a0810010410b9092426550b90601c2041c090850042c0c10701d408103526003000002c136070403c0c2c0d04080300b2003141c455058100f07031840d0060310210030b140b0031640800075a469094440c0025904200386001c42c0c42c0c0e0040c1400d403142d05079660705102040c0300300301140080c160000c8140194008007004407145240c16145084d0300c043d0400e442c48040200002805c200360040c40c1c104541045440326039031481007105843c00241301075040380884c10b00c00001c605040c040c00c0100c0c0714000104d1030f603840d04203051600c0ca40036090000250760324410042d054101c54040e0300240031444d2180c1003251500042e10382882c04403001c0c045c500f544002645a8602008440880c2402c0d42c150320082d40d03401c1c00e41d0707105400d845001c0141c0c644601000e03c0e1a051003151f01540c4004440061141c5030341320003c2c23401401c117000350001c810304e1184006907103250070100b42621881c400075850425450301c1e82143c0f416003040041c0103009121200c03a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 635823866 1250 635822616 635822633
    0x307141801030f0f0611040e06150310181428050105090f07180b04060824060a02120304060c0806030a05070b0a030f0608250b07060c03180302060114030a 68
    0x81ea50011041c8000120390301d40f0170006e103107903403514604030380110b00844c0e14800080c0d40c1e030003042c0485904682480301600c40c411880705a420404078140380c4810040c0040da417010041050003d0000036998047d0300d048410b04100700c90342c1100c9040301591b54101ca060048100480716a05070410840d81400b01054500310061304401003980401c001a144502c0f599558252110b092841c0c0495507403800c0c0201582c2090251401003280076000071500c00003000034400d041c4a084410050410110502c40f89a000100900840c003c40150000c042c3d8030000440c0194030510300021500041d50009001d100b01038000c6220b50004440c00c80860000511981918800c109042e984e8910500170b400901c209074122820724242130f030004845002040441c43c5501c550788900891544508600c014000c074060b400440c1018085e500115210380e00043c0e280c00d250900250007840079040d0103040c0046001100141c0c41000180440190100718641141054000b000325429079501c2040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 635825116 1250 635823866 635823893
    0x14010f03021c09030206090706140301060f26012103080a0b040603020a0e010f050303130e0a18050604050709090f020f0607080d1515170a0605030714180103 69
    0x416401241039100e1554005044000302802c100c01c2024101901d0081d4441e1070898290020340152400080c03060b014828403140c40030014032940ca140e00302402510303d42c400142101c2045006d54052042100e4040d074086d1460340c07003440501c250b1600e4400e62014020040020155441c0c8042c000000e070003610300c0d44c2220800e0004110451800b01180041080d50320113944500d00c0c5600082031540c1f05621814ce13031510000000711516901415940e103e000402d007007845d0070ba00b0401442914864a54001099444c046805e0115515504c0640b0703041030295903641003d800c4c041000400c02079600104003020051004560319100c0c0c40014400c114040c1c003643c02c01511142c00d903540c504991819600c501101d403200a41002e0034000c0030450310b0b0091000c0c40c3c1e0000f0032901e80c1c82500c4c0d24284102e41c0c90001c0c407900518000418040034040903e0756071110f801080c541d405100c810003030105003030b06050200d04002003010301a0716011409068103120011301c04610b1b4943c2c91070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 635826366 1250 635825116 635825147
    0x408060601080429040212010e030d0c12021b0106060e0d0b0615130602070501080c030109020904060b0f0c1204030f080307020c060301090509160e0106030902010c05070602030909011401 82
    0x10180ea45040420416042c4c0700306000404c0c0344400201e10b0542c0b00d1015005500a543c0c07070383c0c048400088a1700702c0340101d2482d07286070300603c40c00c0c10141c0da6400c040c4a0305002d280c0100a007180e4000c15040e81c219040c00c0d40701800142d84841c2d0b91101f44100001888186803500b04445510041176003903a41590242440d01e0281c0040e81d9603c80c03103010380300000210003050385c0d138141004440758003810340a031000600500310009a198801e1020a0140d020b050616143d81d20340750543c1c0c02544000d9001e90800c1d105c1c1d0000442480c817802900b240300444203d1580c6684540d00d49081007080200e411194400f44800c0c404074091100b4000a41d03803210320503943e9161050164074140130741e4401d0b5800f240000000c1850002a04100c1c0200d041404858207400300099690080c601409811038008241c1c004000c1035110b90014840f00e03006040c0f00c200448cc80c0c031410f0030050a0f030020780141e0f10020b413426070760074035440b001d00508140c54442182800307100000c040d0603501d071401c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 635827616 1250 635826366 635826377
    0xc0717070219150f0225050306100e06060703263705070512090109020103060501080405151306060807050f060c030d020d0b030615090a0b0906060a020307080a02210408060601 77
    0x44007907030f008010742c0760000301d280c100000680f0303403100040c0c4040c1b182c011a8001c0c00703420046081120b200300700074181c4151502c01e020b5aa54942844450780000b4419400c2002d6005004401509072100c5171210040040740b1007146442e581141600e50311a184030400704050800b100c031403000055a4101d4002c5040c0400d041e00c54810445040c01181d0301509600c41da80c081c0109820158042c03e4198400e880070320680780d44a0041d261064101c502904507000707000064900d2400b4120a41d008004441d810346502c880e17142e4600312401500b0080c9103900c01c0b8000e0045283c80c44000c500c98030101c48083c649030302844000e481e0300541c11340f4002d40383c020036111400522a04001002030b00036048a030f403031401070529010070740490300346405135180c500072526540c07090183e440e0707865001c2e000102c80d4551070705014240d07101d03501c07410840c0024003020703000440c00401040e032111a94000c2060040b0b004086083d2080c14031049018981000100103120300407550030381c000c030b090900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 635828866 1250 635827616 635827637
    0xd1107030b07140d0c081b1e0f070803150a080304060e01020a06110a030b0f0a121104180c0b1e210702030a080a230c071707021915 58
    0x390f4481003039001102c0d9220004c1340340b03051401150701405000010350b03101111900c40114a001c031460064140680d440c040243c80240c1c41408100703d24100301803182032411030714032030718652078228000480e0401000030074085191030300c2c240c000086008440e540c000519000c15503503240308a12582c000d010080400f4030702030307001f4403031805c6036900f000c42408000203400305030000383d0202d2030407800f091078a030094055003060300c00c03c03080b9100a050790030300900308080d25010300b07035080d001c540400f0701e0784030b030b030510b032294015243d00c2d00f06144607002c820200c3ca810a0008070a80000d42d40d05000c0c080c10720040858644c59508046080c01140c0c2d900c2d505518494541c60000d140502014850a014040b90b00000901d02034001e96592180ca4640000c3c0c5010b4032200c0009100203180b003601d024110481c10301250b048282820218903005555a60541207018a02510380e1180042010b07070075030509140c0d00c0c000070b0101251914040c203182d00c10780c00720044180d4a0410000109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 635830116 1250 635828866 635828881
    0x10e03030619050616060c030605010f0e0a0306020f0705060a0207020a0909020102030d0903090816050d0605130b04060506090708131b0b0315120303070e040f06050d140d1107030b 79
    0x30844042e000141c0440e65681a00b070541c1445c1100c40d41c03c0300c41c14540411402c645210380b1030790003601d00580d00c511100c03161090807103041c030503c0e1300c03a64025512400000052003500c000d050049181002540302d81c2c0a05001d07091000042c00f48452070300400c460710050351107200010642e1030804000038810480d00040389907001d464034203084980340c41180b009054010170240c080381c1c00341d02195003002c8116a03605401c4014403865811a90404a807400285142c00c1240c6c084a40100500d00ca00980c86a9501100c00e55064840300d81e980b051090f1400c2c00c48055a019103d030174410b40c2820b00c1094101284600c1d070700a4900900e60303160300100110140c10100400001110940702e003060f19102011440524055104012181c0d00806505001c000d581c03040f40181c032500f81c61065042400003908400718080790080c0d60f2440401c0e00d07651170044868281c002c03018618000914181149442a400c1000c070600a0240c490700e561040050100d0982c2d612072491802c46d01c4011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 635831366 1250 635830116 635830159
    0x301030b040609290601090803030406020d320c07120f020f07061d0102010504030504090209130204060c06111305011805030708060717010b070809030703020310060f08010e030306 79
    0x540041c207400d84529080c607500041d100c0344c2c40c03074100070070514500c1e2505030046d00c654460703105480c140c1d0001e00020f4003003046a0301414044035089800709545101d004508904020a480740c030000d521147d0102412400c420004e92201134940c08500c1d010300c5480d8156542c00d4400e40d80304101c070007013072444114400d0080d6100d81c16038070101e801540e1101805002004c4900c440707000d030302103860141d026603c1409818021901a10365030319003810850740703c02075440026950f403c8442d26000e00d42e0f02d01103100400c002d05c0141d5a81040c10b096140030303800c1e00c0c2e091074031220b2084103020803440ca035980045c81085030f0090800320075074190102d50001801030380d48415414050f076078000a40420104034036200e00c01c0c80d61018152604215482c102000030b01401031203c0c1d007800305200160040700240703560100202160074070307996640081d24200a800d090080c107074031040104188100546120042d1064400a202e80350a05880b0350340c074080200414400e40f10610201044214207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 635832616 1250 635831366 635831381
    0x50a0b070309090203311a07021606030b030f01060b0a0302071e030c02010f0305010819330f060806040b130b071d030d0c02090c130906050f0102070b0301030b0406 72
    0x3c6109545910307021a0780c0500b001c0a440300790300d291082503034200d035240c03004400c10000c1d4003003101d00304000c0f000741c00d56105500a010360107500c50752101d00c1800200c41803140c01000380e69808940c0c0c4148000f45400c10445600c440103e0781403841c288039029029003558000011884d0042c1c03682e90038201402d1403d8240031125608040085c040203140c0c0c000d6100394024001c0e210340c840c602c000742040702214424403841080350003009102c40f9007495441d404c031140d4040c2e40c410340074007402c0c00f40182154080070b80c151102c01d0601c480041501038000c2100364440701d403003000f0311031600c3e0a26031540001071004001026210001d40120811070368010313025009400c94a451928810250400384000240d80743d0040c20110b4111a10f0300080b440c2103510903941e003691040d00d9500303011400401414892404005021010076144906036000041851070400309015103004280440c010001441e541150002e00b0244491050310042702e044231781c80380c7c2e100103c0da41d03420a14003c01c1e00c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 635833866 1250 635832616 635832629
    0x51203160e01120b0d0f1a010e0108060a090807051e0c030d021b06071a0103030306140d030807021015050a0e1b09010512070816020f0c2103070f0b10050a0b070309 72
    0x241b9098428014214902d55503014690440f06199803180391840855100344655261584a940012020207a0390446046148500e0485041214030703070310681092200c00d050200c403401400c81c105400001c00c91001c1107d026009030803046001d4200a490300e141c0c0d503001d00210020b17140c81000741c840004564049030000d10300d00c040a03080540d580041428070044c1c0010703040103c0451b81079040440c45e092030800608010752a401e559081d40c400e14001c1140c000c3d40100308400380950b6480c020400f00300e01c14140d5400d1f0303e00704020089440300c1c40d0440010442d5040410810700903160001c401d0103107100082e500c5202220040311130b84121a24201e058032201d09001040e6002074080380660710500c00d0311402c013100d080813643e80260001000c0d00d6030191440100b14181200444848a0504820706450121807c45461544044400c070f0306030000310112030a000e80c3c118250b4001d07080c80c03080a406442c10000546021043c0103281030500000307800d500309805240d0f044018002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 635835116 1250 635833866 635833883
    0x1a0405100f060807091a07030810030507290702010f1101060305070609080d0f090621140f01060804050709050c090901060e0103060602010b060f0a020703051203160e01120b0d 77
    0x40300c0000404030082030380e1080102c1e092003000304515039000046002030250305d1b10301d070401101d61421034044d1406085001400d81c00c60300880030400902800002c0c0095000c5010000c4003902a103182c0c1c7c0b582e00220210311014001000140e07400010454260b450380b81c001c0015a01007400f1303004110300d40c801440c40c03050260018079560048200400c031140102900e60440d03020400343c80d010a4081c103140083d48450301400050301895a01003001c00602c80c1c08007000c48660004200e400c6030140e048000a0b082c104040c3c585103100e00c0740901002c0c500040d9505096942582d20740d03150082155240e100c01c0002d00d10032015040d501c3c131003001040f44002c0e594840303000d04050015203500780000c1c00c0140102d031850050003860440038000d41045e20f019400300815106070040340c0e82201f140140032002010a01c1000100c02c1d409080120b5566070501290300d14070300b2455203504041c00220704441d40c1c50383c3c11648241085008400c0450041071400c00150829512078000780180c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 635836366 1250 635835116 635835119
    0x190b06090c251703071e0201061e05090903071a0408070516053a020d15140f010311040c11120415090f030f02030c0411030702101a0405100f 62
    0x50b00d90010003107042c0180c02c2d051000d001c01c400f240051000300c0710070001ca88494240d101340c52804601d410301c1c50640c800011010b4603041132819041140000400c0c0241c0c00d10f05112510b0b12310055504034080c14011881c1082c01d81c0c43c0031765140340368420040403c07500c1c001014000540100d420095002094030414503103064250203007801401200e024100840c0040c0700342c0050500d590002d55030424021078a420a40c01c900c0400052008036000b00e03d61251400191341c0d41c01c1c4207000040000c002c500003c4000c03984114800080c042030790340c1000e0004001040d05016075600244094900ac138014128060079520540300016001d4a40704964148100004400182064910350810080001810030040351180018012011008050002040041c191008021215101600303030380588022100060480da00d01e1072010004000008021885605012500f01c0c0240c00504000c4d00c1ca10030034000b60680a000381c6801541c0da000480c4120f907100003001c0040c04c8030403501540c40d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 635837616 1250 635836366 635836417
    0x904060b0309100b0f0d0c081504120c021509030a021002100513050c120c09070c05010c0206041e02041b0203040e0f060904172a190b06090c 62
    0x640c03007122184494010250f0b072a201c400e880c0a91000390300010309140c4100030810030000000608581107400c295010340c0050200170a212807084180d01c03164804061030507081c100c00e0012940750380390801c500c10009000523960043c1240d4042c044541c042c3d02e480c40840801c1c90203091100203980880804510222241d00140c0c1e0380e040d104424082c44992501501c0155024000c0b00c002c105801409440b01507081c981d0008032526081c9080f56001c12400000c125085010340d02c0b10300161f032003070a50381401000d014040d46000b55200a180c40c0c50b00e42c4036242240c41d441014141c821003d4082c2080d13540f141c020314030540c0e1903108440071000d80c10340a580c2c1d501500c1500f5285500c440011000303032441c9125441240c001d0308014450b681e0340e0b62584008107807085100c0343c51080c0b240440c19801800c0104c0c42000f0380c01c40f58080102007440d9031500d1904040f0003056054183c4a0002410f10318020ba00448240e07800146070700d0703203c4600018007800d9046403104440e81c5501400d0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 635838866 1250 635837616 635837639
    0x3091905040b03120f0906040e0f2d0106050a031401090e010b0105030103080a0305040f0803040c0611030c07050d020418060207060506010e090615040b0708090316030512030408090406 81
    0x454000319001c000d004485000d02d902d4094844c02a0510202845400d4600310307030b28010a200741c0c00604045c41c0944132580030b01c0c04a016a10000c0c0d5a0419003001103c04400050045d1001d054088240800141a40e4120305c2014001d41e009c110011403003c45060103500641c1c001c03448110ba0b19510360715400094020001031168654079800c090f010070389540941c0442c0d040e00d8101030303401c1c03500c005810b054000c1c05000e001103520078002d12014012840c080c01550149208900c00f5190a250680092902c4c21703800700181c55030010051200c00320000101601181e6003600c0d4071040c5842400081c00900001141d85048605000520100704059008102841c4122410003041e01c41000468413010240003043d000580c1e40c010a00034070300b14400a140e5500c0481e5140740644035a080703000c80d005440e00b00c1d41c8060200e0000341c41e140c1400760716170b1140c40002034213109146071200ca5072012801d06e030b18401d110000100d01844445030440703d0302c1c0e001410500c11140e980c0f469122 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 635840116 1250 635838866 635838869
    0x2070807170d03090201020307060b0f090103030c06050a06060c031d040603080a080c030411090a0902060c03040305070518040305130803190e04090b070e01020a02040c020a0212030f03010e09030919 87
    0x881d0b0040a58600c1182e0003407044d2051141c06a008504146071550303002d00902d07820401d56840010760764150055a2001800390181d071003070f07498907903031982450f00c2b400b07075400074060002090800b4820b004156003c002000480c2d0107261030903001010340c1064076400c401d03071a404d030000d040810110612007403000034a0300902591300c3c0d1103140e846004540040c0415900102031001103d018503e0345802107025410200c100000104940f841e03000681a50000100c0d034031799000401d082052101c184401c0e0010315054801c1d04608005140b1035444540040008040c05004102c8190070241048bd8030080c0084004480c1d9402c914015a0701030404888202c0c00034050f0601c1c0401401c2c58010440714a41c00340034103030141c80351001900c011000d44d030541d045201d580048405695180244060008140c02502c1005801d005000d200840011241702030382c400c22501c1000f030800011030b41103444140100359551100038405066204401034240e100048079800e03890030040405480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 635841366 1250 635840116 635840159
    0x8070b0910020c03031b0c030d080912091315212a1a0706020f033c040c080f0c03010b03070b271509010216230102070807 54
    0x81d0140601c580032a501c00040843d640c058209110345403402600048440b0076140c09000c0d01d01071041307075000c0f80c034201a10a2a000040d669814401801d01c180200810383d100c0905061401070904041180729078070b45070084482d90394a90380b80c180305110180302d000d02403800d80b000c1116200040340c0701c030500c4507000751484024086900c46100680c1e11000340c00b190440c040d1110307807502d0005c107040c580106000c3c1c41410108288000951280700506035856100c140307684904000a041da82c3e82034000700040c02c07190a00100700e8909051201d040c2d8980c0740c03890009583e5903841c0c00c1d403016109500c60091440382c0110040350503030114042006a2007603008210750800e40c41050380e00c20311b6215410000b0307030411001c41d08030304d0710f0406585142c0c1441a40c5004520380c2c04500d03c1506001e86920310724000c15006010340c1c1c1800307034040d4001d240640c07038425801d000c001e04480c6c181c90703800000400410714084c140d034028050300000f4503040064030021940c5042c040e05504034244003c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 635842616 1250 635841366 635841379
    0x20907120f09020f040e0c061309060605040b0409020c071206020307110c011202030901061502070312051206010e0d23150121060b0d121101060509150a08070b09 71
    0x103441c1c0029407041050301600201894580303180ca4080c4002842c51110000740b07400740d01c0007191039844600c02803504c03185c01b540a0818514203903042040b1040c940020040100400c010060014040242d5003955124000143c3c5c07802420070482c0382c41c60070b44c44803100c0b0f91340003c24418486a507010314405c15680e195019080d095010191f01c505c030840706d0700d010034103601c01c1041d4038071103038090b56220f030480c0000580305444100410071160320500043c0182e0042e0414001c1111141c228400c4a000307080c42c604006d410154616510710040c0400d042041000c0010305954440502441c52600804a424910b04503040c8501d0712481ea0110403452140c5400390341008041036080e8100c500030020b204c2d4a91001d400e0866002c5514800d81e040d586510360301c1c80e40d0391000703201c0310b150740300d9103180045d03030001c43e000b0b002d80107034000e101c6080e45000c108000a41b50714103e55404003a41d030643d89403407881c1c1e0004e014002140c1000a8a214582000c10200c4016006180907103044804 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 635843866 1250 635842616 635842631
    0x60209030f011b0318021207031406070e1017040804050406060815090417030a02181012050604020d060305010501030b0916030206070305041809061d0c091302090712 73
    0x1d4034243d61100c41e0000341e9108260f001c0703400c0391007540701c100707640400807449403d042203800203154140194511483c3d1340003204100100706900054400c25500c14014005a250a202c06001801404100703070040f0080d0342150400d5204038454080c89462151040c454103280c1020403040d0031500556020b40d20300384002ca0030602800f4440c1c032a098031040f4854600004060041070007000d001180c2e03146004030301e11185200d8001840c841d004010b001a00c5829030000d0000e003418a402c0c041c0154240418058116840050003a0b202d540e10004202c2e0740301c180c0030070024811a4003001c001c925000c804000c00c241904031034101d9000b0090f40000391100c09416460b41c0804140c405240b007071010800043c02c00e140548001d9000c0c1c10081c1c145551404000031106e240e40d20101225680c400e80c004006062164400b02514210503c00c04081c2a0b4200e0790794640074011403288840c140081e06001040101341d406030b0340503211403103606082001078a50141d01e442904601e00300a207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 635845116 1250 635843866 635843893
    0x30c04060b0f07080412030302030402030d0807051e04050a0611010c030b0904060c02030f0304260a0203252f031f050618090c121902130b04060306020903 68
    0x6540a0310341e64607040d80340106094140846600520303044034416030522000a1181305165140c1000d406910050780d00e103413138030416060580303608842043c400540c00340429207521a06441541f182000f4030349007102d01c400601082c0c0540c1c2e120700d50020803003801044103076003d000030302c3d5038000e000240606a16030304140e00750740018403201e070004282d00c0000c6c046121a04600c617404543c0c01a20f1400c12b542824601590040b942030f140340080c8500564500300060040c1c001541ca0000c441c00c0ca500f641c8002c0d100c1c8a2152070030745144402e00055a5a203003a0b01a0208a40c051107007181d40128100e01034040030400c14982c940745a41b655203010781030106507868400810581c029528080402c81741c028a0041c101980240d440200d0310740450100c01c00301d000390310200007000090300303200420085440c1144000d00307580050a52520940d010030560603400d50481e400c02c880089030080790001c00c103115020fa880b606044001040c409507500400303128005900b5a0901f03036a000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 635846366 1250 635845116 635845121
    0x60d02040608092b0e13061d060307120c05061207090f12061d070b0306030c0a0e01050f030a08120a0c08040230031903051b2b050a0b030c04 62
    0x180381888902c1c3c2c00c0d6130f00c00c000031080188405201818030a203080441008205414003822440481c80d9541c0401d0040d5020603066240c5a80b02400d0b100070b80ca4104007090300e40d04288261500140e0427075240c0304002e0120313040d201034400500318a854000e10024051403e0064400c80041404d141020500b16100e0003904240c41c449028000d000c0000d6403a02c00400e0101300c00401040241001d6000241c00c3c84420000c0c0680d800091b00c0381040340c10507052080c809881440b4082250042001400c41d0b801c060440d1001c48503a405485101c020a0401c0a1058024605400000d04110b80c0d4130082120340160011041005540b001d00c0060766800700c15500690700010000d480700c0040d0f404440c40782c80e021003d4182501c3e104901d8034a1031900024145001c425091001041c1716505115481d405100003505100340d0516101c2c0c60642d00c5070546803100c801880c54210044480000140e081c510305200c10040d40c907120396820300400d800150b0398031a00840c010301c0610300c0c090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 635847616 1250 635846366 635846383
    0x7050f0303010f06091520100e0c0103020903060a0203090319021c0f1b03030f06030c0302120304060912031b0b06090702061918060c081f0605030604050411060d0204060809 76
    0x1c1c1d2103c0c82052920702c090303e001c42003d1100b02c03800815a2001a514403e2007108c6c00e480c5001c201003101903020310f00034101100d01418a040610510040000c0d9800151090308201308440c0180c0d00e40322488001d0540c825007007000310a41c000410040c4c0315070700040e03a407060101440c0d003010500154070100c2d613989091a05074006414800803c0c0c1c6043d0703200b07e0084c031038403d08000503120045480007041d24419801070300e2400c64940308001b942844071100040e540c0100295103040c0c103005015100f950030307000704c0c94442e51090320901010b00888400d44120081d800b6211280e0701c41c540011981c80c2103031114003e401c2000807804071400015924094403000300c10760003005096460000910103000850074000720440800003040c002c1c400c07064106525aa031610314508003402e4031a01c02c5540c44417060f52540c50040010039404801da0781c004508170741c08078850301d85007801384400429207100d5511610004503201082d50710b50040045544d95150114186d80d0315a0302921542017 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 635848866 1250 635847616 635847629
    0x51f031b0801050118030b0702030a0311210403111203390a03020d0507020a050d0c030807030b1908031b0105090304121b0b0a080c1305090702010207050f0303010f0609 74
    0x3140014080f43d8000c0c04402c01c40b10791070300c0422050341da03134903803018841081d9882400f6800025a40042071340c113000382010036400482580c60080040d02440400750074a5120ba101400c07040840e0070103200780c2c0404410340a200c2190032902001e04503c0e029402500d10b82e0014500c0d1468a0102e85200884468002d00c010010b0601020b03003013180e10b66000340600340c101036082202ca44152664414035001d442503500501d096003042c40c1c450f1038068400700d80c2080c0007607040c0c8000042d60040da4198045042d1030007080c440c401d400400c0c02d1427801098070003080b80702c0b500030070005030002c06445141d212a045440502520301e46d40d00b01d52041d01c030780c0c601d50400c200c1840410300c0f003501603541c00e200d15071a03039000000070341d817900d022456040b004070114000f88800f28181c1c005007040e0800a1644480d107008801c010b06442c1c1022403003414000d11300c0d000016400341c001c0d0705031822242c202040e200c1078008041d10980300e41c803d0241020002c810400410168428603c0d101925003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 635850116 1250 635848866 635848877
    0xb071214010306020d090602070b01030b1003081801050c0a111c030c2a08061b04060c02130f020409050603061003080f03060f180906060405100512010204051f031b 72
    0x840d107500c4040c3d80905c014a100702d407569241070001d4418401410198081d520381d803500c0d41140340101040d2405072080c101c10112000c1480800e941608540000088a88140e801d012540c01030f071301c50003441c18040581c000e030400380e002e002c2207103009a060f0300c080341c2100040740d40b400e4007a0403404080c0c0117000540e4041003400011002401e8001091070b4505c401030302c0e0741010b03140400b02c0301c5410604c05a0400000d00200441107002e080300301c904d41e481d007401c06050500c0100540c07291036006e441080203407510040f0182c164000708895a600c07800b550f49a80f1005000042d050940b0b049000e88a827000140d111100807130781105480e80a405c0703524042018449407a140c00107002d0950042d06000000304075036a010004020a4031026800700510701543c5507400c004005141a0049040c60b00702300302034115055140a03a101281c8880c001104101d6050080c000d42d0882e0307030000d8803005484210b6000700218a902c8103665414001e0017548201108491743c190341c01800b144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 635851366 1250 635850116 635850119
    0x504060f050915040525021b01050d0906050703020912070b040e0c0f03070e100e010905040c0909022a0d0509040b0f1306080d02060415020c030c0a0b07121401 70
    0x80c0c0800c2003604251020401544158507000150450b0015541482000504c0062440b01c10014100c00d1ba854018000f83c03444481001070f8400c200f00150000341004000282c00b80c281c4c403254000300040c1e0700710904000310310742404058020342c0810000c3e07100e004030855000070003100042003001d45208152590a00d440c1050000d210400a0191501c41405000161210400781c02441c0719204903030b188a10701209205001d034601c04625284d04203c07014011042c0750f60400d4209040701c0d810764002940c000003000450348003440d40c00c50400325000003203d080e0801c03d01c401c1c0d074a00d9210058441103190703010643d0f82c2c440700c607050380010072030038444031071280f600c2e5018800c1204041e0103c2e862401c81d800107a10080200050074034199242c0702444812020031100240303103c03030f000405c42401c2c1038031000c8045050b03014600110f0740020700d188000704180140c0d171a141003a403c558490249250881d4808801c0351b109000900b02c5450001c61021409020300141c6000c41840c0d8a9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 635852616 1250 635851366 635851369
    0x906210c12081b0d0801080a20031006140405010b120a0f02071e0c0f0302092403031308010b04111c0b060705030405150a091e050901090c090504060f05 67
    0x40e003a241054036940000d00200300f515030f694a440c489004180007a024100c0c0306030703000e4010b00040c1c202102c00d170305c40e0038104001a0080504035101d00c0b0b58440c04908546500000e01c1c25280300540320500382400310000b5603544076202c1c3e045000c030441e1306200300c0ea01c03507045000c01d0082c0e0140001154010001c590080002d6009802d19140400090316000003034171503031401640ea4030020756006020400c0028400300c45d18030400392598854110b41c051458001800d80c000191000352071202c01c800d540590444400014021003002d425a522400c0800250115000510036501d6550a007640c42d81249410711a907541001355007241410708800f07548100ca01e00c80840c20032209075441038104070550303400014045051040b80110740e01c0d070030003081c01842c602505420501c6030061000304190303074100001e5000d40b1b0490b0508103006001e100c0e003ca860280d0303400f841d000005180081740200071900b004d1020303440c40d10f52250300c0c0e40d0745041c003007200c03094810135001e00d88a4005200d607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 635853866 1250 635852616 635852639
    0xb01030305071b0e071101020f07060509010204050d03021608010501153614091b030415020a030603060b220c21020304121403040204050c0c0105010906210c 69
    0x915003d034200310880c0c51198a0424880350f2074008500100d840b20420640590054016a1401c02c1000940c1442d125110301860381c028082c0c000d102c00d45074070001d02e1100e02581640d005000c020001080000300e410081e45540c109000a2164500002c0c082001c4d0414000d19040b60007559960b011b08584003012904e21a0401e13141860303030750f4210407107103103402480b078642e40000c040d026522051400c524403180252200f038860103501040c3c20400d000b40c0f00200c1422010340b00c18034076500c2d651482c0c007600d1f44123010140400c1c9440490521042c40d4903500181c1a02c0c412501008000d04107410081c0559442d2161104a0180321113428500e58a4001d000001d06a0401d0944c09100050003070041405244128240341e01004010601032401420f0080b0426800c010034940c00b9920f40356598400100003030300442e1200041034280031444101d84d182100d0030002c2120356141e1403080042d00052040f503028441c88c2038810b03c8842001c0d9010051540030b1145500d683c90080640c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 635855116 1250 635853866 635853877
    0xe0103291305090606280810061d1501051908060a12153b0c0909070303180b07060509010506060c0a110a030c03211d010e0f1302071703040b01030305 66
    0x101b11401d102100940704280d034000010b0030b03840004e4810a0f0b640d80c0784030125113140d031000d10380b00c04031501180c00c440c045400c1e80d000f22130b0686407140e007443c07180140c42501c039a600703401050b8400024107100540c441d50a030b024400c1251500200c1e80d41b4084860917200814002d446048c0d0f140c043d1414041d96888079024800c200c90001440c500907000c0109081e00c003a201c0d40380c8014014a41c46181e00384010351310710004503240209802c015080a079584002e00004080c4600c110704440b540e00c0286191b40240341414949660301482d01d0807401605081e25400d815600308170102c3d91600d0300380141c9141c0034100009140400c1c035600c94200f080b801540e1143c01c107a0504001c40450340e442d0441001d940240705942d180c4003071203280442c2040c030200f0503003000000700d240f018000c1070415041e0032071824640104107003500c40005a1011242c68001c0d8044c4400d5540401171007543c0250148a0107224403503890036039030700348562920084034001c5c060002c450062000900550280c172 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 635856366 1250 635855116 635855149
    0x190b070c230f040e07031a010618031415010305011b02030306180a06150c03080f071707030b10020c0415030803060603041b0e01080d030e0303070e0103291305090606 73
    0x1904c418180e481c40c01e00c181d580003595815403140c0401e8002451007500740c0101014a03010f00680300400301d000414a95000c020414000281c1208e5001c20070482d211000d604110080300550392880c001d4000c0a52122810014140a00d401610390011040d80d1080301d01074040000442c4446400d03c0141c00101410f9600f651524045959542c03440135100c0c02c0b03069110750801c0041c905010701030040007824106001c00a904006125510540d11040c88602041c1c441c55a11440429000750060b003101c0d6030041000c9041101140d07001420030440344094408100150460040314a03080e06404050201101040800c0710350074003000641e482402501c80e40780b01c0302d6604031069190340c0c075800700b1080c44000c4014482660240040d8224051a0400308a44011010b0041d103a010040610050100e40c03024500141d009400c010001804048000c0d00e80702210040185143c02030401401307244000300b01790400340144501d50040c0100401044681c0e039480070401001c1000c580c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 635857616 1250 635856366 635856371
    0x30e1605040b01020f030a030b0901080703020d02060901021c050d0609090f0b04030c060e0304030201140304030207061d042910020a0605060d0204021204021302091509190b070c230f04 81
    0x241a40c0c024000342a02c201f40c3d5401181c803010300c9040000091041c4c003c0581c52300301c02c0c8104016a20f00d0056004030ba03040e641070b42c592441300b0044c4d0800340e0781030300c0d03040302015030201000d115444002040000b10300201000140c1c3c40d40b0340a000c0301d40d8000020503032000f046928001c1100e038180f0984c0a80b1a25140300301c2003c41d030714030060300c00340d18135400f555002180c20720441d030304500c5000c2225880c1c1a800d06526264a000390b0302d0500d44948014001220340b0041c00e029450003106585901910500c44962031038107080302d08c620540080e480441d900200d01051401506000188030030780c1c02031294100075120007000344005443c0d02d60002c0004107900c0183c640d8000f610400c1500c60302c3e81454036090050007074056983c0b0100800e1841048591105e64452400e0500600c0d1070002c2c540300d00141001c5044841e0b0403805800480d0314100008001c08280001e200319440380c80b4000c81e60ba075030003460802c10b8000031030b001c111124190181c0c440c101800c48030365191006002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 635858866 1250 635857616 635857633
    0x1208031f0f091506141c0b041805010b06040b1e0417030a08010f0b04061211030108071e0e07050703030b10030b012006130f170406030e1605040b0102 66
    0x200a14010b40c08412515151211030761090314a08400000349a04d060001180300d0445011078144100b07084000c40b04c05c54005062042c170640c1c041d41641e20007410401459805c1001c041496134442800c644641c00c101a420090404c4400d460072100e04142107030401c00e00040d94003c000b0300107130748042c40809210000300302025512000c210140c00303028640e1a1003e04c0000c002903016003040300d031080400380400c0041030030011070b000c40b8040e00e0117030f01102e20800e484000e00800c40300840d01050100011a081c880401c240045410000019105002100180c0c0682c901440781103103030004000010107190061008100c0d1070f20234a800508250208001903c18040c0c1d1064030000355078004a018039600014001d403014401201244081c0610703140301d5541d1401028141d40040b010394640c10004480600c00d03a40d03512031b0314000004080c0c2c69500040d00644100c2e00041d0800d400041440c6d0040f500111146140f100c5a4042d402d010a101c0039010014800741140f141620 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 635860116 1250 635858866 635858879
    0x60902092211120910090c050618061809070809060403030c021c02010204050a080c030d0f1407050a021005090d1b0f0b0a02010b1f0305040f0210020c09011208031f 72
    0x40020010080f8801c080c4d05000080501e00880c103410341684915000402020800c000c50707003800c6405c225000c6a480603443d070082490300101d1116a04000007054150722040d4420103e080c02905980e00c1c6215a03d08008550840d415900f00080e42c1244001c0f0b00868842c0d0011440798840d80100e6804598510215015040e016182401030350301003014412890601a030300300405035a402410a050510000380d11030808582400034010084114441c481c059880200b117039030b040e403402d0346400b2281071003629400d810108038883c0c0d803103941c040e0169010308103403801a0030280003d2042d01d2243e80d22114a000d2224107464620341c40c90000352000202c10980c090018201c0d19515040103c2c2c01909499481036844d1040c03a4100700144a510f0810700700c02107041901d0007044586840c1007442c0044c6400308080e41084206409690003600000c08031400d100a80c1e00000a070780c0c0e803003000741000481c0c400400b15401007000c038098a10024a0140709020131400068841e40c80f44e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 635861366 1250 635860116 635860151
    0x309250611161e12111c023a0501020d1104150e040b030a0f05060c0319050403180b03250f270e0f07140a050705010b220609020922 58
    0xc01c030380d028a82e4143d00d010f82408015840d01c0d07801b00b90442c9801841e40d0005984000d200061034001407a064064480030504400d0301c42242c401560481c52000340c20098040e503c440400c9c00d5280c00c1c1034035000c144100c10100d80817140204044901c3c2d0300c91181c2240c00715005180f580c1d221f40c580a41d041159414000303102e00b00e11902009001340e4403460018240701c0014280c2120078001c0c01006000d1080f4414116500013008001610307507075910303082d03410410b1695145021900010082010815000114003501800f42e85c240b0a1303c000c0b004c1c3c05c00e030b8000c411900009400c46001c0114074092080c0042030190109811204202203102c0050101e00c0d40c04040000c055070207000303e07104d82c0d0066903080724561078141e0070300132195508400b1b849012803071010800d001070304006010080d03200c19425800180784d084c0c0048108013440340c40f030391480290360306854400c00292641309842100d0f101000a4030361103504500c030001207003241401f03a55842090f2600e80302010f515a10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 635862616 1250 635861366 635861399
    0x702012007031b1404050702190f05100c180f05010302090402071208070f05031e040f061d0c010806100c020303040b07050307030e01030506090c0309250611161e 71
    0x4403000f00c000c40c0f9182e9148030b107004000707030103008603d04014003141c203a0205030301d442000c44903881c040300d408520308024000c00a00d0054014000c01000c0e88400b90103800a013503010140d40d03140000007020954002682241c41850101c1801000412181d400b0b6000b0340f00c0300000600043c1480c0f115102c0d01541c0511050a070001100c0710f08215019030851300440e10b1003864a00300c0e04501d4942c00300c25048045000c1c80d030715940d201c030000d000c00c41081803000782964006010700481540c200303c45207103803ca01d51070130780b13005034852140c45503c2400da079841100020030202070041c0c04141038907461181a02640c00d400200030100d040c485640003010800d115100071342d5141107030f0034010207280e85410124101403c007000c0c8040e540e60509059000204000556541d403140218a8a0302d00d09001c1041007070503039002c10603a15103044036074044511640b159500c0912044e01140c0783c2943e09032100c404d40c1030314ac0074001829640700c0711030741520f4807800c0c0c170780580c0740c0a04001d900c0c0e0a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 635863866 1250 635862616 635862653
    0x9120c0307020a0b0f07060b04090f050d08090d08060d0501060e010806061c02030309040e0309040e0f010509010c0203191704080c0709020406050913110703080a0b0105070201200703 80
    0xd0040031801c1143d8403100505040070418140204031041038103034401c546000c6d000384d88a0b10083c02940c2e441e40320342443d940c0801c0e108880200d0f860300c10740340d00c6810801400704a0400005000200102d03000d01107802030b80d90b180035a0f50b034100304141e2200620003a129903507a400d000c1952076441200302c1c044d009400c0148650724150b01001448180d205a40d808500d0200d60240140c900009070f45003246d080320b022036444000022a859070065800c529441402c000001c0c0786803201050036909201100000d1003140d40d22941c182c213030350ba52000400107030310400140d82480c1d21079154810400d0946046038890088202c1002c2030724007620143da42078000124130407140401c00103000203101038441942020703d0584017428034065241d00a014034020903023070301c00180c5036019040340076112011945400f01ca040082c4120000c8501c400090b14000410b074080d8040c00c2500e0005505070754084111514840b03513049001045c80c40c007004c0c82048400303c00a4802e5480d0440d01c0c81c2d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 635865116 1250 635863866 635863873
    0x1e0a0506040b090c100e040f0e030d0e06160e15132c040c05120307470109020f0903012f121b0c0105070509011d0102100509120c 57
    0x1001ea10f00c0303040055030301c0240e00c65400646000a007503005048190300740b00846000407042002d822100c040c4c03540c0c458076000c602000400200030062a4840c88800343c2d04800c948160341c84000f203103c120f038250311070000f0444020700300e921440d0150f200280c1603058a0712601b49042d052904810000640001035405658500380700700c090310080308120303595542d010b60400d0500da243c0cbd03800d4032200d02406008103c183c0c0b44001c050710400844100740e600018080400d200d03402c1c1603002c440500301000704201783d407120800d811100d4a1204101c0700c040300141180c0d292100340f00003507111104000c0602010b04c054113aa580038410044000ca5036001c8105003208417034182c00c1d20810b401d0001c15503000340701101e100100200511342c014020410103010200000d68060fa84c0520452001207600705802c1180107035000024042e044000c0c0c9844c41a9082c40340796140011821080c140142d01400c141d020521580d000250031840000517160b1100d20030940c0d245c1c80e846181c011000b0760 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 635866366 1250 635865116 635865121
    0x5070201090311060709050910030c030c030c080715030203040201030f1505010f03020a08040212010e1905010f06060c020d060b150309060601020a021c06060b07061b0503091e0a0506040b 82
    0x5800140403051480030b0000380401d40780c202d102030003801c6c01e409858061801080001e0400081101800c0650340014810a401d580d900e49404646010300080720300c4540003c000034a1540003811206541c141050a203204059406c00c0f0025000140140c2c1010b03104d2001c0d180c00f14851080c0d503041e0140d03001c4441c0c181e04041c009014440030030443c408242c410020380340543c0c2c3c0030380815045581124400505c40e4141d4070140541844003840d411030048031038000d040c850706c01c1c2803616a44980000d1003004940041d200071240c031403284001090400301400014540600ca0040c514803c0b040040e106202e00701050300042100f1800d0503840e000014001e19600c104641503015400b4030040551844690108480070740c0e840322032000d282402802000c0000a07000030010304404120790313440e4401c46c20414003038081c00102d580c500d48400d120800c118414400c43c0d00ca0303a9107800901100120840d07009840f01000b10601c16400b60760380301000035005200f440c1c003d900039202e515450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 635867616 1250 635866366 635866373
    0x72c010e1f08070509100b120103050f120706020c0120070c12030f1d060f0702100903170c12032a03060109030305030601030b030a120f2606060d0507020109 69
    0x20800102403660400301507108115949001480c8001d039101070703441054540f1407030781d100480d81c1950080311a03400701080013102c44201214950499015404483c00800351a0f400ca4581406901102c0500d40400810300800d40070303001426a0004e810001032444072041780114440c082410702c02004100060071030601000b40da0901c098107190140114101c88e50360058a04000c90130300c001801080081c4541c41a59040c49640c0c41401a1041c0e540f005020100d8015030700141040f40701e0302c841c00d02c21030040d1085201e50180d070b9001c2e501d0202d0030802c600d5144960850703514441d461081440304d4a007140e4540155004d03001e000c07240d00c3c0d0606000354880107112103100f4000c90a0003841041080d0b0303400413050301125010b0a006a507900c541340100d010781040ca40154040c81007850380c10030407450741070300c60361179007607030340c1e2414039604a0011581e00d541c0301c8a1300d08084042900c465011180480e0a4100074014100d5140c590340e0030904040d14821610040580d55030941202030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 635868866 1250 635867616 635867641
    0x100605040b06030f01060e010c050607080a05071d04150306090c05031c0516020f10020a0b070c1115120a020309102304051e030d0e03070302072c010e 66
    0x405011500b503801c43c40c250020001d4480d0510500d03003004100016044280d00a00d50000c1c502e0b080400d4503124500072002910b45031055694101d201d25150010342d5003071046c65900d00c1c1418501d0700702c4820680b80100406402d01c8140c021149402d070f800040001c006210318140980710b002c8555441d0310700030406003896014041425503500e1101c0340d0001c1648031040751801c480703404404125030707950b00200d281c2c072030b5000949420200038090606016000039401124602c601d42409a55032000e00484050710410300c0100490070010400b001407130240180402400400c0c0201c1c1011340c9240c01880105040c3c0300f0310505039000061000308042071202100690740610144044440701e4100414461080c1d83c050440000f080400c0c10041c050010721b840000300c49001684038009034800707882c2c0e4084868062124a0a062880340300700101c1903c1103103402d600580b101518203141c140c100c06403035001208104001c4100382070210b54130651800303000e9840481049141c00c01910a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 635870116 1250 635868866 635868881
    0x2903010b010807080a09170307050c1b0a050603090f010603030c1401180b0a0f0e0114090c2103040801110301030605060a0f14060702042313150b010e0310060504 71
    0x411020804103e2419045050b15400c1a5514000103001c14581488a90040c854810030000d00001052009166201001d00300b0240c800040e50513107001146803030303814814006410342107000c06204100901e00400510f0344410004159500742c2d0044941070b01315401504114007240103034140c2c0c1d0602c803c03083e5101809811074000c1041880007842400226104074001b040444210000781b01d00d01d9980114000945022b020701810840d5081640a4130400f440322910b4040303007001964200300041c02d500910740180c214640300100c18000441c010a82d0681c0d03040d40f10070400050480024402d03000c06c4450070316095141d50540c9010403e0380c09c06405a44110548203082c0801c48010206d0801c6600c01c1608202d6a01c45d24042141d900855034040e520618140e105005c5844201c154031924a81e03107581c0d00aa0ba5044560b8600e12103c1c0028002c1c101c1020f203010a440154848202c08105050216684100380e001a117019004040c20460700d403550b100300312030b0409005124 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 635871366 1250 635870116 635870119
    0x30f0d1119060b0351040305071a07020307060606050c07210b01030602070c051009140d050d0905030105150105030606030402040908070b0f0f0402011b03032903010b 73
    0x1074450400554452881c0380800c0900102da4420b544222607070f003080f48441443c01d03151010b50815040f50121207468070b0200c1c3c110340d4080304409080451040c4414604a03c2c829001c01841e101c1d80c404031415041040d044606ca0405e1000d0440d100072079100070b20400181d802599102a81e142c55030698000c5e42c0b0201c18413005210200d10444041800ba05481c0e0721808500340742461240b813620140c041d4400750490b0498400031040c0800742d0014030880f4092a074480d481c44d030b50010300c2100400e44601100050000d0b4003484900d0034091507802d90b400081520080071001c0d03c0e2181088000b404440101c0c405003000c0189060a000d081d6122a00e841c10301d0f10300b42160006090382c0b000525883c070030b610000014003159102d0380203641d040c0e0424809500d8034141e1400507102c04041c1c4581402074514400200440c01e24180d86104690607555802544881102800c2c240d115000403014161910f0680b87d08a9541c00304c903003414801001e202145801e14285401c40b58100c5659 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 635872616 1250 635871366 635871373
    0x120f1208090d08040c0f03050106050a080d05030a0f020702120a050c100903110d060603080301060207120206040501030506032b1403070e12030d021201061b02010801090e010b030f0d11 81
    0x440c07400004910000190558100380301643d82c1d51810507050324541c1c100342e01000c0b0031000070060110550007030060341d0068440032061612440040d5072580310700700220014104000080300480b6903000b405105400d200050708241440d070000b411400070468000b42d640c0039500340c6003440410030400d60504800e0b91654490b04444034002e010040d00e00028001d10b92040c0007003200c1e00c443c854020981c0d08400108181c2d602c034900400301d40d01c00c1c03107140c006214061000c2014038000440c3e9200a0f40180f41c603260034603150054018000003000240d00d07001c1d000007407500c0307200181200c0003072507000e01d8040c03032082003100030781440003104203032200c036106008001a19030419070034860140102c9428601c1c0d07952424203481e520038440720307094050002ca28a482d5181c41d207041c84c1039030381c0c0d611001010184050b0f460307460100074601a00082c03160004024101c8a51700c103182c2c1c41c1c180c10012403c4281280400e207044200305a01e00306500440b4000c1c80b49030f100c1a00101e078aa0180070307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 635873866 1250 635872616 635872621
    0x7081216080705070c0f0303020607120203090c0d02010e1f2d1b0515060a12020102060c1e0c0304061812112106010311040b09040b0a06120f1208 64
    0x7452848010500014880c0024600050200c88600c82e4020031130a02c41001d86a00c0745402503d03000182d034110082024119030500200041c025a481000d1804c01840c480095000700421180c07000016414001c0303801800c80203841c0c59182010850f10a854500b141c82c80c0c0100070151400c2031080b80d1542c61080c0d084000c000c0c0740034050000079551038420040d4101c141030700e942d0144400010700c230344965000544810304d080700751031003840100c601d0222181d0b280c2d0190401c0c0c0e900302d0300a0050300040c001407075502c0040084c01ca941c1a91001c12101781c101c200706409a840f0001464084c2e0010a041001d1503008148014415000000400d510328160180340b4169014400419110041c1e2400302d0303d40301c1c91501c80c1d60a041e0260b20780103031505112152101c03070a000c15100b2400c3c11074900c00d103003090302030540c521002170183c07007443d505d64881c00d41005010b000792283c01d03151240020b0301a141802414400d000301001c80100c44245042421794218041802c103001d100d03000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 635875116 1250 635873866 635873911
    0x638210d0e0306010909030813032a0b0105122104180204080c010302041a03130c03061406011e031104030615140d080a08100905102d0501050a0306030503070812 71
    0x840c03582024542504100d54440b03407502f41c6010300741d10400a0315065501900300d20342900d0240c00c0312240209800c201f1640c81d9401d11500a408000d40741d0164460424003500c0007076910184024202d045a1904054440340114140d000f11440c00c0001500800c050004080500850414240c2401c0441c6081e00c0e0100c0d0144901c480100034001c0b0345c001c000100c00360021360070710344078680c03140c90b29030000c3c1c0f030345170242c003c00c514015101d044034110b0000c1e000e540500d0902404981400d80c00d8242c4041c25400c078068a080040c454090301c0a100000008050f409501c80e46205c9aa500056600784105c3c445011410540c1911803070070503020b240400c03d4002114050324080ca08034406546650001c0745600300c1d03070300c401e460b10b2a00040141401d9111010f0041c2c400c118aa28443c1d248101c0401000001d03003090740f0110381e0600300f0040d6600440080c0b03940c3c8558140840c60a41e280c076083e046402240094510890001d0400969040284511b80c0031a18121a0501003121007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 635876366 1250 635875116 635875127
    0x10e07121a04082a01051b1e0d0e070611120304060504020f090907060e0303090a05100216060305150607050a0305130f030638210d0e030601090903 65
    0xc400090340410750301103024010041e0854041070b40d81c0100a240255510350755081042c00c0070140b219501c0c1101040003c1d13281c1160a9000b500101d40c1c40c10204101e5107107030420302d1400c3c1d05400100820000d00c0e140c0c01070144807000721400c0c0240110350704d0060050700c0402c0800b40f85401d500403401d01140306c650b442c10759400681040000407240d445202050704a4954106240d10469130340070002e0203a00011600161807003541c41c150103440c10001c0c9030b130b02d005c2c5030b01c501e80c425050308042c015802c0201550800b40c803207104455600c02c0100982d860344512703400400029417a0800c02001d14018000d0300b645000507a44186000700d036446a644030300321480000c0412000284100e00a03090300c0000c8007814004240c020728950341e00d0000010100920310305109541c0d202c100d654480d251101c0070900c081d1380080d41c101051081002590046410301c64000303a010b650514501c1c0d01005545000c04485e111a00b402c20401c1c100351600c0701c1607002203403407420300d000b1900199110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 635877616 1250 635876366 635876393
    0x1030507180e031b07171b0414150f0d050303130212070e100902030103150906200705070b09101803021819020f030402010c0201030617010e0712 64
    0x101c4403140444a50001d000035081a24660380640b00c007150740460b1007020400c20754021402811243d080399114a549030280d80a1a083c185d81c1107000800780c61501c462924000c590010800108001c00e103600c0d00c0f0003041035400065803203041e0314502c51424003624507120301c0c0c01101c108003d00c0d6183d4419540b444024499141c0c03030004802d0030219241c0404900001c031007481a20013654568840341d03650740040300c90821100d010b2500180180942c42100e068a0f040b00030301c00c0b40c018242e00c00c0d028004e840c8044894a54840104054079225051003055840d80c51a082d911402800c0c024503110854005c00c01c0b5100401000086a490b040a18003041282c10828410018024000400d0301c075580080d40100d403012040d00301c0a05440c40920803460040c0059200002c82e542000303e0143c0303640001030310740400c042400b540c02001040681c0c1d105246c0801e1040d19800c2e181c0a81c140c244002546a44504e40034104940c1400800301401200e01c0020034005181c80358032480005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 635878866 1250 635877616 635877629
    0x1c11030f071d090c0903011a013006090506030d0315140d050f03031e0403051806070f080307030e0c060406082203020c090708040c0b0c031e0304020301060e01030507 73
    0x11591120420301d003020003080c2c00c00c4010444640c0e403605200c000341310750082d18024400c2d464040503a011545c1c1c0046041c2c280d40603074039401800205c00482664a01051011001c0ba070b9410f20182d0041160084201070120304c10041043e08210b0300781442c05503502d03580c005150601c03a240e41e91840140000080320800700800000c0f206a2000c515030015807100035102c1e010714002e08041c404008021341c043c1c50348202d07040680c9001c04403840a103200340c41c0140050410000f41d440a03c102c600240171810041c8040d2422025075074800888451100c00c9428500c040104000319070584907122454200d8009000e8004076140010200e1040e030007490b044c04601800b0810340d81d45c0340440341c8035000300c01e180d040031140c0c0c0c100a5074410641d4003a5115582c08000284500c2c803440c110b0740034682c800380c01c00b5501e081ca0402942134101c0c0c014643d403440240564076611264500300b1039624141e0702e500e9500e0600b80107141c2511001c0e081019640551401040050000991501203520 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 635880116 1250 635878866 635878877
    0x30306052d010c2f0603091b0a05030d020d120603150c110d020307020a09020f0d09030e1003050907121a04053910020a020405060a05061c11030f07 65
    0x7400d000680301d540342d1400290403444851424030305401c0c0d02c88040c02c14010000d41c0d041004081d410064144800c441c1915143c116003410b43c6480d004266460171160002c04000c41240c607840403070700c2c0c07502d140d04140040e03021180d911a40c91704060110340d43d0314110000d10000341140c0b034001d2550004d4080c40811503607880d4a64905210b4000b442001c0c281c80282c900905d480d0400940d26000804207a1241082c40b4000a07005513a00c00c0340d07118540d41c001d0790b00740501400c800c0020000458180c050021860b00c41c0d1007075580007940c002e085040d850008840c10141c46551400700310742c100050b1903a040100101140c4002030242e00da44040880480070b54440c940f042c141000ca2110441e0b10102a8800c070000c4044982030714a609003040c65075031105100c0401480c82c0c4196401c0016801440c914405400e158100300d41c0824081d120250203075030cd101003201e40c0d0058010207035140481c0603a0a030700400f40103c1c0c0c480f041da14912b5065090034038110046c108007412000074000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 635881366 1250 635880116 635880199
    0xe0f060306060f0307120507090e040f030c0503030a0c02011a010903081c110901081605091302120403030c14040b0301090c0e091015020307200310110703030605 71
    0xd4500088a288150111401d07403217041528000d8690320118a00500e501c2c208000200001e02c00ca0540c8102c1f0480708001d070f280e8441e80c03a846103240c02ca40b400d4040040072098000451f030100019405000c2030100001c042c8070480000b0b08440345144494606144204490321a0780d10600c0542900d421010055695105205040190081198104000c2c2c00c01a11111100080010340603190003030306d8041c6681e80d2140e000701c4c200c00d000031280211300180f0120045040c11000484001c0440100505d84403086a1140212504880450000303171100000d0a109074490800c142d81e40845145504090605d1100150b6001c14000c0034003c80e91064013400c1d99100d25641d85480710054812a4141065042c1600c40c00040c00b40210000040c08500c12540c400001c8070306507a040280000e12410050f21103040021003e2800c2d0700d440b99603081400228030b8420b2442c1c2040e40d0308010b80d907110500c0d0103829604c0c81c0d8011403140b8010150941c1c403420300284101395620b034200803480308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 635882616 1250 635881366 635881369
    0x30610050118170c0405150307090b010e040603150608120301140402090d03080603070503030c060a0216120804030305070503010311010c06150e0f01140a0e0c0403080c0610060e0f060306 82
    0x50b101c07948000e009200b00312a8440d00319000c9203074038003180207072401c1c072099480343d8603032074591480d43ca044e8069004080c00c10004003158890041107005140c40140780480e034001030280c070580d4000ba00c80c8000d070303009100d000c6d46500c2668001c0c90b00c000681142040d0100a0b102c6001c1403150040c01d025440003e1032030381c1c850307048590480700103100074100c8015040c001c00300c040c12a80a40244a480d0f40071881d0700e03001041d1202810184d0007003d01c0c1d511040c03c0c01c080c0d08a407103030032203174560018860b0001d001051f1061600801e59940021850981801801d1301c10141900d403d0050400043c0080341031100c80468001080c01c01d42060340d45403400070300030320000c1043c1410207503200d80429003200d0240300c1c82c042e150440c2d0440d0644d03210250700c4031903414405100d60012601f14108840c0d0012003110307600250170411581419925161a0301c02c1e40701603860041e0b0380080d010840d40303d0f5101c1118000d1300c11031404070b442c41c3c5810082644d1599005081c1e100310004000103555 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 635883866 1250 635882616 635882657
    0xa1508130602181201020315010c020d02030601060c03080106080f07030507020f06070306050f091012060608060c0a080907080d1d060a0207150c0f030507050322050f0306100501 78
    0x203510000c110340c1c4404510f03221a40c3c0300d0002c10540f00e2403c61a482d0120304050084d41c0c010080628101010740a107001564004000310f400c80e003040754050f0580240c0e509003c114001d00c1e4a45815042c010a845d00030004001600440305002084c0c00303004002c01e03c2c032040d982c0010541070009217520b840c00141c2c5041041078043c81203115503010800c00c168035422075001c0b150285c400010200c40001081421001211100d5014810b41d4040060f140b01040d80c111041c042c1c0c0300018415103400069023020012a4072004a80700016840e02c4141c0c0140070590021411002c0c012140c14038542680341c0107092003900401a02400a000f841791010500c000c440d8011710f1242da403601003001948414040c42070f404100072208512041c54001d8078441426075005850100b0700500d039600351003d400c80b2009039000d01c401c1c0241100701c1382071102d5030f211035090070752034050602d400104003004d0244250640640c110006009080560038106001d6403004d0a01124050301040c05156 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 635885116 1250 635883866 635883901
    0x616021005070207081b03030a05090a0b04030303061a07050a03050d06080a210507030e130b040f0e060108120909150d0803060310060617100914150a1508 68
    0x30058649000d00c0005a000500d51040f41d544c8400d44030f201c141e11402d05415229604060b4244d08104484401c2d1071140e030051403039180003024001229203c17100159550040c1c4c0044010980d40c1c1810700098100030302c80c405000c66049064a490015550b85894040c04803000782880f601103500080d10a258021901500c228411100007241d0b504001440a0981c51064103603200050032005280c031680c02c68040d5901925498803250140041c00803060b40d00c042d00d0b024503510800c160207540c0f9170143ca800c1504451011901640245030f407800e046045e8403178400ca80c0490741e6450350369902415519044c030100c50f1003e4681c2c1d00c844542a0865942c20300354414003031b2000c10100440b4101440c01040d05508459141143c0d0000c01d0499500e0300444012030040f03c1103000e000340003104036074860440104510107075580d200001c140d81401d110b401d0f0300407c120400401250509800c141c40b40d0031100d43e00410300c2c2c00218805050b084210004000400c0c00007442c9002c3c1100011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 635886366 1250 635885116 635885143
    0x40b0a050303120f130f03080a0b12011d071a161e03080112030504090b12011109032a06220e07020d0915051c11070209010b070302061602 61
    0x1d99808009655400c3c1c150226500c0000000300c1e8003003581410004038001c41d15900c040f03500c02c1e8805a460a8178800c0c2c0042070f45540e80e8851000d004162603e41c24903401d15200300000c00d0a001228452010704011003541c0080d6101490400000280f09170310031007030001030b03a80b41d5911002c80480349800a43e10000d071400c4250041700c80c13081c81ca0308818102030b000b50303107440d1180d1f00c601c10040034048204010f00026020320050007145480e03400449e003804010b0000070003058803c001d40c00d448125060944922010580350b849050500080c40070144450401c01100c01d00b205001a038140b284110b030040b20080340c2103e01c0c00000b401c03120700c1400301503a501c0c056038a8040c2079058404440c101e006005003200c02c0d50082c0141d4081095410000141e03030900c52802040b10741d034010703085102c0384842103032144440150911841c0c81c0f503100005000c2d568011401405100d4006a100216000d420881a00801e0340811007035003041c01142a036880c4280e040049150092409021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 635887616 1250 635886366 635886373
    0x14011214030301120c0b09011e0224070e0d0519020604030b0108010501060e12100506060904051f050a1410050705010c20030a02070b0c0a0c0806040611090d02040b0a0503 75
    0x100e0f00800e00220b58203041c0c400c00c0030300d40c05500c4403181406c501503000182d012858442080745800c041d40f203034011142581c41180c600c901407001459490603011001c0c043d564403001840000c560101a01e440d908091b14041040701c0b4581c3c4491b40c6e05081030000d600f485040705680c003150382c0c01e003c03240116040290b04406584940140340208030038800c00020420b012900c04041c14501050141084070001400c2504c01020034100a071400a02d202c0d880142000030a003a0b903124403415008580a134203000d0400242d41240c9000380564210340e2080300740440412201000e103455600c000c000343d9241c0f9800c4940381050740d06010301ca5004050307501700300c2d43e807058135800903c0c50405404684510884088a000c00d9280d2143d44401300040e003208600303015a100030b10081c03c100202100301c98400030702d03444042a075812908a00400e402c41018401444018050a481410084403c91405d01110001100b266100c40300a014585802070400d09956000d540001080d018056 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 635888866 1250 635887616 635887619
    0x5040b180901090204060e100509040c03020c0321090705130c02030715020309011a03030d02070212010912020708030f0301181401080a0c120308190603021c031214011214030301 78
    0x500c011750002e0143c2000950300381d46001c19890507a807003410b090f00c56100e0901d081011810b12020780006c159100a0540070804202c6c1c49170104002e2484840c0c0c450900000c0d409420464001e800141400c40d0b07661044400b807059070707224504001c4803031002000096207040203200b64114004c2074070140481140e1003020a880e04e040d0025481081103400800c400d007007294800100066100320b05070036600c103102ca6901d0302160740c000c20350940000d1070a4401c4204c103d402d401d4860205048072f090300781c8540340e000c260301003100c90b0103010f04001450070314600d2900b4a00c103000c14401c0c040e0000b414501d24030008801d0b1b204c18950548201c45548541e100d90b100e59480507082d400712a1045c0c8603200040d2440d242c0030451103030b0f516661b86481501e648d085d5402d075801034110302c8c0303140740e0310700f0000010b0344c031700700140142d4024410984500100703040c06400702084d00c40a600c810b007840452241001654941419030700c2c4202c0b1310070600120f003400c24200102031500c10552200100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 635890116 1250 635888866 635888879
    0x604090608010b091005011b0602070f120e0303181c0c0501020d110a12180305061504051510020f071205010b06040e07050313051c02010e0d05040b180901 68
    0x1200c0151140300c4001e000000c104000d0203680c503400ca840d013100c032400450600c10756105008468071035400e068034088011503920740030101d0740040d50444055922169810401080791103a4000e0906d80c185034044040c110042912403040f5940640e00c40d2040655071420b940346070340011846170b2504070850b0620300b031801c0500400030340100c0b4094400d0a01400d041d5100d402c0700f0625886600181046660b9541c0300c40c421401c01281100b803240700012803900c01200041da1001718040c500621081c01c00345480e04102d0420070b045401207060070708005201040c0003507540b6182042d10603d20039040c0b2003049040402c50070f01541c880c081c1c1c80e000244d4444401c00908861b0146008000d8404200c08201940c0702c0d911a8110b00e0103104000791246005502a6600002650304031206030000c0d0748460824040d901840c03450f454551006881540c24401d040c40c5404890060200d14420310000d171007405244680702d541c41000403042000d21030030a003401c80c08005452505035507141c18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 635891366 1250 635890116 635890121
    0x1c02280801050a0f0810020a0509120d0909380d0609020a060503040b19020403140a060b040510170109060504050604140606060406030e12161403120f070e060409 71
    0x401d852280e90510320106200040f1a13041c1c007201c0c8118004d20700c020341100b206019411031807100702404021310100b419501c940e0004110000007001925074040301d004081c110071850f8100a919901d040014030f01b10800006200c100d90b500000002c04440c007000448007614040d010540004082c00c24804012a540018202610807100c21041940303902d0308641600080b500980800c04500100700658112a440c240d600f000f0140540380a40b05c2d12070f1007024800c4440c5416035071101048809000152280d42c3e000c00b0115030600407411b0142d5105201421360240101502241d1076400c1003510075400725185030381c0f00c4020701191900e403c020351916812035056440b4001d152a80aa140c004985944101c1000344118101418100c00b20003e00c1d0310559140c85201c1c1c0ea150042d03d9a03007401a02d4404403044140c50186200d02d040b90700c0101c3e480308007805500c01d100c2075030740d500c40786900381d8050131807210706000799610942140d001402c40c4040da0802400100850030010f0f54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 635892616 1250 635891366 635891369
    0x103813020a030e01152106020708040608060a0305060a021b060906061305070c0308270c0a050f0a210f0302100513020a0302130b06181002031c02280801 67
    0x50b1000c100700d0140e040850709031095010b4030840f2134012407046c00100075014614040ca803002101c0d41e0010b02d1607881004903403100f6020f0301c45840106040100716402803419a0000301620303151040c62030750740c5041c0d0b21500a096515815000300312504090100300c01500034110b040c08031800c5003840300805d5203c03030701070302e21078003076404004000e450540502070780c2c3c010f0f8520380c0c5c0c4503e020314030381b021220000e020f882c2d884100c0c850302c20380d91718289c402030003001075010001420300b00840e401045200c0d5641d60200380200f0b152038923900d01c0d07a40c207200c0c070045501035200f83e50300070201100b00342404488280140b007203062041d48810701d41d0015000703100040f004410071842c1c652070002c1c0310800c0903004c0294006040841031006050030241c0c0d8490060040300803882d120400300280d645d400800c13642c03041c100e00c10050405072510384500707061410319002443c513040b41000c1443d802d44e0000141c20005400060740c8000300038078000d03001c03000406460b0038034050784144000c2200100303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 635893866 1250 635892616 635892637
    0x7061a240a03241406120708270d020607020109051002090102010e0703151d1009030912080d0606170c0705161202040614010c02190b0a05040810381302 67
    0x30f40242d00005e060420032922280e140790110000d40c4d5404000300d4820500808410070340c12243e58815800f0303a4800f6070408041c03d000600f80e01c02010600a02e0a1002804601107a05112601000c1503010a994003003081038a03000d40d075000c1800050780901220300f621103c1d44240300b00041030041e9242d408a000c10b001d1418007000081c0840001442c2c2d82500340041604521122040000c895000b070400074400e040400180d603403062500074040c0410301c165200b040002c2c480440e03140c036200e42c101070001d03810801800302c80c0029a6800800c010030600b52b0a0340081c801040c000200a2590f40b0a040040c0002081e25968610144805010304a001d03d00700040070a0100000c0300701494030106940303800150141c0d070208007040c0d4404140d800462a60400441d07400000c0c801408034194946900340d88500e413281e0649001c07071344080306441d145401c0240d140d42d10486e60343c0000d40d00621100d00d6043e01c9002d42c0c66102800c41d070342da90041d000b0010103c032504a40103884510720 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 635895116 1250 635893866 635893889
    0x20f07080d1403060103061a040513051e07050f03010f05034305030615130903090b07081207021b030606090a2007061a240a0324 57
    0x6445580c0381e900d1000304024804a418010341e94400365018001e103502920516000c9200d0303035568180c00900340d402560030b546500000c0d050145003000d10344d81060665140040101c0d151a850b40b50310300d08120b494650014150340800e54003031103907081c0c82000aa07002c5030b0380d9a50f514042c0c00444403981c802d540c0280030b40802c000001824564140b0030258844604111062480242400482c144c40840d040c2840800c0444c0c1c980b020000507106014100c10b1142013030461f410480005114035a0600305414100c1000003c0c1d0b102000741f04417051421503948800162410b80d5070781c091241c0700d070b2407034808030304104074a5800150718194100d074042c17040c0c00a107000c00741030f201c0008441d425008020704011642d10b03840d6034072803661540c10507c585a44400080012200d602c03401c01030340e0080e10340135079401e1480c0710408070011020455020300b25240d1040c075400d4a80d01222201032039080031414901241c02908420380e01c1041491100003051a803003464416503150084900030003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 635896366 1250 635895116 635895119
    0x7050102161509050d03020f0c1c031404031b0204020d0c020a021f021b0411070305040e070804030230040602150a0203040309030602070516090203060103050702010203160c020d12020f07 82
    0x50748141000c01e44c101c80680340711258403205030b01952004d0101a91014200315400c032018061203500c00c20707802e4101103140c501803240024140c454582408844003054814007000a4001c50380b4881c003580255250700340f0b49a800000c0003401500710000b00c076420040407240071036002c034858031010310885080d1030a001e694180035208508060041c05a40160742205180940b071224420100e40100b0200320043c201c001940240c10030700c01100031400c082800d004460750002d8103336228074589080c0c1054542520000d64809605a8901000d0300c0510340c00405545100503030405030042018070f58450707039440004d649002c4414400020843c400102d9085080c82c0200c070702458041d50340100440c11034a54100035841054119200d01c6070708010310700c81400e40f1110002700118000103840e441d080b00094141c4100810711411a441041000411003400961640c5003900e4a8240c0d141d082610100d020001c6401c1d014029140c005001403556900140e045283d06000c0241c03603616 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 635897616 1250 635896366 635896403
    0x9030b18100b0307051203040b0c030a0314100308090328110d0209070f050d15030b090d050d0c0207410d03030f0b0d030521060a0308030601050705010216 68
    0x1d8003288031280c1c3c1500005020845442c107021704644600308003046d60718041d923589241910360301440440480c1e803c0468102d402c079815101c6e0b040c08070388403800017000b407500c80c240c00d529540c80e000c01020710001040504241c3c030100300c5003110901c5d0150568969011030b2030b0580720084c100b13044030030100d004400d50035802c1486007003c0701680600310020380c2e11003410968215011400c40780811800744030f1211550014004c428060304c0c41c40c6000c2d01d00313007035003002103e030000284800580d0b8058031101d044640c6c00402c4500c400f00ca03840c00180c022844004074245034040d402081121040445880d242180800f42ca122110b0b03100c4070590303803030340303d04102c2d0b00c2c04030003061075022480400d40710100303004c1d40111140c1070343d10000049a80c3c011000903028021448260005600401c034103a0400c01c4240001c2180b10400d0030407081d241180001c0c2015a1600005004c000080040344150b40504180c1d400030798800000d40d16403000c0740e0303495110791038417100359a6940b170042121882e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 635898866 1250 635897616 635897621
    0x2091207080c0607210804120305072106090f05060f100509100903081306090503030405130e0304121b09050c0d0b011110050906150a030609020109030b1810 69
    0x3116488400307400702c1c0c01c040082000319001110196105a05500e210b516030301d0071881281c1c040c8003525840e62908040c01c05650744010310011400b81441d14051204854001802202c0b00c1e20702c2050f0402c43c1d4101c60500c0c06002c1a03400b00152a050144c000081141504650b20400d810340d250f13130b010541d079030400c551550b6403150000401c6081264000030704225000c07502040705810185103141c2c1e207648135038241e0300c8124500106d0004110500c40194003190940007428120000c5081904048c000707100055801e151030398403607452080400782d49091003514010306080c0f00c8400044090309144030403464840c9841081d20048170007103941701c864440c0324003503100c00e54001d041c4408108510020718000d00b060741808500c03100c6000c0080204104500700625100c041842c0c280102d4507403401402801c55150700c191540710000c107454070f466010849401c5940460684041d000690380024250800341888064908000d001c0d80c24400114101c5811001c49100c2000d100b4031504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 635900116 1250 635898866 635898869
    0x130c0c14060c0f0304020607020a0e0601020f1216051e0d020606060a05040302090a0f020a0203091203070b071404150507110103050c0301090b060906030a0e100504030806060c1f02091207 82
    0x7840c59040c041c03c0343c5030720072002665010b840507091610300011038000036480450340d800481c2d45c804080c1009840c2d40d05000c040d100c80000300007000144003c00808180780528014958078501d060001c00c2406810011000c1c070341c0d01030308030207174509602c413183e511081400501d002500c40c0b50040749031400d00e0000c55800402c1540c03a50304080c115402c00820072406452401030ba900d400140e5554969071005150031a40c580046543d44403504c10b0100601d03400092900b550400e0011502003480208802d1b071040740380c44c24440c81c1404220800442c01b442d00180c0460560507a0103d00079080b8000341400c0303008042803840001094011000c0e101c040720326482e10131007400100151100c5400a13544410010070860400716010040390103904221500c1411360703110b05c0a079012040034011001c3c206000c6200380103a00d0f25803009024120081d100318081c00c00010803281c41e401c10701564028046180e441c0b213144041d07984507006034202043e5542303d5142c4401074000200c0000b034000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 635901366 1250 635900116 635900131
    0x20d15080f030a02100f020915190201020c0a0803040c03140115080606010f0f0512040b0609011707030b1306091a070207140405060127140a051c02130c0c1406 70
    0xd1005c0d00d084496018050b00603005200c41d80034407941d01140d0b030780b441040e0611580c500d00768a0f00080015016095603621540c41903901c104030101c0340c0040412035070401500092407035030301c2e101d0f4600f603056541542d0000d40704680c0500f041d0324503401034200c84201e2096180340d15030305498110b49a2100e00640c2c1c181c1c0484e42c0ea0456044103402642605d18288075405d0180c141a00543d6000008108941c11103604e80c40204000c5145031866160340940242c0b200100d038444603035039065031403106020290003180070000007204843c001000c07444043d8801010b00040c0600d24050708100b0449451103640710007000043c00381c6200017034940450b00d0003a0640f95400000040c88014040908214108160440c2d8a190400001d055541001544c8031400c1e21764a403800c0441c4825907071503440d10079a4405410071141d551005014000701c01c14190060401003840001c8691034004000846107041c600703034010054100003034060303860051680d100e569503003201c03554541d001180c610 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 635902616 1250 635901366 635901373
    0x606030625030c02030904020c010f0c0905060412290906150637090f0608010f05090717070f0e061207200102030f1f080304050402070501020d15080f030a02 69
    0x45201e14400d4001041c0b5403101e0041e00e1038a0381960104080e40d000442c242c5031070303444809030715034490705201c0c1000b4a4154a00417044500704400a9080d2189100b25060900c5500c1c00360140711007240318582800c50010941ca010b400d0421241600f14100d13070b50a04c13400303140d002407103212054904c400a17400084c1110301e001c90f541a40a51b01020540c000300207800c482c880c40b403000b690440350340f003030000740c480f01d50b5245015030340b80c003022094000d1003c01c03041034010003402849010750f8041c0c0302e003251004c85a54070540210360300d007001203210b00c0c81c0b0304040c10f00c280c0507040802c7d517201000301c0d641c128420700750030180505841004842c80c260742e001c00024070001d02c0b40000d41020b0075459124240003514420706402e82e001a142030704052003c40a01203d98020421a008100b03500407403030900e45050b414039103070300851040794061600000d0050410000f94101e0b100c40050b48420824900c104001c10b041c0d1500f801012014811070300e10281c840000810f07281c8010b520f6004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 635903866 1250 635902616 635902681
    0x10302121b13150314120702010c0b09030904090b0a0b0108090a0212160b0406030b040b0306010b0f09060c0a020103150e07050d1b0201090c050d0f0f080c03030906060306 75
    0x51248402c0000540511243d030340d400550030400035200d0100450040c2004249040340740000c0e0b04042c0080e0440c0c40007801002803c1c01230746c000017162626a003080580c60103607101400141544160060301e0b6006d86000e400ca8100405500c4003030141b46c0304401004489a80b20064450000980d0b44151a52000942d03000600d041081a034a964501e41510070030f802e001d43c519100c85c40c6401203c90301c00301203006d00825605100360303035030b42c401154244a581100408030b520782a06000c0d91210400c00608071a45010701800c942e280c640242103103548060242d80151608421034041b40000d00305181506510f060328000015565002c0e14240b0b40c0e244c1d80710a507210f030f0049100c200301e6611081c1e01400d52200b540503104803006900007081c841541e2a041110741507640019200312095140800464026109103102c10303844000c1c0f441d10340071401c02c004940908852154648800030801c10034000200388140900c009808503402d81d101d81e00401c401c5480c505142140d086407812 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 635905116 1250 635903866 635903869
    0x403171003110d081b03040305030a020607030b0f100f030b10020105041a16050a1e0e010f02010501061407061103041505460527030414060a030605060a0305010302121b 74
    0x5c00282203003050100c81c45c00d0f5a07035843d05e0440c3c2040107c500941c11010800424640500826260f0300c81141ca074007030400700c200050342c80c19850441d10304108040045125040c002d42c09030070304140c010300c518040e40000300000d000e803608440c200c64004d50140c1103840c041e00e050910f030084854460950000d141320000b1602508500c140350200035424040000070340c42c1301d8801613501484c6c0d0720500c0d0342c2c1444001400e1240c0603299202103a2400004100a035408034041c600d00c035820103525587c0c0c039241800c030094240c140000c0c440101c00014081004585200c280520110820500c103580d2404071400101090241d200e41c03803410710342c100d414004140c600f074078081c017010b0304403191115009146049540890b11100c3c1c0390751007011010070000407802d0f1008825400b00443c5001e082c4a130700440304042091450140001040c107049171b9000e47c00c01c1c0042c0002502103500c629a282c0002c015107428801170b40240c030b58400300030107004003140c031008070b00c1e18280400e41083c5510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 635906366 1250 635905116 635905147
    0xd1a100e011107030b1009050f04050316050703060f0c020706030212070c260c1623010903120810050d1115160503190804110402030403171003110d08 66
    0x10b0850014020300300040001a005078030980100500c903007202c09581001000d10450f00060589043e86c1102030400c400240000201c0e10051020030900c00c60074020710f4580c2c502921078100611040c2088506091005035521651244280e6070840d01d40c09e644080c00d40803403080e40f42d120071081500b000184814058444501d84601c0f551424543c03800b44c00304454402c0030b0325a00c0b049a000060341c0d000b00703081003011194101f03c8003000107079685800911012504203c0304c0f000118011b803080c00003a0700442d2040c1c021500a910561070300107807031004202d1102101c0e40d105102c242280131900e030411a07240742c031840c1e1020240d5100340014041100350041e40c10340701c216040c20043c1c50400c0c0c84031500e0380c00c2c0070311641c0115191402d80320804c2418803506006810000d80c28208008104000554102200240c40044e900c2d282e906040755041d84024400703000c403602c841440114049180b0f408101d07230052160300c11604c5490704001a880151a014005100601c400707441d150861 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 635907616 1250 635906366 635906387
    0x1e0213061e08070e0310140709080c04050711030309070302090a14060d050f191e080a0305040c03020d15110a2102091008010f05010309080712090b0d1a100e01 70
    0x2130402c802095080c00009181c440300c0c00c1420080c98031040e6266540034032080035500f10141c1d042c80482039050083c00c1e0340c3c4040000c0f80a10490711075010841e002d0242c0307805c845100284080d43d80d40d103004d520582c0d6614080c03100324042d41d58400020003255991184005c40f0801c2004181070341c560100300102406100b1080e145402403007c1649107010402c1007464403c50b800b160b0500142609200c03030284401198070300304501920800c00082d80c0d5030215004c03d103903428002032a0703c50f414040113000164100075000596110341500780060070481c8120200c10800500000310f40d204a80c140340201d00c59103001c541691a0300140500d41c901642ca4214603403c014200300d0b400c0002000c0c20054583d150200e0703529030040c0150722840000e040680000e003001d1004050301c1c0c0d160141c0d4800d06601800540c20b0041c40101c40e1312880c88107008101003500244c0300c1c0080c040000c020080034a1340d4641d0610845024030a090881d01d5102c081001e80f981d9642d40001c2d0010f40e0200c810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 635908866 1250 635907616 635907631
    0x10c0f0e010e0603100e0c0a050405130e030417190b190f02030a1509020f0901110109060c110706140307110f03040303030c0e010203030f191e0213061e08 68
    0x1000082000b83c6608024600c500034611051703031203c1c80d00005003a48003000d000400c1d150020025013060542020803642220b01c1922a020f081c0340d074210801c000c200c011204c0700f55000024000030380b1044082c02000003c4200155204001c1c558602c003400e66408034001c0046040c0800900c1d51050510308150100c075845e008201c1e11818a103600072a4400c94003c100c443c0c1e61462180c0242c80c00c00c00c01c02420014004615100052450813035602a28002030304103c01c48404030341041003074200c8c2155661026051204420110010701950f1050010135080c0c410510001507075445000e01c120100c0e00310351098516180c50204964500d6460300c0d080c10385c440c842800405030000c100600046d0300a580000d01ea00c042c0100a1600d620441e40504550091040c0030b40545a4480d0581006c50460600c1d03030ba000d813401e4080a001240c90349090000709480000d988580c43c1c00a0500780381101e000700d9090380b2400c00740c0b00c08400140c036603000e03070b0201b0428010902490301250440d85 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 635910116 1250 635908866 635908877
    0x80913021314060c0601060e01022805070501020d05030a201c0f0b01081302040e0d0e010909141501091a030a110703021c0c0b04031d060901050a03091a0103050a03080108010c0f0e01 80
    0x401d9940800e200d80c0c88400cbc410b4024522405002d00c00140407200142070309101400140c00c1094004059010144c070b201c108903990380301140307800a41400f0340d01101800c0d0040f03072a110041c18840c620345030481054040e5060100702e04400314940f182c0701032043c058440b010f03c7d40b0703007803204004125807000c12608103a46803a4090050342c100501100442696604080805154001004104298881000c050070800120710b6907140300740050303100d4034600f5503040c280381728070040301c1815140d48000400f55000d501f40e90f002082c48000c510a0a0044041c04895010700b50000a4442c07000c000e00160042074408941b1101c0001d86010000c203454404c0c1a0240750310381c0c00a441003610220003090034040d48208200003c0016031054104641460400000e0400a89076104400c110390070540d640d0500020421525551400701107200f1342105c1075a1207181c100e5485201c108213801040303180d000000e07080c80501071790800b240c0b05e03551250000000700c01600c0d040b00d00c031142ca06011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 635911366 1250 635910116 635910133
    0xb0a030f17030103080705010b24030a110d06050102070e090c12150106080f0f04030f0f270e01080a211b0b01140a0305030403080913021314060c0601060e0102 70
    0x4071640c0c05180a07600030021a03550381c09902e000340c02c40d80d02c00b507401d0241d58180612600a0351070f031400c0d0900e111102a07503a0701d65404284500a000d000020b0043c0000482c5002001d00309034040c0f4203580081e003ca80c00c19855208003a25280c00f143d010180398003509165095040c45112541c03da030359841151985d0070341c0002925651026044040003807040002c000ba503001408429030099641c0747d85c0340150400717880041c504141e842d01882403004111400035054800c43c0c80b8000054103800d40f00840c18100d44400c0d0a00d06440340130803121500d0004900310078013048410000d40d100b00f10203406405444100d01802584080d202800502550107a102c101101d5800409100c0c101340202507050000c40750048080320607450007040c03515001c1c00021000422502030369044110b00b41c4614100000688250040c40140301207400840c00d4407114046010203410f071a41c3d1404060601032040a101c11070042c121207810907071286004124042c010742c00040310b804180705599949 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 635912616 1250 635911366 635911403
    0x6150c0114060112090f02040c11010510030c151b03030f051806070302040b251704030c05040b030d0806030c040e0327060d0c0c02090f0f0a0b0a030f 66
    0x141e481c044540d00d001c610300c04006142d030303010070304059040b0704040803c09410203894440c1400c03090f943c02409180c1e194880c01d00c05000d850680c0060403400000c1c4440c0c90084000d5449031420f1208070382c2e01e5070784100440c01c6ea4030301e8240105001d81c6c0e903601c90a011b0700c004510040701c1024054050682d1440b6507800d0804601440d48680e0901203006454070350004002d20304403008042804142c410b0105200320030034102140e000d02080141c000c40301071082d140e0031401c45030f001c2c02401030280c00c98843caa03100c56805482124042c011483d1204d070b80c0e105010941d003c4054581c1e15800441d090800540900001ca8104001604550b9038010180100d01140c2e1400840c481d07030ba001040c0c1c13115503451003440c07146440c40d0f8082c24030364440400100d50300380148640e044156454804410016202e0094140c02a03001840d0307050b1400c007001d4114014600391a4076495501100c0001d0b4200007034014001070352400b626036100c9500e1501d4046000045480413903188100005400d0319 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 635913866 1250 635912616 635912621
    0x706140a0e0d030204080a0311031201080d080601090f0b07060b0a18060504150e150409060e060702122203171215030a08091306090c140304050606150c01 68
    0x51040315900140d032103100c5907214640b9242e40c01220816004200c1070281d400f000c15214801d5034941420400c2080480c1c185083d80100c1540c0400b24800100000b121100000c0030302caa141d035030315801c0c0c09840c0d0714011140d07501a0301034100c0c400d4105070104801d659180c0181030241c000d5400091003202d5000181d100782e060382c4584c0f010181000d0b956003002840c0b045e80028842118200701500301014894900c1005100e400c02c0505101c0014003a0500420000041c04008100304a01a5545441401000750300441001ca1241100040c1134038000551044002543d41810741400c82c001074a8407001c42081c00c8450814a400b800070001c0d21400c1000c1003031034000000c036120103070b041380140400c90060400c00e1000e100c030308900c407688010402288180c5c2050715030b0398a414440105100c0301300c6a04840043c2e1070b104001426030021342c81a84400da040d1342d2984880d008400002c1306000030b030b5029005410200c0802c4203890013030f2040c03d52410719194a4200401039846908 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 635915116 1250 635913866 635913871
    0x8030f0d020702031f0e1b04091523090a17090a050d0c09050c16120e0d0b04020306060402070201090909020102071206020408011b270504091103010b010809060408070614 75
    0x2c0030000303103ea11706072003140e000b000c01c0403040800501401100e9101c140d03074030741124005401035555460690512614498106601d031181030103201c0c15203a00d41070700040000400c0c21300b800401c1c2000c191000340200e4154000b030b0300900e40b00030709026420200b60507030040390550380c01900104001056119182c43d04500b5018101d0698820b1811103000c05556009014040011080010b440d07914013154116a0a98010b50359100142c9217100075030f10358402d0480c071a330004040d04038004220728001c4181c0300b02e209034150790094030707408203100603400f600c0d000a02113503070410240181c0e4040c0c0d003d22552401441101c4900b07640b003800c5a140c144414007910b00c1a00000c1c00e004d44002400b40401050a4020881003607050b20801880343e102c0007100c80d500c0308003c405444c0241880840380282c44000c1c0100040c02d218a40260455400c6012070700035400e09580328070b81d6000c0c03003816201e0905030018100765a501d0b5168615644908022038449640713610300d54100801000343e03072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 635916366 1250 635915116 635915143
    0x18010f090507330509090103050c030f0c0f0f04020f030906100f0e07231308150f0708070c05060f18160501200a08090a0e0108030f0d02070203 63
    0x3815511414210308140e19600b040290078200181c0a00c0c202d0111040104204412400d89403038607444000c07119485800d03203143c0e01251044c00070091040210704600b0401040b400c03603810086014906880d030000400070355000300c10010403031241c206016900500d007030007040140ba140c038604c0c507040c02e90030980f966900c0368845820000d078850484424809899038903907072a82a46019024060510004d081c841040040002c0c914889600b0b4540d000b020b1864210540381c01108031030310754485c907510500001c1c0c440c20807915604141840c01a000ba4002006c01440b42d036075010139a0301d800007802404c10010841c0304d490120b1828020340e4018010a003500d1480d0420982e02c291207403404604c601d00350070100410181e040b801000d0000c841c03080c00c001e0180b400041603100b501c4500986950b1a0048100b41e10400c2442310080012101c02c1303c41c06100c545524108042d070f00300f400340c84030a038802c0102580c190200da0141c02c541c9041c80000d8503000ca2640801d080020038442070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 635917616 1250 635916366 635916371
    0x150b040504240303050c06180a022803080d0c050403050c061309050a05190c0c14190b06090c0c0c0d0c0909050f061602070e060d12080403170105030a020918010f 71
    0x5039080c14040c401c450b0440d02322580840415040c004071074079010361401c004c3c81881c1a00c030a03094008900c0840c1c1803512084403402d40e466580c100740b107007030307001502e103040607881d01010b10581802181640c0079039030040002e1580351864014048e25510900032030f980001103901c0010076100602440344900381090000c0740c10308080e07440302d103010484410781d00c65505007400b074411035030b1020501d62929000b0070030240400c1c089007040d007481c1c1d000c0d81140c030301c844004000040c06403d180035401460203865180d5071355141d04c0742040700d0085cad03a034101a50b0803040000129107003140e002c3d500f00c2e0103641c41d1070ba840da90300c140c1d134215500b4200c01c858035041809120102081401090340c806003078407601c0d0800c061180e0003500d50740c090180c00c0c1a03581c079002040464442010000c001b1303900c03c20b000e80d85c0945507805040404100e60440003c3c4000700030826001c81c8410241c120398000d0300030b25403440a40c0c2040380701200200440d5820ba05002800ca111600740100b4107030282d8800e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 635918866 1250 635917616 635917627
    0x605130c020106320a0503030c010e070e0c0a0807140d090b060a05060403080711060a1107060228051006091d0d080610030e1c03150b04050424030305 66
    0x180c01e5501c40d030720000107950041c4260080d8030032021040c680e0301e101004d2601301c8241c3c00018002d56120741100b50544030205091813075000c154040405000494101c030240c60307942c07800d0480f00001704c8415078000c0c014010200030b60b001e070051035089041c0b824004c048030052000b09104d60440080849201e494032100b1003485a003282582d0450700a65550a0141c10b00011680350f21852100030996000021004144800035007054030241004003181c1d0b9610305280000d00588010350186182e00440c013000403498000611b009404104015010042e2403103594003a5203030301450300340c440b4010300010b00c000c02030740d1044001603c11400000380c0b0807039200301c0c80302c3c6008800144203e07038064800404410740083c80240d0001d000c4803da194414140b41c201c0c0030b0144002421031503c112598014002c0030400c00140d085800e6030b08001c0c0d0f03400c43c049513170321010920907043c3e007102c104424412030900d07030014940c1405c4000c0c1440b5410803811140890302c026841540000d801280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 635920116 1250 635918866 635918891
    0x10020c0105520c14120f0a05041205010902030f06090601060c140706050a030b0607050307020f06130f0302040e0c0a0519080f1c020321280506030705150715060513 72
    0x6291004441e84e4008080c0610314020611151064210381c030b0400c40041140d07041548500111005003644082c3c04044140340c3c0740541c0603040da444203c0c864024440003100c0740f500055118404c46c1680000e094517441c118040e90300003280e003030a40d41c4410403850340324440e03400c01100004007020ba403404c0c3d81c0c40070210300400301e540145040d480b0b40d00410024020542c000709454501c4d404541000211a412001a913748144410070040c555403d40006240c40c00c02500c0080f43d00a0714148840a405a0001e440300c03007184081c1e40c4030318003031130034080707414001b41c10014280c00c650f1810806465000c41403910252808a000d20350210966801207191020310512a042500003107091482401204821b00391000a4000002c954000914540000300d07042098816280c3c0d000c1d206100c415140c006400c04840a90083c801c4020000d000e003061845c03811035258403c03180b400c007001692083c054413018030741250031684441000c00c4950740c0380305080000b1001440018150141c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 635921366 1250 635920116 635920133
    0x15020c01080903040e15010e10030f0f0b060a0804150e010603051c0503161b0b06120d020a03050708132c0105060304020f011110020c0105520c 63
    0x1403410105400c140800c005e0315074980a50b42c2c0003020444060a801d0220004a49100c00700361110352040c00300c1015609a038040c0e0140f1041d00c1d01c42000d010011311154903a0588010000458101c2020010400c03103d104901d0b980c0c008cc483c40783d200200510b1340c039110a4542c7c0507243c03583c0d65500c440c2041080740c10000c1d031041c0d4400d06a00c0c0074400011001810f540030042800508003c01584084054480c012000418130b5410382e0003412200c509120300c589074110340c020b005403d40402030400c801c1c000b40d42d9090704619401401c400d0401d903802c0320039030820b0704100c0d880b46060203081c044030700849000380507005485192000a24a040c0446010740070301800c5245a0403c00602c49a2200011290f00c641c06580003c1d40c00c03211001210303500c503001251586801501c2081da1003089580091228400e40b03002401035803600c4050080440d40900c00b101c680300305040e0ba245400c1e50901740c02041804036403c001e04c08407601c8100d0000640401400041c80d4180300030200007030391 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 635922616 1250 635921366 635921371
    0x409050604110a08100305030318060601022a0406080d0c12110607140c07091a01020c13050612011b20211b030a02120a0504031b15020c0108 62
    0x125070a0008000da005085810301c1a09050010401c05400080105404005c010000d43d400011a83d0380c3c6020101d28401a081a03107070700c1180200d41c0814003642c0f001540d150422004496800c50012a00d9400d050580305070f0f00a4100d03849010004420344103101502c0400d849890301c4031556140d10700303000005154049c640078083c0036800c1400d83c44000402940c00a0541442080c413621105403014a000b0b02500c0000b910401c83c0c0803604800301c0e0441e00e9135662035840842e83c50101001680c8821080e4203140c1c0001240f20b0488280009030407454100c2d401401083c1c0da802d484001500b0344240030444203a010301c000c0200d62181d4840400e2055062002c0801c0b442d007c41c482803902e8030084129030040c8079401c0008a0a14109402c94002008075035034011501c000c012120340725046503480340e015000300d10300c03161040c1c0a04d00310350400d049030ba110fa00d068115600c856144410300d1030320305103000d034280110340740b0300841ca0340710014070303e40080c50800d041400040814400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 635923866 1250 635922616 635922619
    0x50d020d09030b01140f100f0e010521061203040905041a01060813060e0f0606030d03020c1c030b04050a1407110d320a09080d0509011101110d0204090506 68
    0xa080e041010664060f09a41514900401c0f41c546949402c00103209814154466034419518800c401d42e0640180b01c008100c1c07a45d854030460300c00440015035860090400000c180c1400360304c0c500c001e1410651207540300b031000b0a000302021854102078519000f41d0844209079588405000a0000c828400100c2c440d0400e0030ba0b0080d81041002004510003500d000d05015880c0e1079a010804140c22441c0d0402801d011a00030700c00f0880001d5890400f550390714041c0c000e840b4050111442070080768071451200000780803600f1041810141d030038440e0240010140d0b10110000b80d6500c9000341030062142c503202141440540540300d0b11100080c145405200b02c10900001104000ca6440d8114400c2c2c1844003070101e00c042210701048001d261101041c0704401f103d000c007900303c0041c1421028581d96031040584940b01c65035610b80d0240320401156061202e20741c20341c0306001c64a460301e00c031400818030182c408421103141d04048120503083d9004501813210324a10720603a68400c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 635925116 1250 635923866 635923877
    0x504080712110f030a1b020a0306020c07140a0f0501260c0705010c08150103151d040c3614090d11070b0306090408040e0408071a101806050409050d020d 67
    0x5c40c1140030b0164032400c820303d880012032048600666880da401c04000310f4002400707540d2965229001c07900c0da004c81c015514034881c0d41040c4a000d0420b10314000a40d0302240c20305a5283c02c200054541d560700e1900000740c0240341a400642565410085004500c001c8006803224103615100d401c0d22181c10a21042100100c10420181650070651074404001c0c200080e0500c400c0074000002c3e241c0d40c1101d60180780d04100b074006070450382d2420384030b03034000d0030702d44c4c85262941c0180484180005090a0704e8100040030406801402d04a041203d06c0180008035060903814101e2041021100b440c0c20760020360244000a0b00141d0902a00c003200d001342c8040c508200d8036100e0b50201500207402045088002801c101c00d2104403800b905600d10111240c1c900b900e000d060546c0011411074203107103001d4594041d81c204250b01405005200d1034804410b08082d4001005032002102e69485a01d03601e0000c1c0c10307140c030b104404480380104e0203842d0510782103401901c1d201001c502c8004002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 635926366 1250 635925116 635925127
    0x7060201060e0702031c0c020f060c2a0703020105030c040e040c08121c0c03060e0a060302040b0609060307321201140a0e0a200c06060108090d030504080712110f03 72
    0x265004c501b040d1400d080c00001811258002d0403440c0203111103030b030080c5206450030300c0890740b0f400014080c10889200d000300102072031f14030800904c00c078100014082c0d11241003400150f004078061680480c400126034106940c40c6000c10481a017034500b6102e01403125010300c000c03502802250941d111806117686090b0406400b402c01007400090f03a1103080c1d80b08280450030f0721a4000c41d009041495002e006070800e48610b200030062440f04a2103145010016170030350030440152600d04900400f101c5c1113a0b2180c4082d03803078284c45120380c100e0082410801240c4180320351045d03455402c8164049e00d5904140340ca411f50700040e000020201c1c80e0340d085828640c0d80128103016100c144100c040c490b11501080c0010301f4240104050486c0340c459070001550482d8050b00141024404035000e03900c0c0c1c0d01c01541c195000751412042508002c1180e03074000d00a400440d0850710900c5200d280c01255210071000e14400302d4800b001450142204c013402d0001c00c4844c00e000181006546005c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 635927616 1250 635926366 635926387
    0x216061a0d03140c0313091a06090603090c030f0309030c030a0c12030e13020a1206030b06040c09120809010206180a030f02031e03010504060614090f0303070507060201060e070203 79
    0x10145101c01030030403070f8000c6211103100d00b0000f5107812800401c04c49848401c003a511383e031501e406020b0403e8042c502500303608c01c100e40c000b40174410308001d0300c5203140100c52000e003d81070b4002080101a0b02c10102003d040f81c804102e060ba11240000141da203507500d64041504000500c0c40355842a0f2048151801081c4455040c0003214900d00d103180b030719001407400b81c9165001d92030f800c2c0d000034021a56401020303da00188030036241c80da11144c0f50900c1002e0b0004541d0980005403080189500182a07801c2540c02061484800e05050083c550354005641c41c04500150071100c51201090390307003aa507010810560005080c440040000700002c01c10743e51842d01c66006010405c4000a0365601402441112040c1002d541001c4c4800194030700021760364400c1c402c00e40214034100700090401e215004010150b0410040a450b1401d44000c000482c0da412007403031b60501042250200082040200c84000c0c0115000407905618000b50304002c007800801840c259001084101d010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 635928866 1250 635927616 635927629
    0x1e01081e0714041d071e1d0703110d0f02070204051003050c0105181327020a14030c0a0905040b0c0702130c090f08160504060608010b0306130216061a 66
    0x31104192000110400b03050800607504c02800050f2440c0e0195507004507080407461150312980c07130403110a4610b01d42d2010130003400034400c02c8103040034441001051003140b094014814400140d80d202d41000318549000b070403661321a8002680740d9000030030000310b00382409490340c0200d1100200c000e80d440d50711081d0b110fa0f613006411b41000000a040302e020325400b140d076546040301504900c442c1052980f000b0040c06003441d4a0022054903002c500a040031750072108646074003402e40d01c042481c003505121085981159140d043c024120085110340700d0300c2c54000108003041000c125414181491407020703101a010034207102d1b04001c1d03200903895403052120104151240003414184090088a0800003900800200d20516000085135100068084103c144510316214000d58031420007084a00d1449410042010350004001084010300515405900500242c0a0900038290700d0100d07840185000c081e10882e0383c0f0b071002e000d494840c6101071190070341d000c2007412410300000c18 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 635930116 1250 635928866 635928899
    0x603010312031e0c05030a060f1809050c0d0804030b06010804020d0803040f080f0406020105010e072f0304091a01170c0703020309041404030f0504031205031e01081e07 74
    0x103040c0c50f4501d070501c600d041182c64801ca01c07018820011802d035288002d000ba0300030303a982d013950350422304041010450100010102d9400b0f41059039220300c0040803e014000c829420f88490040c45290101c64031680380ca2a501031080d0700c016903940c03c6103014050803070b02412150421908204100058a070400d0310400300d50071198040d2217543e203243c030b071040c6000d80c11300501134039010030f950312054200300c00f40054070043e8009101c1a0380b142c3c0e891021000440301d10300010704e91100050141383d8500c1d90a813003c0480304030510703002c841c078907140307981e001e80c1c81101a0355980040155084050b40301e04510402480e200c40890240c803903200d00c0e100f000d445801c038003e00107030307070f80c00c16000b00101d401480c4064014429080e075085412000754003201d041d008100c1c58608a42064400c07003c54040e02e51204954081d2042d401301110307540c000514100c04c0b00c0e02212842e20100252500e2070080141000509540d15508280305202c0340c2c131480d40720a40c1c0121070900480084010044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 635931366 1250 635930116 635930153
    0x605010206010303050711030a0308010f05180f06030a0b0f0a05090d1d0103090b130302010b0907050301030b0705090d0501050621031c2a2a030f03060810050a060506030103 76
    0xa4491900c0c0c2420301c007c400710303546030f0b5240c810a4086004c268002009504841c1200071b5805416901c005201c40a603560b0514016500b040000808040c180461f4a410070005803c59282c0c3c9159034601184000c29254010014120780030400400454002c1940c01032080d07002c3c220030802e02c00c001d80079005605c0440d0b400c0d1003030f00e03003a0300c0c1d64403130b42c40714402c5600801030032058140041d5040700110070040640042d42054076114280c201610240d001d04002e40d9464690381c40e42e200d03005107031400750001c4c0c00c0003000c1218001e181e0f50012005280c600500001840d408c000007040400030a817440301200e0b584e40460300e2a603640100640741c050b14180321071001c5625040d031f0103009000804904040300c1c542000300160404801c8010424006c2e40c6070000303903815010003040f2034100301254140821001c1c0600002a10451408034814507a00300030640740c1e01d80816500b0050440046da4003a0f55803420800000e88501070640186015943e1070318650441c0c644e001290402030744407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 635932616 1250 635931366 635931377
    0x10c030b06092b0804030c08030406200118150b0f150f0403050a14160b19121b02150c040b0f07020d03030209090907050a05012f0319030605010206010303 68
    0x58242960f414032852402c12400340c19002e040c1c2403402c90440d40080c0426540c0e01030806000c245802c00004076000d079030030307070b140c1c0356840756205101d481d28445003003182c403d9521180c003040c3d001c0002d100340b960b0a00c125103040e07003452103404000440f6080309209104040ca80080d40c0b00c0c0d2250311320281045104901c42e507035520360000c0d1740e0030362107298001482c42c49013400312010301208045102c002041102a140c6001b001d1881c5502c640a5008150700c1c41c1c0200100210300d002408600b0143d00035050584100c1c6000d90310307004030780c0d02010031142d10f00c0203001e80314007942c18001e1108003295004101d0702420600700700c03500c0f03010f2030140704406c80300040e90505144400055400b555801000c0d030010052034a40240650080b410060042c80010081035140c440803c164042c0c4201400300c03e86a40b51200440b01da0303031805504945151031001101400110139600000501d00400559903070718207044414075030701269003800415181004c1440070f07a901044072030440343c051415 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 635933866 1250 635932616 635932639
    0xe1309051219080f07051b1006080d17040f11030703050d180b0903060708070e03030415081e1b0f0309010b0102010e1f0905030f04090905010c030b0609 67
    0x18940a9910701d4012140c00208048403070b98900c119080418009a0f2040c190f61154401c07844001010749007003010502c1441580004036400b1512080b00c1000c400702d4500c0c03d40206400100c5016401410071a004a01004109600000300d244141c0e110341d4091003910340b07030b100d050001c1442c0c3c04c0102082c502c9460500580e4041100038041c54020096511407548d821024010703d2440281c1c1411100c24100000c40122100c16a80c0f140c20103409030509594aa40880c3c180384c00809000c18002406ca203120991010000f500151851800d440401124268042c2010f00c1c009e025000d517013150580d01520350f60043c0a6038100141070002c002c1040c8111008420303004280c0c00c070310010004002c03c0100c503015000407100e80d40a80007040380344c03203412045481d0702c940804480340050712081e04001e21000d034054000d07240074070292401d0840307081400480d58840d9210400c1e050300c4965490900900b8414418501c0e0386040c00c02c01e002c414800701e01c080c01751541a80c03085100318407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 635935116 1250 635933866 635933873
    0x61814210f03040302010219050307060e0319030506130504051b031c02150108061e06030705091303030b030303070804110f030601080f120a090506220f05100e1309 72
    0x8403990405500c2a2568601a01038480d92500300b4403090740184103850711b4064601c0020485014150803101440c03400405883c1c04000d0109122240d009102c10005200706a0442245110002d202c1d90040380300d0a100d020443c0c8001d1040c1c000001038079100c02e000c0015000100421403604442c402079001d0106800a07050400300b944540601d00502d401c440302c0c40d4042801c14100803042c0400d801640c950380c030702daa64001141e0190004200a01c091a040c00c0811566130041c001800c50b25215120000306040700c20070346038420071140000001c4105034050040462210040d401142035240401004060080c003800c050580554101c0541060300c41040700821644043c1c1110001e5a407400000e075602628202001c850040b600801252800b40c0102c0705810410b41c1d502091504000400070749502148292400c0c40005c003403a44d15040402e840c900420002038100062032608091040048000762040d00700000d911401009545890422101460718000052000030514 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 635936366 1250 635935116 635935159
    0x150918020d0503091915030905031b0c1203300103020d02010c050109050721020a0e0c0c010f0f060e070804320109060b1008040204050406061707061814 67
    0x844003a0402144510451800d20b5031000034101c2c2e8417100202c50359a11b0744c0d000c5003259030054005049410401c403980f5195686c21507070b58210500e00650768410300700e100251038410040180310740c41d0000302d21a04a026005400b0541001c84080402954400e510000c2c490105000092003440000d0b02ea40c19644214003074041a039001d4020403910000d403e089a50f59030170311a03a500c000e4801c2044108004c0c40c2c083c2c003842079001d0076282c41c2500703100030700400130001081c500303c00c102840a9822030009004201031004411000180b03008850721032015504150410451700c80c4220521140d60350144021703901c540c0050000b4500301303016901850044038042d41141c00540322002c0000040c065100b0716810b4801c138020040001741e00c042c840300807101e00759100410455000503015046c6500405e40c040e100f03031400940c2a842d02c19000003100c481d07207130024507802070300c050003182d8020062a080014030360f00c600c42d032440d220389030318500b10416040b400343d00035075507503c084101003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 635937616 1250 635936366 635936377
    0xe1903030e011e08101d06090a1406040914031201050a050d0308070f09050a09050f090a05030a030905191103010f020324040615120c030c0f08040215030901150918020d0503 76
    0x6243c0341b41c50030415206152071441030783c030705101d0640b000100d6040740485c800d01894501c158800d40c1155a8041004000c01640c0d1007562112074290f022400407009000510302b2004d2080c01c0d070495410b00e02881040991a0045406506600852804607070406100d650208032442c21019a00301c0c4002220300700c19691040c0d820503080040800c0d1a03000d900520300c03842150307920a80d0b45c0d603040d01c00c0b9174440d2444009031040c0c01c10484510214442d0300002c90060180d811500300d00d600c800c03e21800704410b901500c1d29203640368204039070718080c0146c0200700c234140c1040d03055060030f8001091800b070151029205031110b61000c0e1050300c0c3c3d500800d0051600c0001c2400502103060042c0510b000120755103107aa1804014444003400f07441003800110031555402811000c8500070ba821280260050740d0040e9910b6015480d00510740043d032041c0750020000c1011a00c0300b4441c07681000e02c0e00002e80c1d080c00c146820221280701159042c0b22074044480702410f864500f8001d0a51040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 635938866 1250 635937616 635937629
    0x40b060409050c370b0703080a09050a03030519050630060109050603120a0c060902030a0b0702010e01060e160f121109010f0315150e1903030e011e0810 67
    0x105660390034920091002c002c1d49021139400c004c1082410340310824456150241103005001402050007007403080141d40e62010750740b440000c8402d52620707174514219400901710006074650041207400f811000b50b42e0b003030b00c020442c01d00c07181c14607000141036002044243e0b1031070441028105215105640801045071194041d00c3c0c2c1541c403100080e003d8082210341a00a200324040f10003405000c2003114010011640c81c034003040210b07641e0710040c00d14000c05a034103104041c0510007080b00d04171a94081c26a6400008003401c0c03010728103003500c00503405100042c000d4404c0106d01226400030b805045881d01d0700240c0001030398002d44502140300004076200d86044a444800348140008102c640002d0302c400b4407074800880114140e0360003400e08800070103510003c000b843e4441000003000f0482d030070011401e8030a500030800c480310062031100700b009950b8082013810b4128840c0c0240c0202841d110320003105603d06a0510480704001c4400c10280f640001c02c4070400c001d20001600e41e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 635940116 1250 635938866 635938879
    0x20a180e040302070e0c0307030902010c02060d0501060806031902090603012408120a020c0f0f030102070303020403020a12020916020106030c060f17010f0302010804050726060f040b060409050c 85
    0x8481510445900341150124058800d285000c10100382003440b040c443c4516001451550362020340c1140504034181040781441000586200103a84003406030656240c5660001407a40c5401c41c000e1100b42c2c0901220f010b50003100c5020383d090300c0e2100c802c04194043c0d84001c80307a03c8142c0401d005080f110500015400d1652120306003400700e4485201b1100301100302c2e50340d4096241c0c00c0110344035100781343d40541c0c00030842c0000c608007140e02c104141c4000f04402070030f0144001183c01e90344401002c900080d8009014011441d01c94130b040060141c1d407920b140380c241240d000c207411000c00783c1444141020144030700b2580e8400d4015001450b4080350201c5080c1d66040701400105081030801c020a107140001501c0300220103a00303040307402c0b00b202c1001e04c0707103190010349202d880a042076a4174010341d00d01140c42d22091640f501c0e1354104000a12403a0600324905042c44000380942050710140c00030b02c00400e041c13600d5150880300c01c0b40c00180041503840c0c80c4d490504034070b848503003144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 635941366 1250 635940116 635940119
    0x30703030503090d02010219110f0d0c0c09110313050c0604031a0906040b0109111b1e060402060405040513060e03091005030c04060e0a0305010e340603020a18 70
    0x154001d0165015504540c02c94804004540f41a800e038002c48201c1042c82c0003200440c14100d20405402c0082c043e26400c0d140441f0f40408450b040c00a4100c00c0400308940c900054100040d141e81c0000901c400c10701003101110000000d60180b101400c84d94001e860b00f0485818400305011550b050030008201555840c0e40340762548104900584040d4200b807079900240d072038100440d040b032141350b009052414903828030b01c004009144a8840da2202d445c10b0200e01c900c82e800c0b114000e910a9240010114580c46503040284240c60502e4260581c1144003031000586400c02610700340c45e01144d010846540c0c20001500c4a40c407a035000d48414106902012a00c0f00440100400c5400751602c1d8048100d4481c01c0d2803a2005403102c10041c40c00b04000c001740d921840ca41b156030500200a502d0b05556500d945013500c080c021100d081c3e400403020704a6919403603050185402078418401c21560946c52841c10b140034500c100e009040c0c00054600c0d00b40d02c24a00c003c01887d100845c190207a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 635942616 1250 635941366 635941373
    0x2031519050903090a090510050d050a14120414131805160501140a0207030b0403050c010c0923012303190504021e1c0b1b040617060f030703 62
    0x5546424120403094507201c0401c241030008403c07940c4008000e000305032561301c0d0054043c0141001003015a160301c0c1c007100401d0b80d695468442c402503000342c005000030295401c247c00d0f4806034604940c880e50002072036140700700e0b02c2d60035601100e960700c40d4030350024402404180f440e802000100c840c94070b0400b2000030141d9503a0300d148624001c504407660030b68107004c08440189640078190110341d0b000c4492006a407040300900740c041d00c500c15144081e80e00c0da03031720620850540d4200c0220302c7c04500343c04030240921a0352100e92076840c207400080c3c0b40105861120441c403c05141605189402d2070069015240c21030300c200c105140b031920682180c581e80140e4100f52504464406094804804a040ca004050180d40c0060007140c00c000055442075000606880280c0c1195001252152000d120301030110340381c0c011000b4802525080400601c41c02000380d412000f00c0741030106000702076204a02c4043c0d0b103022040d1540f252903941c005652100d03400c0d422581403095502c04001c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 635943866 1250 635942616 635942641
    0x209220207060e011e02040b04090213050a060c03020609010c050a031d0d172a0c010b10050a030b011e0f020309100c03090914040809130e0706020d0c0b060904020315 73
    0x216a00c82240304002c06172170b101090348114420742802903400d000501c0000c030a0307401028540040c1c1d1548510503aa41c011840400c100d5120a01069103a21010180341d018030007640d000704d03c04000c0051002000c5c0140c912300482440004041da00d200f440414403915a106441121000488440c2a4104001040070240c0708820401c80f01010115018801c85000c1428415000a00b04039603501008801410340010034400215929a8901c1c841501d888890340c07201245965500e0ba100d400c140c01401707440e0421740d0941046024200b101400c0e01c1110403800c0111a0710b4514540da0340704400300c3c034501030450200d038045a0403501000b51a049074600650314440d448d4103020710b64445c140c1c002c4945840400d6106e0201000050008914200a04076000020b00c54200481070165100807214051039a0f5400d0f84005c0060001da50104003030b1079a50305610b4204c407034901d04d98aa1001000185c0320901980602010604568081c03045190100510b918144285442c9000048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 635945116 1250 635943866 635943881
    0x30f0911010311030c0304060b061210050a0503030307080703020a14040b0d0b0904080a05090a0e0a0b4603080d0615050408030913021905030f060102010209220207060e01 75
    0x860300c2d105410320000f4081c001e491140d00c010605500b590741e161034510240001041840e4072442c10014400f80a40d0240d6280c005e020710400c0d208030506020602511600a4120034407941c81070040080d2a54001c200c00c0d409800c62501503110f4440300c1f000c0e641d6102030a208280380c1c80100c0d02040c440303514005002c540d2241401131002640040c2440001c8100b40d030041c080342c40030031400c1c1c030030380c001c0300107165001003d040d8615035699403202035284502504c04c112100d1303c40280346a1032030031142111a00d0b1381ca0058800001c400034040d0040360706105040481c2c02e07500c01d61f00031030329801041c5c001184c000c0b000f40d0380d80c50800d00e50b60050034030707010b241d0344801c1d4020b5682c0624421f00c1502d060b01c40201c002c500e8010600100486140c2c02c110803101150200f01441001c45003d18000129150b070300d90980360b04000c1083d01048100602c01411a07105100e0002965030300c80f0300e002e10094000100d560300901d5058507000c1e00ca8032801901d072900708803c42e4480c4005501c20380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 635946366 1250 635945116 635945119
    0x61e060c070e04110d15112a0d0e01121109040e0709061e18060b0a2613120302160f12090e01051005071703221205070201030f0911 58
    0x160604c1342c204204400d056410060820501e1820030b480c480a03a03484a5901c50036021400e04000200721003e03040180540e541c02c0c0450b110b0140b05168408102d0f140b94810b15080c042d118002c00300000b07008001c40c0c030200648540f200b14190040588100703da0a001014100340041154241083d83c0d8108922807501c4d107a1420b000040d10030103010200c1c10342004410000c8a662034500e901d100110710400c400b40c01c070b0b5204000070b032155028004001c0f4400399115080c02004c049046000c2100450b05040308074094000c01260000f6107480d000d6042d800403400d8981c22600030100c0081c01039050789002051444248002d21400c1031504001074401d007600c000c0207550450446882d0102d02c02c410940744040c006020314680341040072590461440c06604140703203a22003200710348588140c0300d04101c000081c0810080b1004040007205e07122301191103442404d41d01d01c4542c0060074003d6040200c0450f081045a100343c200e40d04001241c0720601c001180d5090402d446000c44903200e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 635947616 1250 635946366 635946383
    0x1c06090b100503030d05060117042009090706050703020a0804091401091407030b060702031c0806010207030f0809060f0d0b040b030a050606310204140405061e060c070e04 75
    0xa0000040750a440301a110301501540c2008184104200901030144c60709040c44215920088202941008588564000c03009000925014501c1503119108031181c0d90140041804008404400141c0d04044690501e0100d665a03500c1c10220f00705400c0020050854a0004001882c0c68161300020008405000f84005590f60381d0340035412a80d105281e5050300c14800300054045000354404041110b010305006d14001450703000038284200c1c001c3e0f12a00f068902e10f001600d42c1e2044605510070000e00051040c0c40c00c41d1103050011542c0300008101c0d1000240d00b0215484031016140385d0b00820f59400d440740d21840000e4064038014014034021898188082480c0c0b40018601c4816a08140600b6450711a103050100240d600850102c1d01c108400b0001d00d42c400103100e840320105500c070b00685481c2810055241d000100c10716034415030508090080c02d44c0c40402c5000144000f900c22850280450042803003801398080c02c0c03500e80100c0d00300140002c501407000384998800c2916 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 635948866 1250 635947616 635947621
    0x602010c02071d1501020709020c0a1103060c0301090c140a021f3803240601021c080405070e010b07110415052806090608160203030a0b1c06090b 64
    0x10701e07030f1060f03812001c51070310500b010a2420144a2886045490600c1035640d8151039600c0c13481a44c0c008818450950b01102d0203105110310a1804a000c0404030f014154906103104100482c4c003060060980080d5201460007075640500100122140c2105826032926001030300039446003200c1700074094000c4081d007044050055803054602e0344100d24100c0300c000d4419803020070052140c03074500059140740c0d0301c0d103210b56070204200b814415400340900c00800b00b450b800c9a1003000541854155400441500e02510901204444904280c900b1005540e100c0c1002450050960b004e1110302d607168001213070118002d8010400c850285800c000c40100040078003007202c40e54001c0c0203c080c802d550620440c50700d602d00c42c95610030b241d44007080d103500343c0c4d1581140175558840b40114901820030810584c100f02c02681c00407610861230300c0480270007c043c0d160710004040c86501907803004d403844280e407810500441e081c400301d02503119101c24540b46000f42200c0c0415680710707804400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 635950116 1250 635948866 635948879
    0x70314060f1e030a0609050f120c0601090e100908090312040302130915020310030b06061e0f040801020d0e1501081b060408030703080a0b010e090f07020c0a0602010c0207 75
    0x2001075040010300041580b071003410550315039a0281d070340b1540c0f50184102c4500403446074061a02040d0042000c0c200401d11564100d140c5210149990090b8405000c2d1403c000800328001d41147d41d100c20205020604500250908034250003035800070b407a11034158240800178003d041d001c2c070294101c1d010804104034001007801140b00095005c01111010305a26010b038001100141c81420002c0d039401800c44041d040e40c00407a00b518458569100420602445a1180360002015919589011400c110300c1c0f02d0016583c180c5040300000040440c22042a03104a13402415150000c41d1071f0790749401100702070300c04110300048500c6004c2c404804030f5401c640841c101e81c80c04004010040403964801440503180d003103281d21100038040021803030018001003c0040c401d1780c40fa000d034a029001c1c0c07411a14074a00c014100011081d1010440d00c1d082c04454000f18513104481c03d40c2c1c0c684008074039180d140b49210340c2022340c2150000d4100d4054000024411040d000e4800c11034a41c7d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 635951366 1250 635950116 635950129
    0x120807021e13050103170702060d0c090533030c09040b010e03190c08070b0a0806030a14011509020c0d05160f0b01090c050906040b090f041e15060804031b020907031406 74
    0x2800230f907200c0810041c03854454115841219115600e0400c00c0c20180e0712000074401e107900402c05c8110014105084a98250f00606804085e812904883c01d504103460469464080c202e03030745004642d602c0d9414256030281c1c0310031310b41c0e141c01000c071503c40c22161015010341d04284400c8404202222020035041000315420b02540c0702d00c9603950802c101c05ca0121502c00000e84495018010301c0a00e0012075818103050070960840800071803008503908040ea902034180c0d01c00038200d0b01c1440700d003e541c403012803001810340d410302e84180c458541c100340000801800e000100035104d0b5041900c10415a1600c8a04950701d650f0200004884480240c0d4540308541070311303130b00840070071050007600e90920280419000c050f1003d41e0300d8140001290032985403040301c1252040102d091186440c1c54042c0b51110200007007114801c0b854200081c103000d90141005090280800300e4640d988420507200d0034042c4c005001010f40d044c0102d003d0010714000c0900300c400440580014014100348 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 635952616 1250 635951366 635951377
    0x1305090903070c1202241903060e0a0615051b010203010324091a0408071502130602070f0504110d06060c020f040e250924120807021e1305010317 64
    0xa4010b8414640c45048003410100f9060030508600b0306101a00d03081070340b91f21801152010303440005406050910001c0a1000101541d00050400c0f03001d01042038905488070b904005800c0068407030548441452030000110074000c400d601c01b0000100788210440100f03283c10301601d0f074056814018003681c05803003035000c0140c48900f102e04244030307180c841c070b0001c1c7e84640280c00603424480180d8035902c604000f03003130200f44690045031510f1413582010480d402489207000800c2044d19005e400391988c5400c0c46103501c103540e540c1072448404404011244021085001041308503150035000d03050450003601a40100d6000321150300904051080700025880400100503451000d8420313600304050319002032416407415400640c1c11842e005540d00340445180c1da0101304d100400412020940d90301040c80070895040c010045a11101213135051501907880a07080c0c503000c03c020420096840c00790340c0058031b491106410244035805641640e2052107070440310000c0004a041d68000c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 635953866 1250 635952616 635952619
    0x1050f0a140904020d0b040b07020c0a06080613020c0d021b0603070c0b090709060e0a0516081801140f15011110020309120c030310090c141305090903070c1202 70
    0x2007440c2468681021a4080e00c000d290f8910f0066990315400541d405440458030810300e4024020450b8050000410945060780c4406800c4d24141000b403031541c1c090f00543c014035403a2042d2100c0d040325012901c015400d60129451026940c3c40255603404542555144108075140d50125280000031640101c030070780d035440161103071912000029500585801c00b03034420b0003800262140940030310350090011031282180c515040c0142c070142c40c001800c1000001c01514601c415640005810350070040b0310400400c030301825204a030040010720b4050f0342001d051020807202025131090b49120790a1030740740e0205036512900541e403451030050700348155041220120380100c2d92b07601440d400148017040740d60603803400341005500d81c803e494101207600004104401740c02c0c050b00010061455030740070001d16415200081c540400480c2c40d1139004070016029030507000d504045406810000e0000459040140d60030f80e4a40c809030085402c4c108040000a641c0c48040c48441410780 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 635955116 1250 635953866 635953889
    0x106090902120406020d0e0d02070806093d1d252904080102120f010f090c110d031b020312010302060c1203070903060612030c1b0504021201050f0a 65
    0x403681d80f80c078080c6d044204100800c5907144820691410704004001a107403264000d05039850910010504201d0000d05503100b03035200442c2000784640fa1540c401034040c980104684007004184a501400c4010701c80b40d030124100045002444d00140440440c1c00190003296030480b48401003681100ca411001501c50950240030000d0310708503000d03103a02490a01001c0b0115041c10043c82c080c0e0000d800c000c4079a9404503680084001c105412500078407401040c40381e541c50804406007003000e40c051505100e40303500d608003460380120100c0154091040a1320998180604005e000700b4000b40000c01010b582e0f5007114000740080300319448144601401d8209a0854003400281d600194541c041440f50400c0080c50002c01005103000e480e0683e580e85180380380d4105801a00d4054020403096003174040380c840000d41102c0c03800c40041e0b12280352100000d0340303094108500e07010b40c40950071500000340441c20309102c0408e641a160112a4000d11082007810b211080364207004e480c48504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 635956366 1250 635955116 635955121
    0x1201051011100c0e030f160f0b16111018061b141606050705060105040e0c2803030909060f081513080c0c010305010e060d0b090f15010609090212 64
    0x1811500211040385031400c1030748040c403004000c070381b50259180e003240081d0003105100356115001039045006010b00100c3c01c103014103110048102e84601a012030f4004101d1010398100020066100f5a01c40018008000d4940c1c0450143c081c840900c401c2d500f004032084003164090142840300600340e807a01e050102040e0317558810711484001e0035078108520801c0300e1080c0081550107180d01406190740d07015200c00091410341e140c04d0040e007041c0d101d1b6060a1406203074003000503403400380e01002ca43e4007079503000d8546880d2284c2003c1002003500302841401105245d0486242c00480300c0c0308900b00580c540d03880e00440e0888040c000c03010303640c1108210429105030503070781e0740e0410718990004807a203010769640f84c402e84c02a00b20640c00d40000030080000d40e0140b15042c0104803000c082210391515000044070b07944290703c001c20412540c0049140540300700a03a00c500c41550088a14410a040c10085070b40800d2146000040007000007103007074105402a80e40f103201c031800790001c0c0e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 635957616 1250 635956366 635956393
    0x3150501110f0708030a0f09051c0609061b020708010c0f050703031b0e120619020a090504151e081b0f1905010207060c020f040b13021201051011 64
    0x15528008031205102e504426948520184850740081100e00d0041d41d858840d030b030700501580580c4000b101480f18101040080b174441c04541045400390308140101d41d01c0603c0c0050003403048004c040c00041c50504040c410180707500742c070349100d4103d07000c0741c846580d500314445c280c4c0c0c900107140c2d00107000d19603444000f030300880242245501c0b9082c00700d0901031081c4480701c40a281d20b90b1800140024810150034103261440a4210491402070702c0c07546400d43c03e0619202c2c2080f1905003c540c006640e0062030f00c90f0755844050a00104203203e03580c03c1b07c0006680c40300900403400c4144144580060b401e07202400079040344d220402502100d1425110365000340070380e40e4415001160482080c515948655144001c98050284860366500341000203240c0b50107900803400b4040400040d04c090b80d6016803180751417204480100d41e0032480d1020507030000b07800c00000007036400854a44120100e100a0505a500075183d1018880b4080d0701158800494000240141c000001d5031046 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 635958866 1250 635957616 635957627
    0x141f050c0904050c1605070e0c1602011202120f0f071b06051302030a03121104030503270a120b0c090607030f0203040b0d0501080709110a050d1b0806030c0103150501 73
    0x813081e00e08460742080180105200c0c1075011100443c1c0f00d030424001405500920f00744aa00007180c00d41075030900f4a100040044a940800c029040c821001040004050310390103c40f03481012142440311401d10b00380001d04e0303106c10385608081c3c0b4074510000310600d22514040321040405020500010b01d280c64503401084060096600610070030f01c12001358400b0800c1040d007922a6441c0d070050560740e010401207c40010240d1003440042004001181000064a5171051151080f4020f402640b208580081403140d5050b00b02005003000121118a880b00c02c2030b49000d103454240c03a45d070b801d200e0b1081c1c0c85103100c140d6012400b1b001520111744030f0084030400c503a0a00440c1c6c80c4c180c540002900c0354002138502d9800c00d031120014469600c0a0100c50010301003c1c2090280d980d140d01c1c0364025000f4180d00314200440420000c42c0179070b07103411454031124a8803010364007000c0318034000d10a036012180e4600900c20740c40d04105c41d501c44e00ca0400303903080711817040c0c0ca0b071400e0400444a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 635960116 1250 635958866 635958871
    0x1a04090213020c0a061d0c0f01090506030a0f091b05090601200109060f0f0e0a0f0308130f03031a18010b0d15060c0201121b08040609141f050c090405 66
    0x7510300c6031059000005105105501101103000b250141c10a0410030b42498103181c001d40074000c6201e41c81980ca62798020828406545040328465160340d5031200307401c01400890b40660001c0e00f840c07020002d0284980c1c2d20701642c00801c0d100b000c0d8a0719002401001c000a4030b1450000b80307500380d5019012440191603000f01e010748008150001c1688038141941c0d10980c402d68515aa010680c8000e40d192240d2b1400c42422406810101a180c0754004100503986c006801e004c4e01800280001c10145142626183d0013840341e04041036a0800130700a00f0718400d000302d040e1080700d000d03595207404500d10300c900010000000d072580c02c002c030825464204204541ca190340340d1128861085ca40301001c0081c20550b610034220070218000100320003240710b007a480d05890680800c8401411000266900e01c041c101059191107624000d001850240805042d2500782c0c00c021742c0155000c13400308280300c8041300c88015540d03448690011990242c4048203d9401080f01413070900f0160012035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 635961366 1250 635960116 635960137
    0x3090d1401090c08010f0603020f0f2e080708060d08160f05010b0f090c040302010f090b0c061b0c0601051c050f0303160504120311120d1a0409021302 66
    0x85012044452500b901c048850486400c814040144191314007407148448481015009110071413641d00860b680e01004444075004941c0a0080b02075034803640514a04032031030001c03078411680d4404000070903004c1d01d4000c400142e800030200f41c7c0e00b849030000c14000c2c0c100403e41d1540d1401c5907607078a0381e40d000b92070540c00040da01d0f099002041c90f43d4854a030b2640920004544040014104408182d00c001414440c94500003480540250003040d681980c2c0c3c2800c05004041400d034080da0b0760540e5901c040840703800052009420b99011a001d07010f9040155a2016034801e14043c6a590094140110869000d03200404c100d04d4144910f022800355114a01800340d03268903400c1c1003200c0902040d20035440007040c000d00724589000c083d0f01c125145071250800d030820640c100c44c1c242d9a1000b03410041c3c8264000c5074008203010f01a03c08041c002c40b2643d0701299004e00c00984100c020010080c00c04912900c0d05003020700400e102030b40d0060510f50342e213100801e0400250003540070380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 635962616 1250 635961366 635961383
    0x51905070b0c031c020a120f0209120d030c091a222c060d02010806010e09093f0703110307030302040509100e010b0702030129030d0203030903090d 65
    0x101c64500c4402880c010400d0406583d0b5034890107014519200c840c241c040d02ca910401803210b1240d80240342455040c400f54003c142c3c11815490b22020380503007480142c1c05840c40080789940300c000500c901c0410b10580b02800b103c41c04402c00d0b0351111548c03090880c00169058804011803070038006151041e107094008080442203030a800e0340701d43c030380c00040d003030313040c811001504030910905d641040380c0b0b2140304441850200007296005111240082c103200e841c50214400d68092165118940005002c1d09924074000d058a0368821141c840039001c0d115080300850710751088140d6060076103220308039180200d070000c012101940022010b03000c1205102d0840c0156405000a02d029030103a40e0168845013848108942404041e000c1155040342940410900702e60074180d0381142c0070940050b0300c0f4145400400d02400303038803c8000c5240e4400180400003610a035080100200c01d50448003400c0e81c151051340e0340d1100342c1d2589607643c024400300742070b450008481c400790b52050301d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 635963866 1250 635962616 635962619
    0x91e010e121903090f0b0702011d0301021204080a09140603011406130801320105010503070516050105010815040c051c0515251223040510150305190507 67
    0x80203002c00c402000301d000130080441080840782080700407000c0c00124541c01d203058103036130010b44120744440141500d42c1f0124000007044d5400e60590b100491882d418200302c0c0303402e01d003400c41503003c20031900c0440c00010b0b0214011100005100c1c83d54000307003400340b40d642815200d0f400c4002030401140d0000081200c288024040b02c4031400900c603000c00410300e08403c000782d4000544006c500e035568514943c51725604180010340c0d604460081c24001c4e601e1304c030507808555502c280240184200f5a51440008204055011078129010081591561480d00b03000f4881e0310015100548400e08091017844189000c000742030381144000c940c00e41600140d910142804500100005020420010040b4420f110741c01078058603100841202801c0549001505862040d040001c41355501c07401c0300703454000180600d145d200d5a25907954140742c24900a0f96a559030550625058100340f884014900f45102000a03203a2000c0a019014203075035070b2108a400907103099801d031055010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 635965116 1250 635963866 635963893
    0x7020609130b0405010b071505060f03011109040617030f09030c0409060c0f020d092105010e33010303030b0d0c0f091104060504210611091e010e12 65
    0x282045040d0700803010600c89201d00030401243c0c8140c1c00800aa002041128001034060003502048890320710001429225130000c00c8641d0080d1100310740541c0b800e5203203d4007005d06c40c0900b40c64041200d0501010382c6400b030325140303604120030200c860f9200740400c10f0fa114102000c2d107030302d58010741120402c100c10f60014003907070b0511800342e40e010382c0c800d8124401d41c1d014140c0801c0c1a800c0c0010702e0f03000700c20f41e00100720240c1e43c440d00302040881d40c08459501201c1030b10020403904400280041460000003d44401e07219411107224814900407480d1600f00300c1e00060308010b003400d80c00d013513860b43c1c03002c0e000741814400c503c2d03002c001746c0705201c00a00100c01144c081c1100200c50103400d400c04a4800c01c40c1c2c120503003010f116134103100030403545610a00700c80036503507261464041d01d03025400b0a1f07215800d01c0303801041181081c0e8540d40c01352404010707000c00e000c11199803e011a5492103401c8404800125030f000500560595929061102040e500c041c42403003104c44075040b491 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 635966366 1250 635965116 635965129
    0x7030c120302121005010e090702031603090b040b0307020f070e040602031e1501110303220c080105090a1218030b0c0708071101080708010f15200d1404120807020609 73
    0x180c12110f0481034840034010381d40d2085403461b0054054034002c03249d0070030042c00303542c1e806002c0310b0036481d42c164081202003500c1440301d080201030301c4007040d4031203450708080d0505410846407440184211034560080306070006e000350888001c3c90503608541c4490b19500d020703500050840c04061022000041e4400030007055621600369465036001c0d03940990001004050786010a0034580e00c240140302e4246030700150385000340844030010f0903113003440c9056524044243e202a09075441c0104201d40c4c158082031038075002d44074014913982000028001e4400030011040030070745d0140c0300c4042c800640c143c0842078019480c010300328180039407503a80100503488250304a4801c0742507201c0007190350308141c0042c2c0080c41801c24482560400500200c050817500c07403c441041800510180c450240f404240c442411203200140405400724442d526110400050009000c0145103001a240101528280d846441604041300d9207610352580f50b0300300c100146d900510410090308140e4400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 635967616 1250 635966366 635966371
    0x50331260a1208060d110409060b06032e0b0d0f020c1605120c03060c09061e070b0f01050303090d0c0b0403030801180225051c0c05010e0307030c12030212 68
    0xa030281e070149010218028040000034004c140181081090800001d01c2d110490300050300c1a030340040c1d200410305043c0054011180300701d8000000000b40051040e00c01e0807421100300c080103c69020f05032100000020310144900b810741001405242942c0e03280d074200344610700c20044090b0074655403040650070102410100741503e1010301d030401550414020716a40c0f10302c0c2d40064a00c81104001203612a600100804504800064020156564242503070300fa030030140b00c03040d5401400000fa143d15444440261303440d405040004990300d600e004041d0680e58007501540c20100c0704c109001c803030030810f8400c55803054611008074602c0d490001070802907001e0341e515800c0c6d51502d0380340124404045c06050606004105011130a103003000c400e00069408240d00e0240c1240c3c0c00c2007420310f0720b84001c2041d0200100d56290304541c0c014007400800d03005000802c44000d1141503660380388035254004010601103501d6401065541d8003841c4510322500740135243c40034641d0307401c203080b504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 635968866 1250 635967616 635967623
    0x20c010f11040e010b0d020c030711130c021f060e100302010f0c0201020d0c02120106080d020f0a02150714060108010212010806070e19050d050331260a 67
    0x5904810100d54a6030040114248941880914190520302c0340c07034100105000790314281c50000341d0340110f800145c2c12501e21a0b012426a81ca174115494190480b007840c828a52180110152a0100c841c86100f072800b6034149400610858544200700d4010110706803041101d2580d900002420b484040c0c41e0900c10181e8044400206080d440050251103e94814608102c0820a2100140d800181107118006223060642812030341d8400620240050002d82403654208040003a4003080042c044903c44029005c1d20074174070314000003da80320235a0070080d520425450014545040300b03801400d00500440c103403c5103002450729146001403c0e0300c00700e0b26039400203c1a4291160303030a454007412070500078200c1d40c00c180710000d254000030480c8503c12a13150020785c4148510f82e200c41c00411025001c5861200c65040c050345a810a81400a043c261581040c00c1e4401e403058103c0c0841e803102440c1205400d003884400500f5900c0e1110744100307081005041030010801010004e030340b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 635970116 1250 635968866 635968871
    0x601020f0a0501150605030c0f07060e01020c06040c08030c031b07150c030f030606052a071e060207120620120a0b040510050103090203071a04080105071e03091401020c01 75
    0x842c1142c4014680d1a90b2121041210520608c4020148141180c20482c481c000c09a22422079003000c0d00100903030182c05141d51320004013404000c0010401520542c000e400e072085243e55046155181c1c415848542c0c4035400422503c6803212801484c0744030b02c0c95190840d04160b85030104181107290f080807080118094960520400d5881302009036403864600e0140500d9150040181103030190034403051900e0783d0b014100c0c210740000d161041801c0b07000c42c1203c0d4569992844009210740104103440711401003d00401c0e52800012460101c46810701c10b4a00303440380c0d40f10403004000c40b8440c1400000300c4122100f8040040024002541e1445041c45907824880c40c81c0b01103a00c0d600c0198003c0c1d08100810012420001d905c0049a0003070802007414550b07840001d042210580007446500710020007000e6440b0a00003510a43d0031050003004603481704003081d62800400f0100c4000e8155401660309010700c6038010a07081340c071944600c00d8010040612500b07903000143d00d04030982d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 635971223 1107 635970116 635970131
    0x30e0603040f0b01090b0112110a1101060e0711010b01020d02030f0c0118060605010f0c0f140c040914011409070b03090a12030516050c0607080601020f0a0501 70
    0x765100c3c1440943e5030712440054004c02d520f01d0b403a0f0000b143c05109260110243c80746c80305c00050003880c00e0a0120030101154920b051a412800079521048001280c044010505005140e1034031038040700b1620341007490031141a42415811940701c107401c05250317074000c0101c2d409441040d00d00356541e21031586540c00742c6480d28010300014440c100020500416911601c187e40007642d6804040c0c4056208503410309032801e01501901c8004620710006005400380110350f01240141c83c10b1540800c0024100c0340e155005446143c0c007900c0524100e8000c1c820744540001c0300071004070b1400c0540c0c9550382d0f50414010952039900000c04a1040760040002021060340214201e204042040b401006454251003450411041190004049004000b070300c04180303201004110b00d5603003103c1100c42c10b2014000a040d40549055401300361003e108198415003e0000440d28a = true := by decide +kernel

theorem cover : BRFrame.Cov 635791366 635971223 := by
  have h0 := BRFrame.cov_init 635791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 635791366 ≤ n) (h2 : n < 635971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
