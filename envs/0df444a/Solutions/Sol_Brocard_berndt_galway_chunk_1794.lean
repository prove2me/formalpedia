-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1794
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:42:03.944324+00:00
-- url     : https://prove2.me/submissions/71250ae4-dd8a-4d96-b009-261b59511406

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 322482014 ≤ n < 322661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 322483264 1250 322482014 322482031
    0xc0b1810090f1202101401091b120e070f031214090112020a030f060e07020c091003110d050319090803130303050903031201030b090c10020c0103020d0b1c0201030c020a0209 76
    0x4294610f50300c2002021000310b910402403040921585008198220078024506014100403010301c0100102d513555001c00c01070b5486c4c4000c940204100c03c0105450088561103000714500000c0c035090120003038010318000d2100301454000729001503e0000781131f10741c0070900f400b0302c4044800d0380c0100702d21f2000b2400c2800541d99050030311048004200e1100c1c0360641c289040360110f14000d402d1052403144401d1703001c80700d10700c04c004d003000615941103c1502d0200855001400062905000d80380e00000c050411450302c00c45540e00c500359040b468281c0141302006000a03035a5501c01840c5000b441c01e070000e1032402d01c2003007070b0501c000340718000501840b0000441100035103042084807000302c2c4140c111221540c40f031a0400074940160344440c0d8901c2010002c440c036203031a00c8036810150f1150010710400000b080150003940084a8031000c80d81d40b1103002e980d903120514009030540310700c100c13102d1407402c2d84009400c541405426000310340c00100068010f0b112186507079000b6003031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 322484514 1250 322483264 322483283
    0x301050a2703140307050d09030c020907050f0f07050307080304051605010507081909090e071d0609011a09090702151b0a0c08090a0f090e010b09040803070c0b1810090f 74
    0x4142c01550980b1584e5803240c0d28914213101c803009c2c55803121468042c14030840b20070b4019180c40314216440e01905003080c0c2003070b004204c1210b11010200040c55618465800d60b401c0040a40b615400d83e082180e007a03465801c600890300c20001c08070015000b40009003002c906140c80d0346c5503026030340030b80440c501c070a20380301e01c500110f5405840c0c2c4034000c000c03200080c070800c9004494561959254802c05040081c0c074244403180c4011b10301d1482c440c0102410821940c6e1030400402190400120700032650881080f41d001252a209200e510480c0f0b5600200440c5140404060215400412042c7c070441e240f0079078121094544225984886240352a180350041402d162034548194251950700c40042100050304440c01000b150490b0300000003002406070f200c2225003600c0c0c0805001e640a950a0001000240110b0146400c10303001e00d080c0386a10050365803141180c1081d42d200030301001c06400004818000c01010111100400c070901c0301079019a24454035500010005009108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 322485764 1250 322484514 322484521
    0x80d0c140301140d021003020a0305060402040e0403050318121b0706080c21070908070b030606040302090c0c0703080310140a06081b0301090c030b0405060d0b0c090301050a27031403 80
    0xb100f010300c201300c44c2c008110307520074414920080e00a5122405803008a800d05001070414903142c4203680496035170285810b201e85d19a40c04441c0f0341c0c001801400f101c081100030b6464448208004203105400320b4459680c1c50303000c0e02400030007021000004c02a8802102072042c9a40525000c1e00b100880500e507865a400310b0086403241d502112005010210300704200300e056100503540201d030003001c1030ba107a65488036020b40085c80201c4810750402c0c2c0800c010001410702c18051940b00b0b628002180c10f08140744010b0b0304111513a4015240440c0220902038050605c0003410b00604d040d08130750101d0396041021440e02840c1e8420b980900082d1000a0072120720940401549019441d0007030341c0750f07121030303052008210b41e200c01400685001c0314400c2a0915100702406031100070300080581003266100c0150100080040410750340a000d80040b648090041078044c0e02c00800104106019010004206491810200c1d4010403100c09001180d08030b1000514007000500c01a80c954 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 322487014 1250 322485764 322485769
    0x1b01030e03070b0f0f15060f0d020d0504061a010207091104080a0302030a022a0d0203010e033403080705070618140f0601060512150904080d0c14030114 67
    0x12028200c150940800180c4070200141c0c2c2503003c3c451000c4004032005174482a0001022a00442d00310b070740328000d10314250307442c9881000340c0b00385508907966030b2078550b0a1094034283e0304140c080410850300d030300070700042150901036000c4c15035044184171550500c4d440001d55500d1148580c10701c690b80c031003a500c0040c440c50115070181210400300d9010519500e0000d580354421810900140203280380c420318040118065001c0c2a0311121140c8210040300810131040440076040b603240d9a94211092241c20900142c984c101031101c10101c040350300a00c2d0b044c244c044804078040c400030b490b00c2e8000280c101418a4010141d0300c0d180c0d0b02c414903458000010900300f2028000c076050186414100141034503000a010303062029601c41c400100141c40c6c0d944002e010303c3c0d0200d04144041c0001d00d24040146500030307120842d546070040004041034a41360160340c03e4a00000002d056030711518079000e00c2080080903d01036010088100d240c52440c08103001e03100384001c1c05441c221195 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 322488264 1250 322487014 322487021
    0xc1203040204060e0108030315040903090b0c15071119020d0311031e0706150305060a020d1d211303060e100e0705010216031a07120e031c0e1b0103 65
    0x52144d00581005545c684145c40c0d542e4000b21101224049141d41488950409000e04400e280d41034490041c0c881c01d01200803040e800400400c1c03518401d0841d40c04110a00e64002806103406480d078a020700d040d078944508054282c8a08140a4244440c00006840b0003082030200350300340ca800c2e1701d803c1c01c2d005a07600318443e400c0902021590800380d51390000350070300140420ba1280d4410028081c41440f03800d401e0700c142c4409230094106400060900409400074104444a580300003080010580e8101e00000150803800ba66031102d4801c003190310304141c00d49140600d604200742840c4c4004082140360b1028000100180d032a005420000c841c1040010b204807a44001070000da03580d0300b03100d80c1c0d031003691084a00501c16641108050311044200d1001d8030340240d006811000d030b501c09501415009003d803010030900907160400e80e112807083c16002c0107510003550342c5440c40700380200541c060481820203140342000f250720301100003498040c000043c000d03e0009102c2c000050307005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 322489514 1250 322488264 322488269
    0x90402030a0c06031a041e021309112a0309210102121f05010212031e010b040e06040b1e0609150909070201180f020f150307090503030c120304020406 66
    0x940310100c001095868164214007480c0140c0c10401d0a08440c00c1704200c241c800040b0020100b000b801c0415280c4140d0390018840072501011411030303250383c1c41c0c9200844200a60a41d10213201040c01c00c5184540311502691580c0071551125522854007982e49912804070b01620074034000700c0200150501861840c0e41056900086442e1b55252a1305201c0d840304482d1003105a443c080c101c56004410040081900d006a00410200301600c5842d28140c2c000f400380d180c1f20600d541c00b00c050325880b080080c0a8126501982d45451030200d0304251002d002d88460f1142e810500b140c80c4c4c079103889290001007075101000c1c01045071444085170041c86452442c580048021102e19403210110004010b480e0055800326000c0c1c0d100001242200c899100040f490841104c1480204082441040302d05000900c1d40340c20300001300000d2805000c0862441c4e42c904084104005036421154100040205038061450190801010794031524a900201c1c04514044041001c0d526a98408400b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 322490764 1250 322489514 322489523
    0x10f0c0309060b01180603050402030c120a0b06041103070c030909060b12060303071707150513050d0e0108271002071506030c060e01020307060606110c031b090402030a 74
    0x1424191100100544010386050750072908110014010354411140c0710000b03244220010b001e1410b260049000c2d10019209903414850074030319150369a5600281d20a40c01182c2c010110f03810149451202408018031040c8601d2809100310031520b07926088030781c40710442c6841c100c0c144c0c151a00b51080a481d0308403c10b52841d046010502e01c04000007032420008d452a114400d66520b401c00d81d403481003000047c04c020012040c07400303403448140504503441c86118541d104010740205c000072500101d42c075850a6081c2e40304001400820300044c04010070603d40b809405103c00d0001c0c00140c00503113010301c07101c801c06045045000c600c1010741c6140c1408159065000800c00c00d0000e500418404d4409603850107d08041d0003851182c01c0880c0e40c8103100100240c40c008082c0c6c1c50190356200715040d80400c01810f40064460b109035030203401e55031201e40c40341298481c40d600c0c01c405092890f0182d440381d60b11180340100d0302064000c4460444106000769102d02c086820000c0038a00240f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 322492014 1250 322490764 322490771
    0x20d02120109060c0206270304140a080d08010f12111201090803090d02010e03030910050604180506010303140f0d0b0612010b120a020406050d09020406050d0b0604050903031b03060102010f 83
    0x409180e000c1041ca02440c004140b5080c1d50116160a0012402102c21f04c90a640100000c1103003400e04980490545030040404030308550341c0c038030310f400e1000c189621030000d41a000180035030308405296102504200700200b019001c9a5158034505032090300840c490003c450a4643c3c51409410046074554085a903588a0800d04107903581c8001924084000d94207010010203141070001c181c07031268042c000206002c400040160f0002c0c0000303450f03290086d4403a00308a801100c0200d06000307151041c8010710440d0301d5814010b0100e0003140b1103d541880401141c0000401002034410f1411507a10004407083c4210000721244501d45030711114020072800066a07010840140000c0030501300b07281d09603540c0081801c2248500c0c0114800b2403402e028130b0030380014542c0700c140001d2010348002003294550000aa1400c00d23408201d4500c0000010030006080c903000d1903401c0707641b4074001c2d4214200402d90b54204c110005105a40754404030002c0c0785a8400d4028800e00c01c50800c040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 322493264 1250 322492014 322492031
    0x12020d110702100c051005040510090305220b220314030301030303180c06181a0406090909021c05030d02211e0c070f17031b0403020d0212010906 64
    0x250340d0007100c01a441241c1c06500c8541d4540a800c040f0792840d03200020b0950510403d0505000304005002030b00c0d580702d80c0f41040545150341c814030200e14000d0310340f19140c000150909401020449043c242014120010030000d240b0740165920a0340030080c0420702d80788414024540800c030b0303001800542c60203001c030f00001000700046050701d010b503031301784110740e0b14060303000232680109802401c042c00c41404101080c401c600031a2205012140100002da0340c00c10141e010301041c120303114800c0002010422150807450200040103401018030008005400081e10300c3d000340300103003c202e000300c41e50003044000d000311482d80a00190454070f81c0c4850290100c999030040e0b20481107200071000c0307070901a18084007001070040008411165440a035860216044104201d400c4c00c3c0c00340c10a0006080ca140e41c0d06664400c0c1c40654880c0341001c074032202080d0200a600304a00d00b084180056100d1500944a0f140c0640d014000144080816801007500c510060724142c17518404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 322494514 1250 322493264 322493291
    0x503120a0e100603120f110a3210020a0504030b040606030227041101020304092910050a030b06040e04060507021209090f06120304060201060501121404020112020d 72
    0x3004a5801d240c04a4121182c0360b00c5140840e6814000078040700304c5840c820b61018458040002e0402d514034004400203601e0a110340ba01c09460021140c0b84100d54000352004042940382490942500300003480b00a11545543c5605041c091003d202e90002843c2015038060011500207561003200140249445d00700a4000e008501040b8410040701c91541044e807070004540c51260b00c804455501c50f2215594000380d018641c6816043d400300f40800100c41c0303042c0c4210380030188011040000c1c1000225281da540c81d40c403072007610600355000b4a04c185c907848000c0e10100001400e001910543e50340000b400c0340665404a6044d1028104210811501c0d402050207000aa003c888566000030700248081c0250100c80d80c0105804000607440e011580d4055001640a88079070b041d5035082c640282564000e0300550f016030b4454208020700e50384268000c2265919003010440412850260380b24050003030f1001c0c0c10450900642540445141d04640e01849920420444080038001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 322495764 1250 322494514 322494521
    0xe0d05010e06161d180612010c0507020f01050406050f13120609060c05040b090913060204060c030f0c11090a0e07080114011205070b0d020705070b0417010606050d090503120a 77
    0x1880030000c1d24410b072200034000031613200200340f8030042041c80044110f482804031080014851a402440300e002c01561010030712440100540c183d440310358500880c0180520a0081c40070181005010032041004a40c40b00c15100440c0f40705d40800e94818a0803500ba00801e02504401042d142c0e004400301007203c0c550042144511a6000740080d5040381019070b4640224450f401d9241001c103c1e0f0036240ca008403a890b0b00600346502501081d003541c0700c0380221b800c0750300881c001ca03d007070aa4005045e004801c0e804180f80d1407500018288042da121021030a105801a0003000008041080309a0540044c0c2610340580d01f00c8655603510341c24075029204a00d502082d45980100105032010500c502e68010f5070010b009006032460542c006d1019800b00001003941503091203040000742040c054940141258180d0356100d07820425402805254158114804c3c1c4c90041c003000050703000415683d07410ad42c4007000800100506100b03041d40700c0d440c3c8642c18542c0940030003401b070065a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 322497014 1250 322495764 322495801
    0x203030a080a050906010302010f0c05071205030310090504050709050c0903010e0127050c010503040c0b070b06010807021504170f22082103150301090f05011a010e0d05010e06 77
    0x3a00340f0050303e8541586071115420b00003e80007441c00c0c5100c41510740141d120005141c801c80031924580d50700c416000c00da8039043d078103c0f89600000305200070403e00f0205c08001d03143c0361600300300e6413706a90741943c0d020188500b0904640355400602180d4400054070903502c000f600030b100310b0000031600c0d802070100668211a10381d046c3c0c198020b90340d01c0d084203895240d0080007000c2149000d00155180c1d0070003401211518414040481d050a490002d04501031050341c1d4030156060071000036008540003400310303003150321030818a2580c081c00c1e140a504607070011840c0d407a0602d00a408411882080d80701c03c6003000000d41a8030781c10070b0811080341e13142100300400c2e00f292603099003522568804103440d07032088a61042002c20b00038000564000c501504c00654141044012034250f0740081401d0319184800b800d2201401020301039905c650954200c0d011811040500180190b82c04101142c014002c0200060810200f540183c448249032000c4448924090001a50502240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 322498264 1250 322497014 322497031
    0x106050d0915231602030301030b0c0417010603050601350111040f080d03020c0601090c1803050c090901021606020c01020c0106030b010f0e01050d03180906060c020f0603060108130f0203030a08 85
    0x44000030380070700c0b420f451181e0b80080382c5d0141d0b1545e403031a1102550f1201c080d100d070701d641c103040100003075a005012515010842e18000850b01c10b00d5414840d0820b1016070280c842c50b005031002804044014006c82e1410ba8024625111f180303003016005e0040083c60191b041d00c0c100010042480b03110524484101c80c0140102e840140300084200d05170300604103a49032580c41480113104070005c3d6046020b0000d058680000c80186121a0000d2501d4a034400e0710503402840207007000303041011055501c00500c2d4020f502c0c01c030f11500384131000c0c107280c0009000c40e6400302e8403180d07200080d01181c10000c0c1e000000e0020586a00740328030780c40d40a00c540100701e40c1141c1c000a0003510004128100c3d000107242450042e49902e081c1c80c1a00304052500d01c142d00001d010a004c0180d20032080940400d03910800f103040c445c41801200155015010321034141032040002d16a80030200c20360040c110000d08480484601c0c11811714002081e00a504d07004c0400c4031051117a1203900c007882940c08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 322499514 1250 322498264 322498331
    0x150b040504230601080405210424022d010e0309270105060706020d0e010e010e030909010611190b060406050909060406051009060801020405090c030106050d0915 71
    0x48400b002458042100d00c1030740d02540000440c1907026542e01507005009500f9a81d403c9103003001c405071503c02c0054440c201c0c002160500003840c4c0c640e807007146018a10390342c0d01c0100418034003969804454401108000035a00010160605402c1c004000c1950100034030555007000302c60ee13140d40100d4012400b03081152000c0e00c50361004070b0b807002d0070544141820a140d00301010b01405d540503207419038004c0e80800042d26080c0c414414400419804000054000000840303582903e41c0001904159481440110314640d41e00d03c01300e04545840c14400400400f000006040040c4000880b10148040001c0d4042c0094111074511921080300c00f008495226810424807050a841c0c0d54500d910080003e0b001a056520160300244241d003c00700c8640e170381c581441902e5041e0014803240e50082000c02c040d0030092000380e04400401902c1e81150b0400710000d1941c06540d041140f03240c0c032800440240601c10112079191584013005210750701003c90078207e0000c0e40c4a44a042440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 322500764 1250 322499514 322499531
    0x6030201030c09030b040204020702040e0607030608062d090705060a0203030f011a071101091505040503060a05062d0a06170601090501050a050c0111070506070815010c03080a150b040504 82
    0x441c0c0405030590b90300141801c5c064030b075031302804003e4004140c02c036041692031003046480e0700c040041f244586c94a55003c01c0f01c46c10805220b0500e4000b402034641041181d5504c05121608502c0a03c290030000f40c00007a80e4810101d6480c2c14100d5100641100001454900304da130302000451140443e0782d407269250766500c240405041110f034109032200d0041c08807000141806d000c20304003000503d8090b991a443d4101d582030182549403003408074000150411580c201403040540c004c022090030015454840b0204441c5c20010101083c0010700303182c40c401200e0b03010000d40c110320b17000d415481e09681364000500000480004078840c10b500d90300251142d03105040d03150980300c1c113a54503420089081416607050300300d0032942a85540b14542000034030f40081c007425030580601e0081003d81005c0390b01602c00d0300007034032060107050f0405000b652039801203900d0503010b626203002000c5568850f03c0c4c0006064102c1d82c0200c540c0328806c0061814410070240061f40d4049804214541 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 322502014 1250 322500764 322500767
    0x1009230112120e0a08070b070b06061201060f050d18062f0903030408250e0603150405010227040c02030921030d02070606032d061505030a050106030201030c 69
    0x80281d40180740242e5044046401031084800b810000e0002e0000d040b41526520400d007020495080110350a101140040502180c2e5450942144064809034070b0460152034011484005000b41c2040c045000080010107210750100c1d08440740440d820445802c2011040c6004c070314000096410908000d942c491880001c4103000f0303500c00d001d60036504400982074245c0183c001e041050745c140811300000a40d080c1c10b2045414144640028102c148125404001048401e070014215042d01008015103030702d0010340300050201c40031480d03003240e8442c5049800b9100d21000c4004400340e20880e10804041c4c00c1e440c603061a4112014001d600381807004a0740ca001d604451030b806418010700c00070207018014641c1d160b051510a5a140c42000341e140c10599001140c201d41c2503545182c10020f110940c0888220703800e01c1400c0130b83c808102c00500d110660910400307080700340d0321100340341c001d640f1107038440081c20098240d521280080c10502d00034001884140c0c080b904042e120540507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 322503264 1250 322502014 322502039
    0x507110319080105040c0801090f060e0114090f010e040b181e07060f09140301090c06110c040606050316091e0807090608030d0903020c0405010b0307020c0306060f010810092301 78
    0x70720a94640c040d0303270300c0c0680580240000c0360141035207941d030744408a15120341983c094044c0c109541c44100d138280745002d008500c40000d01d0994801c0c44280140440761a0070681e54206801a05409060301c590707104690308040c81880f00b5003480340343c2d54140b5101e02d9425420ba0030303802100350381203240d0f528420360b4a0000101c0e08070000702c98810a00c50061700142001c0b0144014000080c6c2094a585000c0082c1d1550801004124145c001044041d0100840a12000151010702017039140040150050002604550b1244030846a0288e81485241844000c11248200b00003800ea003410000384803505028401c828001c80501040c0d07e0400e016100450380c40c1d000540c42c01030504d201c04010406224110218007030100c10b10102e940c3d43c000d19010f0840740582658a007464400a407911131f80aa440e03009400281c1004081d0340c8102001c41d80c18801e00f800c42d026510713072076105c54512035900161031003407401c2c0030040c02c6030320210703a9042c00ca044082c80e000c030398941070011b820 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 322504514 1250 322503264 322503281
    0x3050105010c02090405160e1008031603080a29030114011a0a0203041e0603050601082403030c0a060c110a0b07050d0915020a180f0504050711031908010504 69
    0x10440040b4044010b06054039000c0c0d1280c0220709981d500c40b5200d03981031030000c0741da00c03113410800050306204006482080400007003829034001d51503c0c855100343c2140c480d10380000340c240540b444c000740301c680380754001004814000000034024080040d0b2000e068940d4034440b07010750710300028a188189618403060588901c401480a4050b5a0549281a5201070036040450105020010345c0c002181d17045008100f0180d080084141001c0c0c0040840780004d0445040005070814000c10410009190a02c188050495040c541e07041700803e00d18814031980c0c410a101c3e005900d401d0040070342c8003140d26000ea9542e4109807100d040240d80e074032000407016008000d8040840c000500600c006c00401f154a980450b1010a584400600c510250070a01d00a40c00103400d1962943c4400c0910760b254042c4504d80443e41090700c0781c212a000d0f030007002c4c0500d0792040811610b034000c900341003000190000f1030365104003510384d40e030b121595290324002041803c0004100e500c3c041c043c5024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 322505764 1250 322504514 322504517
    0x3120409060b0f0f0f120c0904050f131b1e0e0c19030b0a120f03080106021b1311040b091f12050c1b0c0f030115030b0406020f12090d0305010501 64
    0x8016101312002c100303a01102040740312181c00c00002d07002c070b241030101920640c5554629a143c10302030051109840c4014035408820300d0001c20440502011440100d445070822204940c1c0760350060310180d02d85850b04403034401070840710150051301c0340368010002c1d00c0c1a18110704254603010410f005034010f068070042e007a550a960f40061078400d40c0b01500800c0002c000103503407943d80500f404140456001510820003007111981450342000c5000c0c010149840180480f900850f41074070121720300e840241c851040c56410750070607613040e040140580111101a640c1d5940ca1a80c005240c0c000355001d4060801c1304408800d108540006400c3c45003291211000c0e42d102d8814a0001c00b4020440e400d43c07c420721100345111040da080c1000d204485005201c80380552040000000070141e050f80300b07078100b280281110340c01019503070880c0d900940d600d02d980c42c1c91500c04040c1c000c0800840705483d010541c40340105103000014050000c540a40c1c2c0c09007a04502101a62000d0040d0b60 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 322507014 1250 322505764 322505767
    0x602030301031e080a02030306010914030d050d02250c060e09010e040302071802040503190807120311071a07110c06070303021201060801061206060f080a020903120409060b0f 77
    0x8a820f6000010300c440ba0041c0f03002d42c85071259294200c5400607581400141d001008001955800c40c070408082c102d80001034401c0030818002a58869296452a08102d0089070185010001ea019240c070b0002e85620600403603402c45030a40941c50150040e1500b1041503c00646580100c030303581c1402d20050309a841a07800c0010440306000060708c12000c40c07040340030001e030030b002c4822044507100180d5405a6100e01d40020907141c0750280010040807440014024002400302040750125030f8059010800a50080b909800400b01c10340c040c0310751000003540740e0070060101030034070300302e801e910704034206445100040302c51100b6400d0180c2245c4c003580341140310345040c201402c2c0c0705109140140c40c00e210b00d40552200c0c0070030780c000f9000c11003600c01031005a03013015844600480244041140718a418801010070364216040c1c014092080c0102d410f58007960101c500c1e0201c0a8102c48501c0c141c540d8820a076441403040110681c5840f9010443c544a1400c8494540d2403d1519 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 322508264 1250 322507014 322507019
    0xd0f02030a0f0e040c0503150102030c031801020f0601080a060507020307020d140c040213030b09190209070c060c08090d0f0804081305100201020403050d0816140f0f041e0602030301 80
    0x1a82c106140541071428801c00c0c1101c055295658040c669160038035588150b00ca04088524060360030140725a1410340d081804054891a0004151800404406640c29041d0304000050f03003800d14840b003142d80ba00402c0d0000c188228001401c0c0d1400d8070a030000c011680e1061012a26030080e59002903104010351002c03004100d4102c900781c14440208107446100d030b8000c0c00034080380d02c152600301c2d480303001035001c0050004c13840d240356004d60340d8409080c1510034540108591090003030002d1040c4520408150346a100762040560030f54003030410000754045200c09052040704850b91401c5100f0003800401da5845241c510880c00384c00d440341411511aa0b031444003a80080304d0000c5100e9080100040658501d0510190349002d6000165034504601b8018200040407400205009541e001e001100c40c007150040c282001038901540502040307104c03910903202d07050290404040c08a041d15030645440c0040c41144c1600440740d10309150303a1000e05503031a0620800c0c0141c1c0051004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 322509514 1250 322508264 322508267
    0x501020a09060c2f100e1503060d060213050d150506010905010c03030b040f021201090b0402040b1b0a02030313060e030f03250209010f061106010b1917010806090d0f02030a 76
    0x2044c0c031007480540700c0c4400c501200482e500e0441000c024000660000c0001c50f00c2c02d00c0b2840c04030b09800751441e10300d18549031001c9500f0480d1850300900342c035400204549551210704170710000e01002880501d01c0c1c43c060030b00842046800b40c0c1c2c0c1c0300c3c0510703100c003103071456006c0e050302800c5030341c10b840755901d26081c0d84023600100221000960090344541c40200c400500341b00401c03450251f1070a44440394100b11803a41150303034840d010b0b03020360310403c001d00c00c400d000400d48404030180561104000c7c2e0f00d6244a0824003100c074000d4151001040e080c0b107903000c1e5400c2c00259075460f03545a00c040340070030400d5610052f000c00c1e04d0040d0800c021541c001001590b200c00c03012442c1c10700088a10040d40800c2801c0d1007607002c0d10b41021460824428158000c03001d004d00703144039008110030350400071a0103842c46905100360b4902038501d10321145a004409039070f103402e42001132000c55a0342c0c0350213589072001140d000c11640a03607094440b9460003041100344c00c40c0d450b401141403a040349e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 322510764 1250 322509514 322509563
    0x15040e0c06040e01031b060c0618060509280c050f0105040806010305070e071107061817030307030e06040b0402220f0b0a0b0a02030f070c030506040501020a09060c 72
    0x4041a038010128205855103507000100010010228411455859818905008000070304101038100c130706842002500d0f4411b40f00c0c00b001d03412000008070082e6020700c110b501001350400818050400d002c114038002d020440d03c003030800d4130410740306105042041c000e220707803034007002089c41015500a109600700302100c19025001818528617007500d580501340390082c260700896403540010018060b03440030f450144e40001d19070404484801180d0071203a107411582c081c8008200c00e1454104100440790001001007000d0f072080760880c591072449580b00d0703004407682c1011905298003210300c5040001e0040c0709980025048002da1920380c04c000b0303007064031003080c084404031007182403600c92644500036881c0c80140740000d0124250303003407050709071103603005100d2100203100c00880d10342c02104844040da03401030200d6554045140c803106d40c0000d60000742540c0314200810042010541c020120102d003a21112a001c1d40d4940403107a039240400018228904910b55030801d0440e02c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 322512014 1250 322510764 322510781
    0x10507080906070803160e0d08030f0705091c17070210030c1202030702060414030408191e0f0c0b0702010915030e0f0c0405010b0a09030f32010b01081504 68
    0x40c02245400041e0704c0e01c1c0401d401c00c0c0e030b08114414003c1e42d83e110250701310082020140c0c080d01c65000d1048240c0fa4011680001080003506106440004003890f100303c0071a000310b03000408000600c9880e04050300710040000d0210f54040004002196000748981a50300d0194014115109420501c41c110081d01101d4080c009104075400c8590102e20240041c41c030405c80355008011510300340c00c2400e1220380703428940c81140c00800c020b22000802050401000c10090380c0510580c12070305c0c02d0386007004108005078902c910004020304001561800e210302500609404840365102e4060341d0b207900c60b820009001c10300b03100d010004140411900d242c10001c9040c00160003c078400c6107070500c6500240903515411100143c07003a450503110307c1e40580300b24010141803c48140d4044c00102c4039000141801c1d40e02042c1104111000010300c0b1002d1106440b407009a0550000c901314081b648481c0a99500741100507115511811040d485180150385503841c0d440c61006010090540c070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 322513264 1250 322512014 322512019
    0xc0a020c060310180603151b08060603070c0f0c06082706060103180b0f01150504050f010e0a170318040527010f052d1005090705090910090501090b0105070809 70
    0xd417070010115500d10f006640c05106100d01046024000c0d04c1451003400300e203036603c284034100040c0515920b524064a83c4410b99052100c00c0c1e1803241001d0381c20b00f001d104018020a40d82c80d012440d02e07804400704d4040c0e1040d04551850f180020385001140c03c0f840641181984a200069541c0d072007500000301c0030040340022840e403c040e4491280e800e40895805c6040c42102004020b488441c03078a0a4610f0030900e481802d01d0700704000901c1c80005d103002107041045070020304460748e580c0c02401004201b0401419088114a03038041d850790401003000107400645800c1c801181041c2c0283c0d80300344881d07159403080900483c81c0c2c020000c0c001d410b83e80159a81c00c0c01c140d0591651250a0040403002d026114030202c14443c0300c03a0545a0711480e0310f40390380109004501c0c41345401c1e5015100100d9260b00c2a54035100203c80900500c0d00c103aa024582e1028042d1011111030504140c50b140ea2060040d03a1b01d0302c2038403003504c4180c2000d07400654200021000300741650050130226000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 322514514 1250 322513264 322513271
    0x30f06021810080402090a060305030423090103050a02090604020a080609100f060c14010c08011a0d090f0204150501120b04020c0d080901050f0105010c030c0314030c0a020c06031018 80
    0xc1d0404a04074000da10030080120f0301d440180b00035841c04500060744158220390902800303040d5a103042c0c490150744603910300d6103d032071400200701340840c1c82c9202d01c44e00a02040746641e984d082c020794038400d0540903400f4808a001113422410305000319030006100340c4441425880c2c017014003c60140c0101031440c14103459501103400709607010080000e0042e9035440c00300110301e0405951414200c003809070700e40c0c50140e8491090b600041801e046030030380c520020810240100c24460f80c031540e16407071042441c1c941c0c95010041021464411b944c0203840070000c040740c0800350308900016015250200300e0030408190110385540112b0607121000c0d0007d404c281c090024036290449403070300ca0001c152038000f0007040760700c24820b05030f0040680510010551510b0f0018203442e14280c07029040042c00f103840410725004802c2c2080d088100c1d40c10661341c0c9007601c0d01b03491750707084140401c0c014000c08501005615081c002d890054441e40c46440145103000b0006c000d070320040310000c0b2050b49 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 322515764 1250 322514514 322514557
    0xf011107090c03020408010510060c030507030e0901150e030c031f0e06071119080a030902030f0d08090d022b211d0a0b0c0c0c0402071406060307030f0602 68
    0x4182c000c0b542c12802c40d0b20096202c1307080260341401d40b20020581c0907111140d41e01000655481803000c010150103040c2240c0e601c0050400711041e1443e000c0d11034001d61008000100c00c8070011510510303071800d035600080b0741c10078810103880d001c0103c002c030f0b030540c0040419044030140c1c0400d07403101200c0c044001031b96008209120b08115045640001203007013541c6c803452546003448045100090050034000c0c10090343d641d80a00d0081c1c04110301050350356000c100441d107040064020b281c0207901140c241d0010700f6001001c405003200d0440c0355004004411110a0002a50322500704201a4070039501c0b2603401040c040261032607511781001101034000801e800d000310881800e90807214086000c0c071140507884420544240c1d004002d52104d034807240440c4025190729000402406050307502c16624045929058603030309065841440020060304121040400b003919840310003d8480d141e0764081095190341081c80050080000c01c0024030000b0030903401407100f0100702d42141c48006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 322517014 1250 322515764 322515779
    0x1e0f0603052710050a1d06010f09112502010905060c12070f0c08030403120e01020c100221090901060f0206070c052113080c0604171e070312020303060f011107 70
    0x1c00a440741085d01340c0c1e0b0701400b0101500d207107032070701144040c400030701035949082d40012001c8014410814141d0740c4501d4604c070300c201d8a003110032003100c880e0380d229605006620020042070041040780403844880001031306080c42d80070b0f5000c00c44117801a10b481e0745030056151f100e5110300310854200154034000c2c1d000603076104100010301000c500654540c1c0c2145404154444901780074000e12601411840300da07030b800640c0745400780090740c82c05800b01140d007007a4034240440b2115402e021100d580d00c1c0c24036207280b014003c0014111601d10312070740c0c5c170502900c1c4908507900c07100040c1c000740c001486d814081c1c0494aa190300c075204403100c2203074885ca4480c0150200f13640d411101d000040b6401d032040300741790402c040d29140018103480903080c000203c00b48501e02c1001c150480c0c5c40380402c4200c00a000c80010300310b07001010f2010000303003d0740c5074842032a030001301c47c1c0c090f1494850000038800002e8a04c1040701404268604400400540c2c11072000c15010b080b501c02e420010428030f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 322518264 1250 322517014 322517021
    0xb07020a0f030b011d0412320715050103052808031302031c0f030c110109060c1d0d110f041409070b121f1e0f0603052710 54
    0x114050049000702c1d50408103017114403883d40940550711000b42c0300740004a02c0710940381e1109401800d01c2050300075580060020100c015801c20858820809641419610320740200b01052290b01c00f29480c1014140001c100d40084c040540701c1c1e40007080c0c2005104d52440c8081c0c0035010307e002490000100d81e5945180d603c1161251002001c0140c0a01107060400a21812a03103d4241e00720440300420010115810600ca000803d41c4403001070245900031002140300c0301211000340481d015504100d009400e2140c50540001d8188100201c105e50020940002d480f00a00030603004509441d0f4001f06801c04001c2644800000b0220031184e80c4c40c42505540c5d9206080301c070326842e001c0b404609008807540003c103143e804000d507145500300ca04166074004074003000990340958041c80c4086088290704005000c24178015030100003600302d0355182c102d5588030507503c5401c1e00c0b104200c0c182c91051300c05000000609401c0c1c1e403000d02d5081d41400780c2c145002100c0c0d000708590190003d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 322519514 1250 322518264 322518269
    0xf0607020a03030e1c050a0e03010905030712080c0d091a0f06090901020a020a020d0f02060706061410020c0f01030b0a0b0d0501060513030303110f030103060f1a01090b07020a0f 78
    0x141e480301e0140c1c4200358050044030410780c290384c00741841081081880a841c0025400754080041c0050500b01003400780c0c115054498001e8002c000c1165645442c03540c0b94054101500d41e1103002c100303080c0040c1b19007140d5206403203010600b42414804800c03400075103940030003150b50301d14154801c0f041081100c0c04501c5100301d2403d03076006080400c2801102000644000116401009203e119a0300040c7d011481c03a419281180c2d80c60040c28007001c4404034510003580300800158910521a407500306205948440f00042d0814502200f0085000c501c8070b2042e015801030300c007898007441c041141c20345038481030501050180e511000200c0301007980d08041040f51011500c0418071510b44642400b42801d0b04003245411800c60003051040c010384401001c00d6140c110311141c0840280c1617983c0743e618000320307a07183c0d6100d190620140c4504605600920302e0606800e841e04640c0300d4040ea481c03c10b8503042d00581c10054000c455912030f41050340c00090950000a180c445e10070110b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 322520764 1250 322519514 322519517
    0x10207120503100807050604061d03010c0f09080c01171009060602031804020711090406020405030d0801031a0c1905070f06201201050402160c06020607020c01021c080403020f0607 79
    0x2640d24003c1d80003032404002d50041c3d0386030350101d0b10074072041e00c4a07007ca40c20b070760744c50a0000b848090341500e001c1406030314800d1605542400444919070707401c40400490350b092500c0b1b05440c50b484d16040f960350011082101c1c0023131642d000c0c2000031000149650703009810350701100141501c442c000d50540d0a141d204600607480010740d40d014040c01c1c0034000035031608542c1546050f0007900c40c0704601e146014294404d40c508004070b4100421581150004c050203016244a4241c074135010f01001d4007480203565800303040181c5001206090301451140d0300c500c003a0b0b07003807000c5102c03500650201240300e80c00f801820000341000c02e8001001301c000da80b1900003c500500f1400c040d010b505250198540b019405021490142d0701c04a0918196002550010703125410003190406010300d141c03000c0e102d088100d02c00b1403041c0c0d0110340d2500c94180354003103d00d2003003904012640c810849981440c030348a075542441b01c0d103100c2c1d008150040e0091045a01a944210241d401c0136010341f030050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 322522014 1250 322520764 322520767
    0x7060603050c0a0b13050f03030d0906021206030f15060109030f0b1e041205030a0906150f080309030606040b03030415050901121b0309170c010f1103090a030804050102071205 77
    0x2040351403c0c0800001800e0001e00d11410301001800007080f808590007040c1c850010401040145c0e01e040055502d646500d04050000c0f900504015009600c041e000da120401e40f400012503504001500380c44121f14407004015030101270001048002014020318100103d20301c000000c604900140802d2a020f01c4558a660030701d0100d6800c0075107039108110000206004000100381c0c200c1c030640720707101c1c0c0c2d051031a600e6a42e500b4a00050010000042c082440c005010030b030341c0e10003003070318040e1441001f03074680441e1115025540d90040b800507a50552004000561604080c0c0056400750806000c5138100364403540c22241c01c0c0c99000048001800c0424500915031788641410782d0640c0c20b103008c000300c20088030300c1c3c4500d000c410f1518080c1926000c00c1c004100360f004c03204081d1308001400315225009007030494040c0440b441f8402109040c001c0c10301991864004481c00350218400401c00d910140c0d4080e1082d080c001d1055400303550070310020000c41c1e803403100322a00c1070031641d646 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 322523264 1250 322522014 322522033
    0x20d05100609051309031209080a020f07050616020f04020c0f0c061908070c021c0201080c090d030807020f061005091609060509040209100509011d01080402010806060706060305 78
    0x39400d810362684004100b0034500320810003a100e81c044040801401000030940101c14202a10448080415000390a01d015041c0092100c040068011901e696081d10000581542d0b8180d448a16004184d4044000c001e4620307c2803040303501c112958406081800044034010010f4101d0f0000c40124115400198114000e550300748907455100c5401c40780035040103202450b0040e86114020900240000c0c00085203103140100031254410380e004141d03c650b50364584101908811110080340441c4112021616002c0d02030280c502844010b0010b81100351320b03880444464030054651015800303403142c1c0d848495001e200c00707840346402540844190385040180090f8500080900c41c0c0c4507881c0455007404c41d030101c0b0301c00845481e45002512880400c000900911503040000e42c800e800040c04401250041c010341129002625070402c1c0702a4420101c40442c0c0032130015001840c076100240043d07000b0541181c0085000e44880c5c1850100c0d5140c604889664005440b558002d0014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 322524514 1250 322523264 322523281
    0x5010203101509180203040303090f05070602100501080a0f030c06091b060c02030a170c0610091503031e0905090f16050c060609130804092906161104020d05 69
    0x40841c62a00d0f2500400241c90b01c1c01c44c002250340c810746041c0c1d007900000880d080c503119030080c103483e0741c000c0e0080144aa00c3e241840e520b407c00d205503800b60040165080b0040350603c40d04c1e04807515900582040381c0140d1f60302c0b08240020300d0450a00909084940c00f05055214011090340f1910000400700c8414039241a00b00c0907a02071005c000e4290803600040e1408608109096403004008590030440c2c440050a8007803445420314500c1880e0811108909100e0300c07804032042640c00308440a10001540c0b11901d250101030007244154007081245900d140c2010240ca4044c640103070b456032200000780ca4034106a51486c181800d0078207212031140080c01c203100e881d142c0c1c1001d0b4a42640304050700e444010041800d4802e90300c1c0000140350b1145040480d03035540c0c0c043c0718165600e4039424890010103c0c0400020165880040c03000d030f502032021a003408210042815082011844c0d4208030481102c0e000c0f00e62540c207204035401c1c1e4540780090181c0d480c0c44a0085401c0ca4040d05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 322525764 1250 322524514 322524539
    0xf1d0c0f0f0f040903050d090506311509020607030507020102160f030308040813060215060103090c14040f020c0c090c09010801170f070303091508060901120309030501020310 77
    0x4419100302544a551540d5540340701c041c034518142503c01140030881410241c0d03460040075456004c03d410021803808110020070a03910400f0030043c3c00c0c080c8140c0503c440700100c01c0700e003c10f0424291004410214200750003001180305001004104000d050f40460801c0d040741c40101d02240c0e01141800c210368040c040301d1901040610010103251401903600c0b00c0c0001d521015092204200204d024000e50404440c00211201c0c030100b02d95980d088002c0d030311207803000340203220050440860313015031003030147c080c801e03070458480031031035040031800c00041d46031410f80c50b0300075030720852140610164009865181c40702805408529842c005103c100031000b0401a10020100420311b06681c2090f4041d045d07400d14400c903401034030411082407512003420381c00004c903c140c42e000410582c0c17000482003920100d5546819030620000e003682c0d045010358110360300c0f2503814014040f101c0d11007600d000140c024a09500260ba580d2622402c90f4016075544106c26030341142803001002050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 322527014 1250 322525764 322525789
    0x316120206060a14030703020a0b03100803030624070203061009061d07051c0207061e140426030a0515090c07110f0310050702010f0b01020c040f1d0c 66
    0x18000720300e00040007030101030f0340b4000c0f10010310034590312041c40d0310104070350320146034050406003555072101c03000c5950b50402c550081150420030380105109101009882c0030700d00180c5180040844c9004541e141610340d09407031101102402000f015030b03010091503016241c00f50142c855a4207240180040d10701c60f82220400d42c4160881139181d0701a0795130280c0c07281c1d0601d4100d84582c1c030800701600821015000300c04407800480d19a05000c4c06a0085190002c072075004008002d0076039005064805c400242c00e504035804000402080c9442481498402102180e8681c2c980b03c86c1616110b4000f038401107401c07681c85080084141121408004c20842111591002d24050300d6521962107030a100070509504540460220f4940700d02800703010600800340d0f4080c2440c050300f18010b1408460400042d0f0808003e820681090700c1080c13503e00041c0d0181c1082c016000510001c0c2000030030741c80b1220740d41c5c82c0c1000b15000b006031004410001c84c0203400c13440d500b441081850041c03078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 322528264 1250 322527014 322527017
    0x10611070803180121020409050f060607110301021b0106051305041e060906090510061707260706050c0106090213170c100c020328020918031612 64
    0x5000601c88044000140d40c012070800d032100c0f01900380100101d800f0b020030444c00480b1440000d16002400098000e04140c81145004101c1d6640c0d9681c0c81c00c1c0200b0913507a060b000342c030401812011443d00c101c60010008090005481c0001e82000074460346401114468240d5541405000510b01a011202c0d0100c0a40080c03105007826190490b010310950050001c1c032040d030400d0020000581c000010980d00254100603190316414456281c200c5120a4440c09103415000300c1c1212500d40503614990000c4c1c001c12520b4107210485000440105150022602c081594101e203a02000240040e00c15036450503107a201d80c1c0a22420748601740c2000807c01c0c01030048c0805410842c18400854024106a90318140d480c41c186050a001121941d00310030301c41c0200252a030040b90080f107040c03080e4121400030b4101000064944c4101503589000590003001502500e001441d10f0f8000c203414995002c40c50424840c42d10356401142081c0e48480314181d06010310400040454074240309 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 322529514 1250 322528264 322528273
    0xf010213060c0311060f090f07080c130b0405010b210421051306030203011401030e07050423132330030109140105010c0305030c09040f14010611 64
    0x9000e80c2441a040381c020501005425564a001d043c0b144040c1140804150182d40c403508080d54003000c4000202c81000d580c1c0b0500107688408140000c084d0b00300d03508500602000003001041200090f120106410781a4895806807002d503903a129144c000d0150560880d44e403a1000c2d0000b035082803d0640384402e483c007100700300110364040782e01c00c101e00d0300034034060300b1962004040d6002d0250000710884811400340c0803d544d500b60b4002e505079a580c0100c4080c2e000100011000e41d00c0c0c800684a00d604030717100402a41c107064204442d0a07440c01c00c044d00c0c08c00031001c512030440e82240c1035405452030010041c1070151013150380c0c080400d04590203828040781c4508a0307940015583e00400e00c11b0300034020521010b405c0c90000c00810032100203a0300d503961a00030000d49080c0d030422b204202450b000103480d60103a44010581585612000d00f16603035079207082d038243c004100c1644c02644525089095120a120705400d00500c0a40c070504da504080c0024004803040c1036121580c2e10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 322530764 1250 322529514 322529527
    0x1107021536040612051902010c081615020c3307050406080a0203010303050306120c0d08030a0509061306020a03140406020d0606020105060303120901150e010e0a02090604050108280902030f0102 85
    0xb0100d51841086c15101c1002a24246440100d0b01100141e030041d14000001c274203003044001c0040402c5150b4001d00c110742c001406480b80008034461031645901591081e8502812030018440c2140b604010020141204488402910300407900310b40c00400920001420b00c401900b01c2d04840d000051500c0445c01c541c1150360280581c8406003020344100d07448501c4403040c038000c01000e041d031751000c2c000c8082200369144c0100180c105842d4881600d0800000411508000403500c0c4103119107000c1c100b00000d161260b90003944084980f0b8101900c1b0005c075880070b26070310f441d14091442204010303620141c40e80311408a40c440d4000c0421a41440705003c41e998000056071139054044c43c0400c45a211102d41038014508140c1d4480c52000c24080001c6060040b00d03094100c0da440130b480c200c240c0d14510000300301e114105c2c0e165071003181400144155442000c805a0108440c2ca035096240d0100391010840101001200d6080351564031031411800d0511102c02524400002907040c0321 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 322532014 1250 322530764 322530773
    0xf1505070818040e1c02060a18140109061509150803040b09040608120910110303040818031c1403010509062704030504091107021536040612 62
    0x1044512100d410340da14034010742e0540e255840903051142c55400c8810025001d59000480120507420102500460b400220082e09a01038a0341042c0c000c40e542c41c1c0001c080c1c0d5a00346d5410032803500300040d03599003140c1001034140c0c420420155040742c064150a807a004040d0103a44812a984003500041d090070840044000240c60540e040300302030981340c644040100d030060003180c0c08107010388107074403e4445043c40700004120b00e22082d641d40c040700d042d411050741d004010003140d91040e03000b0800180401c3c0c000c80a0030a84130361940000e0341b0103807000003d140c1080900b02c40c0040c40d404481c01d90741a042200c1005040480d4006030a541c98030b030000d00e560000a224901540d000d0400c0d103920f091481c00c0400440e0880381d8614181014240203142d904140102071426142908903011b104020301550b61003075008101c0c2d218152007010900b40d503040b9080e00885e01c803840b03108aa480180100302c18001d4910050b0048803030780315080000b55446076115010141c89500c0c48400304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 322533264 1250 322532014 322532017
    0xf04020a02060601141c060e181f140405100614030a1e020a0f08070b1c09030207050307120507060f020a11030712060209011106070e0d02060409060f15050708 70
    0x300307007400c2a0503605c03400711140140340300d01208800078601c10701102e5582c0700c0d15480881911121030710900700d95643c500302081c2ca01040942801075112075004401e41100700d406410100c020100032580104c02c1d0a0b81082c10001e136400c5800750000c00c811a09020ce80c4205801801400c6500102d841765a010a45568090714060414080c040513028207091050300f00c0d0070a40e01038000c610180c1c0d01c4503d507114100c41d0090381d2a5004107030000440198040c182c8403032400d1100f0381c00300c05080017144070050050b14000c40540c0140c0d000040e0b203590500290000744669840c4044013500c92420a0800940350010401d00255122402c01d1f44e0f800036803a282554000080000c009020b000240780071308583c4803450040303960b200c5400b000803c1e0040c0c281c080e0b0a0302c0344548158000030694949104035001d50000d2113203011800103242400140b8400b070f00240215103050303118000842941c1890300040381d281e9035124100030704101005c81c55880c510301e00c0e0003421300005648001c40c9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 322534514 1250 322533264 322533271
    0x31d06011511031b030c010b0d150b181501170403020604080a1e0302040305010f09032f03030a150b090604060f020c040c030b010e0a0518070516050106050f04020a0206 74
    0x100111078100c014070b11810022640d501d00c91072120740303100d10304040b00c90f60f9074002c1e911081030b5402c0500c00001400c00d0703c528480b2641c0301d140260340281c20440180207000d0009425030180d50000101da000c60b80c5403205e80580c208522100030308140a001400c0320311010320010302041144100000f003940847d6054005521032a1140c0c1c0784d1034980c1c12518280c02c03450789500c800380410004245c90b059401402220310a800a0000716441c81d250800c0304d801c2d120107000308a02c40309060032034030b084101c130341c1c04064800c54084182046d5542c0e8030f0343d08115000c200d550742d16031180d450a8094908ce00051842070343c1189010405000b00d0654002e91080b081030010908080c10780138000d1201034503106c8041c0c410081061880340003806044260152070114234151300704540e90505054000598102074200380400080c40803c1001c03540082400040100034400d40d520f041403103103080d8507030340940e0010a03094104020070405020b100c0c006889140304000030301c1206c0c0c011034100c0e40b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 322535764 1250 322534514 322534517
    0xe0d08030403180e010806070f1805010f0201020705030403060b0a0f120305090f06130e01050a080703140106030f0c06081303020c120715031a06090a0e0402040207020a06031d060115 80
    0x1030780d8050720414000500750f005400e22080c0c4c0e000204041340000b812520501d00c2e5502e2100c5c0728484c0c1000c0d190f0083d5040c0400c00e1040d0780d80148040c0d4001c80d000003460090384001450714105881c0c05080da00980c00840300261501c2e9856000e1411000142c003070160002141c0c0c000d0b140001d4101c0c180c640c8a401014004041103050103982c90135240240504084d046655944840c0702da40c810f1035043c019136850002000010843c0e042c07404288003910810310017000d034241561510241d07090034680d038240d250748075040032000070f660120102c600c903c105541c51229017400009000b0140081c100003a110500e08001c001c070364006480740340100241c400c901110700e01c00400f420030361540c1100300c00303032021840c00d50482d502d84e00070300a9a4203c0c1d0710000300752030501005403d1046a82c8568484500380040c003168070443c4c00039400ca48010401881d20145902090440d07000e82d22000c0407a60320300040e48010000b80c244002e40d40c006024080f2981001c010410820006604e04c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 322537014 1250 322535764 322535777
    0x207090e0114130b01060f0906031a0307122a09050702010e0d0504090b1f080c07120305091005160f120905010e0d0504031709060d06060206070e0d08030403 69
    0x340340c00e500398030481051601420040d180d19001d036100f509182c1c20901100e50311040070002859074410340b03401c0100b0a444d56208030403441d1620840c042c1014040c94074003c0c4200b00102e0050b034080100200801e840c1e0114000e01d410f900740302c032030f2503154103c0340c07010700c00c07200b8184482d0341c4800030310143c60450b640010703113440e8254200e004020f0000d1138180e501c01c0309a41005640c11401900031200d06120501255860f0024809031141c251884120210492500c0ba0154003c0d070300e0030b41c01120b40c8d2040382014210740b69006006451060400401d5540d4140300c0001c40500048602a000460611007400e1840e0105484240e40307488030108448069400750382889126498000301012000f40550f24040c10030030b00034200c010f0a1090b921581c0c1c0140c40380750003001a2003c407500542654841061504028000d500800c0e90b40c3c5d001c1000c0108a46000711842071201030301484c8e0041c00c083c0782c18200500700178104601580b08800da600785400184140302141d501607410715020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 322538264 1250 322537014 322537031
    0x13090e0c03120c062d0c0c0705030307150914071212030c020c100309020904080a0806010c080405010c0305070506091c03060e060f18040b07081503150408040807080319030b01020709 80
    0x85502607003901c103080603102e1650a111803259006c002c0c10384414444103803114a55030b6010583c0e2842a81d90041089801010490700c036250340d07201e01104c5000d0105c611707108112801c1141801207070741082100c0c59103200c045060111070040101105030301d00b01000058400b10340030b9a1014400300c00c5116814100c06504a58400d402104c031041d405400348a5600302803030a00c02542240001c82d0000d0b079120005403496205174200780d040c0d500031103441c1c545820034004444484003140305070180001000b43e00005917040001520400c002006070440c041c1c03c86420320840300c805464800c050501c1400d00c01c2080c0e2980c0c141e0440d034201e91040d034142e412404038004035003015a15a59078642410441800201e400c0c2d1803041215641d02841035940c009961240101d0303400560301680b02d81e58002c4001031070038003d50080d01a0214600f0140c0c2c41c1240c1e0b10b0007003141c22440c075540001c140b400c00074110740c21070070b0301024030308040c0000508000001d40e00c01440c460407104a0710707018031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 322539514 1250 322538264 322538311
    0xf0e040c02100e03220501120b0307120b0609010b0406090b030603070f0807030c06080c040306020d09120306050307091a010507060e01050a0209120a120513090e0c03120c06 76
    0x10b400080740d851006000d2915841821501e03504411205000411311515100380d071401e407010780003610306c140c42d400e00c02070a4412010041181a4030142c26104010340444c3d0f1003100354a0262040c8504e2100b452854000c05006c43c000041c0d0140b56550001d0000340060b0740c100350308005135456503078040e13220360303a42c000240303000c3c1180d20000e180740e0450800315000b98003140c000242da0007608074100361079a4440c2242e00800c121000d1088107818030003480014181c0c1c0007421840006c101c0860180410b07125051030100d07110101d00840e40e124000c0020b0b080501101c1c0040c0341176041041a00c2c40840c080a1091000c2c1509040190000f064802c00026500401c3d00d1a220802003280c2d2501211000095011210310f0744100a11680c1903581c8400141c51144541d000e10520194114030b10241d8580d0000a20401e84000c846c0f004903030303410305c3d114101c4203094000044c101c03000c4440905091200c1c441079058000d0040121403800b002c0052285d81080d240507800213030225000c038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 322540764 1250 322539514 322539523
    0xc1e120a0b1305012712051c05040201171f0503190b0417072d0f020915090406020712091415070b10090e031c110f280f0e040c02 57
    0x80380181001755071203201d403110300b0b2600a0322035807050a4903068244c1550f03050714a4062200c4183d204940801240c864035010b03001903820520606007404000f04212176241625012141780200700f00b0042ea0010301c4103000020f08c01400300340d000d082c00480d44101054031120481000c1c10824030a0085000c10004800280340104041d0010b82c555040707180c603100401490445030701e1500c090090400c0c03d090094a410415807240c0d84a80d001000e40c2440481c0b5402046911a4480741018900c56240c80d541540b140b0301c9a41c00607a2080380345410070400075266426010050303e20404d0180608a001c0800091411220203c0195241018024921461000901340c203154020322818160000249040c1d888199007071007155800c4201c0781d980d0080b0f03d0f89061150304121f904088100540c032441c4188040c1050302c2c5050f0190480c00f000b607108510100345007024012035140c2c80950900c061104c005850000485080e884001f441a0102c00d0001c0c0b069648101c1c08000078000c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 322542014 1250 322540764 322540781
    0x40f020d02031005160908061618090608160b03010b160c1502210a080402190308070b01090203040c0504020c07030606060c0302011a01090312020c1e120a0b130501 72
    0x14201c3e6041c2254100d802c024203025241c1010a01c1000c052441321801044024244d61642e00100b180b9070b2040300b1001401c6000a003c0c05101005c1c0750940890740c00051000a4011000085560352500160b2460714001e401c40101200013824188010080501224111036425940640300c04060f0b400014240707666100600d24030b01500b00095100005000000e08101238090700d07074040d4540d012559000c15904500ba00318001c03c4140700150041040310b41060000e03005054880100007200c4450805410a03070300714801140c0c1c0c8080007100040745001d00b4906905500f1420182c3e106100342c0d002d405124452500800da041c22010200038a100841e00032400303200d503d0340d0b071101230060780c420001500194201034208004441c0081c01155001060b59005074451454036200d0072810680c14100850161560307c21055403419080f40d28084080c256070401d1452004000c1c0c803031110f03540d0b52129040000b0610203e9904ca01c111740c0714800d51900d40582c1c050381350603401807a604 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 322543264 1250 322542014 322542019
    0x41d13021e041802040f0903020628060803190c031b020d0c060306090f09020a050105090102030d060e1504090b0103080906130305060906010f0b040501051b0f0f0105130308040f020d02 81
    0x3d1140d04200184010450b41c40c000d07a002c01c40701700325084c20700a40e00c0482c40540581e000b4004280c0f2812003251004024401003c410340055600020307c0c203441071540120a0780e4808182d4040d0b05131480b002c1c3e028101c2d030303041602c02003401c0c0d58043c00044248821311101400701c1d101d0015906e8a003400a29035604c0321803410019152400500186000c0c060b41d0318003841d20061440c081039500c641050030f5001054070001c1407070f2600450f040c4c3d015081150441c08140401d028102860094030003420441c85640052714000c1d28035800da4040c0da07180c6100d1807c0c80a00008644041d0741e550540c0d4101e07100640ea00602c4000c030b0078070304c518251407800b0b04a01c6000014007001181c018050b0880c0400d45080742d036107010210810384103006d04010002c04000800c11503000c7e800402007242c0249559030007145035031820703091034030b1b0b02803044850308186d01400b007840003071003060342c001c0070b200304204000907544000344800170080c4003d160b041c2c0c0f1790024055550b180c2c0e030840304a030f00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 322544514 1250 322543264 322543271
    0x406090c03060e01051219020f06030709050f2b03021e060a0b03030c03040902030a06030606151101060f060c020a0801020307120b01021c120902060d02041d13021e04 73
    0x100318000300280240d11441200ca144a40046650b18084000740042d00b5010010020701e2200c2101c2c0c040d084c8881c000320f07400040500c0c45203054507858055441070700b06817520b02c2c0c068034001c284188090b2142801c1d200b504000180e02e844100c840130000705c25058160003000749403d00d41030b8941189003402d2000485a031240b0b0401d00000164203124001d499401e000030130810041c1070340ca00602500d800030b41c2080c44184888042940070707540c0b28000708808281d5a07a030792505021a100b40d0418184440d01070300ca15075894100c4e84103e49017031468020007509280c00074a2862840e103000301400c00c0403100c0d100040d591200016070290000c80d00071903480c1411680a0024984424402c1c145414505050260343c0080750702c801032902601d810150380a0703030701e01310307411081400724240c07095031000c4180150b01c82c4000790104030300c199401a5100e0801c000d103445c200c11441c546622910201c1003250542007003440340300c1140c0c143d0b8450291b40b00554a00b1001c4c4840300250b410914 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 322545764 1250 322544514 322544531
    0xa0512041112070501140403030207150309060f02070201030b03060124050706020c06040c06050403020a2d03112d040905150a0b15030714180310020a02070807080714040609 76
    0x40740c00c42c111340007621000030300c007112081c030031090085100103800358004107402c22480320310300660741c400802031400044601e0300d40e407560215020480e450504650204811003196011701c00c0c0010310004038001d018a6250040709440402d40c5100850070501c0e07103a02c00740c5c1500580c16501c507a98008130035919000b800d49020303514042107406480c122000800020750b580102c00b20b4042d290013600f001000340c10105080800f1305042c500010a0880104694898005c01f0030800558032541d8001c10921314003080125400c869114225102021100d0095091100c91801c2666078203441c080380300c180e9800c2107400d2400b0140c0010030b050a2008100e107104035603201080b0707804101c8100e08085c1fa44c8203442c4c1140400c4500c0c03000f140c03c05c01210703080c180c41c0e0003400304404804c1317490080802e80070200c0e092649000c440c103003c0b03401150000940d030701801000043c1409500510070a8608000c4642d40c1c0b49900c80e14400b449155021f06803519580c01050241041d054140111034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 322547014 1250 322545764 322545799
    0x7110a2102070e010e0112080903010212010513020a0e0d02011106070c03080a0c0518240403050709090305070305090a0e0f0906071b020411090414040510020a05120411 74
    0x10350303042030005001d410004a1180180c160241c141e130b80400c4640d07090780c200001030000000c10403050f02d220509000102c65a50309000411150403080c00321001940750000b40200c00110301e03d51705010340140a0190ba807130740f106036060114800c0741c06c1c50f01d005442c0016a00a542c0000302916800b0720720030000440c0c1c10403c10700c0171724800d684d05081a40c441039060b0840fa0380c0c9154100040307080102002d0030405099044420320000c00705410b03070504412508482e2800009034021500101d8100203104092003100001c0860080611032050390b41d40052051040040c0181404800b080c04401902c40883e04006482500d1100780f03a8100405040c036841e004588013801171061b40e000441d028400c20003e0385080758100d008540c14109d034204006401040304005120005008041c4c69130390b0b50184c10345420200310121000d0403e8146a4104102250210030a6004119544a050303012040b1008034a419003c803282d0303103c500c0d0064440d407180310780c02c0c5d000071406598003418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 322548264 1250 322547014 322547063
    0x4080706020606011704030804030207180b0a0504020304121103040905010323070e07050a020c0325060c0c03060509010b090c09030708190803070207080f0606010305150907110a 78
    0x16080364003150300e5a03031004011240d02c0401c61802da541c030411004200080e003e000d0742500584240181c0c1d0003144c0720310a4035030101c180c11620140d991134503044082c138208009220b002d807800703480079071940c0707000d884021040c4070f840b2012040042003280d40780440024410b460140c41c8119040c040b0b0750796428421024500c152007503070510140302003000a030340300007192403c5808000d006038890351102d80075141ca4201e03031140e1095024500210603541e4090050312106003510202c00745440e02d105c404248a80560005410b101e0008411004203011420210490303610820100d071035070355003c4e002c2c058081d00300d0807900000f0307240601400510400242c14010400e9013101c1c05181c0da041440e0391150505561211445030b425840c02065050000703640c806681c0c0112400a9603400000b0f141890300780a0920b503070888400e100c034075030f07040c0603194001810402003400d45128a00003040c008019110b4414090100c18a16100b401408554405500581200f5135000f9004800005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 322549514 1250 322548264 322548269
    0x13030f06180b040206031503061807150e190329160c06090204180302100f09021305040c050d050c040b0411160201090e01150e040b031b0402070206040807 68
    0x8581c140510100c0407039600c0c0c07901e1915904904007100b00e890319000d01c0344a83c40070b08112201140c00c507801c105c6032401c12178240a10700e00300e104aa1131042c0c050203814484180c1101c8021840313074400e0804164061000292008100c0d0b203000f00150b02035200501a0700e540c0010091441100d0441c4c189005415900103545140303003401d01d0b03a80e0f09000342103c0300400032174004103000c1807140c0c020880650103000e1083c8050400a02d110007004925140d204548040340160701041c200c103401a02c070b000c0c003000e0800561041c054001140d0004242c070500d6410809215a560006810310034248040001040068050300d114001401c04640b40c2d05070015140c05542402d480107014180361241140c40344c0244042c40c1450360142646000b180d1004083c0e0401009540210301203000682c118000c200962068603800c8103900e000d000040850310651003030f0b161400c1440319440100b00041c04a0350400715081c16140d01000034001e02a00c40040e401000100b0041495a00015503100307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 322550764 1250 322549514 322549523
    0x1a0d06080f010b010f020a03120e011e0f09021804030e100c0b100605070f050f0d03230712020d20030105030615131806091209091112040813030f 64
    0x100f50441801500c10260401e5101c0069100c03007001004213104947c404070249003010003043d0404049030301425900c07500444240c800410074006904200741c0700750000c447d00c080051040c904e2a400080c0341542c00340419006400030030010301013512a032000103500c5130082001c5840c3c20800001040002003035011101e84003040c01064500154035907039000c0300c005542e058a4100c80d96980701411200c183c0450302441000c8140043d484184410458080c603654001102c03ca5a9880041d50011040c10440c614050301802000c65101c00001c20540d0325140c0540c0d12044903004400a14400c034010234107000d20300c1600111112940254100d0790109d0440345191a60401d0409a144110074264001c81d0200350800d40c0400b9000b03820740122804100b4410344461302e404090b1030b85031604881000c1c011781c0c44440140c001e107207103003c1c0003145001c20200c6010214200c00748941c003a06008001c0e0100014100220401264401c0482e00b6403084900d43d40d207021407520310384240480b07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 322552014 1250 322550764 322550771
    0xf050c0409140108030d0c05070602030a140c21090f0a0804030302010b03061603050604020f030a06181401031e02060a03050f060d0203060403081803070812070c0302071a0d06080f01 80
    0xc034850b1110702241a101c0610145141906112600c0010804100083c06124090003860085129840175503c2a4000000854002c0144c6406905020300074901800308034140904080c110311400201000b4902c0f50b0b1000d502e882c1e03084418a05503d5880206003403003580415800c02c0b501c9400f900850f4402d400078003482c1c21100400d030700d4500c1141c9000c40c18480c0d4900c18901d9109801a942101026000500c0c200b55038000160540c0103c2d951014903031240000c200005030f8102d40c0115403c0b01d04200008086400d000d58101011700c400352000301c070000580440070041c0754038204658028840785d40c074100214013501624045032986288001d500000b00c00742007040d03098012680c01000b400b05e69035141e509698028000d080c0804418034401d074607803814030030402042c0701800b0703a44031500c801a103508807103841002440c0504004c801750000c00000d400140c64400d4070740034107410307a80c07000002400d542c0707010f541d40c600d540d641041000940640003041c4040050004c078000d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 322553264 1250 322552014 322552031
    0x303053105060a0b1005070c050909012f0d05041a04032d140a0e030f0c0406050604120b1807061d0904030206070507050319051b2a040f050c0409 64
    0x81240e40c16104d0030f402c00503428244044500c240000c040b11071040901061080e12200801c03141c04080b01c02c07115580d514240188001400036a4210030382d080920a9924542c40510701d0460041c140079480f1151240007160400418004a0012284483c4042028986030400903c2078010500740460800c41a8080c0701058106012442201103921000c0c4160350603100d6290940c001d151190400807411000c0c0095038060044402e024034100c028004282c40d10100002c80e94240e0050384921410001080030054000452000301c0e044403140d00f0942d183c9808180c40c4a0410245581d4050041c0111340c4075009000e072240a0f0b644c000d05c641c0001c0310f400303100c124241640c0190140c1e11540009040c14450002410760703521460079242010b90b80069155045a200e205d0780200f0408164010b0b5500f80c0d001410064a900004118000445408500400201124081301d0360894103031304007511650420002031072400c0f8200030718034006080700c2a54002d03007d400c506604003910b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 322554514 1250 322553264 322553281
    0xb06041d01031a061509011b080a090806041709130203010f03110d0f06110702040e0303160203130302010f05040503191506062001060e070c0303060f03030804030305310506 76
    0x1894130900e0f010386140741400c030b21075034220541c00c40b43d0072504001400952481e00c500390921142410720500d00a41c41d0802c1d048040e0000e50036400c11034450b40268208804182000408144101b0300d5040310350754500390010410600503040c0b11030f0000d000100010b20140035105c2402201e00400003400032807000410400080c01a0b42c019104986000d640404200103038040c05c108290080680c1c9400f4066000c1000c0e9204060613540d02d8102204002c624400d4401c1002010954030203149000081c0e000f8100304041c5e400068104881d0404803ea494000c4040b200030340710003411584d40e02c1e00780c60101740c4280000b80071542190a05e0071302851072100d0003420242d034119100d0b1100310012291110754800413044d15003c540d2110000102d015041c2166409030006035a141d01c1c180c840c0c1405000e9980d980d0107000605070f2503c0820100e64812009604203900d8580400c2e01c0e120000c00864100300d480c42880a2250724510850518514000000e101c0c428401c0d00e074a903445009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 322555764 1250 322554514 322554563
    0x3031803061e0f09250905130201080403030e01060b0f030907050105030603031213300507150902040603080301080d030509060112120c051f05160906030b06041d0103 73
    0x140b910041c2c910340c00f02d0210070280600d55482600d841c00c407013803080003c0800145004d0b4440c5001e0200e514034052100d040c26018103a13100807401c021600f403900c1640001d2005000400107001c0556880d801e0721004801c0d04048001e1000008a549840100400f04015407040d207010500d44200c03400042c0c2075005100307481c811107008029504003c103c4030303004a010802400c9024960000c10070a001840001c1a615844038804d81d062444440c5c088500d51040020841014018184480c0c1c0000c0d084c00040c1c01481840b210100700e1a140e44041005040a80c02c001c160f1540400080b42c4003900050b4110407400940e41403100d6101d200206032540001e02500e0300906042802102081c10200104800d840501d00880c404141e9100c40d070424090020000760a881e00e40b001202c4840d6024440e002840c03c40e0390210129010000340c186e00e07591141d20700f80f503200c214000d85c0b690f8501c01e032001400c01d4a00c04015044020366500c2d801001d0104641c0400c1c22661901c0b1a08a00da = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 322557014 1250 322555764 322555801
    0x3060227010906230c0a021c0b04020103230901020c1908070602070201050d020a170a0c0206060906040914030c01060b040e150619031a030c0105040b0a020c0303180306 74
    0x1c46141200e8140354007212600b001400821091000c42d0800000745440300043c5229413091000c0d05020b03206d13204022481650481c3c05c1300107800d0034800d0011500b40011160851750900b00041c842c40c03071070171064188503081980c0004050560400003003900c107400a04808038101c042e24071420b58048000d4a00805120203070a9120500c0180d001444d2503006040c202d005040542c241051341c0e01030000e9a0241c0e5814000400c403400c058101c090034000c9681101d5881d1040c411080e500100030343e100c40c001c01c03e038440c04038030300419a50744460740464042c40d00403540d00300740300e400300d035071a9039902801c51081550b10f810310000315900c185040c1d8060381d000342000901d5444415000154a49070f24046500041c1040140d90707180914011120061650300c0108842407101d0080741104802c40c00c103406074003c1c101d6580340e0307030340001220165242c0c50b2000e91220881c070000c910307020601041da80c051000260000d08200704601400f2000411002c59082d6500c2c0280039000c0001d04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 322558264 1250 322557014 322557017
    0x50f0f031612050f07060e0c0607050a030e041104141507030f0804020117040609110307061218291b0301030201050a0c230f030c030a0521010306022701 67
    0x480d241d80008281400d051000302851400a040ca00c40c01e41c08034003a0b00440088505640e034191b0046100b01c01d202e81d851504013198821708240039512043d1b250111044006d04001c9212060034540e5100c0d0f00015011a0200c61151034a03160784d640704400040c01002c92203400342d080c0c000c100f850740300c0480c1c28041e1316503a2080d81c0110010261071500d40a0012418400051100e40d00c3c91140c042d0503118a00404022803140d201d4108558049440c40700c140c000c0e04003440c1807081c6900301410718850085000005208141010311080c03000107802e0081044010801248410b030702800a4403154002e180e039861b460326881c0c80b410003180840c000c10303441f1b402072004102640c01440a00b284500500340f01c1c46a0406541c0c0303001c2610020402a25450303c0d0f01c800d0400c0324104100d599030314008000f103142c4082071780c960740c4c1d03401132640050400c400068000b130030a20900c403003c2402c4a103070b00c42c07500307503101d1400c6000381d000302d84081621019409052504600d4013003081060034103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 322559514 1250 322558264 322558297
    0x30408011a061902030c030a0e01030b0301060602190201090b03090307020907090609060c02180108060901060e0108030405040e0a12020c0108060103150b030901140a0204080c032802010e030a050f0f03 88
    0x19101140d0403c030048003030080d40400e204040840e034052009240c000b80e141c0d5820108403d070030015040782d014505043c066850b20405000060300003400c0500c1103400351072000300740203905c0103d601001d950880038610030040f06105480c44000003600803d032007150030000aa070780c0c4008542c0310038a80b01c0e480005a160608000d140d01456501e0700c0c40d4006042038980b440c2c00e5031020798081c801c0e4046481076100804200101300b080c03080102a0140b41044040c6524241c0100e540340030f2405540d2143d0b0751032072815003408040000c3c08000d9071110b49031200700c41c0c422000e03407104645c101940c0454100e200190300756100b4803580e100c0e07130301130403100c11100e08006890b84181c100074191010341d9070b62214480b01809031004140b15205517100541e849080804d06810160514035242c000c0e400200d506136200400001c8240070144a000c0151080403400121144820315108641600070b03a40802c06114000c0350a400c1c0d54038020498014103c0504083e58901c14000036407051450b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 322560764 1250 322559514 322559527
    0x1e050f0c040504110f030f1006110c04020306010201060f140a05100c060504110a12020411040807120606030c0e0612030f070311070302062802030708090f130608030408011a06 77
    0x7801e504c9600150b10301e4180504001c0480000e50880c5d1058920400510344207007040041000340f5054006003000e85410785480410904240c1da032030300703054030038800c5030044001740c4164800d60240e40202860182d481c0305607650180ca10301e414140802d1409049482804141c50031301024024084d006550751004c0300c036840d21a100100005841101c0c400300d01040c1860310354460103007001504040ca246e620915070f038070400007202d96465401c10081001e1208001004c0e0104d220000c88602443c0c1d05240c00b0a8a400c00040015800040100035020301c04110780310fa11850300d21901c01680c0303d420880d0350301b5081d6038a005015981008c454204170700c4002910864a0b0a192520380d070807205c000f034a0340c0c000b60081e00301401441240e060101030003404034041c030343d4880000d0305002441c03600c0d20b11303120081944681d0054038021200f0602c0c00660f41c4640c240380c1400900001f0401481e030b00d42034501c2e143d62151288541c658204040d00c500b07a0f68604022010b010300810151500300c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 322562014 1250 322560764 322560769
    0x60927060f010914010e09010602010f0513020a0308130e0f0105040c020c031e010b120d090609030c05060318060c270a1e090f090605010b0703021e0f011e050f0c0405 73
    0x8544c410703528100803c0d83c012150f03948445001c1c901802003600045071030480100b07400210b0f80000d006d0108030040d018540c0140e116520384c0380c140e03038101d2440c5940e40113003413549050302125400006282d4003c0300f040f0f250640482c0990503540c0c112420710003036000500890b5554039902c80d55525802c45043c5802022400c1ca540181c00c0902c400800c5c0c441c013040024409103462030101d000794200c59025020168410948409060541801308a881c01c5444803000000540159030081c03c0010201e00c007550790a005200c0000c001040b521a850611949141c0c0d42007502c0030b0700d1180900368015801e00c0e0000111481234001750000d581285004243d254200341c4c0d600c0c02d80504002d04011610000d640602c008805405002040112007490302034100d89050b070280c10818402d004500c0041d40c0419140f070306100c076040880c0c810211f0086079081080d14816207000b03611340030b0780c030200e000300340040c8100e520b50f4401001507176a070312500b0810f4903040b104581d050748c0800062104d031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 322563264 1250 322562014 322562039
    0x6160201140f1005030105092b14030a0212130203010e010e030711040209060d0b0a090605031c110712060b030d0512070203250203060a110702010e060927060f0109 72
    0x1007090007100e90b030544d6103011900311181654104002c1d0490700c892541002e0f42095030420b69142940440b00c03402405000780801c040103c0c02450441c00004603c20989a4040c0c03500c245000134400c000b410401c144107000304642204a000e0350a080400400340703418403442c00c034102100e010310b1900d08503036203510344050f02c4122154003641c24480340210b521034002602c084042840b001907001500c500b00044c818440e800341c0c00e5507003040c03000d01141d05c0109494070001d00382c280701c2c5000343d90110103481c2c00a01036115010f500c180c203030000c3c225600000c106000b6008041c200000c4001c2c109250f1100c100e070700c0110200d181080424488507200326480c2e803101c01841943c2c108a00010007040f40740c40084203000408c260084c49007589018048180c001c40141c00810a009080720f0b040c40714000c40300041c0c1403003401c00c4030b00c1e615200c0384101c07004100c009201c41c103203984000700c0c010382e245103081054082ca08031002902500300400b1080105a0503140d03e140b00340781a402c81d000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 322564514 1250 322563264 322563271
    0x2130506031306150602010b090c091c081606150305060705030919111c030e0f0103110705011b0e01020709021c06080f1504020f010c0215040806160201140f 69
    0x10b442d421500c1010034030920814600805a42c015a541498805c2c001d0940300009190752040781c0385007c4c441d070300c60040100d83c500041903071500d124110010850120200410000c1c1c10800c00203613500181c582c16a221185900c259000c1050468a14241a45080c035001c010301c160301c9400850395481c011405103078070070030000c122070101c4c06802c15a404500d624000301c420840342001420340307181400c07ca00e884004d048284e510344125844c010720b81e00086800c1d5019a00120f03140605074420780050b40c10018452a08d44d40d21000e2607c9030080c086020f550179041c000f1059914900c0c0704100c00d030701244050380140151400c01790003a00030361218401c442d042980c05050039141159000b910003c018981c0900300d221f08000700700307003060480b15417008100d0380b007800c10005a48100c41920700324020b1901344981741c0607101094818000d41b0080c0e0000c0404100080c001500281e0a4405d003c4034041c1142c1181c1064243d00761001c6004400c510013074000003400704603030441195032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 322565764 1250 322564514 322564531
    0x110421020d03141303050304060f030b012304030f0f021203070b15010c0b0a090b0c040f1e0b07050a06060b18040b031c020610050a0302090a0f0b30010213050603 71
    0x192903154203213814084455071040b1041e07000450100101c5400603602c440040c403070309040c005000c82d1400200290303055034444841e8a410140301c0059500303c01510301440c1e00c0007040f1240c00c158100703920070801d5040202d11070f42c0034008203881e441d00071055a1401d50300c00340401254444011011b070302d0310540107080c10484650491804280c1100c6424042e40150300300050b1313094039080c90400c460b8020660700740150104001c00804484da84640d044a818400d01c03c4018840e96103140031507195070080d00030410201d001811b1180101d400050a4440e40080112507554107490116000d112a0083d8120b1904003030340a50409400448901034010705a4200c0e55002c0c038444140080b461510300103a000100704a0018141018800a0f041c225a4080524a168001180321000824512840e501c0303008245003c10541c0002c180013000801001c4ea4200a00541c01116060030743e2694030b040d50407a1000100c418401c42d80d030302400400c13030b550840c14403062100f00d62000c1c10028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 322567014 1250 322565764 322565767
    0x130b0a17060414130606150c02060d060503030f0c0c0409030905040c11060c090a080a081b0a21080f010b0307030b13060801050103031728020904110421020d0314 71
    0x284240840060188180c841c0484c14803c00098140a0121035258200031681d01904018048181d00071202e2044240d040301d525a0302c4002d850108094541584400e80602c4040b60010250b03201ca00544000f07210308003200c01030812101000213943d5070040180202d00c60350b000344211700740364004000138031039401c12150080326105d01c50315205048402009038000400d000e2800e1a2010307243d4010000c410091040e020030761202c599900c10810300002d032000311005244454420300944508540190a0070050380810200e511000c03a290314110000e040180011841d8100f000340b1410307552400c45242c150340c1c40e60000c0d00109900700380e580e4810781c01c501244028965000d031902400052001195952540c030307002e401c2e0742c122900f1003655210142040038004c0345c6000009203400d15000205806440b0b117000c0000d2090401064009080c0344c00c410707071441c116006108032070b1801408446074001d044c044002810070207000b540800d80607400c10100348680c103042c08403000a52101d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 322568264 1250 322567014 322567031
    0xa060b031909021e0f01030203090d0813050706120c0c0c03030305090c06040f03060b030f0a1b030506040606060e0d0203060109020f0903060103062003060306040311010f0f02130b0a170604 83
    0x8a1304504c80361301d080610101841a062400e00e0502c1410162083c20103505500384041625114003800c0b40d000300308407140c2c00042403040e035441180d40e0641c01c00b0568003120307154000141007600c1002101e40d4182080c2041c2d40d0b0300c0c843c5041c1404540c001d41801040e41c25990b040f4043c002c050030b21a41481814001600340e07981d04018001442c00c10364604031a0710314a061026115041e40042c4a608071000400c1500c002241068600d030348609901a1800c0c40b841c2180b000b956a080a00b551051000f00000c00a0795401340080d00c00076104c0c0d440da1008201040701e40d112852000f50103070441001001808120340203002e105c1501d804850070300c25240301182c44e000007603005490b40c5440d100020742c942c4980c54810349201b80c400c45e03d840d614007400407998500c4054402420040045c140e01d01c0c80b6000c0d07000280804140005001c2036002c4100d00000e0340100e00c025030707540c20040740010101c0480c000c658a00d489a140c074500c09103003402c09107402d00c004041c1c0342c0064a41211 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 322569514 1250 322568264 322568269
    0x82d0415110702030706020105060901030b071716080f01081b030c06210a18030f030b0a1e0e010812130f09020711030a0b0c0c0307061506080a060b03190902 69
    0xd403001100344044040d1600400c1c0105171401a04d58041425a4500801e02c102516241e01480c15640c000c00010215103c021046841c0461111414842c006017810f020380407022888503d0440020ba0780c50a090304c0d0040418000300c028402ca030700541c4a00040c80d010074840e129540b202000905039100004950f020030007d40c8440807144803c403a06581c903c00c5500c0d0320700b0380c1d00305102e040200b01c0049284040f0745c104030040c0024060100315003032616442d110350013807501c1c1031001c0c120051180c0e940c00d03955031218400b0089407081c02d800300c02145920307411503107904075050803000309104900c003009242e41d54450f82d02d510302e080c0c42603004903001003100001c500501d14804010f80d107903154103000a01a01c0c0380c104600c65000744100380082006420b451ba0840365141c96144d036030300c54210803880c600c1001da00a0565080552700c04480101c04a184110b40241d01d4587d100d640d1188244104e031194001c9102543d02440818880003410001032110741c03500e44005110b1005400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 322570764 1250 322569514 322569521
    0x62208040602010c1209050c010e0d060911010207090504150b060c0a030203030106030b03031207140c01050c1818150d050610150306080307020d0c030206030a0903082d0415 76
    0x80250303449101000713400c1e0348840300d400340d00d08034030041000d100250b82d40d0752188907440280781001104402c0410b107076121042c4c04002c5921500400c2044507078139004d000c0506120303405000d400b840f040020441d03840c0c02420710550340403503a0b01004403003a0200d8000e041c12080f25411510901c00f40c682c24208101b10b0301824000e400560b107070f41c5403650040607500c1d84c0140074080d800a0042e4241c105103d240c460b0484540d0418024070180000780000600442410220560804082c041d18140c4103000307200c0000050301070700c1c0159aa01c00d00820560305d14600111204140001d000080307100301404031050018403c0030340c8800340c0c940d03510705002591503032141c3c035a102d400c00c0344450500d0000110784007410140110f918044645440f409a410b0203402020300b144506c0400101c00c41e000065070f8020203054507401d00c000c0c070300b004003809041100840c911704085080018074228000c114001e111901c1c00e003403c051f030786840d1500054400c0341ca0500d0400300c40d055087d00d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 322572014 1250 322570764 322570769
    0x10506030c0913020d3b010f09060614060c07030b090a020a080114060114040504090c0902070b0403090b0f030109021309050c0721050912030409060609030203010b04060806220804 79
    0xb00f0168a496101140008030303128111140302e0000c2d07000200d100350ba205e0b0301c0150740410b18103a458507411a40e00e941e0241ca160016117510514003800c0038100035107544030505641c0031954030301080c0d0f5603034140401441240c0d48001d42d540b00b0501013000400fa00c1246a100740100150351003082d890303000c28044051900300d8070490351107900b01400e100c64090107a5104209107000c801009984944480034421f602a03240507544800c141b1081c0144541141c0040208910440d070343d88084c1850400030b4010b580440000d044000300090f00c0d44403c0960b64903421004110307156910f40140c50000354088051190020003007130002400303400ca4803c0900c960024130440b66211401d103071007581e00442c0380d602410821043c10341040141d002061360782114041c0d60404491000d00b03901e40c51030083d07034040e4000c1400c1c410701051503644601c0380b20459100350024000c0180c540c041100b510807034007454800303901900c001140b004000d43c6015814010242081240700f10380c5807085039074441e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 322573264 1250 322572014 322572049
    0xa03020d1803080708270c0603181e0303070f1b0c1d0f01060516140d0f0305090a0308181e07080f03070213020421020f03070608010506030c09 63
    0x10741090103064010082ca50b1201207440c0082a40c41c14000403491808005152a101d8042895001440e2020402e1400f1008004e03e41510303840c198031040c100d00350315128281c1c68081c80c1079161003280d1800034040c1c0241d411000c3c1d0300b180e032400000c4a4001c000b900f190100f20031400c15240c1c450101d1981000c1c3c43c022003041100d1400c1c0004c07420051411110ad0180355041c80400407003804880c845410f4a200745003141d95100030490041825090fa240234160403a0311842d1441e59400042070000c50b68581c0b02c80180c0d02a5410960407100200c41e41146504895200d0000031b114680c0039a0040c034000d00c0b54904003003001e003189082102060f8190700c8006d1401410402001c02c21480100401001804a4801351803166140d00074010300a016a4080300f607081d034850550140c03006060442901e4000403041c203400025000103000c1640100e070155410395650a000c68044159841e548440f500d50346000e0501c10360f948020021045180240a8400304e0b907111a090584c85c0d159 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 322574514 1250 322573264 322573301
    0x30b060105040b070b0615090310180c0608091e1e010615050d0f09050709020a1b0b2e1205120f03090f1f09061e020703120216080a03020d 61
    0x300342071000000c040c04180e12180000e110f4000c407549c00254600f035101c0410000318510407000c160140845000000800c1101d845401150007503101c00903502c07803500c100c200c2e8490315450810800c04074030714810340707550382085a80000d1034041c1c0246039174080303800340001040d039502d820040c0c508a8401d000b07000600002001e01a00c03a80340100800b40c8030b42c2e1420051520603a451654034410b500c43c800b5250713000304d00c4840311802064503105460b4034513000040c3c8110307484c00d0710800c0317000c844051030141c410400c002895074003000e48040300f803041c0940b82d6050500515209031402e00c0c008031000c0c410310b581100480c00b400051301c40301c0701030124180c803814070000c600c1c01d0034111035000d0101d6000b2542481c04031004000c4071244d641804e0000b50844031403e004006c0c1c0403d81111250040c05036001616000545c014800300b4020303034558200d900102d080000f42d11030144201401c658418200c0d0103d40c2d104002d105800c041c1c28014541800022b20304195582c1440794504e8884 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 322575764 1250 322574514 322574521
    0x2805040c020705031e06010e040f0f0b0717150d060609020a03060303090803130303030b0d060905030c0d0c08040522050c180105070309360e0c0306010609030b060105040b070b 77
    0x13410416440c003541200c0c40302c5030900a11017200c0e82c4900500c601600c9a20103804036040c0840003490034845508284180074000290a01c0c03a0620030545060300024680c920003812503200d1038410f4065800850313000e0440142e1010404548500d039070913183c3c0341c0e550304005150340e2188010400107807603450110b2a1031841c10082c1c03204e4990340c801c4246030000c00601c210340401c001440180c80c2e160600242d900d2070070010803d4004c00070b00c000d011030b282854180a020f07000004d00b41c04007011003164407132010101e0440b1110712501d0000c01d03c0d80d09100921041c03500051080c04400c43c501c1d0441e00091a00171802560002d40c0c901e1100c6000140304030805840307070000c901202013800c0051810200e95401000f0b84114814041c0c0e032600c04548100701228070b50311814980c52105030700342c1c0b0080540c10790020107000c0340c0c4850500c40d140b4a08858140451140d040321100c0c0c940c17055481c65620307100c42e004401054107040090401c004036150301004043c01030726024445003541840c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 322577014 1250 322575764 322575769
    0x110f18100f080f060105100e060a0c0b0105030109030512070302190c02090705040509040f020103020f1305030f01050108060a0e120304060e0c0118210b040f060f02092805040c020705 80
    0x114a81024031a0f400c54901000c0d040d00004d04941100c40903185104e1181208900300c7c1e01140c01003c240d0b000b000000c100358038603844110b0310000b50080c9402c0342d150766150209401c89074940b070001c2c08101c042c40440702281d03000e00111391180315424054a010031680d0a025123408954000020a1403a10b0400541c14080c080d554007402c1c42c10141d142c0f505200001e030504600500084c9030300e40c60000c18086900c6501501d03803220352002c00342c0e21118041403451400f5407074002c06010348a50031030030074041014002c941c12140f1031405000c035500c2d4008008042e0500c040c03002d0707051040201c2e00d5450960343d00114480e0380520750000d031408404490301c0c240070520314420b0400c2421401c81a240f2003110030039080b51040f80ba28158205d0280b8584240542401c002c0d0101c603403a03080000344440400c0c4204400c0c4141020001c0707250289100080f8019118030a81042002072013054480b4104c00900f5010f001c0d043d6102d100d507442001030251441c2180320170058209010800050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 322578264 1250 322577014 322577039
    0x3030c1d100819061d150a031401060b03090a02031009030e060708040b0304080a02100b060f071103030f09190f0504050612060405030904150302061e0c15040b0f04110f1810 76
    0x261b94051038030901404000500c100c12140006003111000303800040c03402400b544044000c001044e4500e449147c103113445500da0440300d100741d0080c007500702e44805084e0305105207049036500d511289034150081c011b009141e0080002112690fa0420001c1000e24000c400386100d2403041c10996a1080c0b4047c0090405681c01e400d100d003242071840401060b51030305c0070340b80c0e010058040c03191103550a04101e11402035041c13044d60140000a50700c0080d01a0000810241d00e0550b24110008427080c001c00c060f44141c442d08850303440e011130030b00c214501074000e0350b08a080103250420501e0070704910b5081c0803017602c3c2183c2d2640005200040303414680034000e16104040c0042c031240c0d01e1a000300e000791240e0000c14521611000e41c0c00f410481c220140c810072041241210348408821480781071401041e2001d40d1a02401c60002d000c089081d07075620311a80d40600408503658255062001000400070038546c0f02d0318000003160121007441c1e9180c884c020580300390550501e0071100304401e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 322579514 1250 322578264 322578271
    0x10b071a060a140a0e0117010c0215160c05030a0c020f1816090305070e01030c051210050c04360203130b06030705090403030c1d100819061d 62
    0x4488500c0800c1050350b148202e900c102c0354003041e088400d0400600003131120718a6080200c01400500000c200821800d40c004508100c20f0003c000d000b44102003603913548019845c0001300c0c5180d800103089114902c66131826a03405003010a5482426500e5500b183c02003490715000610302681d000542c61700d044182041c20040c0c550688501e411400181041c100402d505a104a01d6510a640c1481000080011a000801c3d07400c50b0740c40d000d481d41c060f01d082c441070f204005d0303001000c034951400750400360750300300c445000b006070f6000c10030610017400000f00360070000c542c00e12000402d44e112003481e20b070a188200440c440d480351618014020740705102e540300070354414401c12120b04002150030b038100ea000b11031030b041940c611000900d040584e40085800c100c40c0010f00041680603081b00390840455102c1e41c036906c440c400a8034820303544505042c1e22050310290b40007031900070701030300d50801e0404007132021005031021100c2c19281c055028120300701811078183c40049074015160781 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 322580764 1250 322579514 322579553
    0x20301180c09120209091504050a1505010f0504090c050301020a05041e1412070504090606030203060f04051c1e0203120c0309030f030c09030a03260f0a020703020a0b010b07 76
    0x20b000f414041a02c80031200300500900601ca044081800460100120102c807a44c401815510380b8241c0382c41625010360003400c07100303480020303d5900012514001e00b8140d41d851200004041e1810341001301601042078180c440250800300070556032004e0000b4003091420303440347ca44d9145840c44100d07032207490660781040501e0b8010203000c0000030f40c3c44006041d000b00c0c1c010303291038003141000d4102107a42d03101035845071800600401700405600100200e030b0086050300c0385981c8101d140024a030084900920030741203149040070007000140300c0c400c3c641551629100759440c5040b80341c03510000094072009079002242003c280d402125480d51300c1803100340c0540c2541004101c00d82e0300e0040c00e98000e00403102200081040c2241401c1e982801c400a086900c003401c0c0d0304000c0d0851181c2c01d8240d0800c1e4031252a1441d030708285800354000c800041c1c25182d20744d43c102c020030082d08008012411130083c4000c910209100403842e9010b00b4420242a55404141c40c0540d05800883ca4402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 322582014 1250 322580764 322580777
    0x90602030f030604150906031118090c010f090b040b030a050c0712083723130c0503070b12060406180f020f0a02030702120a02240d020301180c 63
    0x7603030341d08800240c0ba0080020345001c00c0300c15000c60100641c44039500f09400c8140382c614000207201901d010b6207000c0c5400c0e60544201d095224441d40094000c44d203240311948010360082c000d51250361012802015440c2c60710040d516241203480c9030388a644224004203001c400e0002140c0107205203500030340f01d00451490f01905070f951550110340c401503a0240644180004c00d802400c00c9100280078201c960070a200060840713500c0004d2901c0c030550b0900340340042c8100c4c0d80b030005c01c3d4048440b0ba03440c0c510440395034820542c01030b21080c200464450350192400075098a04000b650058280d01c900f00d6116142240c030781d50700940060400344114100001000900030106070ac0205541c8004082070001e00d0719501d00103442504038554a1070400608100f41e16408006001c0b00d078401ca4036040c601044d011351742d5a5602215000c0cbd071000f062042049420040741d5004815072101450508003242000d048089070426407024502c0080403041105031700992140e400c0b190301600b00030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 322583264 1250 322582014 322582027
    0x901270c05190e0403120203180705091b25150b010507020901090c020a050d05090109050a050a120f061407081b0a180801050702150a0204030807020d060221010609060203 75
    0x88180b080d0310a4004100008000c2000e04d4800c200a03962000401021356580c142400705200d40c002c81e42d01c21116004804011469160a030a81d80c0169035200c0c1c07035000e801c00081380c001d0341c6d800861007202d00081d941500e81ca6030908034601041c0c90040c850a400624030741d0350803003962940c4018504000d02008500c0059231100d1107c0d054800d4840c000030303008146c1c1000da241210211003d02244a008001041b0541c404010060b040c0281da515800c240c0c0c80e028804001c40500940d03030300824026080c44840c80d207070450030416000741c0400201c840240c541c0070850b500822050852a52403040001541d041018a42c00404103403000d511801070035402c101c10300903a40303c030b810409028001d4491000742600d001c0030b042204005c00490429402c06992031465030100070707455080c0b10010710300360310a200b9582160740281c0580e260440547c00c00120380002001100c0d426800d200c42c000d0400500c5003c080d402d9900b203190035950600001902c0c0c103c456001400719802003214 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 322584514 1250 322583264 322583299
    0x70603050402030613030c0b0906180c0612100914011a0304053f0408160b1903091407030b0a0b1804020a08060c18010e06070b0901270c05 61
    0x1e03654040c003017950070741d65030f074981c5001c0b03461402d12400581200c1c891401c0c00108140841d00f07900402d140d141e0030180c500c02100ba252119001c074481c9620110902c1025604034020303a0295100c080940060916034543c10240102c481840d86006c03440101001030042908000d202008d0008003241c1034114640781e42e407190703102c030403902c4121130079142c0b200c4c0d00d100701607529480d603001c0e15065101e007100c110529501c0c1e240c21038440d0305e040f80b0410a0a07890707816109502d50542e460700b0482c034074040029092506040003508024100f40d9140c044002013001d034a498849034003008094107a66166043c164900e03040030340640819440e2441a26141c0ea403560b402055441b0101c04001d10750703079400012428030b0254401d8415000340000c002c0020308000092901741402c1e100e07080108102e500464003580c00c01d003a19080001040400085000103100c0c0d5404001d50001107242a000304900b20038130b04c2d00c210b140d002840c3d421072608200c1c2260540001d82410f4502015090103100c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 322585764 1250 322584514 322584523
    0x310308070b0f012610020f03101401140a02100903020f0c09130201030b0301090204020a180b0a0f0c02040603050f10060806090723100c03170613020a1106011707060305040203 77
    0x16005000440d004c0303081042c404c140000316405441075401c40d1a141040704408895004031001c078522105c440b07002c00c030120550101e424600b010f030369081c40d042c18000750000c282d004043c01815482a00306899a2050501501070154480d03030140022030407040b100c51a1411500c0c8903840b03414242d04202603000011401b402140d02407030302140c10120035020a004007440340003e034011b80002100410541c2010080b50031201c9242c00c008526a5031000c05003a000320940480059891460f0820803446081407100032030006100040301ca46e29030769a850a24503d420306866005482c0302060080d0301e00c9050300401070b4101410603464043c1c2002d459032140d0244a08031400c2904e4406900030b0b07101303200341724800503081d8607503481c06100161900700340c0e030411400038840c4110b884860000300c01c0c55000d220064801c19150780505400d40113504044c080c4010010050401560410104103440c001c2030030030214011419401d006c01d0034403006400c020241402c00041c00b00507200080e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 322587014 1250 322585764 322585799
    0xb0a0b0a0302070c0308070b1b0f070209090f010906051005030c030a02011404080706030f0b010c05070b0a050f0f090111070e010501120e0d1d0312310308070b0f01 72
    0x150042c1d4450381481c010b03610902c1500090a8411b020074094208800c2c8042140607041c0b600468550308503c811844e41c5100304410002d81800c240041f400504000c40000e030440c081c42e081c4c2d2002c0801c1885582110340354441903400d5500d6a040c00582c030020341c005405000160b000c0c00c02d400154002c29540e060380c4000a0420028203d4a00c5108552080c1e41c09400d002082d1307201180d607400014041c1900c1c40080035810701d0408580c101d503005213450b0240301e6002c8007409150703180021000403900b00301800e1b0709105042000000b805142c00007012078a03202101e4907100c40c0c200000400304e600c00d85006440d0b60000c81d06202b554620541c6504440c0309203818080c014240e4000e4001c2c2c1040029001c1038850b0200c00100240c01400181c59851000c0e02600c491444504140e0b888084464240c954201041302101c10403a0542c1c0c4c3c4000e504412020021000741c03090207aa0604940c001e03582c0300e07400b040100030000c0b806565a0055600100d0f44400e50428100e04010200b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 322588264 1250 322587014 322587017
    0x5010f051e150a0302091507050d0c03020313170f01051b0c030d06091e0501050607140c0316081204050a05010c0201030e061314010e06060105030a090516090b0a0b0a 73
    0x4040c8065510b40ca60400c2d101c0400000300d440b48141040503000c2e4100e40c09a9200314151800412010503aa00f9580c04541040050110441c03503071050701c0c0c04601d03103429800c5010400c40c840c0021601401c1e030000b0080700e45013520810340c1040d143d003040c4442c0000405d517410a014800c03400d032010113a411a0900141d090303551658240c5080c42c520504032064403490900000045006899000098460796036003003041d48200125007104440f404d0046a60050342809180c0119049006980c0e03070000e02d038211021916490b0001b4540056002c00ba05009a050014080c2441c28040345054031049840740e0f00f0a411709002a902d80d11394000c680c10480b00d00140c2007903a00c65004491400c0da800b040c0d8070300c4d00300f0310311a14445500c0034003a0b1b01095091444171000405209082d501c1780980e015040326102d0f03200449807a0301c050300580310180c4a072003e602040c0140490484001520662411645031850303604c15a01c943d007440e489041c41e100200701c0480b04004079660000305 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 322589514 1250 322588264 322588309
    0x3070302030405011413030308090f0a0c1e0b03090715020d0e090c070b18070e010b0405010809031c02090901060813060c050c0609031210030807080310030506160305010f05 76
    0x140ca181e17150b18000c1506804100b0f160440c00428140c01c402c00302d0041c5250400d44c1d480e0407000c0031059039980d000300018441e01e040002002007110f6440c00c40e850540e0034440005081c0d07031b0444401e01d9002070b221010b145e04070b00020000620412014816a101400648407051686101603c00152035000b54020b00300d603c00103c54103402030468445a9203c9011055410407000850241f1104900700409100700e80c000f01d62421032401c040d0403903410b1608149058100b4004503205000980139085521040c007074840c58101c8001f150303401d4276201c6001a11a507030326040108000060344174100b4000c00390203001010683c401001d803c10341040d13021544c04603c3e10211102d01c500544e1032040e026510034400c44000110062404980d80407035014251688a10f0540728011031000400014081041d40001110b5801440c0e00c440e580ea180a05240d80703032203c80c10140101c031100034001c61240907116041c0c2501c1401c0c050500d0001c4100840d0a0801203000c0c266032a4074010140e25 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 322590764 1250 322589514 322589537
    0x15030809090a0b040c0f08060102010e1018050312041106030402011b020a09140117060610180b04030602120106110a0303022203030206040528020d0501090c12020a080307030203040501 81
    0x800d0f001046500d00241080021550090008142c03c103904a49170001c0c10040203d150b039803050142c425914451005410401500009240100705039136064200252801c5c5d88004910280060088480300708181480b80c0303040e00e0050745810b140003480b3701c03601c014000c0c0400b40c0d80c0008120903000d22440e1640d0b00b803407140000b0301c000d00f00ba400401d1450030300744030b080340010740480207048071b070a40950480350011421440e201c100c00ca413240c0c1c010300460340b41c0c4070180c880c00c0340300e0804400c14002003185843e02c40707401060380207810507180543c00282d0280100702c2929524014105880e14208403031550682c1620b40c00607800240c101038000c90f100d00c050710203044d540c019907040340060b400141c0d6441c0180d25100211419071321409401c0091880070020006250b4001e450710100d5590b4507258200300324101800000d407020343da01c01c51000001c244c0d400c0340029115400d40074a03007080502c10081000d449030005803503500103000840010360004299000d454007400c15100c01d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 322592014 1250 322590764 322590781
    0x1101061a03061201020a03020702150703021c0c0c06030603050d020c06271807020609060103020904021203120103350405040902030a06050f070801060c0b070f03060801090804091503080909 83
    0x40ca5201c0b004419440000c2c40f0906d03540603401000000d2080d10b032521030300010315801a140c000c4400c09400768009209589103d003100704000c49240203401c12071300340051900d41450581c1550030171004a9968502030042c01420402042e40100740d100400080f0402c0001c80c19500039440c514055a607503000100c00411010b503100309040c409043e461060031142d00300c2c404144140d6030000580038007804105490400304055050300d402800d00c0406031a00c0c0d0034001d03c04200c01c01c10040380401c0c00050102d030058050035008501404a04e940e0017604043c1c99035040b10035441602ca1106a0204c1c04c500c00310605a50464404590003e02050b203030010a00701400c4d00b10003407803240780c28100150700e002d0a00c3d490080400390345114140c1e80b20070060f200d1006506002e801000d1391030015034983d00c2801c00f84c125083c03619010444590321440282542c0c0c801c0012140d00c0d101007801c1c09940981d202c0c5805011081c00090340d00c9141d40c81d040000e110301c1c1c013014000c10620f0700140030003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 322593264 1250 322592014 322592029
    0x1051f030c0302160606060e0307030c030201051606090c030209090316060b2b0605060103140a050702070b0d1d060606071b030c08030304060c0e1c1a161101061a0306 73
    0x1d00e1481611800c4004c54504a4010b04070360068901084018000d0351107810001540403d8070380c002e102c1501c660840d0010760b06600b0298429604400340d00101d800105140540380801d07225413036030050700707040d4810803a01040c0248a0505548140182404180006e012440164020740006400e87c0501f012500303030b07025880100b254034182601601c84400d040362034211140502d000308002c2e218080118103841a51030440340703101003000070900c5030300207620141e00001180100c82c407441d65105624901d4010640b031079212560340c040f0303040c0328041c0d424000750100508060001d40c0313003d90000c0d015000c0d5400103801d0840502e2106600862511b1800c050f50700103100144066407045030942c1d9034030883e0111001410501e041404501418400d81061401040011a5040503200c824680703504c8a0a4501d04806918400302c503401c0d484090040c1c0950748018501007840f100504990000c0c407003090310b41c2c549841000030702403002c0380043e20704078240e085e580c90b241d40c000184034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 322594514 1250 322593264 322593277
    0x115031511031006030605010201090b280f1a090601020613061107060f0c0c0308190209090705040501230a05030a1509150f140d0206070c120b01051f030c0302 70
    0xc0d03507400410311580040001d42d036401c9441d13641c0c00380449030315900120f0036244d4101e001400441ca02c00403914682c0c0d03002401c07500300c89100c244030329485082142405d890051500c040d5040ea140e8002c402c04490f600264035402d0141c400a02c94100000002e6582c80d000700080c44048c0344807070150800203181c10106081580780d04880e101c4605040202c001d0030810030310392816250031031040440380074103054010703241c04d6103405a071907441196036041905200b203508a4203500b01b00c56212581c074403c403c5e01400d85680d8907a1943d003410005040c2d2507540380504540100100d26089034100e14040321610042d0b403030440d03101c0c0c0310f4111580240070340c0d02500d84100e1701d8440c041070300803e40d0322410b02120310148440c0000d684603031000317003e401400b640940400104100e2540d0900400c0c10a00c544050441442c00d2030607259a144040250000f400c000c0e044c48030340003482104004203026000807502545890307904419110036039411000c3c0c106240c3c4030364019040c140240c3c1079071034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 322595764 1250 322594514 322594541
    0x6140f0102100e06330f0d06021c14280605100f120e1203070e0607080405010305072f0f0703050c0405090313090906020f0f0307020c0301150315 64
    0x4003021141c980d40700e02d402c5a0031080345002d42c01400001203105e0101000008100c10500320080c1c600520050000448059400ca0b08a038446000200d4510040115498903d00034082100c80c940304010390301c1180f030008280d50044144244104c0b00446c400c1e6003088140c0c4814031000d010b100c1c078041c0036240d000c02e43c006810a8038080d49900401721140e42602c1e65500686000581030910803641e614000c04550341c00f8448032013080d21f0b02d9000b144c00c10300e1401c010260021020014480340c1c8032420031240408007080801003940c0600800d50049800d040c1200000300030b9440500019801c80b0f1403a0f01301442d21110714045040c03109440c070324900c90a407101c9580b681000c0b56074643e40c15010703001e00d1030040098040c240c01f00568808403080803088540350305d003c10040c0684003590050f02c00e581e0800c08010042102d100518288000103207850b103d1a00c11006414507400841083c041d034101300740714000c5400c00d03030403038190396000c80c500c9440da02019000008042000f200035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 322597014 1250 322595764 322595771
    0x4080c0111060c37020105011a0901081506071a131509030c02120c09060f0a0b0c0709061203030f1a10140a020a0525060c1401090b1906140f010210 65
    0xa041134541210039030703149044d4000740300320713641d48000d0200c0308002e41042c3c1284405002c0300440c2d40c07245070310345d411071118001c5881d400c40b05800103040307a01449003111351121210b0f0b000d90310200754605680c080b0390700055039800040d42c0c80302403c1c0c240354100c0d0208507a4030f074580070416004280d4900398070b030042c081e00340782c411322441603640d80115800076100780a200002100d034580031700c0d201c40703299000d402851154070301941c640040c0c10880a01416004488011a200007540301c0c00b401002812543c9500000302c2c03d010701280c0f110480c1c0b219460605c0319400c200a1543e1080940c003105848000d881001408211074501d032121207651030800018038140031a03400207022a0032405001541c406412404441c0340d407042514980d4809000c40100708041ca02a0042c100c2c854003c4103400070b0340700034601850131100d0860040b02d41c598000d040c803e00301d41d150441d0751210b40c140e0301006524188900d00e21040e00e002d41591144d0051030803488507034402e01507160401c01e003803401d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 322598264 1250 322597014 322597087
    0xd020903150f010911034003031a0d0c0b0d09060203010b07050d0f120b0d021807020c01020c0913260309010f06030f0f02040e0f0304080c0111060c 65
    0xb010310002881041842c6041036044814101c8070300482e0300814070680743e0020300b5011001850316055244000c8403080d4128081400c0d00c01504040602c0b074400e980001313a0546032240c0703061001a41195070f018800005070100000c0c440c0000d4401c2d64550030b120754440408601c030401501d6901e20040c0581d001000005d402d100e100050020244a041500c61820325200c0440302c1c11502c208500005140c10403035903081c48554008800040003400d030308109071240c1c0100b94001014140d0b090a00903170b0041010a960501007050340020900c080c2080c1c1889070000303101514050405d0900c0c0c091540c0c501d0070003244034814070541c240402044519a10351001c000b080d042203401401950920000e038028504a114200550b03900c803c0b08100084551620302c51940d081c0f0301241c0050390741032488848001003001945080100780103540d1075050510060038003075540441c81c18400306050118010b01c01241d52540316030304c0c5e03000507158513411116210028100420b1582040c228860 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 322599514 1250 322598264 322598281
    0xc1306021006050d030512101203110d0203090102070b0c07030203011103040507140a1203031113030c0801050c0405090c07020a0b0a170405120d0b1f17010b0d02090315 74
    0x208450107104200400019540d01c0c01e029032012030f10001000503104100401003101c001ca01c1c143c00c42d10070340c808400d694442c410708264542e40f08007580420751a0760301c41034102c0304100780c0d09070802c548061030071b2240c8100040c7d034171010341c02928001000412581001c0320204500401150005e0007440800401c104288007131f4005e40d8151340500500d403000c1071441100e4403002c4140350280031740d0005840c000003071031001c075040821820075031603007a10130341c40d203050021389820203d0503088040700d461803900105400359a802400a6418001003051000c0c0c45410358045402c2501d00c07420039a11000c46038a58464040025800b900d0b6141c0071031140014000340510303080d207807100325682204205200000e402110020450390000c40d01c81d0030000722001918050066440119401c46c0c840c00140124810a0400400d501d1724103824401c154851034662030b440c00503c00c0c5600d541820b14014140c41407040007244150001070544054408100c030551400c4034480034038090809080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 322600764 1250 322599514 322599523
    0x18030c030b0115020a0602180a0b03070e090402090a0507050403050d3902060a090905090c010806010503090c01230a031d010b030703060e0f0703030804120806060a080c130602 77
    0x190361907525440080340d420301100050300c0000464000381180e900960b2110043d40c0301c0c03200141852841344111006484542c421005000400000c1740c0346c0c03600c035030010541d12144010b50b00c5008400305100168680b40360300d5801021800b0041469540d03880c090382e6601c211b0b440100144200c0449114460744080c000d4404181d040c0d010240d02260008800130481800740341485074181d2104400503e8008010102889641011034015075541100c0302102da0442d81360403150452603401c07560f036900141441d4480c809081c8141503040800d841c55907110503030b07003050600041d0803840358900e00c0c0d9014103060400310200740741d172083c48500040c09004219480390750b211412141c82500d11040c014a10005c0700034001b440040e00e0340d22180094001c1540820040c0140701e064420814148072a0010b1030190b10380144da030419280c40d0b9030210a901d030210400005806010b1155039460403100005024500281c164407a0000051980b00d0ba003014071440c11000800a409070f000704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 322602014 1250 322600764 322600769
    0x2120102090d0f0c1508190609020c060a05010b0301080304030b0c070204020d0b0901051e0108060414090a031106130b040302160f081002030606040b0c010b090a0204081606050d0c18030c 82
    0x1004280c0e101d40d2064151100e21782a4000780210b601900080d80b55029480c241e4100461000007041040d52280e13014120380c48582d100410703410040400c01e21102a000c0c0c00e00618810100c1c03032039503240500250f26401180401481290600302190482e561903082d5002990020811541e40b40540c044500030041004841d010b220090000aa00d1070049007507140178404514100c03201042e503004684200c40244845d42c450b0395100e2020340c0d05103141c0c036a07200d03126100c0142034a40007410041c00400064100018540c0800100450209641c80174ae102d43e0380210521440d45a034131b8164140140320580041018443d07100142ca2140401450b04403814103080d10110006100c0340401d91000701c0b07003030340c00c005c04100c20800190990b00170b010000d102c400014442020b400000e040703980036112005070340c0c0c002c00e05000802042c00740c400f07001a40c9004018651520a001d0411300445031800342040e91ba40c14103c003d4054103c0b4814101041410f140c81916031402140051250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 322603264 1250 322602014 322602023
    0x103050d0e0102030405212e0216020f01050d0c080601201902220b1503060d080f040503061f0f06051603140310170a0201050702120102090d0f 63
    0x2114950342040c000c0c2a201d1880700103070f0240d441c2c0f90800040c40043e1486480c0900b0200c000c0d03400fa9070014040c00034034030389400c035400c0c61407404125001d51820001c0302651501280704021400c0040c81005440c24800e5055840501000c48640141c40a0103100200313010a41800201c108841d1300c042c1d03c0e8403804090301c802c0f0a00c80b40f203100001080c81e6210400c0d01e60300501088002400508411029910060a00003483c0c1c409200035040044000d009048a4a882003d4440c0c030b0003c000e11900f120117031059055107031001c00291100c564002c045c066040000d0800c440007022412507019203000340c01c403811030401002d8040c0c22500c0304040080d6880c1040042401e20000982904070f4030140e03a00c50a20381c003403040c0c10310125228401c809020040810464800c80040594454030158800040d56460118001100d00d0701c00c0245150760003000d21980103070303004816103d01a40546400098a60003800640240b16000f0102c1d1701c020760650980c02c00c20341103404034100e40714 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 322604514 1250 322603264 322603273
    0x30902100f180b041701021b060105090609070e010e13020c06060f0612070f0201090f080903060a0e0304141305040b01081006150804021504060203130b0c03040e10090f05010305 78
    0x207030100342c6000040780266195040100001c104a003400a40d6116003c0100001840c1041500c0c0315404110402c405001642028004008902e0000c4829a0020055681141924000b0310041100029111503414000c40500c0181e440c0c5513114143c119000c51102156102e54403240247d84603000c951483c8151140c01d0008001e080c04400e1301d95400180107000055250050203898410314040341008642da01d6040c20b002c10003010178a41c840d4043c03030382160349107800b5080c5824032030020300c03600896041660a80c01c0100000455044410b0076550a00d0303800e0310000180035441026840001c01c4c145030511043c400b80d00b164030304032481e8000310384041100d6207110041c0c48440c41070040e0f0020076007900003068000c0003a181c0c01840240302c1120402c1c0742c0c0b5240401e0308107420204c01a440411020200d0380000340100190207850490b030305202080d03107201e6881c4514050502e000c408400400d520500c4405200042c00e98410148517030450141040001c0c0001d10080d6154400e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 322605764 1250 322604514 322604537
    0x6100c0c060e0a082808070209010e0406051003170f0403050105010603021309150501030e030712110d081306091b0303120b01080f18030903100f050903030c0406030507030902100f 79
    0x2c0010300314541101341c5d0040201e07905561119502c2c01400d15007a10050800c00c1002c0042c2e6428214038060202002d100c1100c1c14242403000841b10000d0250180b82c034844001c0c0003161090701c42e600030107151410250390f1599084d404050f0302450340021f280750700344000800c102e40c054024111060040543d032001c0c03a84c920f1a031080c1d0340c59184114246407004000d009a510a8012110700215001141e2500d2410b90b50000e003144000d40c0400050b041c011404001041440301d003c46044a01c0c0428140c06c0126003a0114910208001c120950f035020500c104100712a110b070b0b48401d41d5829a040503a2402c0c05441084502021080940303801e050600070740c003034031920340030355402d003404070190340c6e240c034001ca0780060240601480d04c414400d00b20566400c10840030100500fa0b070108095808403040c800f59071024240c195190414410410110070880507282110000d2502140c035442c0c00c4400c0c1d00401c1804000b940040584d1241440b80f50401d80804216010ba035441890700d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 322607014 1250 322605764 322605779
    0x1c03080c1206040c0318030207031b0302010516020406080a03080105030601060815010c020f060a26010b0a1d060d0504050f0706020316020a05041e06080c0906100c0c060e0a 76
    0x840c03207032030903001d024000c00326031582019072148140005078140000c0a5401c0c404546a103240d0400442c0184d120b990103004011202c12522a9203400480b80b4507401d041d9400a0483c1c000c43c1d00b1110120440f0ba0008d0a540d19500f203c0010b001c0d0806072100486c0904004210040901540340240310705800000e10b14820f952040c40751540807058209100c840c0c004449400d1403203820307640030f00e50001840165807400300070f040d44400d1341c0302da13204056030151f02c0400c10b036550307010280d18994000403c51040d10400320f075400c07182444c28107580d0000300f90030300781c00b140c0c0603049800100100310f02e48500055480f40c1d02840c0a0b10403104001e08052a0b01d64030303485070142c000107800034007003609540ea42d82c000200035840141440c91103a203c40c007150442c2d85102001c0c18414920259280c16802445100082d0240c6c070050190181941c000c02c45070007001d04901d0041c10f1100b21b03c641c041c45400c00e1201c2c0f641c08070400d441c80390348210040902052070030b21841150f6203a00043c411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 322608264 1250 322607014 322607017
    0x30702100c0e1f020a17040f1205070303050c16060c05010b030714100e030d020c1203030f0c0307030f0c020106080d0203030f010603020f1b010204060e0f0d060506040b1c03080c 78
    0x2030300c008100f80c0700755850040803249002c01400000c20b520841c8885400101d0000350300c0c90b80c10207414116211450841074910681d140c3c0e0010540c404079490300320100781d021400005480d01810300ca65269801840c0d145414030045500821110200010881c1c6600041480714070b03024100038003040c8614000c0540383c841c14400d02e240e000500e024402d41781800d0458141ea040d00f800c3c01000400b410000c00d041002942ca1480160030402d0450500e00e8070070111445030061000541c190320f40300045034480c01c0b01038443c4103003072004800281d60320301c20f40114010102d811014000d4810794480a03000e040c060290000c54007480800680c420300c00400d5074400c0001c400d8614041e4070b0110250025441100f0030001d8040c20403900400400324040c3c0300300c0d203018500040c0c2d15441d2440080808510884070761060786070b070031199103954031088108502c0d80c001d1170005041e15404001001040610396440d0003050001d6802003040c03458a03003640c054040c0d1034460007a5111949590a07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 322609514 1250 322608264 322608287
    0xb0901031b081f03020409051e0d08040303020d0f0f14010504021608070f050d0f090e070e0108091f02030612011506030e1204080d030f02041d1b030702100c 69
    0x542d142c0005040314a07602c0d01c140501440d50000540140c4a401107415601ea1a0041d1100d03880008000c1d80c004000e52440110321081d00602b48103600c03118003c01445000d40060308041c0c0100390803141c640c040e0301c554141000213004016003004240c25401400901c0801d081c2c4c11a07010000907a4282030007121807c1c40101d1488901d02100da49001c4103412104040c0d5a441c040058140056020411690403c030140c460030300c0a030483c04001d10300c0f140b5400c208120540bc405101c000368110090440b001001d00300341c08169520f503103aa2401e15100d000ca01d03000340e034400c03440d541c808a500075805a1020b030f86410089000d6240203098942d4048120f007902515081004105d1080d441940c5d0440d510096506088028200c0e00450b045034000c1c451a4020103014032440d42c044c45041204103000c0015814a894039010300365182c400107038002080b414100140c0c01c0180c20000e01341514003889125140d00301000d009540354003a80007403844625001541c1c50344c074003404500c1c86 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 322610764 1250 322609514 322609517
    0x30c0303090a03080c07050a03083c0a021f06030209060a0b03011e0e190b090403080c1c020a02060609010605070b0c0912010509010b031002071e020604080303010b0901031b 76
    0x180e8a1544d07842c55401d5221140c290018090031708041400e50340e00e01e0803c0118000d915054031144181d020b421004d4501c49a000130301c5101c0c0d4800388035004e002c94440b41200ba82d81141d1901d110b8201a800c0c12111540200c142d030380c032000040b0304002e6904c100107680c0203550070046540c40006124001d1058014001080400e10040040001565801c41500810741a402c0c1441d5141c5150b003c000040d590811000755042c8804810300a612802030601d104448152050505407000740417443c0103082260f628a0004443e100701e0078024100044110b480800c42d990500d140c00251144400c1d50070510400b12000009140c920403c01e541c88a90080d803050744540303032028a114150b10810003d038020038107804220341c1040a201e094801c50b055800030508066000170542001105500708848510502801c00030481c85039501c265618404280c2c2c2d504540c0d030001698074080c66000c03101a1200000101c6e201000300003410b0b900000b80c0301403140540182035241c001c03008128000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 322612014 1250 322610764 322610779
    0xc09090f060f032303070c170604021305090a080313050f0708070b0702010e09040b270c1e10051804060509040f240b0f04061d07121a030c030309 64
    0x40491110720609113a1251983d500e01460010607400f800c42e00505015144c1c810401d4003003110150345030f8862907080340350000d0030b03003890186d0016445050101d04003603a96691000101d65180820646800d00c6e00030011a4403440c0c40312110003400300c0110116224017845685000c03480000515101744d410803c00307024030904141b1100d145412003001681040762002851506840e01d00d182d900a42c043c112001c03c1d03180258410303240826443c06190040c00384034140b09c84000201b21400e0162080391401b850140703a400c110124109a450103900a21201042001c1500071000b4103504101d00c440c90007d9511000300700c2100c2031072068942081070b500000c1e0000700c0310f0440c0410240709032100c02d03480d24103110a0b00700070001e102d42c40045560b01040705c00b503d4060386190400c5401c642c01e014140c10010070086104003040a00d1410f554200800c0e8900d00800c02c0d080411076000302002400c03415904980441620400c1c903019004000705115075007000b0040382d40b00b840281226 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 322613264 1250 322612014 322612019
    0xa080a0c0524030a1e0207120f0918020903030a0f0e0303070803150310020d0614060415110c10031a010c0c12020d050f060f010e060312030a09060c09090f060f 70
    0x101c0c0943c40100307055103090b81c0d082201c05040105201c01600d88003001c0058075481070740342080c1a1061104001c00784003040c1340144040754040d00b1101074903c500400c0030503c15407203c44000c0d014072800d05900d40400b06502c1c00e8268807100502d203c5281c1e50340c0341080740c580024181c49104459010b00f960908200107a8211410309829598810143c201c9003900311032101074049030844c84e980c00007191980c0c0100000e1044103032000a40790f00b01e6a47c0d1a05142c0845020840e802c00092000c1c4a0b56454800514000780944600030340d01804240004031491030080051000200781071104c040005c0300c0c00c0701d521075002d10108503440700d0b454031400d003018035082e10104045012684805a40f04131030009005000508002007060000c1c0200d003040c0d0b0b824842d007503058001d41684495401001419030b00021040701801108040f01da4a480e081042005041e04a1000e0215030a1011240d5040c1d44074807500c1c1101e004d0300d020801c0304e12159801060310dc2d1071042084000100809 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 322614514 1250 322613264 322613329
    0x5060a0b071109091516030e0c030709090203071a0706053612070c060f11030706020706060803071a0703020a17070201020c061f06111b030c0a080a0c05 67
    0x100ea003080f0100d048526080b1901c3c0c0c1c0041650782140c1d0501d40d46d0203102107030038141d0140201d0007502000ea0240c440386041c000425907900b00e91080303052007a1030b1401101507443c280030b80f00141140c0d079041605050441c903942d5059104200c1102c030315250200080407035003401c43d0a402a142a00702054808400e00703020030246c1c0c2100c803103085004600d41c03054404085002000800c0c810142c1600d02450040081d12030301c101c08052040c0300d00c80d4000780344520048110790f83c09900040050b103400c3c440c140000100308940281e801440300040280900c042d8000410304001900e40182c2c040d940c00c08100d0076400784141c0038021a803107041780c03485000d2030a20309130f02c00e02c01e10006060080c0700d803201c2d04d0f0840c2620040441034440920404681c49c2c10f074448060300700790030305003c40607034030312115594407a0b46810302d0740d004058020b584a0340c0912402d883ca0340024100103201e44c8400046407902260360080b105240702103400116414202a0f0728a80d00170020226101c0d00c0d07280c103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 322615764 1250 322614514 322614529
    0x513060b0307081605030606100c121b03020604052e0e0a020a0f03050d02010203190e1c05371115040f031101110904020702010203040302031005060a0b0711 69
    0x1850754903008125002c540201d00300445152001a40a0051041e28220905080c05c0e00900028010501c20801d078030074a0700a03070200c0c282c5910480415030894800c501711055a418284401c040180034000020b141d40081ca49001d64081d03c240da140040708900c6140360402e41800307054400900c50080b42c0b00d84580d106280c8992024240d070342c10442c0c2e90000c2d4100c030140e04a82e090b4006000280140002003110400e007000c640002c5246060070b4595903005403078020f40340040c640361311014140c100103004481c00d405200c200004000c1500001031b00711f800c07844041d0400301c000082c1e80303200b006d08001039140c24a14500c2c010320a0105008a818038a01089000103205141401008550034a00f091050307000b41c050140004852800404030715041032031007000d80c10400d031036201010f48811079585030f404986c0141e440d1101d10040c0e05600460340301035414007903c520f40020341410f4100f02e00c12481161000001500c0f4040c010f401d0161074800b4140c1d0000d1700b401d40d06410a4507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 322617014 1250 322615764 322615781
    0x170a0f110d0525050325020307030b040305130608011404060f051512070503040605070503090d0513030605010e070f0f020d030207020a05060a020a030905032b031e020c060109051306 80
    0x10f1500f407940c5084a2001051542c10310f08941641c800510305401001050a040e900466041c0c042034550702038000035583c105a0101078101e284c96004901014000c10448010448610300005041d0f07132804040d004850901c1203500120440440380c42a141511941050703802407404145c90314100002e101104000c5819658058410000760300c468000c0000d803446113110b55101c07607483c500382c50301c5015a4009007100c420722a051041c00051034020451803461809843d000d600c406141380c032600da00c1d200f03a2000c0c090034605000406c2e003040c1c0782c00240c452615600e902c3c5c0c1e800d640140842d00e0040c25208400180c0004400ea65158405e40061811301c1c0000c110140c0140c407400082c0e540d50140d001600940e1041c03085e00101600004910002c3c01d088004e403c07241003500000400307600f90004284403540b44130300792960f04d000f41d0210303800b0000d02c281b00d43c2d80f102c04904031000350700c84021584107100300300002645030b4007406103902c28501400c0e00220213806a0f41d5401900012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 322618264 1250 322617014 322617037
    0x140303070804140a0504050906071409040c020105041e080d0203060d080301080309011d030c01030b06071b031506140409020f15131202180a09170a0f110d05 69
    0x411450011800c0d90000d00b0203040c03603100850015008204200c845621580451300842c2031104001101c031000c40c031181c1c8405c6034200100801c030341d200d460b1181d05c142c0c03a01c1c1d54030915040f06a410b80781d0541c00240b1491103078080960000b510001c1d100c2898448070300400400c0c0c10440800d80140700c0d0003464100d41c0243c40188250f00d03690741c0002a400980103000d07560300104084078151303884040c143c94041001e01c060035140128012a84420f07100341490305140d110703448441283c0b580d6040300d0003550410491050810000c1020156009a01c402c1c0c4904070310b5440801c0451030392150314220351110028044501d28401440007512140c1300a0740d111400c44800c0c400d071f440f11501c800c5101181d200740c0b9504d000403980c40070500d540390052a190207455184000580702c0f00c600b5402d0741c6d400407901c3d1480d611900c0620140480c00002496040c50b000c0e58040b00f802c2002030f192040c08e5840c0c170300c401c49901100b21100000c24403610303e2039104450000c40d05019000522818284 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 322619514 1250 322618264 322618267
    0x21f120e0721020907121d0303071b0506010306200406090e180f160b19030203060a0306020f03060907081306021e0c071a03040f0b150301090606080c030a0c140303 72
    0xb600000d0704c403481110310501148500402d00d98501c000d12440d800c4e46099004141110346a07079400b076903400014055810310000c04c40b40d1400f90b0180f42503007071090f8042c046450310740c1c40f4901100a442c14003050032034480082d11600342d00980109850a6542d580d54088a0f1460300d90400101e80003c0c214118401c640780e0518004042030107400840e100c001c00902c400d0f0b01c00c407030b1601c420b021940900992001405007058001104a54080841c07482c500035031645c076640c0010310952521b6000400280c80010010040810040551722441048400400d650b40d1348006480c651811030301d02d010007086007040c10014589a02802400101c108400240c0031081814006c0368003640704044141d000032400c00240410204045510407a48901401e50030650303104000d050b00003100824034500c200025035180394240201118000040091102c540b02d82041d0300207084034001c4400c82d0080d601070b0031a5040014000249513807140401401d03030b00c0d007804101254002400a03506020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 322620764 1250 322619514 322619579
    0x1a15040207060605090a0204060e09070905030a05060601140301050d060903091a0702040c11060703020a02240a060501081501050d0b06070b0a060503210a020a021f120e07 75
    0x2180d20250148074030520001032200c4c2807500f009a052001070449000c0350041005001841c0d00580032a9010f4042d645c800b81a02c07494001d4401c0070300d0f50800382d014450003039640d007409000200c0074054002030b2540c0300c1c1c8442c0300b020003880380700901a0903041904884804002002075000c40c036068064075010924940720212028403030004815046500d1000c280038066161600c180020100d071410500c40c03a40840c03244035140d6000074401070034140e001c692007120300d000744030304000061002c0b69110f03000001108051205425030303006c089146092001724280d400307034040380e018204040144004100d01e00c01147e559000b100384141705915400c40401c261074440182c010207201d03010200e0f0fa45004c02c5003401322002c03613001c144258441452201a080c0885c20159111500d80700c890361100040c0060349002c03400c46009400120700254000d0645c086980c41d40c803551140d6a20900601d12401c4406645032022142d03a150401d0400f040403a41004104031024141f07919142c0100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 322622014 1250 322620764 322620769
    0x6120b0316031703100618090c0504030302010c030903020304050d05030c07120b090a030807050c03090a060f1407080315030a05010e010603020901170601170a02041a1c1a15 76
    0x41100d200c603154100c0400600420448200c001d00683d41c401c0f04074154039005111001010140c0301d54414450448298050300750b015050ba0043d058041c424009003018401c001c0c02c0c1c0d03015100540047d480c0c1039040c801d49100e4001c09200381d41580c020b504107070070403041182850540e0000c4071140b000700044058400c090254070000c11030f05256000f0201203082811403211700600c85035054014000714400280c11000c032541140142c41c009480b10b10200985146124036140c0380d0b4410202c0b000090300d560700c41c04c1c03202d408146954051b004148211101c4035402003000040003c8030034000600d61f0381080b40290510440201103400301900f6841e92821101080c9494040381d45070502401941026680d02d401040d0080362036000202c0c0c030000715118081801003110908805503117114168040005151180c1c0040041001301620803803110046e4140c0440c5004403101840c03900a0f50280c03000584007900001d540c4081141d00e079148000840003843c0e024601585450400c13140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 322623264 1250 322622014 322622023
    0x1002090a08060a0c0e1215180f0c040f0b0d080a090b04120c0e0c070f02040b03071818031b020a0b16020102060c0901020d0e1c1b05060a0906120b03 65
    0x2a043c4840005609419410052140c0c0d12000024091030700d06140320305030030002131a8000348240054080403901d8132000360507900c1c10f01d42038100a02c244000320003124800300f98140c0c05102102c040280300c010590440c240d9049504a45c1d11060205060010580c03240041a80003031038640f000e100c948038400300095400903000031b1614415076918008000d801210b590103004a000014850b28210030020114403174158001c05030b03424226082e0454881c1d4100151021004040e1090350742c403114411520502a00c0e11943c8505040700f5140208140e031141e41080d03010340d94082218401c01c031242c809034142000b00d03000180e031000064240008409001080c503142c0310400c04810310300009140007c01740041003030a0b4104131400045e030b000103d10020210038106004492400743c0050000c010f007148049840407000b50030750821920320110218030807c055240d02d5241c6503401d1018900403282188086122424184529401040300141240c14282c02086107007050010a061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322624514 1250 322623264 322623271
    0x714030c060405070509010e130218070e01030609180f170307050c0115060915120207030302031f050a0603051302030d0906030c0305060d12050d0504120e060c1002090a0806 76
    0x81d800960034407040000510482c00207040484071101a035040c08445851100c2c041e0200d4805010202c0010031910741c80c545414520f40394201000a181203040a410010b0360300c0c185002a02c7c0000c00706090744203206400d0340d4100440390101c06141d5aa03901200003013610142c420000030b140f178003450031000f00110301c203600980e02e480d101e0500c00700650a48200c41c0740210340d03012100c8280040c81d4099003000c00c80d07001c01c58903404000d64031803d849034184c1235a5400a9400000c3c02c0c3c061503056001180281d1500e04100318a040540d4142d0007588580a8694000d414206c00c100c3c02e8445e402941e0802002c00c280031241d000c941c0044d140454103070900300402c00c500d00802825030144502d00c206030003810706111500d41200010a17071900e80d4001071552105440860b415032003070060761106640c629081141c0d00705800e0418020804420150010f818000106000e003440c9007a40c0603071441b0401070400203051a8010b01940021000d1074100b0000c401c0000e2821041000c03500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 322625764 1250 322624514 322624537
    0x702010e0a0e070909060608090606010521010b09190b092e0206090106050102240c070c0806040b1e0a09081c020c0601061b0308070c0614180105010812071403 70
    0x110b04c0e1524241c00203907101c42c0d03c503070180684442004200000461801c1d40180246070003966401c4202c085000200065003981c9101313291000440c1c1e00d10400c0c01002201d40455560242011614600e920000c1a00a040f001607043c049282c2a0a08040e0540f44003800090f2030003421460090304440300e1400304c880f0040e4829000e0140125003032040c0405440300f840500394615003209078182840740b89405002c40c005207400264560755040954010580c01221891544da1b113401c0b099a8184c240c50a4a00403c21f60201d0060f80c1d40d59090942048810139080540d5107a5001000522200e4403d8950f00000c0010380844860511083c0c4030707200480300181c540410b03d407460320340001608a9001d00c001c0700b0300d0790304021002803e0103d044d4140760801c035030b50b240001203804005a0500506d0b050410400c805c40607040c121380343c402c0c1754420341d5012101c1c4007261182a50740078490700700030f50812401107550031401801410124000d1816083c0662082c02481c51a400003c0186 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 322627014 1250 322625764 322625777
    0x15050a050618060604180e07120b15011b03020c060d0e0f0601080604080a0e040f0b04050604060506030703020702010c08160b0c0c0607030207020102011b030f0e060c0702010e0a0e07 80
    0xc0140b80000c0d40602c40300007070044901c40d02d000d20226a003407140340070343e10b96800e94000c0c04800000d40e400000c21990340b001501c0900d503841105100c1030101d89021204400401d0010b141d0880d0f00c0c2c0c401440380030580d2114594101686100c4030600b010b030b8290114026100034040030b44540c40142881c1c1c1141000003101c0d01002c00e064141140070184c4030b80390b005a4010040228001a00c075081a007260355146d8a4410b40b505a5103440c0720f42039560058103041e03c3c2c0b204501594002d01303404000381c6013489266120340030001258100c0c0a0154014810300c0403901340e603c203a003d01141841810300400a00f1a621031070015040810803015a1b5841a001030811852400d00b0343c00c80e6601c07031400d0520b01e100c03c000f40ca81d50000c0009081507408200c24096a100350881070008200700d800407040070710440c0c0100070b004000004c4884070f0805a0302d007081c00740010303203600c648510304c0340c1d600f81104c50f0300440e504048075410300d41c0031103003480c0810f614128041c508c0c040c040c25100c90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 322628264 1250 322627014 322627021
    0x6050f091009150c2001050a0516020a03050c010908070b01050a0626190e0d200a150204030218010303172802270f0f030d030915050a05 60
    0xd03150204a001151006041100e50000a03c440d004400c503d10b00e0b0300302055901a1900840d02c0340000460241d4480c401c0494101c407400640c400f43c01800640c80038407059545440c0c401003400c8200c113000060303115080060200340710303002405000c90f44100202d2402e03400c0d100c803038840d00804404d64120050358010025031604c0e45114004000d2800c081c84042c11098412000f02c00c402d00c20b00c5620495000241c41e6a18203a5542c02d81c007144000300281c0b07400508580d540c2201001000c04030b65454185102d404020220030710104095004041c0c800aa0b43c8508075495081624140c95809002c04401a80e8401c54803e0f403c5452001c880150300d9814010a460b034507503540b0510090313003c1440100c1c140b0cc0a1504102001201200c0013002c10724640007d215050051092441d01c2c000541004c0f01214401402041120135500740482002001040c5841ca810035600d54407128003180d11078082c1e0490311590723005403440501028801b01030701c00c0d500201d50341400c0c940c3e02e2041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 322629514 1250 322628264 322628281
    0xc070b120109110414130e06070201060816062a0f0308061e0f030f030c0a030206160f2a110415050108010605220b04172b020a06050f 59
    0x414014031030080d040c40860002e268076a114401c41c00b50030001c5d00b2001040071151a0141041e03400d0400240401c95601c03607a0a01d9195401a1043c030019401c12100050030200001c5400315064a50720012801380b60035000d40f1182c034035860740040341e08010308040c00d80e00c0b019021101c25001d103560207070701809481d00800c043c0c00100158400c0141510700e1200788401524584404015142c00c4140082c480c000384c500701c445900200c00d03110005072007036910004504082500d1098080711440d8841c4011295001c046030604c0001545980d810710705644a120016000500012000c01000c00c0c01c0c00c0e901b198041d0642560080e5800855002c1410319104120b80c0c0c802654281110908200000301100c0c0d041c0f1641c02007140c082403624404108180d0301c9082c07144041d003582460b5480711050b0745908544201e601000380482c03030040c4584042038000f298040c003018410b45a9880700c2441700301c036408403820304620581d07850b400014131034800d031400f8401d050781c59245480d04135007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 322630764 1250 322629514 322629547
    0x3180f01030c08060d0c0b032503020309030d022511010912020d110117010e150402070203250e1602011103010f181b0c20090c1e0304030c03080a0905210c070b 70
    0x3810350400d48100b04020142d2003b01c240c2e154914212400760b6500c4005107003d44540b0011080905d840744c1c00c421004000000306250740c2220281c075040200e950711207000c0700030b1400e000040e40042c4694184000540072400b10310100130141010196a5080024044540000d0b0444062015801d05020140030785080751081400210350a514007042c1c1d50200307403100c000305d424007c0d190542c001c50051007000200d103800362a119070300e1411440d0894806420408445520303000d9442d16118040401001c1c0889044c0c51061425081e00343c0b6060f420034540d80789c00405500e20303980708031402c102a11013400414190340f43c0c1c0c0e40000c2c0c3d0014105100085400301840d0444800c03a2010402c50b1900403030342c0d40c090400211242c95000c403580c0c2c5001081d4001d02a40311560001c200000c068200c20003e06240c0030ba0346e500c40700d0761020f8500742181c007403050244c141d034400304400140b0750991800e0300c0c280c2c01861015081c202c40d51000d601d0710b4103640101008441c0403600c482034415400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 322632014 1250 322630764 322630831
    0x90c0f06040803071127040209010603090f0809030a080a020a0213050106021005040533010b040308160f050106060c0501140c03190b0303180f01030c08060d0c0b03 72
    0x12242880c20b442c041c101680c034030510f030700180308000300090090203a0b1601e155200e2100b40c810182c0c00e105001c00110b1840c201204d080303208000c406e0011600c0351081c800c3c202d0141d8003100b484400c1ea0151580d04440c0c1101c4c000661511401c03031041e0019a0840150050300401c4c1c004100000c082d10400480340501c81c1000d03003044c034201c01000800d500003003d000440c860710000840303485c0c9080c40c60030198461400703181d9480c240327030903e00244101d070402c1c0070110248904040e6600c41010203031034401ea02c000380c0210000c0c0140c00c40065680300c02c9031000d220785108684401e5554030f007401c0d200a0740c01300001c901348210604c1441b00c280a0088590b2881c00300c40315031b14201d5030b02034841c08050903124450b1001506500303483c44a07070203080e054a00600726174a602c1d1403603850032540e041d540c02c02d0041d4549058000554000d016020514140ea01e400c81a40d9a08043c000f8822030b0500c29680002c16540c000b0b03240840200030340c02480c0c02e1a040e445080750045180b003440e00d42d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 322633264 1250 322632014 322632019
    0xf20010e04050c0a030c0908070e0106090603060f030818030a060606030c090807030311030f041e0e07081b040302060417160e010b0307171302040506010e220212090c0f 74
    0x58200500a540c580480f10100340505002840203031640c1b0441c1c005c481707604601024860030b1408200103812101150480314940c0e10000002c0d01c2c1c610440540315148201e0403100c0c01c50a0610000701e20702d0213020b485c000070380090a1540c1d4840003c3c9000035038002590000e40d0740e0010f00403540d00d405460720001260038146807903882c142082c0d41c0c4043d244800703010006025000d2071051402c0c01264181809810040c1d111602c400c20304200351002d00007070355808442c550006a00d0f0b491000c0a2080c582a2100041940e40b0504004015200d00140200040070000800160b441c1e80242c006420402c2c0700046d00058034001600d02200c2c601703801039058040c2c404102c0c03034440c2e4100d5415220f03082030150300c94840302000d40304035491001080514443e80700f04060142c030b05541c104214000c440901c0b80341c03299401036a5900c40554a50740044850390001070740090038082c80055401c04400515000076000f003900c1c22101a941c101d070540119842c03929a141410000001c14400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 322634514 1250 322633264 322633271
    0x40f050601020d090f0b1620030d0824010207091e0509070302090106030902030304170a03080106081306110904090b0f0a050c030708090a0503130602071a160f20010e04 74
    0xc1542005d1144c0c1c15108a4010720f00c000b41c202c1e400400600da800381d481e8000c50884016071000783c10421419042203881c081e2107800000078400303100d44401402003c1040f83c424010b00000c1561400d44600c010301415441b44442c00141580c49209440d082e0080607002d4407400380c00c030281015980060031342c005640c4030307070414000344e51200c480a04654460400155240a610219080d03001c0c075440f0134802401104400c0e1000c42c041100641140b00c4d035244a01c684e2580015281c4082c01c1c1c0d44181c191b11640c40742d50004034103500c0b4000b051807198030242000c40e0100090180c1d444042c00b10791000e0020180500b0007a4044a69084034a030a01408503243c50701c588051800001c0c100d4003006421408151780b06c0c02801031500d81c0e5004020340f6030b10203900f090441d43c21703078038402c200c01449403100000340090030008401c02070308030180003450090301c4e411031803d000440f40103540385080145000c00049003540c0c1002c3c01492184013003841180640058685000740e511103000310305 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 322635764 1250 322634514 322634519
    0x7080c041104030809190b16050f1b101103030c1b06060102060406110d05040506161103071211010e0c09010e0f0f100b180406060c17030a0b040f050601020d09 70
    0x10901030301c200c0d03c800d85e5890b0b0100703042d80092240f251958802403441c00001031445406141c040740e48105e50283c00ac0301c0c4030a04400e14141d581603603d40040d40000f88004e2800b0354034248910f400c2d011a9850485040d51294107140d066900a96140c14500740005040403407100d001c3c0e07a840362285c0c2c9809801c43c1d160140c0045e46484000b00300a015a5035405411000904a025940301c0503084804101d6031406140003035072030380c0c00d4070358129915075000c800b41da40d40300c1c840c90b4402000c034001441c200319065480300555800a0992014012440d40002c1010300910a00b00741a00e400010190100000140100c608040e04028151308a00e4100684078081d5189180c2002c0c0409000049541e148002c40350b00580344c002c05101c002c001408404004845843c000b5004225020001d5603541c504c00e44092440103001841400c240011807042548071025651180101c030011900a140b00300041c101e40c41840d080d0381340d640d65800d11040b5641005038110118403410056001c90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 322637014 1250 322635764 322635773
    0x180909070e07050d06030b07020c0f0d0f020904020d2004051014131b05030105040506010504081009050c100c0b060306072a140a062702120f07080c04110403 69
    0x1a8001c1c1500305125001440031640e04e010b51004008607004110541141040c140083d110a210a1100e2003035004070854000391030905e90300309009510014042d4180296030030300580300300040081e64401c180c1118100450351541c00d80014011384481000300f520500304200446401820202650246441c1400019031007511004100c030211000701c5000166022030000d4141400c407004900c80782d10003114541d405c10051816140304581c10b01884d80d500c4011207003400b1300d10030700300e20754004810050b5160583e1b00c80034005020b0803d84810041050200b00100c0100755100c1c00119142080000c0c80301c40c0f103c054000204031301811f024244810b0080c0841e1110706982401e0a064855803d050303000d605e105042540100414003400c0c282d00240e03107a404c11750054a480d810b023003141494118529100704003042c40c5000e80480f102c1d6070203101812282413076168851041503880c0e40c040104201540041c20b90070014004d0421100034030003642c02c4103242d0380c0031140600081c40040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 322638264 1250 322637014 322637039
    0x80709030b040f0c06020705040605040c05040b070c0e0106080708060d020609060a17010311090106080c041403150c0408160509070e0d12180b0306090109051b18090907 74
    0x4035000701c18040c103519030707082c514903c006000d8020400002c00c1e000080700c40c2c0100342c4501310f410895042016550340c80520081c0d429034028500003c00801091020710701200180802501034401000082c0e242c101075059a8000c1c1c00240100e4051810007400b582d00c40e4803560300c0041500c44455102d15030303012880034069404610f10455010840d844414820070140f540075001036a1034000d565a418240c00b048003482d00c050003040c8080003c541c0a014601d200c0c051454413005074541490900b071003070516095050b1581c180200c42d984090104100d1059005201103603030640d0b11450320504600d0300710503060280c034134403551000f0440ea5032007980c000c1d40198581051240d801004000a000c0f10203901c0040048d0030103c1141c0c41c8540c48034591a4514641081c8010203441c2c0142c0405400f0840e62240d00c00c01450042c48204010303007040383c0114065090380701c40405080310000a410612328415810700c40908920540303020030146400c0020000900003050400800d402d91 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 322639514 1250 322638264 322638269
    0x12060506040c0804060b030307020307170607050a05070f0f0b2e05360907320d021c0f0203060105010c0201020703060c02030405130b040f0c020c0d06110703120c080709 74
    0x105076448403109481c0d10123000303c414403a8020250740040303884035a00302c20700312001ca0000c9903209141c00641e4481c0280d04035604000291105414141d103566801040c0c0c8040c0c20032030f60021501004400221100c840d940508101038081040890b034001e00c0302d508100c0d841c2c0007079968905030b0400468407800750707585900f82d8400007038221480d4501e04ca4030b609204c8041c06201c441a5040010f85040030449106039199020346064803407420f0200076031030880d035180c2e04480448040c804680d151131300d44d42040a00c01b512001943c1c621030964001c10380c3e01d45040d05c1501000003000d0851078113100003405403a003403d00150514180d00003d5440709136000040c09139a44943c40043c0320700070019a07006010003006c81680300c95858100c030140c4034444846014500300341c1441c0070140c142c0104a0000340030742c02041051500e2007000007850075000145d500a0340d48010303c0d212402d1800602406000c0d03107481c00546800301c400411100111500d5040001c410f0a000710258001540c008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 322640764 1250 322639514 322639523
    0x2130515130207020a0303020a031e05030c0a18140a0801110f0c0a060213080105060f01120b1f170c040f030201110114040506010807090525020304080712060506040c0804 75
    0x411050400741d8000074850004042d40c40306015000004169000405622580c801e50702c02d1021240101c400c6440301c1c1c2c1406000c04610203100144101001c80058090000b4628045200040303070001c4041146075a04110b19030461f401c40b694503401c00c1a02270004000f41402040042203068070380070785008640c500d071401540000d503022103440803c0b4860850390040e20071941c1c1d46402c0154100010b4038804c044480d42400001480ca240219a820603050180c680102004a94078908002c059403040c403580a070101c400d101c4c0c070030702d40045200182e600e51105018560502c84240c4040001426a124030100704814440307030205552200c01c03680e083c01c2001074160f80540040c058205a19184400300c0c4070744c20041402400141d141c100d5426105036109075454024110503a13a0449502d206041c03581410b036002501d1103102070300e02c14288180c90415484088060820059030300c0b0180001c0b81020380c80c2800410300c10550464401c036401c1001c07403051007000c0d0100200410251 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 322642014 1250 322640764 322640779
    0xc03090f03120406030f05060607320a0b09070f0b092205090705090901020c061807031709090a18061e021315022d01060b1602130515 59
    0xc19480030030080c01c0104280c21240c3e140c0c0d4440e070008008280021000c5081420100826000c0c100f0798215800140c0150043c030b00d078107080d80a4561355100d1001c8440342c05188000c222598030500a45148603c10078213000a0f04112610a1401c00190081160b810140b0010440c18280f80c04071540010203442052a84100244890525201e100421111030030001002501c2c02d011682e4810350702c04440d81d100d5070722078a40480c201c1c000c910800c1d10035400310001c1400c0f5099050721028031207410003116001c0d6100d40d2014404100c030014410f5a200100701020b80f41350100280d9808003650b4001c11071014440307942664815042005000e00390345034015032904002500d40042c959461005550741d910b800444c482414045c413079102c1405898090035240e170710100d0305495004103140d000d4000044541c4150706250200c1004c07040e036584800024104964002030001d000a8011070107906000d40107000c040100414035541c0d251400c420010a0415204005014007040d607812 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 322643264 1250 322642014 322642039
    0x605090705040c0f120c1202130801090f1205120406053616030b060616060c090612051b0703020a0503031005130b0a120807060c051e0c0309 62
    0x403400c0203400e421003500141045111014030b6003142c49014601c07015501d100e0b0719501d01000c041211005520708002484e140501d10290b001a00509903444441e09504101603036104414211225803904482504051400c0414099a030410110300c69241c06c000d4903009503028580151040144001e104c15910008280d04169125810303140b4030208002c5541d005e0ba4510f24000d030003000000500d0b5210341130b02840e41101b407800d108200daa12814144490b2504d108014403a0048066594403043e40c04406007c5a92802940303601c16031900d0b440b174811b0500c40d00404450801c50308806d031609260078002c1c122810a5070003090701d24028203584a10091078100d0610070090405072980c4008800d0111040f0710746a240202c030022030f01c003a0301c417507440c920300f0949030484c040e543d111102940422680400c149207549844c0301e240440c3c0717001c1a594401003121142d00d42000051004543d03c00d15011400c01c031211031000300501c50400003800d461942e07070701c6988001d0f03015000c4a50403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 322644514 1250 322643264 322643281
    0xa120e0d030306140f0d12140310090e0f100e07050a150f1b0803060409050613050d020f120d020408060a05060f0d050606040b0f10030510051c0605 65
    0x405600040061110440345890704008000d41014095007029034640006240b8911304080c142c45000d20243c101e0780000070584420101d003040201920038020b18400501c12080504001c520403190495144202410704c074010044420005120005500c00f5a0045108000141d00340c04819201800310f0501c40e07406180b801c0030303815803019802c4034801e40701240c600e804030b40c240403d600c2c0d5510f101c800610048120380b542c1e030041a40c4c54040301005001c002c20141801160b1201003d0004500403d95a5405103410012941060340b03241d588000310400109020301501d0240d103100420100c01c0130000d19440b0740748080b171240f140400181d030060040107a01a10000c0a0840c1074819910b07004034800c001e031004072105846000800003610b11880c0031180c100300550000700401899517141d00b0300c4024108210180e900c505400e0300e01d8040d80e0b420307280c0a24000b5555000c02c45050440c0c00768000304103038105500c00d00d18084c1c0c1c0041200211424020a81c100c90080b8060321880e58 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 322645764 1250 322644514 322644527
    0x5070b0f0601030f02070c05090702150705030601021204150818100b18180706050304211206080a0308010e0103030c0213020405030601030809010810060f0f0e04060914010b0405030a12 81
    0x1104c4103074a00120381e01e003d214008082a08594003035032808013070313580d40341c04a8446842c01ca2040c440400c9402045081e0703c124060b60b40000d041c01100ca003014880c2482d07810350010b9110b156003040a45800d050039030b01c0815580c11480d40c14070065210b40140d2866110381004510510b40e40c0d41c1c41d0741900301c0c0c0da80b1000c00d04440003402c880e040c1c0d041203204035840d1000c00c8003030a940d115401d0002134492141c0b085074400ca4100319510002000c03d000301590182c1e0740d401c5002c025884140c415010003a20031040102550001804005540d01d00a0b02c1014168403140d60512030900400100384c0220b460716403203604407960744d005400071440c0da000f8044d41e04a1501071240ca40080201305010004128001c02601c442503256680000a4000e41181c041c1d800000c030b904441982d83c2e0f008800f0740d018280c0c542071008500c0d03c4440414101c07100381d80100a0f039516410400701010503201c840d400341030031810041c039060a250102c0d945a80c003000041a1034004954242c01a10548 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 322647014 1250 322645764 322645781
    0x9020102010b18071707091a0c0708030a020c0105072a080106090506040b030604260f1c0c02030712050f1b060f060f090105040c091e080c0105070b0f060103 69
    0x818924110038814000b401d81d03c0c0407103095010420300c8965261026144c001281300d0045a40e0303110308182051304c00c1071007041850f210402c800c030a208400c10083c040c0f00c0140601068002940c0310b440440f402440e00c02e1041181e0306005007044004046905004100c6090880600c003800d103c82d8101c00301581815940300d40c07500e5280020109440d3b0b03050300094011074045505100c100071030710406407240d038140c800410b054075050288000504c0f42da00c0d4960701403180840f90414a00e2010048130b540456111124246546c0410010f405103129071a107240783d910082d8107221650380c80e40103654000725580140400882e07041c015101c64021601c0ca000b030400100150308900940a030744403401d4a0180110124400042460425120561105000401c0b00d81c0c581d28000900c0020400301040f603007000450396020442d100e0594542c0b0720800202c0702455154541b11440d03003440f0a00100c64100001009000040b0b41c015030003a40048941000940544074100160300904079036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 322648264 1250 322647014 322647019
    0x904060b0607140a2d03210e06040512310302040204060c0b010503031606020d09120c030206090c0a0302010516020a09091a0606070b15090132100309020102010b 71
    0xf40307004407420790049440e4448a20910400e4900c204194000c688007203240302c0356054442c0c0206000210348685015a03503000d4200300f001caa916001402e03000c1d80d083c922540e00e01d0b0700540c00d110400c4410400061421303030312200350303080c4031030b003090b040c00c0c4c603404401c540004520050340c045200d10000704000955009104565442c0d82d0381d00a0058003c800c13040e54487d00c040c0000800d81004400c0b81d02c500403800c0c2e0a070000c480d0b0342d2540c3c0250052004244074503500c544190002d10070148140400066440f1264940c005d464028602180140441000d4015011181654807020700082c01d5a0f82420200c0e200e0301020103120740542c1400e000b81d4031035102c00001444803000d502c0703400d0460290000061101051804200398102982c0c0c280e0030003030070001c42000c900c502c0300890b045020f101140200b4405180080d0300200283c114a010b155052a84504d110340c8004c04400d50381c0d101d1700c0380e40e0004040c0004040940e108104001d01d5200c1c014a01160703c01c0d8416203004400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 322649514 1250 322648264 322648283
    0x40308010302210a140615100c2405090d1b151b080603100204050f06070c0801020c011a010215060909030906040b130b0f1e0405061204020405010609050904060b0607 73
    0xc0d07080030015080132030f45c10700050240310302003184c0e44030b110466241e51340c01801100600601c4c410480d01841107640543e003914508440e850b01c4104c0a14070843c14004031804980750804401c00760400380744912107024013416070516401440781200000d40e00343c12480c4080444001c541d2a400b901c0280741804803143e00d03001a1018540000301140140c2058080350290400450351034102d2041d0300030300b54055181c00c550206131800030000c011107071003400c0b44140541d640a8803400c1e41c2001c0f2858030107035152a02c0503803203000c40040011211092000b8070800241140150950a02402981c05052000d0019003d6002001119241342014142642e00c6545038010705054014100310740c0e0800714640001292807500701980d1601140710b1103d4074180d0001f2888058480269030320b1404035090000044e983c1e00c03030018100c01c428007000030304503142500c100021240140c104000f803194079a0280050388980118550140d402400020388030019000204d07036000b9480010903072200c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 322650764 1250 322649514 322649533
    0x9090215130f2709031404060302090f0d02011b050106080a0b09010e07180222090203060f030316020402072a0305060705071208070309140706090e04030801030221 72
    0x501c040e420440b201c0030003004005071601c4041c5003205150350020780550702c00e46855240503c50f402181140d109051a860a42c240c5104200716003043d408103020a60103c3c0c1138455041004107500d07098012501c00c00c410026900107005640800c2c10300846240340c003612400c220095000340301a005180446440c003115181180702124101d890301059400c040190480ca84002840016a1140c3d0950544d4130b140d0a0700d0300c001d4001e00d00070781c0354840035103001e261884130300f1900d805089200c0002d03969150070380902a010049441c0a40a54010018401906c08200f000340016504a038050795032403181c100301c0c007410b002c80c2c80720962400281500c0c4006108130f4031501200c1c0310300151421035403240011b403079500a40002600e0010801030000a00b442410440d91000c2103040c0021382400c1c985400340d242201240c4030000368041c3d8030034410541c0268540d4014128500152414546030760010078904041c40000d004000e81140c01d100d100302030240002d03141001040b500d00c80d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 322652014 1250 322650764 322650787
    0x6030901020714010e0c22050a02031e160e0a05030d030b09180d03090602190216050f0a090510030b09070603060e07020717101103010807060c0c09090215 68
    0x500041044070403d44540040f60750a4060040606040d450400b0740140d10820007401900e1400003600e00b1509940f4031401c3c0d400c2158030500d8004c0394074050050312031424242041301d039840101e00c0607000100d9401c1080c0e0341030241e0030500c104d0140c601048043c84100100702107100540001d0741c1070142484420400c0d506038800d441c4840e00301c0c3c0e1419142c590742481d541a440c1011204032903004000307440034060090b00a2004c0c180b0400d00180340040c000b034039103500030340a01c282c0016040f01194020241c1c018044401401046840c44840b00c0a907001070901710080c0f1651101c02d03226000107107210704210b5100c0085400060500d03040c80c20580d499140c1e03040e4000d62b1b005c64038042000c5064440c4071049071050b106500100189403c000b8444013011089005080078071842c1c0d2942c0c11070580340244015101c00070003030790f22941041030007800c0c40302d2900401c0030880c044c0c240001003004400c0c070070210f4040b00c00005491000d800403074880f82039107480d075000395400501c100808 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 322653264 1250 322652014 322652017
    0x60d060f09020304021f090504050c3703060503031e040810060f093b0312040b01050609010210150308070f02030c030102090a0e090709050127060302010f030b0d020603090102 77
    0xc034402c40d06c41c5000c032018903c900c0070040382c10342c0c003001650907142400305050543c8840c0d048600c3c07009250811903400341c4009070b10540e41d03020a4003d06c0d520320381446000301481d049403500600341408030b18104400b0035580e004180d02c0c00081145e45841e17009501d4500c04940280480005945e80300c0c026841402c05001c4602c1103c12a00000c200054424500d129105c1d0600c502e00210784242146841e140110f1101910151015062242e03071280f010304000030216a040c4085140b40c5280c0b40c02c103651051016441103004100812000c0702507a8041140d00e00e5422610000a80162044030240b0b651019080103008808c006400c1082c004d8400038481003901c220103c1301c0c03584462041c503090380a114504c0ba00080301003014024007111a0a055101c8410401c03262200d80c2c0b6048002515400e0b0b210340502d08140610619124001a000b40640d10742d0347c040c031003070b40366030f000809500c00300404100301640c3e0407076005030f9591106203003043c0381c0082002d92a42410142d40303000307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 322654514 1250 322653264 322653271
    0x80111031501050a0c2a091d07030c0303110c0301050a06080610060509041d030f120f040f06050c1902010209041d060103030c080d020409060510020f0c060d060f090203 74
    0x455030380950005107601c614211082e00103140e8845c40d488105d690303070b44006660b010525140c084440860710600b002004004002c001462011600200e2560340c101183c18070360b5460709940148406102142804580c24126903052400400344c0054040301e80c2003060762030401c2d900d9400c20007841040d100a8004205941c100000d03200c0c507803141245142009680e100c2d10020403c140304150507031400b58013440c01002800c40092603690301025060840d0701c400300081c04030402150f55904c000c3c3c07001a00754000100b524131511400e05441e035540315103400c1c000400b0940c0714070024882e503d81d0b0303003500c0d40a5941c554142c24030100d4035020380070b03400000146014601d8015808103032165503841c400601c0310325010700080c2c0d00b1a1011501e1241e10007050351050820456005000420b10040c001003001000000302141050200304a5030300f414949000c560100e0029440c840300404e40055440045614543c1c41c03200c04030040240c0115405850511042e050000d80c0c0e903040e0300117510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 322655764 1250 322654514 322654531
    0xa20060a050703200f0706091a160816140a020d030c14090d03020109020909030c0c061c09110402070606090606030e03071502070803090a1106090d08070c08011103 72
    0x9140d0b1000400c90460704500c03c0105240c001d0481095810846002002070200f0001164070f130051585039442a154501401c0382c0011030080d075607400020341b0880d6504074500340982c400765950740500a0a6040181080c04284000c20700110320500036807060704086100f01d0b046480d1503030580043d449038990090350000c2420880000a06840b036203501c40c8040310480160304041420050180700c04030b41d070702202959079134401c010160341c0e5841c450b445074504000650b9210311080c03299080c000c040105a000316020300942c041c000e072591558140c0c0500850000700301c00075061004040510f00c8859420a10000f2081d042c0186500704e0b80590b0081e4009102c0b944d51100c0c1241161400041c0e036000d40c0060140c400010122500e12459094a201c003500341610b0307440ea842264025a0000d100e603004e29400400c1141c042d4151000d100101c5196007030030411300128511303c4003a20b006100110000c0c0c00820444a03d64003001340104000800c52454101c40700c0b0400c3d401601e201c507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 322657014 1250 322655764 322655771
    0x4020f040b01020a060e010e070b0a0f021504150b0909010f061a031b040f06032310050d02010c1203091a0103080f0a03020d0507200a0b010b0a20060a 66
    0x50503080c0303802078090004060340140844d103801d0b1a01c5004000c6050f21448030b54a6540702022144108209406030101201203961540d120001805e040025060803095410031400707440340e040b00b00681503000380c001030039207034103003805400f10004d10b03804481d10351000005040c40a80801503012010036461600201b0905843d6a2a541340342c192a10a2102c42d00c2000003c151105407045100b544045015060402d0f445107101c00c44045250450320029a4030030b8101c060351080c100c002e2407452400c4800060b42460902200054001e0044d1401080203091610071641710340409401c0c150041c60b0009950754081000f005000d20b0700b02612944280e03080700d0079240b209108503049030740c010402031406a10150410150b080f5420320020b1550a0084a00d484810f0007100e210b902ca40c0d8414801b00f0300c81152120303603010410703170b41c1056000c0c015000010300810051819251081311503900da0f8041c20703044501c074034043c2c201190b0440c2c0743d40022004070002131759401800202e9061 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 322658264 1250 322657014 322657039
    0x3020a1e081b0f1b16031214180411040902040b0a020c0907020607080403050708030a0f050a02041d0a0b031603020102240601111e101a0105030f09030904140402 71
    0xc00e40f40524148680120f1082250015243c469030410008800410540702490002a60b60302c0d0f4076080d50040d1111403002440c1003080b648120300810000408888905008008580d6810060201100c601a40e522231400d12829182c1c0c0946004040c4108255a03071030b2501c08151158102e081c0c401c4c00b511404035003401e94903280d0010307880340030958014440c50741d458400305c490141c013030020350a02504200c00341c00304800c9002507100c0e90051a011130a40480740355602224802803103940020310500c41800400c1001507400150380c0240e031886070548990483c01c00400410840c250305218044841c0c5010001565540c200c84c000d80a031030161079225041e200c075030207506514214070100300010b492076004103c0d100c6485408411100d501d0707402c42c480c5155142d603041c7c1c02c8181d0b11000b540f2103894028014002d507a030032030342c103500700001190020b03110340009040c40001c80d0442c40000d100c0e0341c00300300795015000c00a0061102c8114081815130404007170300d00307034015144103088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 322659514 1250 322658264 322658311
    0x71b08030d110d060303020f0d26130f050a2010030f06080304081b04050f01050418050f21120105010c05031e04060e120c0409050307051c08090705030a0303020a1e08 73
    0x10b4080401c201042c4200407065815284440018065400b0550000712f00d404070340d0704e4030214106440b40c001000104002c0c2402140b000405050100d56004040c5481c85501c3d503014001c40300146007000710f0360340342d4000701e04007510315a08489410700c404940000c2801c00054015140600c20a2406d00b0707403c540280000d464084802c150610700d401c00420050504c1d90100104d80c0034a61170100081580d690716050000406070308400358880c3c120041e03050080b0904d01e04e659a1054080e260600d1412070500808051040c44c2c1030220341e448030130500606200b1520409030340c0081c0125501541c81d5621030303821034068900001e00641d0a003000342840240070300035030200c400502c04101d0400411001d810500012a4140400c3c13203403000140040010741c036010140c80d402050750b40038510082210f10010710b10045035104050402c000c1d1400710b600282c098152401684c0e5000301c00f000c0e542c03410015000705a00c0c001c440b05040e02640004503034010602103074031500001c2d5041c103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 322660764 1250 322659514 322659527
    0x31b0f02120312130c0e22050d0e0102010902100807020a05060c1b010b1e060c010e0309041b0806091b03151311030606070f0c0b071b08030d110d060303020f0d 70
    0x14100c2d50020020b10180400050b000da1181104049410104605641c0307405110201400c0f00d4036401132004278030305504200c0c0800b082e03a0a00c002c11030040c013500001c540c481680499001d00c0b40e14004291901c0c400e00c10710581c1d5402c04100e5404e030400000d42031007540b02c1010680d409024805201c102041801001c143c0d01c001061900c0c41015890342c00d0388941c00e100c001c0c2d0700540822240d51511803e02a410003801c44202a6031121001d609200c103451507041040d00b401c1c11554071400c642d400ca01d42ea40c101e18140c2d21aa465a038040c0c142e100000107500c5d80315543c0b4007101b0094500b03207945401c211800295178116800f50040b180c081980d00004920303c03000d80502c00101700c0d0811001501c0715a00404d4a1110300c1c4161b164440818103907042010380020004041041c8603c1440a00b111041e000303403540f9a07842c11b20f103580c4a018140d1400201da03100c003450304002510109662022054544c2002080da50340b802130754694000700015120b01402c450300004500451 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 322661870 1106 322660764 322660801
    0x2010e1f0e030705100305090601060809070e0718090c020f030c100b04060e010b03070e0307030c1205010f1802040e03120105190b0412110d031b0f02120312 69
    0x50000c9c1c00e080050700060140503460060000d054400158001207400544c0b15182c203446542044482c8007290301e90001e40c054030f4401194241003903000110105c07540d02140d40080681200c66202c0c0070301d58114905801485541c26071100e5034205414021006000191060311084001d200d0b02d02a001001d440c00c0220030400c9039074000201c10b5400c0d0088009240140ca16503a0f444010a21b0041441649440c05504104102508090a600c0f06904148070000f100079010046c2c0d1841041030780f04500302100103803481c80100445020b084400000306c0e05a080900340050303d00d25000b0b440d80304408520020b1001500c801420180c1007507020400541428280764003c02035010003030b41f244c2911b400d02000a5041070200b10703034164100d0f90007400713804e6062007129106102406504007400c6040c0780c40b07e0402000400790f20442a0403000b8903103c4a684403d180e1703803034 = true := by decide +kernel

theorem cover : BRFrame.Cov 322482014 322661870 := by
  have h0 := BRFrame.cov_init 322482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 322482014 ≤ n) (h2 : n < 322661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
