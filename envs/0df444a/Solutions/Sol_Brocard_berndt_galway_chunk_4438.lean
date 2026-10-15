-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4438
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:52.168541+00:00
-- url     : https://prove2.me/submissions/f38ae8e0-6ab5-405f-b073-df9f02fd94e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 798021582 ≤ n < 798201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 798022832 1250 798021582 798021589
    0x11040e060c070f020409050a1b1511012406080108010c05030c070f05010c030621080909041a040b180708070b090d15020901080c1c0e0c0d060606020714 67
    0x200e82007031507009655a01c0b001410105104158030400075485428092070f0010b12600194960300180906040d840415181c00303a00c1d8600c1c01441050708003400c040200300d00314029103102100c8810780700080740c2c804d338558112007032892f1250042c6800313500070b030144040e582c0150124003401484008020344400c03114058520b000042c10000000c80c0000c0103010040c0b0b521210001d50b91000c0288040030a01d14060003409460045149001c800b00700741442c141c15120502c1201e030001c1845160030058010700403a00c500030300981d525418100680d1901c0b4028510701d206600669000746141080f4210410f0680c003417070007046030f0340441014018404007080c0c81d1700310b40f65816000d44c3c07901d4840104040c1c140911014204802840903c000440719070006c040300042683c4014403952008441200c500030a00d017910002405007141c40a0b4030380d60b003d403801c1c50612089600d1554100005a20b5002d0303010211407841e2520010405c9607010000f4801601020303203001080700d16040031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 798024082 1250 798022832 798022843
    0x60901140f061906090839030a050303040b1608070807081008011a04111201030b0705220620030304200d080c07051206061e0a0303080411040e 63
    0x40554244500d011500a0703443c04140c0032000b84684103050610b5440c440544541034921807400c542c0607940c046408001c140d80852000c40c3d114841030781141200d07410000c60b10004200341d800d40300fa4030501000c51420005144914480c0308064800c0c07030903403004004080580d07040c4051080e5207042c040d1682d0404445a8402d10130b117800784080d40c6401c40d03202002415802110070b940307401a800700020704000c000744029010b49040c81041044103450031280f0a800c41141c40e20010401400018480c4c0e0b1000e4000f00d841c84d2441c00d2904a0101e12a001c20500780c00c1195250b5000800030290007404503031100316040a602c0c400507031140d01a0300c0c1d20000b00010651000d40b694141c0001c1904406140004083d0a035044003e2914011446601000d81c0540e43c0c41307100b40c00160f92a181c41118240d0b41752901902050302c1d1502800908103130300d40848070340b640680088a0756240d40544000560180d07039100d01c1818942040504000c81c00782c60342c0100c0c2040341940281800003407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 798025332 1250 798024082 798024091
    0x9011202040518150d0302061e06060a03020f1e0702040b06090f0f19060203041d0103120c0201021f0c2a1b08011409010e01090c090b0a0e0a05040506090114 69
    0x1505510381d5841522450382100d090b030744c41d4002140c08011080c981d00150140c450481c410b40003c45c1c0c58484c030502c58968044443c1640101708114008003035100703801414040001d8401c0f01c0c100004108000003212400581740c090000109000056103010b008a4441117001e5501e139180205520110306040340d458100742c000c02c9140800b44103a110703006c0115a10028040c000384194a40800a450360300c24814440c480d00ca4000c04c030402072250300c41301d040b240d004540e0810000844410b4480c0104048180e0560103200d842c1032103c01c0512400303200030051000001d0000369004042e02c4034001c200f081322100c01d17400604014000101e0180c41e0745410284115086506290b8510b11680580215a140d4240342408001045176454103028003048002440805054a042400c9442c183c4010b08000c2904ca002c010f42009036000300500c460180c056070b0002d40303400c8141d074030102c20365522503415070710010041400800c0c03010541210140d4001d01503d95281c9035a1000b030b90252 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 798026582 1250 798025332 798025369
    0xb0d0312020f0c01020403050f240a09110a03080406180e04021c080c07030201030e03070308070f02070512061b0315130914070503070f0807120501020f0708090112020405 75
    0x14803501114003030010740f6181d901920080d5680c640303902d002e43e21082c1c0316914090b07510030080d44401c894000103204010a4050090314055540c0c284000050308100c1001d64206143c5012000d5540358554100c0c0590b019600c090390b00e038074003c002000c00790300d580a8440c424425078203029a2a4100c5d4550300250102c1e10580d2424103124003040c07085c14094001c02516001542441d0325502140b64000c5a0007602c0800441b2401c02480b41ca034819600020001b4100f80f0004803803d009444200300d0b11460720403181602d85071800f04040341e031106003841e596800402002446c0303030a6200065544580c414050541c10846480001c0702181000c80380b18511800c21460f030019144c0c00700125603007080030a91004440389107070382c82d8503080c001d1601900031480c01140300070000325100300721000301008011251074a0300b1001c0e150580350040f1100e540811088003c41451405000f8190048440994a000e050005410400038501071190b0500501041059544190301c410b20f07480102c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 798027832 1250 798026582 798026587
    0x10f170604061d0601141504051008090c1003020310050a05010207140114210a1a0415050d1a010f140405070909020a2006010509010b0c101e0b0d031202 67
    0x561040a52160f1601003c054851880002105d0070310201013540040c0035518013171b118040342070070007551046000d0150090b50300101c54000703521078550907038403881f84070980310205e15035000201c0845101c410f02c4006a0044280400016405190f00060600b00c5603014600d14100010b13483d100584070780031104010001041040c2d00501210228100c54851f881d604c0341006021103484950b5800701c0a4001e03c800007424407140c1d8030a0545010f03506042d1410502c0003800c120240032900d03030411208452103000146925003611803045580301d88202c072100000325441a542141c164400c880c14040d445080007103c100035007400d4000720642e00030466a54416050346d450f18607900c14003680740b00081d80311070540e01201c1008c40b409480b0940707651982d4128000d50350b8034207000c1d6513400740c03d580040100c500405c00500b034400c0e42105840c03513000100c0c0460700301e40c7e04101d015008451130a00e410a4001c5220301001c12038100c403600903458494400500c2501848816118603500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 798029082 1250 798027832 798027851
    0x302010605130204060e0328210c020315040206070b0901150b18010302030411061b0604200102030a1418060403050d0e0607030c111c0b010f17060406 66
    0xe41000014207009011a5960201041001e009600c10300c509400140b1039541c85280d4039012a012071070303882c0080002d1400807000c2080b90040240351301202d14200d9484404040080707040316581c103400e181c440c9000e2100743e006050a0260215405208101741d108010050f138031a000d0b86c4da91074004800c1c0540fa590b411050340100200300201015540000300024441d011070000d0446a40008941c01602403e41c01501a80400c0d50b0081542400c81c0c0448124280714010b05440240c0d200702d9a40010044011070070700c2c00944054030440110f001d001c50b1222007450492004400388011407401000c100c0c02040041f04c0e6020500d01d600c0014403002c800400f01c0315081200d4001d01c0e00713a850b503903490015600d0140381d80700c0e008a21010780c01149460204d060b500c0040e0161200606524143e94200040c0c502d0f44aa070b90040380300340100e007454002c0c0c031722401261052912951a5040581003d60902ca5a102d1071169085030041171b070740000410002d404c96888500403800720314 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 798030332 1250 798029082 798029087
    0xa0b04031b15060b0702030307110604120503040f05060c0606041e060617060d0b0703091b031a090d090501050d0e0111070606060203090f0111010f020a020312010801060f0e0403 78
    0x1616000c1c0707811019a8014405100a00003210604928420100711080d507400c00640e42d4000c0a4003e50b15400c02c1c0b20420100c5c2604000242800c0002c0402d8a000e40b2203034440d040d6241030800340c400f0303403010500b030206001031517071040909000c031101800d102c0a85400ca660300b0b401084c0a02441e281d0640026442c02d17084102c0301001001001d1180b1600d9903001440c2554a588841e10580c8203404526107080440e08082c0294000041490a98882c1003d40150803196400c84200c2544016207803040c0c3c00c400500065803148504814600350b03005007001d01880030b044100c4a0b0041e1100302510b640101c1c8000c11070740e00307081158070760328400003050003041c40c88076444055003002500680100b4078401450000c1c400d01d01001040d8480d20200d0f640d02600d004030f43c106419016000301d41d07006010260009072a00e0020a40c0d412030880d0a01b81d0b004402d502c0c01607400811850041c03102c04407461b02411541008221051030103020005c0c5601500c90b00230401d40b400045014180b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 798031582 1250 798030332 798030347
    0x41809020411180a0b0f310b0a030b0a08030324100e0a06050c0c010e040905010c35040308071e05270f0613080610050319050a0b0403 59
    0x2010303008102c1c3c540c0c80302c428225000300c07828101c2c0c2c4038109070341c1c02061103009802501c651040b0200e20f02e0074204402040304810001081ca0070101c189080100000704d40314602401408100f03100980710404090041c0558080b289114840d00c910b41e005d016017000001a26070144000c8a2072000d80208905000d52003518030750950041c11a0101202658000400b103400603000d90301c140d08a65290f500301c1e06402111101c0d81150070604000c40030b5032041c01c0111803990700a0000901880c103944450854000c210f1039002300d100318010312419003c030542c141e80c0c90a80040304009610b60780400e0014480208014107104030600405c2400d0312505030000003407086400d03110907030a040b06c05411600024031107a140300329074004044002019a1920f02840047c0141242c0c3e4441c1040101e2604541d0384242d0f80c2c442130900040c009402c11100340682d241102e10300c8980e00f080181428002407540e40600d0200300e0000701d00003440050314601030b9401c02016147c030744413850102e4040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 798032832 1250 798031582 798031601
    0x1e040b0d0212030414011422050402070c08061006090e0403052502040c030e0d0e150a230c07090203190603060e0d0206060f12010b0603010324020418090204 69
    0x24545422500c03982c500100410955104034030711818198080011292a45140b1011290350310a01c90104412184089013050101441a2036101c0f500c2d040850200d8002e050240c46900071810200b007201c03014400d00c1c0e0484202048100c5c0f09080441c054a4059207102d0901c0f071010030740003d4203140c462410384001d17a9000c400c1803131a40401140c10b0448800324400d0348564502082c0004841c0a032180b90f040740036600251006088500d400d0303a00c200440022504040c00103030010030420740b00020301c5101c8854840a8a820641c140e03045481c1450b524502e441a04000700c8402d4140002c1344d10032120424000750340c0303542d1340d009080d48000c0481c000103401d09000000c0f00b080340d19084004034619500440d4160028800c00705d03038510040d10880d0b002912840f080d441c600f00618212036104080001050514400005c0b40c0c1650090b4070a03690000040000c08c982940c12561080c02042c2c24425030801c1d040601d0040000a580b02d000101a0303941d054004646a075000302504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 798034082 1250 798032832 798032839
    0x1020d1812150507232a0a0c0f0b1c09051222030201051e04030b101d0106020606011b0b012705311509060b1e040b0d02 53
    0x401541e14280c0081c0d069550695045803c110000d021380d441298440e00035648242c01c14142522400b1500381584540020604504071b040611401000e61442003049030164005143d600540d0410450440c0c00350032860251044060401640d1007070410345810302c122040d0300c00804107241800c001082200ca00602c02d000d148510411002c440c4054031700d00c0f60b0205503c03e0600d060060010036403144c040280417600611440c24400690945003013420301c2c0016407481d044d125111130b200d1723203c2100c03031424600c003400052005060204c110b0703a80c2e118403542c510340d5504110000c1c0d19002d00501b40c42c100490f40c900c004010005e5140d1070007094108c45a01d40b44d584800f40403240303880400c0f010403410303a10720640c400c6402922800380301e1416041c009000212040031842041d4201e000b0301440101c40f843d010104603000c000d402c40d110b101800040742d0900b40b902c0010b64249030101449440034000680340c100000b0500c6035500710480d00000e1012444001880240b40264040e42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 798035332 1250 798034082 798034109
    0x1806010b09012615010324091b021b012a031103070f0803041b090203060f100c06151703130509061c02010306090c02060f0c0901020d18 60
    0x14180c403000d0091010003401e0341e410112a03642500c0e20b021454608802032003240746000104086549204c451440c001490007240d81c1c2e940c5040e08132084519030b06150f04c401a98001c2020810900ca04900340841c01010309046501303503006074450f03002502c0ca608001c0c03d4070500c65140c0c030480c40d2000c002144401001c3c56140610040ea00091601c421004240804540251f51900105440800d6442400c48000880540d100001900068011074001c110343c212080380c00c40d40389100000d030242580050303e910304403041051048001600500400074604c54a6500d03601120907058907800a2001c1042c101503003001c546103405034014040c00441c880f0088020300007200501684000b10344d4424510f44600400504020035680f6550100c035851043c455080315403072903c51240141800100140e40b4084101501d000c1480d460042c4c21250800c807003c803080f0f21403608086110801070a02c103403040040d61300c050b000000703001d1000c03415980c110b07101d081103045c01514000c0071504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 798036582 1250 798035332 798035339
    0x1103090402030109090506100b09130e15040c1202060a03020a1806020c011d2b020d0c03050123130c03120503040515090a081804051008010b06120a05180601 69
    0x600d0361885c02c41d4540608404210313450f0a102c581d0b01907500e94440503141c4000781c400c002183c40c084c0f0b940940e4580765010030f21020381c10300000c05989071705101c00c903151400d49455503d08440380c01425034410310402d4203001d03841c0d480c182d40c110320f901c0c10010380d19809507409403176060403040280060a5590004280164042041ca007040f50a0304c40b10480640f0328030255082141031000b03500203000411120803185110301c4000004c0403400d034003407180d01903000310300341c04001c440a4a80d88006402002000030900c03a079400340040021780b000c0300c604603c4540707024101601030030414000d00d500c2001d0001e2900050029135100c1041d01d000c10b006000942540c00c1100d056540740a6500804000e40003880c1c07061080182c4005482141255611191139402600701195209503540d10107d6907200d6104944c000e149000000c5505850445000c1c00e6403604285980038000510213441076514080c040c0c0d40004480e18086440c1e541d107039201110980c0c0502c1106544501c40000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 798037832 1250 798036582 798036599
    0x809030604052404020f0f180c091c0b010e181903030605011b3003060f0501051c02071403030f070206010e09061503070b0c01020301050f04061511030904020301 71
    0x34080941e001000780f03040c010701c0380d00058820495010303411040741100103c0500d400250012245001040440100990a0041045641180c62500c042000118008503160013020007810030504e60f071410103c526651411a03000061282d015000810004110001c83c1e614950409001c00400c0754009241d401c0d0844020f095000d0a902117403900b64041070030351140c085408580d80448401500d820f01d80e568a0400744c2c0c4525241000409401c45c0103083e1000c00000c07007061507a903011401320b0400c56295155402d0390301c400d040c001b080140c4040344110711041c00c0e0480c0d10610040e10b500c1c0714200501124040540350f1612b001c000104040f40392494051070184000e50300310703401030307172034011484200c00d050728900c580d50b00c0a40041c2c030914048040b24080400a01034651079591812022615007141c0f00380c1d0b0840c1d40200052180c1e0800d100e003250080343c01c44047c0700c040d1501c180341510030848200700c0100f080d8100a804011020021102404e90150046640b907a582152 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 798039082 1250 798037832 798037843
    0x50312060609010f0c020105070215090909060106091a07081201080601150509040c090f06120e010b0a18150b030906090111090111070b0f030105090115080a09080903060405 76
    0x114490a160008114981400001d98221850685a032100501d500030203a5501c010250128100803040150400680360000400100b21503208205c2e1110203900c01c200499000514034045644400010000e00d80e01549132400c48016008030700c1c94a460a003949464407030a030010341900d2000a0382c1d513204000580300d5049660343c0007a80e0144e40c945801d0240c00c0b00000003840082c82c2130104200c54a01070f405003510203042c2c204164115a0f0304012198004160702c000d010a240c6071300c024000440d80a51079644050000070849060b00c040000d00d0003501d40920052076031866070200105943e54080701c2c0c154250103400064559911040f641a4012501c0141c02e00500c1c0102d41429014000d0052100030465528100760b502c000450341c400d154582c2900920030441d0006140900d0001400001c10040c80300d0307507c0d810001808100d51040e441911040600080c0814140e03201c40220341040500e10007040b0307184d081c01c00c0840c5008075000c07079034140108002d1104115000a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 798040332 1250 798039082 798039097
    0xc110f190e010314030f090609130c08090d0206041a190e0109030905010c020d0605070207170109060608030a0906050a0e030313050f1203040b0a0c0b010f1406042601180503 76
    0x720480d61602c01e86130360f031a8002c4c00e440000c003890600401d1810f2410b030000c1c21031060060101d0ad00412480700c920180c5070829010b001244046040c086041402e201c4e19143c04020b000070b240c50305081c5d1b05d0344c1140615580703034a8071a0900b00461040d04030740500c0c21092010312002d101d03003c0248005802004840402c030f0102d0359a1300c0026045d40600f0044071030a07001002c0d41460525900ca40015110041c0124110301a044c1c0c0440c3c40021200c1c8841171011550000a0300210307854071400315039641e0000c944680c0140aa00d07501e03a0b100e0009420340d196490011380702c03901d01000b034074019101d41c9856031501000c42c0740e82c0d410021840391000c03070304101c44c10304039203907030005100603006c1e80b45041500d90003c01090000c0c1002200510180205280c02001b05945458605c41d1000a070410103884440c0082000b007000d49980c03000c081c040413554189400c1c900f40c0307288004006001240f0010945403882c01c2c401070203511107000300c95025000400100c40c3c1c80c020b41c481e4440c51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 798041582 1250 798040332 798040343
    0x90503070f0b031302040f020d090b06060c061303021f0c08010902030105030a0227010b0c060a0b0616020a080601180f06030b0f0c040b07080a020d0c110f190e0103 72
    0x1810000c41d9010344116285449690300d103840c0c0c440f00c0001c2407008a41030b0b821584070580310206170340c0752000380a502c0b80d644002480c81032502d4103048150300504028865503090004822020003c18a20740045445103841c04603103092030700340d00b03082d848284442c40ba40035034881e0300c02401d0743c0c03c9000360a01c1540e030480359a8a5001110032400280580c9030960f000c0c28150006042c102011284003880c0030707000c0039080381003007141c00742e070000d030031040f80c0344000304030441040801c0090300d07000391400005108a81280c404503005014446e0290042c20003d203a020654032003c40502c00b41464200b50390003903840e403401610262281003e2009107240202000106a05215850030303603030f0241c1c1c825150b80311503008429528003d0b25241c80d402c0100000a5280383d04c200401c205403041c00015110f84031224086d040a09440301c0c8024001c00b03c0107070700003c0c102941310724109002c07154202c1c20440b240100d6401488000b620303004803024803011504090801426048078442d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 798042832 1250 798041582 798041593
    0x60901170c060a080717160c110a0b0a0914010e040906140702060105030f0a02100f09080312010f06081003061e05040f0b0702030f030a050c270405060a140f120d090503 74
    0xa00c0c21403040c0007c58114840c0928285603043c11031081c1c26040400d4011214045240c0403c1c0000c0d25074006a03000a105070800030f8003121844d00004040024203842442102c0003d0303d40018100e0ba0008200300e104a54030440d410800c1015404500380c0101522000034500e003004001c1c1d03461000707001d1584a0b1150703400403884076000146076201c0d1940942082104044103005982e101c40c2c0104d040280058410042040c96080010f04030f280c820003a80c400c5545001c8002c66a500340c0d8100c2000c0110705000c1110300d036800d1400004480d408003002445a10015600c0625442c0d03064103940c160414051005000e8800d10f200d040602404006105403a820342c00e1b030760383c4280e401040b8913403424800100701c52460f50050368020300746c8078160311341084d190201540706a040d410020200c20003807090200d08081c402c0300c1e0310050550300c0703040070350410200c24050062101c0041c8605007059095006440d41c00c9100081e040f020101e1b82d2251084001400340c15090290a000b0b02c0384 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 798044082 1250 798042832 798042857
    0xe04050c090102100e150c04030b010b0a0c030c02190e090d26040302070b0c010c080601031a1302190903060b01050a0c110103060f1e0e060901170c060a0807 69
    0x1103004403200107105800601c031440300752139684040d00c52941e480c0b141d40100d0b20038100002d114008036200740501c2c0101d80d5a039041d46000704003460180c00c04000148140580c040058002c2041d200c06909401d00d00700030744103440000c01c2c400100d1000c50030100000c0d000901954200b4119003e00c5440d81500e040f40c1d4a000101ca000c141c0500190800c0e000820340013500d800b405065130000d00910540d88070130340702c240d00c440c642d12041c00040140c0d544c1c0181031000c0e520108403500100240307010b0018039050561641c0110f150006640725541161070890400d1042d8119042910b1401040030407402418000c0d01d94001444140d61b003500b01b80d074595456104104556101105844e60b0384241c02c1c545907440d90302a101007082c1403654402012440651090302c41008250b6085440c607940e407040120202004507601000848000605000b0982c0c1c50b44001419914001c000c1c00140c1600c074007003454514600f0344943c00010001e0542c0c12554000d00d12803041d03075151100010041f5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 798045332 1250 798044082 798044101
    0xd1a060a0804120c051b270c0a0903020a060302041805010f09090609141e0a050303070e0a0308030408070209090a1a15030105010b0d0e03030c0a12020c0307030e0405 73
    0x34119210006041c4400040006504807000c0f10419102e10300306000180580e9224540b03005071482081d62148110141818a000c102c85580181b2009402442c0c02c4649240150003801600c039012000000c40e9201040d8400c4482000654009190403030442d85c555001d00258001d005900c45031071a40e132550300c120740a0080e00d0403942c4039074966040a10780700100c2c0c001c00031000c080360001e484481c40000324840c030307560348417034076400c406001e2004030202034058a10745090b44903010340141410801162020040ea0361003811030070505016035150700002c40c0000140c200406000010050005100c011006026210b20a032025100e584802103400e58480c00d0301001131000d10000d80401020800081c2203800104410010040515000029007565004d800070911842d0120780845a007015000740c9510040d808003451440c10400c0c0340c01924804d031000c00090007604145400d00c00e806a04903210100325206494940d201407030000e1040085c040c41500c100c2c10301c004549002d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 798046582 1250 798045332 798045337
    0x1212040302190c14010504090203270a0f17041205060f180c150f0c0102070203060604090b07050a0203130905060a0602031312050a0b01080f0f011a010c05120d1a06 72
    0x3e4020035044103003032400010f00d104481c001040d504210040c400046c08109138000345010300c00316590454194801a0f14000820014190b0391482d03005039910760100b44c60b00c00d118801034010490001034000b186c203041d85482142c0c07121045d00e00d141d503a00c05002010907050700400d102c58803044191940c0c00b507100180542031100240350000b01081c0c6141c9000031503215030590070740342c1508100e81e00002c0c54954105020000d0b01380d40000d803031130440c5030900c2400e610030002c99080000c108141c4424028250051400052101c00101d4202840c000c109031a0528070031400b5003a015165500a4007400b010740b505402480a080302158940c0013006990310b140202c060341d6281894250b1034590000c1700d0741c0507540c6014144040c00031400c103811442c06011401d00420310328280401c194030f0035140200010080e494850b11003000c0c406543c005040850034070b010040d101281c00e00c582080340c65480103a4004c80003401c00c2291005401514a40036004074148912184009100b540e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 798047832 1250 798046582 798046633
    0xb010216090509011506020d03061a030609090a08030a060302130606140f0706050c0403031d031c0527130501050d061d0102040306021305031c0e031212040302 70
    0x4950314035040c040c0007500c0d4070665100c0310480c008200c0d030a2100c06031070500340a0304a000103804c21402005030740d4240c000c0c1c00040c00d000d07000e1899005030341240a20703400302405080c4102c4240b008508c003440100108000c0b01d4001480c9580c03420101c3c2070707100802d041e1000324040d22901d070110034503c03814461a0111204d6890f101100e001d01001c903141035029480c0f8200300320060103000042407007485050310900c06914410f95407800d5040141102d0b0800014dc4224000e24000030841c1d200841e00d00348200c0c95403241d030030300c1205ca041500c0c0380c004c1e42100004000c0d16801100d060040900d11403000d0025a0319003800918081c098060b10000d010350790704801001100c1000404540c008180c45901c18800da0300311460007082803d984c0598030549a150f00494421502c82410320582c0c01090100c0003002c070b82030310040080f14414054996014440400c62228036030318240446010302580c0700456a42d600c084050900c100b80a5806400511034900403028980c251942010316 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 798049082 1250 798047832 798047863
    0x60c210518060702100e07180e07050a1a090414090105070f0e1f0302190806040605010f0f200106030b1905040203030423090a14100b0405090a111c0b0102 68
    0x1040c1c81d0852000140540c00007040e040d104511000440808c48106501203211200300812480c0010800302d24050849d04054403803c9001c1c000c1001c140a25054014800d0b0075a1190701e501e81d000019004107003036a8002100c5405108010807003806601582c4260519256415204208181111a46540e04085804c860460924181c502c04d90031035143c041700c2898050b207070002040c0e54101c00200540040c02040c5d24a0500c1850718243c01010003034a000c0ca0f00ba03862101140005049a92001c1080e00f4401d001220343c50345070b03c030300007170410700c0458000b444116a00d00d40144025400c51f040140840303454000700070780203a40511809550002c3c010350505041c05100c4041400041d407001c106150b104c4035801b1900e594240c1845500540000a000712000e59465000d810080400d440a01044420300554180c0402da030180d810640d6000071756a610034400c0d00030400501403407601302c0081107103810071742c6264085c9601c0704004c1c0240240d41c621001a80d0310070028040707000c0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 798050332 1250 798049082 798049093
    0x902100e0a090218061210080d120c09050603150a080c030c0108090c0907050a171b09040b0901090203091519050a1e020a090819060c210518060702 65
    0xc00c40310b40c0c01070081d84401000c40c4944240c11000141141e006018241000424800f00842c0c00c2d1135400c144006c0c182c143c01341800c640720100040c500d00b406501150020768440c80c0c01511440307000c49001500000d06000d0343d07402d00ca406945004d007404d190038401e200400010806180c013240000c640403000e0018004032404100540300b51000409981d140d00c01c8403581c1c4d035555079012400307010761280c0e11946e5841c664110000c003101201004403400f142c800051000501404613185101b018145411f134441c201840040c014141d40d8800d95030241c8518008500040703680d00440c0a440c405c07080340c45075050002103c0242c0400c4901c042d4001030100c09805c814040d030880c40e8081131300030340010719021104424a851070044800710340d0642c04075042d51419041a42d54010b032600200a124208484081c58060311510900420083d20751960204d160300541c00800f440010641a44089540080050003000c003264030295005044000c6003401d0404191756000d031003030f94050301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 798051582 1250 798050332 798050339
    0x50a11100504054507030b0603070e091306110d0b03070e0f06041e0f0e19062a050703030b0901030b18030405060a0c062403060b04021c0902100e0a 65
    0x406585141c100a41310420f1350118041e056000c0c2000042850103002c00c070113034104400020304860742d00304464080d09041050000039900181880310b001c508903200b51466a5010003000124003601c0c0041c41c0904004d020041c005100c8060522100c84100400c4003a102da4101581d0b01d50344e120720311420400c034022801c034080460b00350b44e0105001c1d20105442904000c1d4a00410342c05201207074107036a5090030000f41e1600c1c06580b017410f460400418501641000500381034805501c000c003041d503160f00022a04540160b5010380c3d2400e0140c0ba981c084200b040076090340d1210300d04400003490300c05002c03194984000158142d80d000901c0003215521280d80c4a0355031484050040705101c1488001aaaa41d842c01020f0907491540d0309400043c41d440e1110a940421040030003000c020210340c003981ca00900d4003001c80350040300101e500302e89400450024400c00900510b030341040c9150410030a00e07500001003103417082c1d4100b0500600000c040341c030b45055000e019407018007514200f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 798052832 1250 798051582 798051619
    0x40b010603050618190e07080c06070507030222050a0623010c060c0522080c1009050303040f03110a03020a12051608061b0705060609040f050a1110050405 68
    0x1d50f0320001c06440300380d60b0110481d080d07000303990481c4c2128150b8a0300140c024081c082c2c2c000c1c0400d45403503a00416103241030000c0146c803901c442d854180100c00114108042c004100200d40055401800c2da0601e0304104803d40c401c040d00404040105007040d01081942481d8482ca2003150b00800940001060b6a064450308000d5640c8031410000404002c07004108103120f22070315546251180c50b90340e6050a078101e04030b0921540031000d24000c050800110902148146040790111600704c004030300c80c2c4040d0b620038010f4011903007600c000705000c90344c031840716035600941c1d000d00941665480540200101e4000c03e000c020341104070301d1402c010100200f0081c0c034020b840741e000c0d110b504001d22040c3d6801001c651260720107078080300a1004000d9821403462001640301c8600e40b90880c1901d07000c0c4e40360409000c0e40c0c01000c03400001014401c403c002245000c1d8000281c2d044840c0b142819461501a41c94140c45101c50144918030a406001150201ea0029207118400c42031031211 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 798054082 1250 798052832 798052841
    0x2121504030804080d06080c1002070b0f2109060f0a150501030f0e030d020a082d0402060c1c020105090307210c0503040806040b010e04211e1706040203040b010603 72
    0xf00c42a4405000710041c13200c3c5c1c2d00502c0007420099005000a01c025410042c07104d4038484400c0964000400504c034181410b07080700d11034074009040c0d0365181c000040d203036106820403858a20540302c100a2200b090004600e0078050700807060945890b48540c3c00742c1084506861308091800140c90081060b5402078204401031031803034100048902c280605c03582168880c1c13814a8910f5400510490135a4119000c243c1040c1825840d00310410040701142a503072181006010161201c0006007c540c4d6150468610196002c10341d2011121701c00d85100540b0400c3c90100554200f00018150080000981e020540c024046010425040381c12030340ca000b601c0241010040c0d07400c0400c01290703040004100505422008000301c0c50710341051306030444103030401100c6003280c00a100201b5100c04541c100611240f0804414841e441c1095800140c00e60003106108084154040125001207452000c84004090b24a65aa4680400040b84402c0718001c044e4072000006104c1641700380d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 798055332 1250 798054082 798054091
    0x50609010e01110111030a0507020d0912020f060a08100603051b0c012c0105071b0b150405010902040608090102070209041214040b1902010b01020c011b080304050703021215040308 79
    0x14406040d000c3c0d5040142510000c44645021041c00824040a01421301c07230306911412903c0034008100c81c00000900702c0010340728a0720702c503000f00c685106540d510b45160742d007114010b000503a140b200003400360004200700d942c090b07610407801000812600174041d05204244034082c10721220280841040c00b03401412085150b0340d650a0085800000e0b0307910f4840f030100124500350041c01c948499400e541008007650100010f1100380694002c8200d100e200e010b0f07001250300002c1d0b440d407603082c40c09000c0000d102d6219043c0b20000684040c02d5000f0030039204607988082160340c480340301d00c0c240e1140c242d0003504900684005030111b480b0700b01e120756200051408492402c400c40c06c8150301c0d00b02d60000c807110403001620700c8006219820b00c45030301a00c1d00003404044035500010b5250041601042c5c103201072201035040307400f2003400118400f81d000003596101d05050070181d1742c030092400124011401415810b0b9034440015a4010041e921480300b00e540d6281c0d9012240100040e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 798056582 1250 798055332 798055337
    0x6032f01030207151a1009030c05011409030703030e12011808130b070b061f02060109051f03050a1a040b040204021606020a210e0601090203090c0d050c011206050609010e01 76
    0x8000707805007640e034040e030050b405082e001203841c1c05d42c040803c2094501941c0e00028010151401c0002038a084215011a5802d0814070b044100c40104100780d072103010182c0e07515018400300031040582010702e184e82444141d45031032402c001d00e541709003260945400d245140c90782c41d080400048a004c0107203440c0c400c4140024440d90395004c014510781000303008449491582c0e042203c507040141071480c41200c01c500c01d0030300f40c0302c28601035142c80d018040d841d52240c40c0c1c40000e107100d00d82100741c10036080b400c482180065a0341442610781d2441c800849008841c5202e000407280718030212030086400907000352040e1150b600f0000203601141c01c0030206130080001001061941c4044d1900c11010b4032000c8001d40c072a0b00d41c420101c4008004a401403a00c04546401c00d4001643e0b415140096001640c940b15040840c1c6001c41b410036255000b1042200340c2c00700600030900210b24102a25003010605c0c030000070b0700643c2c056001d0680c000f00c0611190165620070350b58801111010b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 798057832 1250 798056582 798056603
    0x100f27090f081e0301050907030914030a050712021204140307170d030e01020f070212100923010b01050d09060b09130209102103031b0306032f01030207 67
    0x2075641440210a21200792115030020403600c0e03114541038040328410f0070030030003240b4540c10178001407003010015054400301030b900c241100400484402e2040081008401caa49500ca4910010032030b03404207208580c96802c00382001c80304e60000600c0340f081c5036019500c5040c43e007801d0080c400303d40b54044c0c065251089241c005440e140554042440c0700500024012010940802800340e40041e8803503441e43c0c0c0304001642c1e26034042d03810744024550485a0305041d15404401c01d1810ba60000c0d44201d507444c0c8011041040354154040c1841c90300c52042024084a0340c02c84c070b08942d044510280811401c0103202955141e40d0f0054880314404c00c400984d803040076006c5062068111950940031520361103100a51908400700d07030303200c10309603840505c041c10817040011480442c0001901d040b205180d000425000e40c018031000d41c2626100c22038882c0099000307014090500c4280ca4541c840d0090403100400c0503001424091020104900c20301d18900442c02503100d40402c0e01d008244 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 798059082 1250 798057832 798057851
    0xb0415030b06040603060504140f010b0a02010618020316090614370314012103050f03070207060813050c01050a03090501090803040201181a0a170906100f27 69
    0x3000b015002410f8a9640054420b0405041c00112401d0400e10940c01a2202c10800310401c01403003c0d0559121680080e00c68400b0b8005a014100399049000403003111200d441d054074543d070245102e00181d40c01402c141c40c0816003a00c0556203800780d0b600140201d00034030b161012070700050036290640d548012442c109c03039800242e021141c0000c1100380040f40c1504020b542e150044201011003090094104d5140071204482d04107a039076030707244407190250582c06140c0105e0646202025100003d980d0789014030000b91038400c20f020b0b03400403648807804207404040d4160050102c0307a00600901e403640110300107641da50007040c0c5500800d51603500740c80001e80f0038050101038621030140c82d0b45900301880050010f00c8045843c05142c080d60804211102490324140c56244510146c5503442400c201e0071a0b440b510141d610380078201201c1070010800d070000f007192245500c1c94407072038800c1c1c58003e140004002c0d482880c18610091003011600e44072a01e00004000088100040c2c8031032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 798060332 1250 798059082 798059089
    0x5060c03180d0c060b0a06210603140a06110c0c091f0e0a050612070e060607020a0602030a02100606021b031c0906180f0e0402040608010515190b0415030b 68
    0x4040b50403074002100d46019004028442c002e016401400711036020034141004401044041000100b207005011031454040c40d0480e58007240c05150010902e15807010101e80c15a03440340c90040c12070b00140341c010b06042000c0340e17606581e880c500b5580a0011180345d0000c02c40c0303400014009894280342c040d0f2599500502100c2180146540d6640120914180d034007181180d00040200e4010714264907090390121000c900d003020f0300c0c005060010541c0303030b00003c90b09601581c10001c1d003101d8041c01c045070b2140c0001c05802241d407030b54200c1d4001503e8002c040203032a62440b400015903c4500c2c1503001c000d1075240e6120801d030180c07c4071900c80700440d004003035201d1088100c0114049440a02c000c96100a09400d1751144201c0040070915001032070583c0c202c1c1c1c0c2f080b0f042d1000c081c404101155202e8000c407009040c003500034051070401c80b090002c0d030400c901c415031042c0c4030380e503008030171108080400044414001545040c6072900c40d21384040803549508500f00b503a00d0403032072510369 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 798061582 1250 798060332 798060343
    0x609062109070e1e180708101b1701050d030302090301050106030b10090e0f07051b0d030608060c12071107060c020406090e0c010e011b140606010c05060c0318 70
    0x1036010007002c0051905a140e1100a0094400c1d07007000351a0540038603203810b2021540c2c01c10580b0810b513682c0801c0000d5182031000d140c05c03c040c1400340c0404c8002e120880e8202500c05030406c1d00d00c4e03191408590301510007903006010002c0c0345c000140100b065140c03a080c0d40010300e000c2d040140c58815124006400c40710260811800b01ea600c5d03080c074006007043c0b90711114003c00341c100002514100015401000700061081a04120080020f4400c074851010b0707450004151662408507210442c41c06d4903050003031120400a0700d00362000505d540005206401040d00400a0f40380c0798610120701c8806500401040c20310021450710b1461038000c00c940e034010140c1d41d0312040c0710300f4103104020581d0040d610100c190b81c200841e03100504004036250340710490908100384c0003c01d900058415003c3c0701894410110103681d600180040c00c2c03500c8001c0041c41d8156050340d0b03154001500c0018290700301410690043c000108491841710055811105600c2c03022113501d00700350301c1450710707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 798062832 1250 798061582 798061591
    0x30906120411060f070b0402060903010203090106061e080112020f090109020c010f0e190c17010204030c0b0c070b0c1203010839190e040f0b0604020906090621 70
    0x8054510802042c004503004603403841c40300300c2d41e0301d141084075526004070703004140c00945041540d5004c1000c560f00c1004035450b44030090000e43d12450694040c90003130043d031140300d0210780c1403c82621b0961321014043d42d44802ca48611030541d080018003071803500500f81c00c903000105440f400030281d9500420714001c2680b9030015079910000303000542503451710300c3c0d5000d9050070000001d0311040c021581259070241d628010303d4207034003814036035162041688141c003440c0c14081555071800c010f400910680b405602e400d14207542c0c686c2120709501c6664404000f541242c101404001080002024a00c2440c0e00700c0d0203c42c0b10003140c90255000381d110340030f40d40c42403142c001441c180e840617107403040e1600501003101c2d00c550300700c040007800170308024443c8040d0b000c3c2c0c080c02c040d4503030300001804600e0700342c2c80c2c28a401d29003400b018140c0070054401c2d102a80000e00e462515008644140601604081c03d000080040c01035076040b5111081009070742c5190900020400d243e010b00c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 798064082 1250 798062832 798062857
    0x30102070b070e060702090703020a02011e330b0307090b040e04021206091902010c0501110901080f0105060d0e010f050c041403010605060f0306210d0813150c02030906 74
    0x142001400a0046030300c0d80c10090045105220361070244e0740700600e4552010303503409c016076100c0c4405012401000420440140e001d4a03070043d072034201d00707031f8820b0900417407100c100760802c060003a0a408072080320348400a039121580c8140151003111014580040d0a4140700c1d41d1142c548000180540280e00905035100c03180d0f0401083d485d2200d04111150780f44c0c0042c000600b0046c02c855185d0306c80c6035064212a0102080c507046911440c40c4a082c290020000c2100840481e8400c00c554040c0c3c0c0d01600040b8400c005c500d43c40031083c5001d040b100c00610140c40c1003084880c0e480a0040e1060829065613140690700340e810719402520302c91f03428210101e9440c1d042031020322044036042c0407113000741c0c5030800a0201e81c603000c040355406001101499202d84d5420002495801d14040686403100c017032514076100a000141e105a142c2c540d01c480f07080b5682c1d4501d8446681006501400c9202035a076581c20b00841980701a008150700d01c10b6a1034484d022011032101da1105640d0000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 798065332 1250 798064082 798064103
    0x250e040534032006040e010e07050a02070303080703330f03020a05130e0d030e0601090b030d0c03020327040e150115090306050711010b0102030c0709050a020903010207 74
    0x150201004400c441c200003020009098086440d0403410400007400001c0800109100280d100012005020b560b0703030740141400d80d0380c3d84502c00949078460a11401800719480400709000f28080c01c1601c41110301a802415814030b0b646040765100030190190050540e1101110b80c244460b00d8040001241d8540d4a401e6101103900301ca51007149a20015440d5455041400165502c0c2c481e401114421a0020400140d156620b002000b01d15a601c000c0d1080d5070801006580503003011280320a0101511220307170782e485203a0181c81100804a5140c0c00100a0baa071007805001003c444034000d104880c140ae1440800f9040d100c041e105070b4400c0b0300c01c0c000012a52034580150401c20144101512007480b202d0208a91030b40c040c0a103880c0e04646040d9000140d00c00d48802c401182c100500788001e0801c0d0034007600b5160100640d902650814180d0303000c2e940000100c40b030085003800180307000c91400000100070309015214180d0b542c0c08118500582d94240050800c840c000c002090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 798066582 1250 798065332 798065353
    0x120603030e0909012c01110a09030605010b090105040521010e1023040221100515011d310c090621090f0611040617040203250e0405 58
    0x401c0c040081801440742e0601000104482071001c17010220100600041e5803503808401003030140001500e504481031003c149206132035400001c0c5c1080360f004000070042640c966084400b248140c4240c00d002c900100402c00050910f460042620812081d2910240317404214007801d4640d10700481c0c0380c1b90b111014010034000c59209070304942c0c546190851121154010308040c81c20028070181c03043d60140c40e8013203265110130105411041c2e0200313582c1a08400901200242010740e00400241c00841c403500c07007540941c130841c48a0440c82c0d8000a5130403507004100c410801c1550203c04030901650140e0000c50038091a4044489028081150750b0740c0e10f00101031100c1c5920200400003a546100c000c60100d4041400c0c260344007101107030040542c00d100c10580044240240b21038901a141c5c2040550315000e0000d0700e4559407202206a02103d1f0010400030503030b8081c0d4542c01c90054030f05003451000040c1c450364040c0b4034220155595907080e814042003103505032000c1c2c0081c06581c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 798067832 1250 798066582 798066589
    0x509061612020d08160f090f06080106030e0c01140c0c03190204180c0e04032a020f0103020a080604090c030f0506010905070504060c0b0a02090613090f0204180b01120603030e 77
    0x10700ca03540080c5804c000390715110550103015101c04034190144425a4958100c2c0b0344a04844405001e40c0a030500110350380d01d400031b0106000340b043c07200180c03030b280700340320040d1010606003030300e80059441070198541c144400545a00c480c246254a1054040810b1079403000c0c8401440c21000e0080d400c070030b074400d00501c010340320b45840e002c40c0800711381540000640c1a6101c103003500c07101c40507005155140e18003a41d60280256000d42910102c1d100c001c403982d0f0a8460040d024801e407810411040c00400560a03030040c01c1c915408607080310700141d5141815400700b184140512120350313640d9034a0701c440160503242170068403150070020042c00307040704074044d194120700d052030b18a00e010314003500200380c945081030041c003607100326010039440c0e10b040c1c045c3c818130b0100421240d0345285040d1a10344481c45441082c04260806d040c805e554001807007502d084402c0c01381130bda0120f074800b08040060622a00c00b50500c54804c140d01980c034054402c01c40618440c2c0c5a215407403d400080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 798069082 1250 798067832 798067843
    0x52505090916120905280c0b030910021804020f040305060105010f080f151507110603161115041112010525050909040b070807050a080106050906161202 67
    0x14540262038900b0b0069103a03500c6000d001c0c1503030380c04800044001482c64410700f014074022a441103072a61101d08414000c0d0002030003c018860242d400800e070382c1c2c141d083e14a00080750b4182c0c20f50028906210650595002040d0100074030340329071503003811080018120b13081074017501c0d81154049400d1040140400c4298050802400c0004540c00c0c5890300401c030030350081807110b900241d14040f40001c02d0f0004a0320b44208000d081d074054103200d65101e9402c1e0820002500d40c6000000d642c101030401c0011240252075083c49480c03268500f03501543c10001c0688601315610403000303c04141c1c180c215425005a21404110000e03440c0c00f400c201500d0038040c0c0c0000180d140409001881c07801c118241030007102c003070440801500e4880203813094040c1b14500c0d40c02c440400100b02c100006c81c86101e03c11415903d500907a0b88400004031a94094000c0f410085400d280045c4031880c040d201034a940e403401401180391251306031840c0900c0081640c112a403400c10480106c089406000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 798070332 1250 798069082 798069091
    0x5010f020309100e04090f030327020a090507050f03010803040513020a09140d05120a080c0301030c1e0306180c05040e0304050402070f080a09080d03050702100525050909 75
    0x210b041505141c000b40c14410001c400205200d11224441c0554455410100c9441e4001d100109200302504028010b0541400c41d00a64030844070042141c81780b00c0305500d80c107a0050700302c1e42003d00f0040141c00405000c1c00d030000f400424021401c003210385100a6004e8507005028603111407810080c404850216101494100c0c01481143e00040d801000241190003c101a00b14421080c2c003058000240201c040c01e20f001c1d0540038404540e10200504840945a407403003042d90700c0b0001c900403070000703010081140c0101d4a0420141d0401c2070041400d1442940c03c1b0011540c03541c90320125072003001e1086100100b58405004d0080a001400040c41c1c10346013880000304003000c964403031166020303003441140d020410505120700054142e00c02079112070301c996151481d03203000c0c1246080744940000d0303111320301c07060021364400c0c01200d00070314241d0010100a902c9880750800360900030440c01e41d03c204113120024080031500c0700c80c0d000c2604d80351940e47d0441c0e40d0600400400090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 798071582 1250 798070332 798070337
    0x1615021b01020a060c1110050f131e0203150f07090510020c090a1d03031b0918060f03160810060e0403081306110307020114091207060204150905010f 66
    0x40503050681d802145826510f80d018800040e00260480c0a40348000359070351044180c070030900443c85c0c038a6150f1141d07006207003d2010070310558404400412000400d2801092425080f010041c1ca881d200c886a2001e44001d0540c2d00d54400c40150140310302040301c040500705448420720240039007015100d005000c00382c501c1c003802194408060741c0c8104480109018899044c000b8010520550208400e0166100d0060500c0d00d08041c05540360410366070820309034415036a130303e07204980f43e044620455003e84440304505100d04c5101000d00014a480e03041403007d42584055a000e10021040c40d61075040d0309041070038844854903101c018000c1c410100d10b404420f20000420b040042d03030055140ca48411180c3c0c582110804601e031580300245568240b103017582c481e40110700a14825103582c0d000b00310303407058207642c0300c02d000003662140d920782c10030b207140c0030100b074a88010030440d03004000151800b95514032000b101c1000342400c0000407600c0c58140309941c2e10080c003641421561 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 798072832 1250 798071582 798071623
    0xf18100903080910030b120a0302160608040b0a1d100608071211010504090e0601142707020307140a1205070c091a0916081b0318161502 60
    0x180c0c2d03084580d12694503407601ca480c04822200f881c030b109800402000201034460144004140d20059070398003807100440150040109003ea8840c1040c3d958007296000c0d620380c6000d443c0c580361500c0310701e00034180e02d0140e900c8680000c00d2458002519800d05414801000d00c2d4140b00c1901084175015000b500a0703403c030101c03c100c855101007604001e181c021407441c0c2204092001038070180300307507030144111905010017001c1e0786001064007412a13440d0014202c3c0300b8420305c20090304400d09010b020000c404049130310343c003010810035280e01401500440345000c03180e07298420141c06012134080682e002a80300c07000c010460b04601048001f5052490411001d566491501d4640f130069814103503039104c4819210b84540701d201e1309110090312060881c200881e0284c1c0745400300c58800c010400e4123022400700606041c0603102020425030082c190385400c1030000e2081d0051440b5040d0740302c0c10703c04512062483c0b600300d005000468204c103a02c0c0d40000080c0c20300e035003600004074443d00c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 798074082 1250 798072832 798072839
    0x615100e01020303360f0d0c1211100e03090319080d050702030d230c0c03070f020406030507080715020601030c06110115080115090c02031e0f181009 66
    0xc00d0341c0e0401129000c25140e03115148210f5054400040c000034298101e602c80405c1d080d01140740681403282d2030a0340c02e02640d1080542d1100f082c101c005100c40c049015240900703210380414501880741c10b094410018141d03003d04142c40c203041403032080b500002a0f41e8050720301003001c244004a440e04800c0310050688400c103d0b4007a4103d284800354885000440c01c92080c400ca42c2580522034040295010000240c500c0740042868040344c0c0d404900415614003041c2c041d1100c4130800c40c0250310306502655101006540f0305000c98100c0d450340400b10010381c080c0085806403140c070703000f4412a45441507916802c1c100701c08000175900400010b0000c644006220800d844560801040c511098484180140401c070b00d40700071010b1000000c5820741041d040032135242c2c1140c049404140d10342079030004942c031f2503045001581c01044075039031a032102c5903c802c03190818112075080848403a0110200c3d1300c042c541504201c819805100c0074a072038615165418a2031802c88440343c207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 798075332 1250 798074082 798074087
    0xc09060607080d11070b0412230a02070302060d140a0209031009050c090403081803040f06030c110106030507090f0203070e280b090405010b1602010f050403050615100e01 75
    0x91001c0190401d400090780c3d10f8001c10a4014281400003108019902c4809080019080c0000d4504980390005130b07000c007080c1442603410f0002070034aa203144001d600660303441d05080e40039045400031341c083c0560001c0581d0390075005e4030103080300c40c102240c040504103401d420b00e1002040c43c40440d01c14041701201707807400201000f251000040c00940303040c20303050a5103407800c4d811b810b40e84580769104000030182d102c04164021031102c200d024904c00421601b50b00ea00403409030500110341c01004001d55071081c0c1004036410902e042c0381d6410303c03d0304040c600791050760f08140c44c0c41c1d0240c4020000d43c5001d1148080128a00c04118118180040c00a01100184001c0c912810081c4036261084540b840a03030103414480c40c02c00d500c2940c80a1101d003d030003410126104602e01000003030000b05d81000c40f604070307011901c0390000d00b0f910340c0103490f00d003011060a82040414400800000d13410400140108004a20181d503c0f00400400c5079000752550b0410400c05041004a09070744c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 798076582 1250 798075332 798075337
    0x1513021c030e0d1707060603020415080c0114160f080406110615010c030e0604080f100507020703020d08070503040f06120606050a0e150d02160606060e090610090b0c0705030c090606 80
    0x113480c040996104100d040480180000ea000030b540140b62042041c10020080300d250b049a04400581e15880900001034130024048400c5035001c0e007042040f500d2580340100101480c500c17610025509000540f590819508260003440110744684920071b5001000c00407160312000560726500e8520700d843c00203012401521000703061040c0751089202a075116030554004c0c0c0b1000e0101c850344031008800c82d60390102d004038005054602404650518400304428081c0c035006404007605420741d42d03e0b840e40383c1c000c10003070300d540c0000d010100b541c01009229800a00c1c05a6130111594020b107080300445880b54885028003400304440e9130499044824016000c508a602c44000390701c2c0011802c1c2440381c0480d4440491000800340c42c0c04181d100b540e21468003034501040310315280e000c107a844020001a06a10004140c000744052070403019054858a0602d003c034542541c60300c0340580c03508014200d84003508072400034002420100100000304004a400300a01d0400303502150107031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 798077832 1250 798076582 798076613
    0x30d0b0d0c090b12011b14160b0a0f02072012100f0e010f0212010e04020a170102070f080306041413080f0715050a1d1513021c030e0d 59
    0x89846120240ca02d0b036580c4d41825001190381d00038840b1460200000010001040c000c001185140c440070361241c402c14240d6920801c00c3c0b80e05507401e00c280d00e0381c1d0b14805000744403000642d01e601e030f0768000310801d0010304144c1d0b10502c034103034411031014904c540241a00b6009070148007042c1c501c400f01c2c2c0000409020311742e88410005410781140381400c02a01c44001e014543e907007003030940c0080c21119401084a005010b00440043c1d880d1108024440010741c0c02a502055266046c4000c4410000004007401c090000500c1c212040d43d40001c020740d0301c1c00507510060003208004039402d090085044544003081080300718903102d030101a80102800c1c01900d40c0300301141c050034940c241402c8401003500b000103000d1000c500c0391500040c4c6001c650a010980c00d011040a500c204d00001010320001d950240c501c00c081c000c6d00111021000300110a038a03445900c00c001b41e00d4465260810764501502044038151a0402800d000c24020a1900502e10965036801003400c1c0743d80071841 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 798079082 1250 798077832 798077849
    0x90106030216120e060c070626040305091c060603051207020306180a0512071115161b03050c03070501081b0d0213080a0501060801060f0b03180f030d0b0d0c 69
    0x10f030700000780403210210030303506040c0c0100c0000780c484002c8174006041300844000365100c03081c480e40004030b0314168032020f00745110311010714046030009001d40d026241c0000050011340006001c25503051100001c01410784403503a481f881801408010300800004c1b5101182c4c440c46c01031142d008c00c1d9180002007003200c00328851150361901c000300b1300c684200c003a0040104c81c8090281d00c0c6904070f942c014042100c000f9150a580300c001e007010b109080400860302e4015040881c81c08008030b982444100407502079505e11004444410000410f401841c0240020207040e85c03014103052a281c102d40050f410700400204000004c24000d2607510780c600c04541070383c5c4407007200003424040e01442030005000c101501d404a282c810004a01c0701e0f10b4003910085c04420340e40c1c14207500304d41c010b0103440040000c030007091201040d2807000b142c10107d00060203412111641002d828040180302580454100052400550809002d000c11075030084650700740003011541c850f442d4074203a01c5208103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 798080332 1250 798079082 798079103
    0x1b060c0e0333040f020406060810050a0b040b130b0307031d0102030f0c0a091a07031701060e1507060f06051306140d050a150c1b08120903041703030402090106030216 73
    0x10441504c40c04c650099026000f80b000c0f0342c5580003c1d0500a0840320040721702c0c040f207400030740303480c026100404403a0f4815003145000d04007008030246502002c0303002ca0501c44568000344070100c1500951080c8480e0303500003402c580d484180c03500f905400c0090921a8014020f0005e86d82c04c91203010b41141061004903600c80300342c0760030348404841c0e038000000f2214039020008140f220800420381c16100b640d480d048070b60305660003d03002c58207002c1c0f140064420343c00070b00c150500003010304040314006811414100196600d4040d00c43d442c50b045141500c41c00204040c1c00c00d11118800c00f05124803e1100500303003001e00024000114145120346c6000c1080f1051080900200301655044058a1413071b100f40d503000c00c06400c40707000000004180542004044001550440469501c10103080c43d01c00c1414807a0703000303400580100c4d01da000800c03002968082c1d0110084401d0031000c065500c030b00d042e004001660805911030000d2500402c241d55902032880825452154044039010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 798081582 1250 798080332 798080341
    0x12040902070f150203060f06070f140f0f07080d020d020309271501081f03060e0f030c0f06010515030f09120d05341b060c0e0333 57
    0x55035001d0301e60b009840e00d40400d00d2002c2c0c0391419001107210301c5041d99141404059402401040e11076640301401c1e4110380b041250010381d440c04003190501100003104c03203806001d40c4940c01c14011010102d229445070104001e0054180b0208130180640c1c00500307000c071303007141019407288907049911b882114410340c803694580c502440c8407940c99035003211007000d191021560079080300d500e0406e0702141c0e081300000c0d03c5c0d80813102004109031324907002c088403d25582d5540041c183d4031400d21064000c50301c00850040c410400741c03513206500d000802b00c08807051565424510182c00c43c034014441c40e040325001c00c0500b412290400d00b03ca05580040d568034101505080d418003d60009000c00500401400d555030801401031402041c041764142d43c03045174203210007050000a8a050355032450449250165032800c0c0440354640424000c0121941d13124120340c8048007000c003040c4500d0161116003420080002c2e040308a10300c80c04203001d031402079907056140e0204006158103040008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 798082832 1250 798081582 798081593
    0x70c0602040e07030504060e03090a062a0305040303030510060903030e04060f170705040c0f0c0309050306040f200609060702220b1f09090b01020a0b24031204090207 73
    0xc400401c0c0e80410402e0354100000c0081c007401056405550b16800d1070544240c50101000300c0d0300f250401806912032918114096a01c95100c3c000042643e2503070141e40c40c6020312090400c134061003652801d80d124110302d406022a200a0321812402494802c20300c40142c02161100541e905801c00070b1841d1111b000150141106400002511000c1d03000010b031104408029404e02c142607050f03c0c0000c0c1c03901d090200b00d0f09884003210004900140030150301d800381d503903004d500340280b8001c4411342d12100031a1400c101500c3c1254680803d40c8010180413500011500c50341d01c0d80d52488109825400245041c01030004185c480d050006280e07046550b2451042620034003841481422080d03140c2030310040000c03010f0b060044000f000b01d1044028988540800f86655860ba03c0e070031303420310070b01000401c0345a04450542c031030441140c1c041020031801714400e00201c811503400d0f02e07100c071030314a546c0c82540880d4041d80c403031400804e03d5034504c0e05a40980c1c1c0c05050061b100d54080c00d04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 798084082 1250 798082832 798082837
    0x5041d06060d0f0605040f020306090c090d050d1d0d0b0a02030c0c0a080703170708010b0a110a0c05100905150904200a0e061204020f220608150f070c0602 68
    0xa5407242d910380b409168048106411000854104071420020140d0750380d02e032003da10003154004d510260210001d00680001800b610b59160040c24803061040f040e540c4078030340824040701c031001c9540d0115112210101c00c2c0c500e01304820544412100c40500c1c0e032904505c01002d07010300c82040d0003000041c528400c0c002034030041d0b102c8c3d07001c8070004102c40c2003090566112403015130002d0381d6240300c950300c031000c0b52060380600b680b83d03228200342e031900c6000809078100307610500800c040d8164440000000308220540703140994240b80406290504010103400f00c0180c070401d011100e68100500d80d1221091500c01c8203021015a031407685c0c0380010014151500c0710008000e400740c007050703c94403940c086e0060f01c00980710019a0100740c002c100e01c5020380041d0214040c4480e00080050510401100e001080604505a4140340d5403a805199030041d9050b00540c1c3e031290704000c00c2804009110308081c1512802c100c6083c50f40181e40d0340480208500140301c1c00c49804410801550304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 798085332 1250 798084082 798084097
    0x2a0806090a0b012103031e24080c01050301030f021306030b1f151d03120c0c1f300209010305160509091e0703020c0c010201060807140118091b05041d0606 68
    0x100180c0004e12320821f0640e00b02c0c1540e1503030b400507480100e0140800180410440416110700c2e007540e28560320f01c4001d031070140040385c01902c1964225005140c1d0b00070714000e141305030040720062800321010340303003150315100d0700c403400c95000400c0121000100c40c00b5014121490408400070f01ca101c49685801094092505407107401041003508074041d015003d11120a826240314890300d40400c408902050300f2458916620006c401c007040c001d0700d1803c84030000182140700740070300080c000780c5040c540d0014100240c00081c60301b92580c0c10710500758131514594445903030481102e0018a14042d1a41c100c1c000c9140b9004900441e0010203c5440c084010710440200d24043c1c0004019400854041080d07204500d01410a58010300605040d184400c004101242c070701401911300341d40c2410000c1c10712901100c00c0d404602d100102d00054140584041401101c80c81040c02e10020311000c0d00c10010305010900410f40c103400c140c206071820b0110304032103403036040002d00716110300c12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 798086582 1250 798085332 798085391
    0x9040b070e06301003052a040509070612020319091410090b070e0328050307050109020a051503070503061305070f1206032a0806090a0b01210303 64
    0x110610302080e10150440320303d07000b00b940f1180545030030403461103100d4240401030081d08220455080075403000d0074942400300300074440564031001c81c0410200c5070b00303484c02c03407c58121040070b00200d5004000c0000925440d0303411441c510308400040c1742d10800d1142d0344031081c0c0350781194007032007001d007401c890441c3c00d00181d40e19095007440c500010300e541c100c11a04001000005240c85001d401480034040e00034000d098400008414012509141d28000e84150030150007040807071401c1011703040d107511071800001d00901a004002d507414007544114450740c422494a8003280120080c0c0350020300e02c1c240030b6240d8803450b0018a0111074003000e01c02e0300340380004012520303a0148603a201c400260316500f516200d1405040d040c1c078040c0c00094250902007225800c0301c00c00e240c00c0c0380ca48070045807081c800e6444031403441c18010260b8400565038000c0d131192003800030600e03041d80100200d00304d00152070500702c022040d50501c9180a003e1543e584100c0c2071113101d0040034110b20803202d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 798087832 1250 798086582 798086617
    0x303010b0703170f091506010f030b0a080307050303011701050106020d05090a0e090d0305180c0f24040f05040917070f060e0f1009020102120c070306110301060e09040b070e06 77
    0x1c84c3c000c18219035100340c0344640c00c00c0707904907400140214000d550680d10030303600c88801c03c0151b026004c07001403a030300000203500004250b01c09002070310f40d040c07103207010b141e0303e516140100c940301d6140a03480e900341e40b4280040192a400080d400303a01c04540c200700352a8a180c0c070004041255680c410350002030381404000d0b40310404a0600d0b00c200d5240c03010802600c41c20b000c0d428685070b024a8101c25404410190143c2c5000d4481c2100f50000410a14152411140030002c3c4d440f401d41c80b01c1038032000303c0c0511040d060038808030023500b020745040050600c5030b2200303000e038a41040543e101d503c00240100500441c00300440c440e17030b082407041c4404a048291107036500c0040c082d80c8c2940c002c0a11001c0c03004011300501400540580c0100562900d03212694a0b03170b40016040016881100710001c005841c5c0e00903c070510f010010302c540c41e036140200141028140024242c8a051240104400180d083c150360390811950b03c0c2480c050b800c001d0201c1d101e0b200d00b280f0701d040e51012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 798089082 1250 798087832 798087841
    0x30601060306060305090706080c07060b12010507170402090403030c2c1305010e0406020306060d0e0604020f0607030f050d02130b04050a0b131e030614041407080303010b070317 78
    0x1d80c00000894100d44d50400190351041d0300c054550005014010000b061300000c190703280c1700d007005801250700400001550826040004030030101c401650382499448404000c060ba8010f20042c10981d40b10507060024502940054020b40700100020281a80c642c120007601e0b10480610313480100401259003124141304a40d002c040c41802081d201d40800840c5890004440c0600f5049400c2045968030940f10350390344001035007009103ca40c0040342840510741300205e5005080c80c02100e40090591420280144402d0001107000075010f00c40070003407a40065401824000d032042d040c035205460f40b00449418000c1d00c124802e6512400e030300c000c08152107071808020720449808980e0f4404143e5506081c113120300550300041c0304004d000400f0007001b60307a2111000c191051440b407503d01c035100e50b41d140446072441c0f2041521003c01040100304140c0d20100c1030124003681c010080e051415074856035070312050040220102003c80c803102018011903040010400034502c4400c0c0d03140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 798090332 1250 798089082 798089087
    0x20030c0105010e400803011e0605030601081305100e0303090601050409020a060f090e0c070512040f0b07020a081e0705010e0607031b020301110a110706050403020d080903060106 78
    0x81c207000f0210040c59010104000002d144500d1160421443d060702c0814000c8201441c2d510b010007403c1e51100d000b002010014103100c00560103400590480350b9210341240c81d031220b1a009070080001e2003c20000c0c820039a801001795035014500400e0724003817400e01e103882400e10052414040603207081c00440103040d1000300c06035100b041c1c84d10840e51140c3e070b1307101040141c0e2a59a00a90040500030042c8046840307070710391404901c81820a00c0185559803403051090004071814403595002041d2202000000d0003207c00301a854600981032a05200b40f02c40000303c2441682c602e00c8000071103808646a001560004009100a441420f80c5141440c1024070041c41d40000d540220000881c140d03000d1302c980016241d010307145500341030b203603501918003400c50000e00312002d4a008104005990901803800d180a542c0020f42e140c40c1c503001d01400443c04030303a00e20b516801c028420b106032036000069400716501100c0290303000086007841d2541d07110342c10307555070980909800490041d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 798091582 1250 798090332 798090341
    0x6041b090501020c0a050a150905150d200f0a12021803071a03010b0d1b03020a1205090c1009090603030903230d11150f06030705060f090120030c01 65
    0x1042a0284c81c0b000c5080c500b0070000c294540030f000c4c3d002d00405c2042c000d00c1c00d16a00480100c1450500044454480e800142d0b140d0441409030402e40e00081c601100c1c840d5400780004804984c110550502018143d068042c01010710600704890040744483d000f0b40b0801a00041c0d0211480440d42e954103141e1041c0c0c98000d121559010b0301c11854001035910f855142170f503070521240c02003800c5034200400c44c40c855016034070b40782c0215110484103225540b0240d68000a40d600e884c0161365610030b82d00500340700c80712052001060b140404105071050042814004d800007101c3c0a00d03501d880d60403d03a802c40440d08000301880c500180401010741201c03107070742540c0c060702101d0a40d848501c0f602845441c00b0f40c2159980e00081502c14240f80110200c109003116981919010100704110b0b07075042c0000c0b03030400011f41d400424030059090a02a20001d0103003910103501d08800c018a0400610400c00024100142d10a200440082d051a035050800004003030f20383c0d0f100b125942341d001c0c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 798092832 1250 798091582 798091589
    0x50604120b0c03040809011d1206010f060c02010e0625030e03010b04020304030c1101020106080d0819020c1216020d0b06120601050f01050f09040c1106091204030b06041b09 76
    0x1c40000045600c400340c44054030300c103541c04a481894604038400464041c840a103020000301d1500e051030701c40e0780e225400000140102c0c0000c064940c034000c20782240744160b51002c0306200c40c40c08a81c003d40d07030241c1003454100c2c054a6980d95805082c5200d880f20030039040d41e4101407400b001520406a10010380751001c00124024400000030700b0402c401c03888192002030108019030510750019481008100107038005000000c2c02a40d01d40c9018202144c901d0b0300310000311440d0800c2900c0d4101f601d0444d04007176030482142441210046135680300703894040d50025140100740416040400c41034140c16550261542c00c4440181c40d2044131141c1c1a10010720444550000203040c15001039001d0488000400715402030081d100151a130b90300c18200784d40b56200400402c1f94646850160b1110124941d48400c0c40a100181079410110043c0419109400242c0c1c00c00703841c0a400162800e4075000440790155440d038400040040540092030003c00029002d20990310f50031020000c02c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 798094082 1250 798092832 798092843
    0x90d120207061b150f0501121506060e010c0501020c01060603140a090818060c010c020a020a080606030c040e0114010b1c0501050603220b1323071a0405060412 70
    0x5291240300c256801d041c40215070300e14508516003e0042a01120300001c00a0007000015544103402060825144248c11101214901da401481000103012130345003402c440710010007400f0708010000f412002c481c6d02c1c0504101012101d141403100070760484050320044802040b0a99841c80054042c2542d810108401c1d0318040000303400ea0f8080c0240c0304a254424802860b01c51401c4081d1921140540700503040794060106100e0b880c4244118200d000d202e80041824070598070401405080c203030444c050a402c44018040c850300c00054410242104030380100d924085c14000354014101c8020007061407194500000c1d0b81108040200740715404000c0c100c0741c103502c4089035010f8403004c3c13140c3d85d0008401c20000e81c12100342120300040c125080c16403516002241c43e0f4042d11801681c01e41e50180185080310100600d4400d00a50001c00341840c0032454840c441d400e0b1a100548078001c9004181070241e55003010070302c100e5014007401414140c40f10380301c44021000d018984c504544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 798095332 1250 798094082 798094093
    0x70902030426070f0303050a150e0411100c0809130f0b030709021c05090703080f130f03021c0302070506041424030103060b13051501021b1311090d1202 67
    0x15000816002c542d951904a03100c2003035004c80741d40450003000b0040c02c24140503513a0000c1040c6d4262102c906009200d0144200000e0600d820180f14a489501e91107210361018511350246a4202000405c01900320b959503890741059004110080060440f440b0301529100400c0c0070190326501a500000d030a408550705a51200300c600128410310f441058058109640001070100310b80001c0da0100c505425105c04e190740c1d59413268030390400c80d0750780c04031040840d01c100c0a00300c0b500f001c0b0042040000700e01001386550041030030312a500c1c1e11100300072804050311080c98000c01c000301c0108000390010395a10f170740702c0e9008050440c030744002c0c0c031130000741c8000c41070500c0c840700260aa00c000c2c05d04514691031a035031100181018030406811170b0340c4030380c4800070341c1c21881020320600035103120035030201c1c1e040002418425400c120000380340061851400319214010800d0f4618454440043c0074000c1680c80c43c06030140b5040c50341e01c40c017080c40c43c00c200b02402d00c42007000007143c1c084a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 798096582 1250 798095332 798095393
    0x315090206300717060301020409051311150f0918011202091501020d0f1110090209101a16051c110303070f030c0c0b0f06181501030e0709020304 64
    0x11200070040d144100054040c840d0304000380d11942d803d0317030002001000145031170354954580094a00807034407002c0e00d081081c3d100c818070142c0d8940c00c03d0f000084680d0308060303103c00603000c0a40201c0306803451380200403852150f580c4503040c5983c0440a0094601381960f036907221309900d5008014120700a0100002080d4800c0820a81e00364004c416000352a1286107804122000081180318000300000041d02d01d03040d040500400c07030001104074020880c021a4014003540f110003a0204003010020070003004010407983c001c01c51200c00e8101300b03070f0f500100400143c00006c895030203403290090170001c040003040c0c020749101070764a82d02c030140401c66908680b51240800c58408003c82c40c20310500102ca4030076032182a5901113400c01304d0a108850322081d000031800c8a400c1e0000e8074000600c1960f203054454050610388c040711800321441d00050400e5180c00840400d41819281c48004274041c605000c4000600b0710a581152a45080c0c01c001e1808020100f201c08482c2d480001c40c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 798097832 1250 798096582 798096667
    0x1407150f260403020709050c03160509101202070206040801240e0c0f0c06100e01081f1122150c0203060f09010b030709020c010b0105130315090206 65
    0x304800d2001c60481c4054055045081c18200c0c00100101c1c01c50280c0b00c00800e500c28140714884c0107094040285840b0325009446210049080c01c542041c000113100031405a078424160500041035844e04101030031645500c84d000c0e015141c0029442103002c500810794040541c024081119550020b100060500c000c214001c20203004400c00900ca00002480c1d04c0740301d0700104413510241d02514640040c81c0030040c18041c090382c40b81900b0441000420810060320006409810400003a14401035086002c01e080c0f020a18a1107020f610b400c4c0009107495000c0030703210041c2100d100d100048009000483c0c0c038142e940071300c203000402c103281d1055a80c415250000303200c2d4098000e1051307891701d090741004002c00a011058540d00c2e00d85084a64038244403010080140b2080983c4940307060811a09641c500e054444c1009001d0141103590200400904203c036000700c8162030350b040b400303020405052000006500104005800d5000c4801d184445901d400203040c04800c08500d001ca0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 798099082 1250 798097832 798097847
    0x51c050103080d02030c070c06021e1b1915182108070512041215180807080d060f06021c09051903061a091e0a02071407150f 55
    0x3502c111400d000e5101c0d40d80700355005640101c028001c403818002540e507a0300741c1610b00d2700042c0c01030b00000c01d10079151b0407003a41e08108a081c5405400700c01018842007045103164500d071881080030340c3c818a09071620469020180000803400c90302e25803444800303000e21040b140307070000601081200203598044c850031680070702520254640141c02c9500c90030300d00d0300a44019185d034049e9411b070804031081d6000400082c52840407101d4440c01904050b48120074102d55042c2c2141001a03005c2d54001c003202a612690b480303105141c40c2c001d0307820403000314001c205008001900d80100803450017004040e2034102d43d03503542102d02602c00d43c900111184040c08000b40490300b45442800316261102202441c1e00c004800200c0580d40c0b40c8502007564a120390798202191114081c0c0d0050500c018095804040001002c903903600c4440c0c403c06942c00184541152039011442d0800c0102c040914000400364004840c4601d48820f814049120000907020114050302100011240204070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798100332 1250 798099082 798099089
    0x11b060c090302240a050c0f06010608100611030f131203030b131503062f030702011503050a1716200f0609060702120313030218010b0a0c080c0d051c0501 68
    0x14174203141078a00c065903690884100b410050140e1405200c20b848104041d500a0442e582c0304a2241422552084100c80c50b410050800482c2c5240780c00d486800011071300741400c0b040d0000c0c3d0303170b20a0200c0c2005a0b210b0340c07c40b0100c40b948174548001d040d41034000d810304041c11a0324501308108008843d084802d02188011480c58503942040802d001e580001c0e104110300b0300740d81064a60050703844107402d14240385480550003000b8400340590900c280c0c00e044090760741121826007181c841c1070f520585a003005010083d20040b062030005454152010ba5501d0342c40d004000c0003a250600c03541c1c084486811130704c05030b0400d00d0404e29100240948841010b441c00d8030b800041400d1107003940c8030705816a040705500c1e0481083c450204020020314041c0320511921904520410a40c0214030100c6904d00c01068010f21500080c0801c55107840c003a8146624a03500c2442c005565001e901240341c0c403030040d8241c5540303a94000f80100200300201c1c090100b1821618034880880c0c0d03080c00b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 798101582 1250 798100332 798100399
    0x9030d0f020429040b070303020310141804050c0603130308241c0b010b0d060509060f0409050a051609060819120e13020a0809011406011b060c090302 66
    0xa600201d900755403249210696810f055652030141c440009603c07a61103407400701c0000e5800002c1042e02c1c408855008041c100399450380c3c01540100380051428554100700010303640c0342c040405c08002040240e030304c04400203007003c0c0e01c910344069842001410303030700b0940208050100040c5031110003419034401005126060000c900514141301900700401510380c03201c40c0d00c0d40340402203001e4011035802000300030b208a03910381c40244560240d504039032206000303010107400d1024603910108000d40c46c18080d500040d0568003420000d00e440e8043c0c0d00a03145014004c030150200004c8120781041d01d500d46c0d0140040359440c5850344d40c40b0030745203c905100e04201c400c440040e4415060880d03108007403030600700e0615000d00040341200c1c8492000c2082c0d5002410f10801c4c0e401c0104903a0004041d8003c1026450048250480c19001025681000a003041c1c101d840b00c3d41c0382060080b5500305200700710341040c100c0043d1084c0040d000c203910170400c00b1844c210090041c101d201d01e0300b0b4500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 798102832 1250 798101582 798101609
    0xe0102060115201009020324181509070801061d0412050c1204030b2d1f0e01030b180d030209010c02060706050703060b07080f0304031709030d0f0204 66
    0x10a4100e03180031100c07007541810240e1400c403041484041200ca1041314004030005a120800d1041510307101d011070745100401500f01600400465001c03d140d4440f07041c4046001440c01a448581800040c442c1a200d890541c814007400590014101c0203845c201c02c001c10000e40c440c0301001800c080074070b00172054181d1000080000c2c402128a407841e003014180b05050520f2181c8803400c2c0a03000b2400b1011004c00314041090205811116070054685800c003a610b020114528120303140744510501191f035002c0105490a0814240a0b200034800c104940d19589400b140c1c10641c1d82844103032100100140414000c60b0b440b884101c004a1102c018844400400d4040c2c0194000701d400c90b050029038000d10f00503031283d100802601c1d10038a0000b07160704e407014000e17080f10a15000802805d4040c4074920000b0030140844000960210000d6103940d668030b000c03902103070b4616002801c11800e00c1401030303422000016048101b00998103000d144204400d0340120300440c8034600d1810400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 798104082 1250 798102832 798102869
    0x70201060b09042007120e09090a0b06150d0510050324040f06050a0b0a06020c10080a06050303070308160e0f060705010f06060507060e07030b04080313051c0e01020601 74
    0x981c488880313440c2c038011520035081c80d200d401541c1c1e00f100406440744880401c81d44603491340400c0010300d582d03040313451080500344450301d0b55646c42043e030b0081c074868030360012460560300c25001a00b2115609521a52110300c00001c1d8050b14045e40e9000e49402a108041a103103008505180a1405d20192556015040700240500400035105803000d824503090100468450b0047c2072158040034000710b0604030840501402d410742d548180110b420440c076035045c50350340c00000171070803245107003040c15a151500034400401e5203a001301d80c1403000041103030070590002c054522940b08640c8044140744a0300003030710307145240c0c0b07a81c1354450007040e4081000d05d050700c040c0400354041c04c000070f002c089686070002101c8a42d04000c0210301d020a200302001440e006502e0320080c0728010f081001e24642d525080100003510042040a01000080c4800d001207041d000080d00007044400752100d60588485138400c000001c40040d10078a107442d503950000910b64105e412248a80182121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 798105332 1250 798104082 798104089
    0x5090402130b0904060209031b0604270f0504031209020a0603020706150e01050307090204030b06061b1605040b0d03080705090301060906080f0f07121b0801180506070201060b09 78
    0x5814030802071a907a0740d0040c1d081c40d01c800250500c650710034400180c1c4e9017203040425181c0714003000c846081803289001a00b20361901da0644040360040c1004000c0c500440e0100350041150300d00003c40e1a1501207140104801ca8001a000301d02a0b00c81d0548011180107940a44000110103904180d00c40802c112541c13103070b8005e009403030080000241c002200c0c20480d0824100380c0c0000e034810700810041c0301510b02804241c000309030701501149001d1840d034a4841e5000020002c80c400d02000c125803441d004a0309104000c20f2651b400e4410a815a0551643c8540c2034001c0d41d025518208840549045c09800307510300d03076003603281d100d02503403424001c842647c0860442a055501c070680059611640d000d220041e10060019203a44803640041c1894001044502800da5202d03600070001d00d040d40d04403601081c2c05c5070051078096030b0062405000c0c6d10507444075185621703040b10010602e9844d142000d5445c8a801520916280d224040303081e91840c4c0500c0a50b128100a241885d16 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 798106582 1250 798105332 798105349
    0xb030a081b0307031b0c09090515090a0c03020d08090901030b01091a030c0d170f04080111041203140f030f191a011d030a030c0507150f030c020f030c210405090402 72
    0xc2c8100645941c6c65190503d500503541d001904031801c0d4840c00c14052901c0d200851107901400860081c1100c020070349031071031a80e070641700207801400740150302410f0029020403500f614402400d00f144559403441e010828000074406e00b5501c5180803103044807a14981c81000c203001e0010002c1c0701d40d2a003441000200e0340404003c845001e075180d14100301c40003c10145c00601c810940e0755444501d004912400c1d075440c040400424002080144040b0190000044020b078051600c8001d00c0c1c180c2d04202614840c40d025003090003008000c04c5503500c075140d901ca00c40d0008550180b614440ad200902c1030351130103a07481c0715140c42800c1d10344855100e400400786030180c40020620b2843d481d4046402e044840d841900010000400001800f1040101400406420313054210b0f410342e80800502130010b09486004140e202c0301402203081c82002007103014100502a65900d0f501100000d0750fa000c2078011040224114900d44400ca4050080e03c3c2281c0c07018105005640d116402c00c807044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 798107832 1250 798106582 798106637
    0x1090e0603102301050d0b07120920191518150305010e011403060606070201051207050c0f030309070b281d0f010e01120b030a081b030703 61
    0x14402c88005141c110302034010a12125604907404500c0e4003560640b01d41c0f410142c20040c05200c400740800f0009032040f50040d4002005d28141c00400000f5120f800500115000504104000c82000701f00300c1d0400c8011456200c2114401d00c0310b0090250078000d13101510540e02c0c001c0032940300c040018052070321240b001c0344001711401400e8a40d80c40d10b02e404005404c0a001035a682d005011a6181690f00c0d800f41404920341106107607540006543c1c0c0c60024041741c0102c101048076011640204142d5030f0106160710b80322950f00d07015400500790340195040c100382d0701c108240c0c60368030030011088a001c0d0506401610882e407d2005041e4540c0c010000c41d1110051003207004070701600300ea0b0181c40e80010350744556699602a51075030f1070314128100d4622954440003605101da81150708804400300c203003082d6440307100030781d48200144180c05460790180100d08204080021400082001e003002d014901000c2a0705039095070f503402a804004c020402e00540c92107000303803140791300303060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 798109082 1250 798107832 798107839
    0xf1b030e0c0301050c04330f0306032324010506030705040308040f0f050901060206280207030c02131803080c16060212060913170705010e100b0a030201090e06 70
    0x414401e02103030854008558507540e0313005c01b24050082c441d50124001a40c290002144010320040c0851161844507107151000c1c411820303820400c90f80250801e130000e581198441d110307103d9020425902c055054903c80c03150203051000c0c00b90078008600d242c0311180e01c8028030b51580c20902889110b0340050701c81030034003c05020004c0002c005000800c040c01c0b04001d2244003610f000f2050042e0461a00058850403200d0018407600760700241da15884030802144600c41240c20150b80f4416004000c07611010b8000a242000d15410008004410f8801e59150341003c601c030948500301d5144000a0700c480f00501c03e070a0120384904c20075500403c100d82d165182400ca80d20120400e413800078101c98007900421100b00f002c03070044d80c3d681c0c4000203a03149282450064800c00344151440d030300909100c82824402d0b1000b1b51682503c00700c941c41002005500407004480ea99182c125415048142c10312024a0040c28000031200441e60b06840d4034140a0a00102031200c540040c5450740 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 798110332 1250 798109082 798109093
    0xa09170c040b03150106170c0f0a1b290109060815071b0c0e150a0501050f0d0504060b030d0903031d03150c13080105010b0d091b0306020d0f1b030e 65
    0x2a44071070500b01402425507440e48904407410311918071030880020b05000410009001d901c0c1c0d9201e00008840341840546003a80044440d41c0404400bc04544805000050b062040580307010340524440302200c0c84441c818007aa983c0c0358030740305440207400f80404580102803412000080c90044642154107801c2c668056030b10000102c5190303402c0b400945114003c1d4004100d01e24003e01a281c0085904548480c000b01d5040401d81d0806a841114100b0070300181c1039803010f84002c2540c01441d5407030003d20050070a82002406031490148991082c0070b400a140f0703000d401019460100ca906494888580b0072914a80c0c84048031314907000d03054001eaa4134500c3c100309000c442442610004a41038840c6d1030000d08171000c00194003c00301a030f02d048014011550004103640d1848012000400c21840e140b5100c8040c50709520300315480511003c001c01040b001c0d40140a24030b6214004000240592220000351440004c0c10160b0a10700c04001840c06e210b030b0400c075140c2014404907078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 798111582 1250 798110332 798110353
    0xb070804081204061106060a0e100b030f0103062409051902071a07170a150b070302010608010f02070201080402120c0613050915010f030507021903050a09170c040b03 73
    0x30b050a514449a11220600140521940e038115400480e400d540b8001012103281c1000481c0d98001140201d04c0c0c110b5601e80020400c41784a40d040c00500680c0742c1e240d88900300a1071500c80140203000031aa41414130f20300c00810300c0fa0201010742645201e10350010130303141c224420300038040900004088001101401c03580602030005200c468402c2c0500050304036000e003140d114000c003802d0203040021000040800d03a40540c00144c00010000000403461002009944d044480c1d42c40b44080c90781c00f240240c140341c1c06610441c00c03610003d009022020b0390300014003c038418908002d006c980c0c0c00303000c1000b5040211010520500800450b07000e5405d100020303155400195900c110072503202010300031800c0481019400c000d540303040600b9039035002c0c0040c200b0203000c2e04181c1010b0f41d8030002240180b00f00650b183c2e03407441c204c00030301141e0a814028050783c0b04404241c0494501d180c000790000441c5900720450041001070807a03241c481c8104000341c8011039006606119246020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 798112832 1250 798111582 798111599
    0x206040c0e0a091e1b0b0702040e030d0608030d050a0c050304031d04021c0b10020303131b09050a140c30100303020d050a1e050714010204061d03070b070804 69
    0x101c1e21300a22001c138180030b441d03a1409544100200d4411041902c4411080000c1b44c1242d0580b104264105c0d400b00c0d840c0c0490404c80d103075000d1071207491030b1f540c10b08400198842020009015607210303010b00340301c507075100405070040d80d49407020302001680400000340481d20860b48442020307600400740c0980121100090144d07000000070f41150485588042c6048200344600301062409444268070b20114003000b07926800010003501c1030303420504c08002080040000094900d4980001401540d141c003103100040004030784001c003103860030741815000c5075070f2030515106580c4241c00502d030040c8010403401c5c40340c4050722030401507010501e0007014a076408085106e403070b9070151484e01d503285050081c03510184213034120520004000640d0002c2d4440812601504488400382903a030400300f08039043d119240024085503171085005a41c040190003c000311085a80c801d0840c5840016807000001c45801047e40355010f02410889242c0c42405403680034014a00346080c035940300d224 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 798114082 1250 798112832 798112853
    0x306030a290a061d0103020a0603090221062d0c0c030d09050a020307150504030605190e010902011d010215060301060f081501090b0603072703030309020a060206040c0e0a09 76
    0x2e203025031549824001928809004050011003031411143e82d49560081182c9010502a9800b0541c481103071138207544401741ca00b00c407040d42d45182e00c0083c000d0820b0548440050300d1310315400c66016060b060340c40040010740311803241c0c250512116211201903503180e5000003030100040c003060000e40a00c0500780b1980d540c507401030300540b00b44403152040608025050b00020584403900380c2080240f903001045d101540d602c80f03000903e40d114010005200544001b28842d40d07410300042c4080081e06400c03203003a0313a100780c0303a000440302c40d5140d4140001007402d1860069101d2905010440c0c03200c801c05420100250000442c2c0b034603130504401c1031005801c400c1d520390204131544d0f203940e03007040040e00512120204020390f041809c00124184405070514003080b0103420300c03040b08a02d0144114401404641c0d0719003081c1d880c60050080e03e444242a4440c40d0200350016100f800400c0c054401c90740000701a100038200603099030708000140c160300ca804c0e41d60704850000340d0b15244 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 798115332 1250 798114082 798114091
    0x3031620032d1605120313050106061b06090f080703110c03010207201801120c0911030106110f100b0909010b0102101e0c05070203120306030a29 64
    0x6140e039202c0941c03040801006401880005000c41641d141010a62409032103852403540da030001510010b0400380c0c0780c0b41101d031201c255048000103010240803081ea01030301452040c0b00a20100d030ba10401920074071010b142407c01c0002c083c20103800190507034848440f8034401c443c44c000e115110380f149407654001d40c40c1100464880d000c6d04003074241c10460340464041c01c80003035107803022640c1d410008480501d4541390410046012996036a40c0c8480b411130010780c02d070071100569440e40c2c041000200b12038140c40f802414407001c0360400260143c00c5400c2da00c509001d2440c0d01c0d0030411110351480070704000c1c06006070303561f41c0e0702090300707016081050124010202342100c80208000c540c5801400fa4086a0302d0704a900109903000302d20222035480742e02001071300d88041c1c45050101603110482c910103515005a00b06090742200c00307402101c0c002d9007122a040020038003481e4610064500542c16880200640e00241c041e03010038048900011144c941c4201910094180e500c0c00c0c0c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 798116582 1250 798115332 798115397
    0x406030f0f020d14010e04050c150904090516051c020d020a0b0d021908090a33090b0f0f04020d0f050a121103040303050405041d0d080103020411040503030316 70
    0x2d00344801104c1100a400341541b1004103920341401d643c0c0741e03500e08903a510203001c3e40c0012510580c10000a0a5030190400604140b0030170040d440d1080c0c50f5840c4490201600c0c06000340800d050410004021941c400520420b0311100e280d000c0008880000d1b2040364400d08843d404602c2c1c4d1041405030900031421403001d80c543c0e81101605881e030002050400812801e40c042100701000029042459900a040c07040c1c0802281004036501c5480300042070301c04102c00055501a00c507500030702501c1d010b40c1013254141c9609010029441050310131441860400c8049009890829100d91146108207140000c00300560364442c188108c0400c20b450056003100805120b941104040c141da14a03900036501d40b50445d9400b41860155019140c00755541c2d203681d4540389180019526100842011511050070044005001c02001d020403401682810700321450010050140ca0076214020082c50841e43c581440403804d403104080b400c00c002050020008680c00300403007820050014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 798117832 1250 798116582 798116591
    0x70b060307050d1101030b0406050a0308071101050301031205210a15080607050d110903031306030b010203160609031e050a031503020d03181e0503210406030f0f020d 73
    0x108160a08501d0390009014800740300080d00000e01e0003414001c1d03504242000655140b042010400500c11a007015400c04070311a0080b06001043c4041c2100c1b920036030807803a82084040044503a800300707100003403030b009005442481590049004d010b007000c4c54007840d41d40d26946e681c0701408080075640307140c41b141d071380031001d42c56040c1d02d4140c40070b04007180007840e9500340610b00600c0c0c0e1041030044141581d441c2d030350741c0c4404029422a0f0b4407150082c2102c1c5c89403044a40c0303003204005841144046460200c218926500200c142c650000703485d42170000346041c0762507803c041d007140d4004070b04204040c4003151318104410700e00c0d180e00703000703565850321003104050180c2180d02d41620020034040c80e42c01000181d5803290724419040d858034114888001420990003c81c0c0c03250000d920000000c959032000c1080e9520b584202ea030100c2c2241d881c0c140d0780f154051400e4603510081103040c4104401d000c43c82c040e820052040640c1d0764001a9042010318800881c1c010b100b08070380c403d860303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 798119082 1250 798117832 798117841
    0x203060702010501051c020a0320010807020d080a0c0507051203090d03020720060c0307030e0901170c2205150111030c100903091203020606090a15090917070b 70
    0x4200255008016000810035941003400044250f00e5101c0c08100a00c4500c24034030440d1903505848000703651140c048a0a0f01881040c1c402201c103201119000480040000703090364400586042d00400a407034880d22512102c21140c0a0701c0b900f00814113224040064900180080080c0b10309a1030000c41f958a0381405a1490300f4603940c52040000c0600620800300481e19202528601020041d450070a0580300001b044d40c90080500394034460001045001c05e041c0c010a02d01c0301e4140c1100c1c0200c440e80c942483c0104840b800e01e0845044c1c0c80460690f01c1410000800941c80b00e601c1d83e89440103d200983c078041c1d99040300c141046078034514085002d540c12071182500c0c0400c60003c0c1d400d040e10380e01d140d40d031000c0040e440c6000f240c6a5841e0010326004002e22001b8142103400c4484096450030060b544482c1a2800c90150b8201030005034944014420b00e02d94013407160f03800e55414500540030018000804040e140304500000d800c034400b0030030008003402880385100783c510340341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 798120332 1250 798119082 798119089
    0x13270b030106030515280501030b0a050705070308180f0c03010c03140c0304030302040b0a0f1103180f0307172113051e04020a0302300c030703020d09030c02 69
    0x14014860090b070402c1c0051002030404160354108022100c0d212030300369218810100c0041e0500c0704000c4040800311a58200b8040c1e8001605883c0075410368200350716140306107400c5031400c0383c03000d002900030720104001174401c1c0d01c0507030443c2025684520300d070b03000d0020f90b0510402c100f03520550344c44002c007031007981801e00503003070b0580700c5040070046c0c403040703410b0100314a800824104103805c0c0040006d00b014001d80c156009407041203810707500e880400c0e20203046002d002114002107104007814040d44000001190580194145907807080e481d00418895a400b060141d9541400f0341840412050141c282100c0d140c0e1a20000f009060344140c0841e40c1c4101c917424074500c4400801000c2d07002254102c9401c200c0318241d440900562981c031b4881224540144060340c403c1c000680600c50300d625402910010340100d008002c012007038041c500120205c05241d000229100001400caa4664009107500c2081814054500b48148a10404132103580800710301249161031007005508 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 798121582 1250 798120332 798120341
    0xc0206090a02060f1c0f0b010e150a0c140615091815060102190507090b03070315090503070c0b070c0602010e070b0c0c0931030f051327 60
    0x2140480541440101c0d600800d1043c07080204080703000100181018140b900b0b1401841d21380801d00007003242409071200000545551429540000c914100314041441d140540010b030042d401d6050b8900240300c02d041d03602104545050380c031486080d034104042e00b020f1180034892005450301e1000e9050510801047d0000540100418041141954414034001451313041105050088050643d12940100e10700300500c109d0790f14103024444203008000d40020100b040d95001d8000b40124ac2c1400e0600d0703a56089844068400100409a149040a00d5000051480c000d03410f980c6046010b45a080d80750481d81d0114000c0400000c041d000d128603451070748080c1240d84001d20480b4041c481e80daa40f04903034099501c0c009400142500210010000302c002118044c0c1303110303810310f8410b0401006180011403034000c1d07a0510341011082d1a10b140c030409469158581d1002000b81c40030880b40d41d00041907400703509081000c003142c220030305440b04205181141d070304000f03640300e0502d440544 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 798122832 1250 798121582 798121591
    0xe01090c1106010509181606021908220512060403172505190201021902030c1902131404021311072012030a02060705040b03011509180c0206 62
    0x109501c000c1e12900400300d4200d045400031511203205450355440400e034540011090031151140d40007820711075854141c21000c48003a902900e4114040800301c86400e40c58010040c9041408c00c00c0c14070b00c2c1000400b450810000c140d55001c0c0e103440d0004200d51201300030f90008181e001008010030158041d16410350200003603106031003410801001e4030702c1d40d20414941c0c0c107005041d2016502520420a480780ac04a0403030240340000c0715000a8004c0d4890340d03a00f204002005040b081090001003126002d600040060440c062846211610420203950490788100314140070800c601641c004c0c1550220081c1a10390181451302c10083c0d500e2841d10b0610304c003030912000082c007543c4202030b11400c50700140c880003a1980c1c2c0c01d40c0d40c1c1e00340032903084c07135402041d410312041c000c4c00000140c034070b16105800b00c812a40301d00c00c00340c0e05400341e481080c000000410041c010802c2b2346204000f94065030400d00c40780d603203600305000340010070001d018041c0d0390344881c1d41c83c02e0750421100780c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 798124082 1250 798122832 798122837
    0x151e0309020d1e0606091a030111030f0a0e03040b0301140a0303020d050c0312011e14090a0c0318030e040c0302160206071e0b040605010501051804050c0904060e01090c 74
    0x3810300c154082001e45142100140c45810300052001e04803600700d040c80c0320503502000411000791246003030001031004620007440840f80f80002c041d207044c14814031482e01c4019043c076065503912980f0644030f200007000300d000c441d26460005e40c1101c0400152025000480c0001e032030358180800c4d802440c1200031170b944100304414080011070340204400b440e0017128901250340b54622281c5a1440c481c085148101d111600000200350341d0303003032203548848610100c1e40e100c25520300f0149408100708009030391000c2c0d000081600401c03280e005008004160a001c40c0c031101504410140c1060803c041e80030406100803507d86180501c164011004142001c508090801e6119140501d461400900903c0000741d420f0900c08504030200640c5a0350044106804003850400d140b0303003065600b25402810320001207001c0d070040080d038445a05007407005a21140c503a007080003801025050064400c4108114210b0381c4032405001c002c3e203a02c803c000415494200400126140f107002c0c00c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 798125332 1250 798124082 798124091
    0x30c1209030913150e010305010b0117070f0c0317070804020f040e1e1c020d03050708010e0f18161404050609040b0603032712070b070b090304151e03 66
    0xc0c6569030f00c1c80030000700711000300003982007401e22600108841a048001e400210200001c100f1905401030400e9400a03070ba202e0381d6800c41c103090150301d80244d8100010440c02000508080d1007031940a4021f80280b600d5509030b80000008441140142c506100141110b803c005c00d50070702480014244105441c2044035a041c1e01d50280c5031000e000c2d980b000100c1c00d07204000d9191081004d002c0400c0a01690545820034981c040d6171420418200c5010074103007000104810300400c0620704840140641e0a0b85a0390000820409c440003860114003440a410400d40c3d224108000309500e00503102c0f0301c10180c188154195030b03c400340b0400744160305180401c0455103030001410f40143d40400c107030781c207038a035503000070300f98003c0d107200c440b060141c2860654894056003514406003030644110718100300900c0d0345521100503000c0c240d2012420000f210003d091035800030b91084503030003501d041548030340c0b0112413038400d04a031000064240d144d590034402e010443c0380d551003440c1030400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 798126582 1250 798125332 798125347
    0x2010e0111100b0f0405070804060609060308030105010c1406010f0603050108010c051e070204110d0c0206040302280b09061006050a09090c050d090b1830040b030c120903 75
    0x3641e0303074221085250b140352660703d40f0f503807501c40c07480b000700c0918000c209009919000e4030090240303100300c03815104642040400620000300c0e2289800780c07500715103001d28581c00d01d00150f1b54984505070031502c10360300c411904e46000303080c4207107806082a8000c646215281900060a44506800c40e244691420030032181043e085011a0000325052807800018807a030381c03450b4864000c100e0b004c0d410a04003200362100e000010000c250643e420702c404c00040600107400c03a6100700446000340540e000c2d01c02c0d0002c05480030888aa000c914040050780343e0015a02d070307401380c60140c40070042c0750b121105125549503c4c41c0c00030050700543c50402c1c10092515402000c8a50911421091558521000c0d842902c28001c5452070b000107102400413120031325080c01c0007402258000300041491203000d8036200007141c40603040604021a2428078992a40c01e545000d1400e00b10105090411002034110051b1024601c02d5010420181c0c85005001c42425841c0000b00b003104250020072102c1e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 798127832 1250 798126582 798126617
    0x100c141c1d09040201090e0c03011a090a1a040f0801020304140f03030103081c09050706020d090302060301150c12080a060b0703021e010204050414270604083402010e01 74
    0x600c8046040742c0b2007203aa01d5034001070310480019000441c0e40c460040400401f54040d41c0190304a035031000e0001c845500f0201c1e200281d028241d2040d41c80031f01d1050400c15450081d5401c82c42c0041d22600501e0180e45c0c0912080c6001c43d0b134080340c0581d401000704818080d00e620300c05101401e48020300440115540015264401408014000200401d50105030816043d0300e0340c250702e940a00300250034480c2882c0d03a0b56501440746000600c11804680c4110b449046000c00f165400340c007042c110303401e200003404140d000f020401d04010000d03402c0808120b666202814640c143c0d110805103007400141c8106039020f035002a01a801c0802010340084ea0010b0031144401240f4000351100e268007045034007901c5603504c40c3d61f0041c00c240394060020030a840c0e00340a0040c1401d25045224054100c02c0c40d440b07034107540003894000c9130026010030950402070941d814640f400600d1a590951001035811094110192542e000f0096204658100b5890060b41d002404c1c01e4109082d8030554 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 798129082 1250 798127832 798127877
    0x220b03070806010909060219180603060f06031d1f0c081501050a03061a0d06092007030210020d02040501020d020604110d03120e03091903030905100c141c 68
    0x130105601e588208000a0200c0c0394180c0350f10f00d50751030500d01d007442100402051405086600c1801000384840021140d009100309000c6501c0c1c0c00c01c2401d054544003042d002070044004483c1c48910001100c030303400300c040c4a0316800303c4d100324841c40e10b9007d02d540750040b5220310000105001c158000e00030301c0040c02c00d205101c88001d01e4001d59032521034401b1400fa11003580190f41080d05a8070103d081060070018002c180b00c075280811440d82d48102103001d8498582c0d00c20a03501580b583d8035101c0b4144001484404c0c000d00444c5c40940c01c41c070040080b03901400d488030510744d0104d001d012a607810311001c1d101e4441880101945d061540710a6103480000800c4c501ca20051074020f01058040c220022025080210400025405071141ea0301d82d400644142d10a41c002802c2002c181085684901581d82596a01c0d0a4908210500184100c40b00030202070000c609001000160400c182c00c080c54280713800ba0800f4a0040160a81c450111100350140885000c03241001001d1909 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 798130332 1250 798129082 798129089
    0x705220e04080d0e1e0f0a15020f19050406032306040e0111210105010906050a1409030a060b0108060a03021c06091a090d170a09060b220b0307080601 66
    0x142c1d90365884658604000d004030038240d4007034010240303d1102070981c0300c40d10003242c05035030a45954520303007480980c40b52a01400144080c41c03e03952401d03035000550291204034446c240d954600b0600211210a00f4404107a11001510004d0148280d039410b00408100750200c02210440c103807101c3c04080d0503403000380214002d0313035102e01410941500b50441581101c01000d01c6603035200650101400e08100c1c03581111204010000040e2548602c1800c02100d200c0c0c0c0d100382c18004501403c07600c01001c081908120881407201c81110f0794184918620301c0d105c0c4000140846020b4005841200c1c0104900d10802c0740c01020030240e110505074005052214041042401d401e10384100204440c240151200b401004120034501003400924011500c90f01220303030688082c0d10864101030300c083c40c004800704030004202d444500b5044000320b14894000891900d28072004a50100c3e0180320180140d007045030048000c540c6403007485140907007035000d880080c0c00c08030050b640e40018031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 798131582 1250 798130332 798130343
    0x3090b03060d030f0320031008030f0a080921030403080a06060c06020c01060e011211300a080a02070e1006140307050d020706090b070e09150d0b0705220e04 69
    0x240c07402c3c07451710a070300c03c03c1c003041d98020081900d44200d0b0043c00c1600210783c00c02603448103890216642d4000010744020142d004141490407501c01070484202001510b42c603214420410140000c101c0801003c5140000d0180c4a80b05c0c9407500b0010603014002d8103038000903142100901004e0b91000c55225580c1d082640982d0310000c40311010300414244d40400b803a92031650000c1481f142c4540c03503c00e00350242d0b80942d0303021072803420049680c850003104a42c089134200042c48006030700510b9081602908256854840305450b004039a030f0240a980d0b00503009080306100b11144c186001d5006511000c3e080f02150404002030401c0808407001d048400000c000100550f10a000311054003221403002d544030241458064060b041e0090300320b80307034059100000c400c14441d800003500d590f4010940011911103121045600500c440c1160304000c0261641000c9840d859225000d00078582da200e907138917040c099a20b000510b40110000684042c0e00c204610390705644400c0d005138000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 798132832 1250 798131582 798131597
    0xa1205072f0c03030c030a02060a15050f040207230f0c030307032d0216050d0b0f07020f03031806070816080c090d0c1a07020307090c05091c03090b03060d03 69
    0xd190841c901600c0b01d50160b4103100000c1c00c00c02844020001c0c03c010307483e070380807109140c030343c00707050300070750303004160004402c444030908204a1808010a40b0710701400b41c030042c0b03801110345410300d141640e000384040d950702c4001d040c0c4010b81d04012228031050b0300c0010b005a00600d10010703440e0310540b41d01408000e03034444c3d502004c1212183c1c00100d00105140c0d01400031040300e019440b05e02c4c500702c0c60007074040d1200002d10307824042d0160080c6a4800c001c01e1701a0707103061903040d1078080030b403080c0118800c0d40c51190080308200b008601607560202c146050500706540c003880c0c03a0300100843e08000001d018040500354141c0c21024800c1d5a08148a0603510450070303001c0c50182c0024540d001c55559000020312148040740c0064a2503113110130300c6440c00514003c614400c40c08025010b6110001c01c0090800550000c41e40407000e281483c81e00f140c84000071100c080350b01c0000f0400540f101100304264000700580014031084040500354a0441c0010740ea440c01c5000c05030620502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 798134082 1250 798132832 798132917
    0x606010f140d0e0f070603062309090c3a021f120c120608030414040f09050109200109030b0408220b091302030c040314030c030a120507 60
    0x40303400c000800c000c000104e903610324144c1070b000d60710380f071600c03810000c40d15059000c20340050b0500e000038540a1540c90b90040034551051102220004041a11500910781034620a948110518440d50010321f05562603020406076000b009031041c1d44004810061244040181c4801442c1c40186504041240360b21310710007016110680400c0e40c203181649000a10f420058001152400391000b11400b045000e442d0f100d950707541d02c1140607180b2603a1101824603000c5c82c180e0094003403034480e080041011400e84c0c3d15a421740e02110000c0380c50290341c0000c864405401481822445001d01c0e141490901d50f80340c140f81940d000d007020300f0320f4400044030302c4019180d00941d44002d40080e4a02155030b07482030b80d503490740c0006043c98841c4910508003402c9807174600a480c080d1007001e2199141c240b56544040784500021846681c0380800d00201002c88018005000d4094081d29007452100501d21075901f1950014120000c0c004680700b1103140905a04c03031102d40714090491a01a03040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 798135332 1250 798134082 798134107
    0xc0a020c1003052203080c090103060b0a020c15070b0123030a061a0406030c05240a03020403230a0605091603111f050a1206050315090606010f14 64
    0x4440d90401040051660055810350045201d0841c900301a0384104001c02c1c1c010103400e03450005400900c1d8240400e41403031140d030003403921001c1418005540c0340d46009014040d044044284c003d6040b0080342412410208081d01d139452100c416907282000d555201c45822906000d01da04202054030440044c13040445900d040390002021210440c00a103003601c00f502c214203800c1288064030150340c0d52070400f40262030950741d0158811240c50300305024040741580302100008081c02421011100e4414000241241515a940507035250b0450510100d4814560210078070108921102201c001004c01c448542c198024400b040c281c81d0840b106240440b030a004004400b040c050000410505065010540ca42925808940001040701c807507d200003c0e00180421400c100100d241c51240d8601c001c0d21090890004006480b50042490001582e01d5000c1c80740e00301c401c1c03200c88141000410703404442441d2102c66031051140040c079809130541d103c9112603000c50004510390 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 798136582 1250 798135332 798135343
    0xa0b04060f0c1e0c0e090d0306150e0d0201090509070906030507050c2a060f04030605072d170901050a1a0609010809030403050d0c0c06090501050a0818010e0f0705180c0a02 76
    0x20900301701550383d0402c16582501c903a040b41e01c03c030109140c41000560489401008400c0c01e6254071841c80d15100c1c1004c1c88483c0b80441c03412410444201c9020941d41d40340003c041c05142c450b600c182c2041d003404c80140407114068000c170140507080c0003105d241c6000190f031800b0b00c0c0c1d011140140091500352180700b07180300c2541181c1d03c0781e008107150b1010810000a403080f0790255000780015190300300103840c2900c4c5003491004401c4501090a03c4448241204501419a10740402c018034980391000989500703403550000c82c1d46a2040c400e05814600415000c41820b041e0300d42c180710340000080b054414410b03a141801408000a00381c000c050003954029500501940c80349420041c00400c0707014130304030132148100c0c3d201001c00e186103ea0b8804040e41c4040c2c4601c0c0c6072450061041e0313032108000b000903007101e0544840400a21081c0604609002d0301402000308140e8016107909124058000724082d035001880c005009542c0040543c202e00540312403959240c0c113250803802c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 798137832 1250 798136582 798136589
    0x7170a0f03030e1f0b040f06082a0a091d0639040905100b0304030e040f18051c031406040e0a0c031506050306071710050a0b04060f0c1e0c 61
    0x6413281d040a0303805000c5a000f00b0305005080f10300300048425062054102c1b1074078000e104841d070020080c000110381d0060303030b002459208102c5c3c500d031914560002d517403407030103400c011001912800141900441440b101c000700d000b4902903c030610b05071a00504d070003900710200070788040b52006451041142501c24640f01c1c01d101e038a07641d41c2c0e02c40c1101030190006558a11400c00ca18500047c410866001d5900a40c0d05549502d1a1103a000400010340001000010031503921500c0b0944000c0e401c4044950500c9840a841b00f4042c0c1204800000500070105040c10f041c100c3c20800480c0721000c241c1c1c040811140098040032140c0e81078640003644100030041c0b14905408000d2040310002e0003101d80b4144024000d55440e0024961907100c00c1d00c00201213007164540c0480011011246640883c20398001403150355141d00242c1c01600c20ba01000803460300180c00c0c0046e59022280c039091024a080220b0311030100d6036901707110700030813450b02d81010700c049400c0b0404c003200c80d40304000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 798139082 1250 798137832 798137863
    0x1302010e13150806060618130f0f0605040b0307050d0b0c0705100204080705060f1611031207060b151b16060f030e1605041e0203040507170a0f03030e 66
    0xb202d89032440e9100150203000740440c1c0c0c440d003c001a5580744c0b40f02102c1054040091481d80103c0d0300041c000c400400a01802d070080e16a04804030090240c45904000710a241010450740e281009000842e12900c1c5524081e4001000500c400d459503903540390b00d00d5000003003070324966581000300d4140c017484000400c14010700d1410040d450017031f00904103480300341c0242e0b00400e50303510420030b243c40740210302d82c82510306119101360080a01003169403903008a1808014445802c000380c103000625805441001000c140e0030140000c0d882101e0b1418001d44a504681d0003440014206002d50540c6c0c0d04e48420342d5502618081d4140420f20524043d0303480030401949070f0070054020080c04100320002172400306400d80c050400240348400401480b0010104c030b0510040c000038044903a418140070102007407d4240030102d01c01180306500680c058030840e401d040090080d102c55495051440e402030b0440400b207101c100610b2600c82d81800c00080c0802c4250042e42005142000e1049 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 798140332 1250 798139082 798139091
    0x40501050f0d1e0c1d010608150109050a0b071e020105091201020408011401081b0f0409060b0334081b19081c2307020d06111905031302010e13 63
    0x40200c4c511550064544680141e04010031178605940e44032000d108040011f200b200110b07181d00740d8013015104100b01890110140f684600108a9140055220500c01e02001808100340000d044070102081d40c000940701e04440b0780e400090043c02620b440380e22400402c240c007400036001b5411a4010300000c8000c1c024000318010f01044070700c0c00d10601c0307114080c04450301d81180c040d50700e680c0c001c2401040300d01340030109410700004000e50f11307044524603610030003201503903410030001c520501104110401844450382d010f0002c501c2c14400030700c010800c541401f002801049640201c101c4c42035521844004000080d907214044420f001560700808022508410106031030350080c8100c0940001c2542c08001291000110804560440d141000f1100340d80584401007064900040200000b1101b540342e0508480825601e0107e60b82d0000d0076114604031900c2030f074020591810140d06620f41a00b400401080c07102e0004d04118046001407050b039107110a041500d50014010030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 798141582 1250 798140332 798140393
    0x901050a2102030429010b1b0304080304051f120207020f0405090f1606082d130c1208070204050c16060204031109011a0307140a05031005040501050f0d 67
    0x1002507205440990310788070480040e05d00b40f14641280c1d50074031960300c4151030a078039040c154000f541250103110003601ca040c42864140750300b00f020304090040da01c00386a44511300400c00c0041044c41b440ca00a001c50645d03904440743c2c0000b0300700854441c2d100701613500e8210344000390103041d01190090b4042e2a00c0240400381900040318aa0852118100c0317814001c00c600486c81c0400c148075900004100000203150003a58941401c81e00720250074078411080d1180c0641c0c58140d08a603103d5100c00c2070040003083c03219074403040004001040d6505801095070f114030003c0d21401c0d0b4064044e648602c04612448211030840d04020f640c8480c00070141c296251010280d807140c03000391209140340780078464528010300c00c00c1c101d131a032025040d00b8009503802c410503030304020151800d00c602000c0d40c9510f071042500800090a0b244d54040d5249132541c652407201200e50002da004070326100052003241c4401c40c10418050003207601e40c6104201e89040f0050114a040641e01c8161508103007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 798142832 1250 798141582 798141647
    0x17030403170919050a03060b06040906031202070e0712180209011d06060327010b03030403031205072a081621030c020c01030902030c0a030b0709050103110901050a 72
    0x10680078400700c918004941e0200060003c00344107000781d5512541c484001c000144140d40300c11007405d00540105d0505035102418412958194420781c0c8442030144540304090f0306110510141101003800210360500303680c000d00d140031060706a20b1941e600e80d010f8800e840d140c2810102c00c4d500a200c03800303560b140c07152240314070f03401110f40c1e81e404008400316045240802c180c0e44152200d4401342040e55515281036251a5141010310065603070751111425520705000500103580640c550507940e5481880300002c54500410f210200510440f1160074503924507070030f2071844072030107410410700c0141c1051162482690721802d200c01c00d2041801c200801410310303000501c0d10307160078641e0862506080e02500c0c124201100140c001e60300a003000d40c000e5200c030349114005011605807000d9079000c50760b0240c458005590303618410f810480410380c000400c030082c1c1020301e42071090b038084e0109220350340105810141445008070300c40410500c1441d180d03041424080d00d421365484900340c1c0d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 798144082 1250 798142832 798142837
    0x10b0a020a14030d2d05060d060f1b0219140309041d0105070203070c0909060207050f0606030f03090a0b0d0902030a1103060c0c0a030e041d06100501020114011703040317 75
    0x304c0300c00e05200000203513001a5004a19600b007201d0200c0c20300031840c00348002400010f1102d42d202d8400c200c0360380420b4152041181114126400040d600b05914915009141c544110400c540c0000200019a0903000555803804d501c00b130000722141400d203145086000b40140d49401c03501e0300b11604010100320604903160001c640c02044940c0b030756001245c880c030480d800a400d0b0300442d00c04001ca50850343c00a01c1c4680103c0c401420326401d85c0e0740b9401c0900390500e900c2940c0c0b205043c0200ca150901420300008540c50040d417802414001242400c00310b4844c88141820106850340f81c40d41c41d0f0040d205282c0d004080d100041003900c2e14140b00b0b1584002280644100740014201400d05030840d2012204000209110221075800322402c00c10307440308541150301ca00581c03081e295076041040f80e11105038007070105860b1480f0f142c07240d80740030b520242c11a0304100d51030448014810034070f41501c2c2010756003c10640700300c207018617504c83e0358002041b500c00d55458000c1184d12001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 798145332 1250 798144082 798144097
    0x14031509041e0803190c0903030e0a0b04060c02030c040e0c010309061d25261608010608060c0f09101707171320010e040606030b19030b010b0a020a1403 67
    0x1645183d8038071741d030f0210200c070621003000c400704809020510200380105d020078500d241c000d210510300f54481c8035003e0346070880d5105001240c1405029011440c003405001030314a420789040041c041002d200941d11400b00c16018103240c0c0d559401420b201d503c0d0000700000c10b4600b49000c0800c41c0c041455521034458401a070018680d407070b00f1284018901880040340d0390f010025400b8034081c2220115800303c01040c0000340708400240d0607640d100c062410080c030039400001a800d02e0030280358180100148900030000c2c040080313441110b44402590070b000c60a03600c11110549054007070342c0000040c1c40da01d00c0c240d810020000701590000f003417038016100503014030442d11000c0b01480e12040c4400c0007800044d14035031202c802d0b0303d000c00d06420100145044501d100445002c01d0440e40fa41c0c0115000985902c01c0029905000d0740c0e940801c0303401c0b10809007580c03668079070210340310041c010613030070040009603031152034805c00400c80c0d0a0b400401c41144401c40c408515500d42c811017 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 798146582 1250 798145332 798145351
    0x61508040203100504051e0f1e12091e012a02040c08040c0e0a020f0d141e01030f1106190f0201091109060a120602070314031509041e0803 61
    0xf48541002030040602641d803000c003c01d07425042c82c01000604240784640c4100b841280c800c0c404064007080810744880c00700719601c2948030f5a002540c10420700c040403c6604100700152042c58852070b0003603070511244c1e0180c3c1400b460b11001292800c140040c03104032444041c4940f0101150340e558100024402c940421040c00600720690780c1c501d0884010300101c031000000c01c20150f00c100000d5001d032a03030707000610700619026031a80542104504401885e07645040e1500707001c908402c5c54001c4107203940c8010080707652a0082107010305001c024140c0d00400e01e0b070810024180c92901520300c00518142c0c1b503020304007010b030450110720071140010301003c200c1942d06006200b001d241d00d801251102c860000d2000f40950319170042c0425410a003c500300081c070200919113425154810303503025030f441c803036402c1c010490b0540c03585114a200d02007081c00f060b003200064510100c50140c90041050380d680c10000b5150305041c104107906c80c1140b000e81c2c2008080380040d8441c60154 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 798147832 1250 798146582 798146593
    0xd09080a0e1c0206090d03110d020601170f0d050a03020d0e0a020a09020322110603090d02120f04030f06060824090303100b0c0a080a0f020d030c120b04061508040203 73
    0x21105403a810b204400c01130340140080118540320305054819103519402401c140caa0420030344003540c540740c01512506c0040e0440c01c01413180e54101d2120310800310000004103204880300c4262515200c0440f019401d0040010301d80c280180641c06964001c52440300c00c00c08082c40c0308955403038803113400040703102d9643d15030003062251140c42902d00800d0250703000128001c180f04070b42c0030440312050170b80c2c0040450413000142c1e03a9600080d132180e90b002010308480c6d0554000649420320500b98400c4160003400b002d00f2075081c8070269400c0f649c0106175030700d040700542001c10083c0303d25003015010380503c682140003030145420703500110904078100946641d030050601d0b168042658000700c2c0c800c040401300701c00c0101d500501709840749401581c4802401359180d2000b50301105000004c14001c4421401444d01032281d0714124444d82424030083c400c42400420010785800400c0c035141c0c0d03426248440b61140d03400b90700907040010002c111012800005045080212000c81c0300384640e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 798149082 1250 798147832 798147859
    0xb040e07060917030910090e1003150203071b03030c020c15040509070203270f010c11011101020706050916081212061807080f0702030a140d09080a0e 66
    0x18844085600c2665002d9845080a02e9200f0804614000400030720051040c050255191040740c0460496500da0004007494154410314400380105040c040c540c0309141000441d80504500c0d10704558802d0040e909e555010050303038500b81040c814054003580800243c10507401d03610a0160350a150200c8140050407001c001c10362880100354100018240403c105a0238074212080c1c200019005807805c0030700445d43c1a44e25458003500340000c0742c40c0602e0805c0c2c0c0c14400031030030742d081c420b20380414030780d0264607003080000341e0a26207410824200348a200e545001e40c1618160b9074400f805101c107007000b8400344e03030360709203040c2e881d0548116402c002981c0c4c0001440040c0640a11724460402002020052000708000c0030380e504079110044035400f015021903e40c0c481c04040e11030400e40d051688100000303d400401c4202075520810200410300e8004481d2198440003072032141e944e01108803000c2c0500b4000740001c0c40c05501046c0c43c03400d0354100c05000c00070300c030030f44408140008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 798150332 1250 798149082 798149111
    0x10c210e040204051e03120d050103120f02060402010e060d140a0c030606020d12061208070b0702030903070b22060c11100f111c031e0c09050d050c0907030b04 70
    0x103144038071075005c21405074141c24604040d0001710382807001400d03107070501d10480001d0380d180c1c01f0203114107010365108010310801110703152254500415190080c00342801c224040d40e1120301510180c1804000100048143d41d4001100c1c07241410780c03418000020042c040d51030b2014252002c09210381001d8401d03600901c03900c80c0004a13070b2254010810b081800304280c5143e1444444c0100441e142c900210300c40751000840307210b0a00c200300e21030340c2d20301034240120355001c041c1a00003150010031107442695030001d924000e4810041e11a42d440344c0d4100c0242408200002c0c81c04640c880b5200042d59a03040b00c9020355240c06020f100300b1564200b810001843c1c0d9400244c0007103200d00401c2c81840d07200d40e11010204a200084900007055480303450429480b4800281c0081d0310f61031010654001a1141036060030031090038000006032600290200a035802203600508003e180d420a10078204a100701d40030020f0700c141c50600b03012600070301034020400081c1c05a03061503485c01e031659 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 798151582 1250 798150332 798150337
    0x22090b01050d03021c050d0929010f05120f060f0601080f010b0a0507050109050105090d03150305030405040e0304030c061e08090601090b040906020d0203010e0906010b0304060902010c210e0402 85
    0x183d1660117802c07010000300e8040d041c41d01c0b1a0b04802081401d04c0280c1034440c103407113460b5516025108220705403584d13000444044085210580304407a92100401c182c01000240c04240e84e02102c0142c0f440045500c027514160400842e00c040b4482c65040c0400a10009150b07401481c007030740d44c01c0c1250386100d50030b45103020a124280d0240000c01c64040c2c1c02c0d100c0c0340034007a0648141c001150100868a40da803d40f0300544c0e104000d500600c00c1c0c64441034042c441d82c12030304400c0d19400a110301c0e58a03440d840c2c2c000c910506020340d07120a45c00c942c0d8071040c0111009590300108202d405601c40000802000404184030784540d40c26075618070060007001c0c8584580342c101e0060603a03a080070500000340c40b0382c042c8107800549800007140010028000f400301c14088010060b1650314004030700341035040140104081790170040061101c2102034044940c4075130400f1022a2140b820303c0121003d80c2542400b41426100d0b040000c803413600843c5107203610a10766255201c2941d0041084102c3c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 798152832 1250 798151582 798151609
    0xd0c060f05160f0309180c020606030a0f06150e0702030408062410020102040f0b21100e100f030f06050601111e0c12071e2322090b0105 60
    0x10388004002c41e00003600100c1c19030666100349000c9130304503519804442c500d003e031000012040e85841c00c1c040e00300d5041000030781c020b2046004160b0f0031802d031118500c0c41e049241c05420140c96541a21221819031500801040720070001c2c0268500310000a4032500705008416440c040c1c1d502140410725080b40d800300d640344451180460190007000c2041c01c8040c28081d00565400380400940780441c1589c000040004d9075005a550000c2c44480364070a810400340028451a0028000c0324802140860300f901c00c1c40341003482c0c5446500b0b1060a00440f50f2020014000c01c020110070000207041c15411584142c0c828011a11004019201c69032241949011382c0d01c580040c8281c0076644048200318803540e01a034040c1071000e8049596045a07051211280c3e005d51000c002d2140141c0412150204501030402c40c80d003401c24941404000c5480704008002c41007416005548032200001c0101c402d501b038001403003004554102610310314405403407108440000003440d00705883c40e039820 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 798154082 1250 798152832 798152857
    0xf0c0206040b030a090602041403100c02030a08090703020a090926090f060405030106030b0403020f0115090c171807050a0e070804050f1006140402360d0c060f05 71
    0x5103410700410b640d490304004c00e5403501544131403900005c0750b0b80d031004102401b000340c000702034841007009040c074102c1b40c0140d43d52550702d40580b0300442540401500c43c1d100031890040a00d48031a03010320b10300aa43d4001030361042c1078403000101410560302c85681e6078803c034000f000d001c40d294801d12100c20300341c0a01007115030402036602a03140c0a078610304004801840d80d400c0680780c5011030300f1a00030b90011203c1c4800780d010700090540400030724402039031031802880f40e200da00b0807210660911340300d41800f442c1c0341c107a28448140a44244011200500e0404401e03181610884440104003540310b80e045c040c030705000c180c9040181d04181501c1545d2411186511108000c80342c45500038401d44c0e0714000c0000b01d21403810148410401140300f42008201d00341004030200c1c5000074800428400c3e84104070b0401102000600c40503161160100780c1900401c80403d00008004d901c2d24982c05064506114108a42485907905031501642c1c1c098040d060044140c5103446207940b02d021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 798155332 1250 798154082 798154087
    0x201051c02030a1d0d05030612011e141003080a2c0a060c020f0d2316060f1b0501020d1104150219060c30050f06010f030e0309031c0f0c0206 62
    0xe84c5006d00c2c02950440801b5020710040031115a40134211100403074100041c800514a03005403500300d000d400d034013510815066078613080c102a00c400c0c0f40e4152000901c4220003240b40c0d006540983c0d1581c1c00c00300403000e48400e24051044154840c8603000c051032040043c41804130708036202e003841e00da2032640540040d400c0300c40001000401e100108080310511204030300e2124402c144807482d00311b11380ca400200240c0700c601825545022141d0825820407040d00e40000400c1e501500003088801142a0044040c440e8288070b03029104413007840210a080440300e100d03243c01c2ca0014401c4500500d9140c1000040001c102d88852011001001d00c84518160101140720303548074030310541841c140800091014880880015645036034810b4843c0811182d2140e0b5810303016490f40501407400b1001c062812900180541c2c100088400400d6509d02400794040409c03c102d98403603400a0407148078a034003605512070030218000200005400a4210958900031010385540c42e500405090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 798156582 1250 798155332 798155353
    0x60507140a030e2b0503270d08240607030903061a040e0114041713031a090a2406170105040311070305070605030c090406301a040201051c02030a1d 65
    0xb2030b5904003902e07104400100c860080c3c7c5c1c45003040c03541511444107401a266800f81404c014003540c00080c0f902081c02104c40715442c600454044214003a1012a1701030344078480343c01d0844cc0c0c88000c0d04010b042502d0110716684103011a0030001d19040c088505000075040b00e0744450a03110701460750001c0404d80f20108000440a40d01c8484c5041e00d0301e241d5080201c0b620a01510005980c02626015280c50403041d52286100b2081d600c804003600501d00161a03958461114800c59840302420041c80c01045c0001e80503001318006007080e9218a034600d089800403402410261011004500b10200000301c840d00407a200c02240d030850003920341c8a01d411810380b4580e1004181409401e000c0040703002c2d80c0e9407072103004060700089804442000004500108140c5560385079a102d191810616000480da640c038411071421102c4001c0d100d403210310041c4ea003400703000242e01103000c000741080c010201d1039000e14410890641c00744040102c01d808078010442854110b1000d0f00041c1004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 798157832 1250 798156582 798156587
    0x110702042c0a0b010e0603240610020c0a06050c03070c090b1f08040305030a020418091205090904081b030f1e0c1b0f03070305010504020a0b1303060507140a030e2b 72
    0x141c0c00b10000d400c2e180b04485200c01c1d43d05441c91409240d161408000034403006040642c2c192b0012841c03800100420000c0800191801480e0303c900c0702045000282d10354400410300560382580e901803020320308540ca403001d0402400c0d00741903050080604001002800f020342a140c0540241a200d00c400c40e221500c0031a600c0e44010f1000c54410b40811000580b401c4c000319103c0b4800d041000002c14490320303c1d110f00c0307e9007224004420230209201d0030781150781d01c0c220f141d002a0300614080d43c94801c0f0300da8060125014002d0605401701160f4140401800b038004c0100040a900d901035414003500b00d15240d0213545c0890b00c0c0f07540a80300c9490800031403055810700c0c0c10002c19070300c00c40a01500091809150750030854150751503000340411410502c002502038a0414541401c21188649004481c05244005040c1e1500c0f10086010706005500d200c1c950401c42c000c140e03448494041c0500900742c101d00c080b00c03e00c00c1e90345e00041030480601d294015100004005001404d40004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 798159082 1250 798157832 798157859
    0x7050a26030403030e012d11030106140d090210080a0b040203010303121a03161403030a0f05071106160203060a050603030a0c0302070b0d061a0a0210110702042c0a0b01 74
    0x461821b036580d010030787e186d000c0d8500c00c01c6091400c3d100c25421020a980c136a801e6030501c8188420b0040248014040d198200940340744a01800b0740641e11a422581100060036074030380301035044158100c404070400c0d0301104042c420103040c034081c8445c4400c0310902c0100d100900c000340c00202800c42a44800e54150040c2e0071003402e150000c1d40c0e8102c1c00e0300103420201d102d00783d0760b0040c081100801100c00c07041610303000715130101c000d541807480c1813001820304609441d010702007000003d1403000f004420301c4520040030011b4806901c030030b000420301c0b00828144806a100344120300000e034000d002405800e109510180c00707541051014002540c0031840b4000840a5015071100070030b260007850081d220f480301d0407001041c41441c295015403110030008510aa65008102050205070001001440040ca01078001070056520685011a0107001d00095020b03042000d9081d82d00c000c1c81103c0d40410303404000903141803046e44941d43c0e51210040c001c05038542c2c2e500400409214606 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 798160332 1250 798159082 798159101
    0x7030203120306030c0a080348030c01090c03110301090c0509070e090f070f050a02030a18030f03030509061005090109020a031416023a02010e010207050a2603040303 73
    0x441700e01007424800135205e038543e504248019880814201a10320b810074003601c020070017031401247c0b07501410810320f00d8145907216011400c1180c42c40c065a00c3d0400848170b100c003001d0000c002502e02464008400c910500c0203982d4056a454825207914040c802c8a000d507620100c0107102ea417801e0b062141301200140322500b40140d400070b400341703901c8183e003851040d9404030311f0460901d8080400b40c5188444291001001002e020702040c6070740000c2111454081d0382803006031030075281000c0207010760701d40004043c4103078000b54408141e01600310700c0c0034072405c1044d0381031a0340e00a82c5040d81d210510034a6401102034004010f00f804542c01030000d02858600484d40e81c500300800c050691054031100d03449808940d1b20003459038103100c203901c00c0c08031500400c8107414200c9000d58000520200543e0b015030b418800306200c1c003d40c446014044e03941c00070b5403101c051f8100161212a14002500c4080c80d402c0c480014040210b003088200d030010750f1050a5845980f4114000c050240 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 798161582 1250 798160332 798160339
    0x40b040c1d060d06020c072d030803040b0907050d03020114010905060a050d0512040b070302010501060315150c050715030e011401030305130f090204140d020307062609071707030203120306 83
    0x110104a2203414803150000d0100d030230001c500361815001c0302000100c1d50150740d138010300911062001a030641c041300d801031742201e00381c7c41135125503411a003000e09580c0000c0e440340146090400f090f0701908030010241100900507100e81e82c0303107030340429600111080c4d54052456101440a854198500103459010703008607401a0502d020241541d8000d4001d4a0002d01c01b003030039400c041c3e090040703a01400e010b150504c02e6202120100711040000d0180c41300c10407400301046d0034680f06025103a405508202195030701e50740c4030320810303809041e901c03240c00090a00030081c3c3e00100501452200c00110a0343c1c411980c03030f6880880d483c2d006840b05102e07020402c4000207187c0c807600149405020020380042e80d46d450860110303402ca8540d40428004e00504150b5005644e020481d64100c810300d0510883c28036880460001c0783e204000f29a03d180f000c1c01c107100101c100050f0303043c2546e28140030242000001c065645c4e442d00b980c4802549a8000f01d02c09500301c6041000d941c21000c0074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 798162832 1250 798161582 798161587
    0xa15050d1106040305151501080a0207020409150b1c0f030e133b1b0111060f09070e0408041208070f03080f3105070e040b040c1d060d0602 61
    0x10700062115441a4002d40742d65000c00800307503182518001050304101c1d05507107203144051383c03030000e000120001c0003224801d40c040fa0100c15926150042e00f4015072180b05a070301c40049642101c000d009014071070307016179203000c80d01060555034103480c001c458000314902c00c40b11103035404992410703031182090b07081890900c1d401c070103619078040d4034461552170013603840e55503004a0302200034904003c17254410111800c44d00c0b1364007001c15851681010440220105286a00142c418a40c420b100008903c10f0303038100f018400403a000c1c24007540041c0700b95006280d55441e5280380900c01d440150034154100300c1044000060421812658401d40489050201c0d6445440c01171503580c90540c08581c1c003100f0002902001300410340e1220450a8100181403032450200c4800c20803a070601700d611007910150140310081121400408841d07005541a103490710384210b100d41c082e6400c0f112000c458402003083ca0540f206003030054580c065030714060fa154420400c07400705480b01039030240e0b800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 798164082 1250 798162832 798162863
    0x131a0408030f07030e0d0b0405010c0503190f180c0503010e03030402060412050c0402070317060109060504091e18060b03010216020f2101091e03080c0c0102040f031a0a15050d 77
    0x443c1b51305c8034101e02031040180d41d4038060038860700b0f44214440c000c08211040041158560000781c1c3c15400003d020000030b109045004000001c0840303513058aa803c0e06a01050b080024261100c000d9880a40007030003006042089190f03240030607100254460028082401070701d4141c0420032210b40140d08039107d14031901c01140486e48084401d90018111300320400e40ba15854156540004007840e080c2051854103c0051150180b4003072488415296400082e0710f1000e44900c051070140d200f010008208411103944801d40b4020045a90340d040c6035103001145030601c26940241c03104902d00080d407030250f00300040c0d0000c5581c081d901c101d0803003894240032802804690141142000010541a542841503018100084a41c42440c84000705000264003510143d0070014900106850b03031a8406024003901594004c104000ca04100c000107121040b002103e00581c810078002403038480f0018241601c980130304402c1d8408008108000e5414a0049030140c94003448906904060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 798165332 1250 798164082 798164089
    0x909050c220e1e06010e09011806090213061209020319050312070207170a11210a0f02130510030b0a090219060306170c0123131a0408030f07030e 64
    0x40980b80190040348030241c2103c100403e40d01250804400d00700180702e9503c64001840815050240300002480d1125480010710340b80c003d078000c1c0c010700714290749038001c4503030b80540c403041d9105600c0050019074070090304520364401c18071030540180182c07201141c03203041300c03208159400c0110b6051004025170b0080c800c1c4008030600032402580900a4203140103048141c1c50711001d1016080e070810340a960008909a0401d00c0f0b59405841c8410000300c0081c4008650588000811560180342413400412a2010700141111300c2150710311803100d50350100c04c0888504483e541200b5000c05001c0c0049500300381400c2d8450840344c00403400d119207501140001218184412000030b26000601c00a80c250140d9800b0345419040d0110100300e040d492680d40d4040032649050000c3c10310038054034008038095800c0000944083ca584a040c0040d2607003241841c4910410b51856a201c06403181081d030486040701c0000300110700b000071310060150741d98060355040f01809a60b0403a280d03640c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 798166582 1250 798165332 798165359
    0x1050a0c0f060c08061017040309030b0c120c18041505041d060c0307080106051c0e0309040f020c12180307300b0a1e1b0909050c22 58
    0x61096101240384206104081e05601010300b08610402002c002c0703070031b07082d44900342e981000307005600b80b20765851340d0a00f5156046141c1010f030410405d5820802450343d100018108004140c3d2440d0317580e03a4544104c051030007592800d1182e1581800c28880501e40380e04081f03541900c08004001d05d950350b000040881c8e02e901003aa4074010020220030f00365005001865101140c055524950b1600900041038010140a404144500410410f42402d00c5ca88941071203144a5001c216a02d0305510071541c0c1c1c1c10980405100d04d003090140070106c0c0c0c807802030f04c00300c41d106c1c80140710507007c0540e500900e81040307601c41b540303500c044210b004ca50340c1002510020540000205034000c02041e80541800c56200303100a5890b039406800e002605c0031481c1c83d8408914000011030740041e03d000c100d601510440f1062445c00c140f2003990358002c000071000c010025840b1034078820382d61030f0b901081c0d400440780340b03410010500c04070600941d01c1b1086110740411020903c80175444604d0700d41d045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 798167832 1250 798166582 798166613
    0x909020d090204050c09031f0e06130b06010c1509060e030723010614060901020c030111030610140d0b010c05062517180c060d0e012901050a0c 63
    0x2a0785400300320040d030809200d25a04180c0c00d5042902e000d8111010031395800d00d071310690311545008007124242045a62101e401041d0600548840d824028204404810003000549240143d40041380c0d1641c064040c0001c4264401c00e1015036043c0050460001c0807000001c0d00e49685a904004000c031042c001042000e21620003907540c4100d00b02e2880c0601003c0242c290b0a070f1418400f400010001c041041250108881080d030f55661480100e0402100030b8078284c1541c2040500282c60b8003e80181d440f4400035510700c5c160b0940f882d000c40c0c40c0d407096980f4284083c0d081050300d80000098100381d03c60201070404c0d060b807051558032036150913001c4441c0801070003c2c0c840c10380b4132130070110980103b00b044d180040340c60030f255034000007064015250070b130010016040c0b110700c01c1c024040c1a054150040019484240c00070b03841d40503085c0019203082d00e500e80b1040e01c1000c0900802c1d00d84191800b007200000300c80e00360040d982d070341c05421400188200aa00c000010b04514180e0343c3c00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 798169082 1250 798167832 798167857
    0xc090c070f1506050303040e1317070b070e0f1c06020c0f030a090e010305060708060a320103050405030d02031f060f0207050a06051c0207021c2a0303030c090902 71
    0xb4400440e030504031142030704014800d0b0001c0100f0080018a14a0160040211646034140b02c0e11841d00204900201c5c3d80c1d17506194003c1100e0003400102c6072424030591340b6885000280003681c0c2002018040f018106c0d034040a01006002009007444010407060301c41c5400514040c0456501c6150401c8040400c0b034650001848041c05c6600424050003000080440202541541e4505844850013042401005036102c00241d00780d4807403007010020100d06c040780c00c001c1554400c42000c68029000c8003078007007a5603d03011042d44a071140d1841207811001445c2050046030504000c0d6001521400c004000c1802e0b1540ea070310a00c030783ca0002c1c02152118a00d03510001d0001c1d04005055000c10b105482c027220401c409500711007213460107440500c05180c6451190002e1001340620f00f00650040100c01e2003610503001103000b0303041c0da4001e410030444001e600c03040b20001c02d1000f4141c510030418803030410000303000750000080e0078814105221110380f00c004a40484c0c10003426940e2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 798170332 1250 798169082 798169103
    0xc15020a020d080646082406060a031b0e0a1502030f0304030314010611011b090b0f0c01060924032003150f07120b0a0b070f1506030309050306090c090c070f 69
    0x108041080b41040c4009204411000161f20031420461a400141102c0c060100091035046d894402d6100b407070110304401240210001c2c00e9070061031880d01694850046803c551b010a140201481c120314482c284d600071881c100d4540510308003600040d204070149034880c4440302500700c103000d04a000c6c2c40b0b940d88084201400c503c4260948590707942d0700109020f4520507030a403e40c003501e000107070b417148802c1d00e40d1182901c200c1c0c011885100e18496183d407038150003151400e16038111071140d155803011540300d0440041c000c00341d6000c80c4001054510410b20f10070b2100c0c0d00410349000c818008041c0e5450b820741942c001841078040f1a9840c0c14003605c400c128445412421014229440c40c204000c000005400325001c0404c0e80183c0509002c0821980100004021003002c3c0da84c1c418640960081c8840d0420003a00850000b100401d000060104490800061451160001c00010f0102000303030703010702150000103000d003008048100050008620104051103180303115461060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 798171582 1250 798170332 798170339
    0xe161704050a1a1b0c0307060219020106150906180b0a080402030118021309060230060f090a0903020304050402070b010f050118150c15020a020d080646 67
    0xe0b10318040403144120070b40f4007070034410072042e071001000360b4091045180780c0d40c3e0500c1c104141755000340c06000303001d43e00000c1d130400d1103959410456102c0e90150000d0090303d44a40b15000b505485583d0364000403600308040102900c5040c9032000d024003000200f50454a0fa401c3d030340c22f40d02ca001c2c20340c0880e520b00f040c071086003000d12030444038076144c0d480c041e080c0e07859a0002d00700d41c000b541501c102d582c440a51005028107a4125070780082d002e00281480d6001c106007902e4400d40312005900c5200003400503041c2d040c410300060064200601803c090358442044070014484420190700314401400040340302d0729184014400c2e6401141d80080303541c5802d14114040c1c915402040c10010414115811101c054003140c0648100700500c0000a0421100311400307100742da07000d80140b00d01402d20701d41d81c8096000b0910070b03081e45c0c02d4808007100350005032140c0c50250745064200c07042605c0c1c42009111075100c010205070024045551b000385141038031484020641400505000c0e80042 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 798172832 1250 798171582 798171593
    0x24060a021b120c010503041416030c0801181b1e030c090c0c3008070f0306081b03010605041a130504020607110d060515010e06040e161704050a 63
    0x1816aa0703011500e80304441d2811840c103803038502c0781d11070314140031011011804000e070104c11100c90110540803226600304035130380036441044510041e01c9002110b00b0108100310103005185c090b0050720703c44000080c07596101d51028400642c80000310070b60345c40228141c0f08000c102c0c080300400d0f03000600b0860450074442002d602c103038800070900e850301da00764082d00d0300700c3e000e083e62507003081c10b1282c1e8426000c008403165050381e0200d9079000300c1c1440040b40303a810440c6c2d903000e08904c0d982d01850780f03086942901214081c1c060400070394001d29502c0340201041c1002c520b949805800070a10707070344d1080841c0c180c51403908001d40b07981d000680c102950819582c00f0040700e20000090041e42003a40114044d8803940070702510008042404402c0d607282c10114103110390f8080b41c100180c0c5043c0e4016841a44046c401d180066004402c2e161980b40c884c0560b403d498250201701a03a40300d80406481ea00d607044502070611411080094000c880c41d0b6a091007180100060040d9103030750302d1301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 798174082 1250 798172832 798172873
    0x60305120a1e021e191b030605091e0a0209040204020a050c0709020a020c0d200a05030a0501272001110d110d030501080303190e01020d0e0f0303070824060a02 70
    0x2034061581c0319425250440d4170038000c0365511500007104100302210380d03840307010100481d0406000d0034209828061017520009100c034031198404445a50708942846032074440800010295002041c000401d000d803909038010b000300003560800a00d40101e0b100d83c3d5003401e0190b0300c03007801c140d4042400f121217601841200603604c011035440344a0b0890740e651010144000094000383c074841e0020031b0703603501c030080c100010313040080440d0f003501011302e8044c0c040c0296038020040c251410880390300c40005480607405040d400080e1a6000f80d2421113100b1580240141c6410000c7c22140200c002405000079041c4049655a404a0750b8048400d1498206102070840400d4601001003042480100c180c075008403642c5104500300c02c8140c0700700050100c4000300ea40c1544005075228000b26150301441402e84900150f85c441c0c0700c001800c9840e400100c583e0004213000c000095200301c0602c10509150301c04070526485503503114003184440d044050940c000d40d11522190f450b051181d440d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 798175332 1250 798174082 798174133
    0x10f06030f1709100c110d0b09010605012a02041404080301080118080706020c0c0604090e012304022716020c03120d090f1a0613060305120a1e02 64
    0x28101e18224200c4042803500c413640d0042010040940e000d6420041010b03110405940020a0b283d00800607080200c0c9134a000d40e4030382d14540c40c29034000781d01d500482c41e107066083d001070142001a001d08410500c4c1c108580f040342d10550b180e0104910003210000c4900550090243d9a1650b04208030142110481038291480c061452503540010308040c08031120264400c102585131014040c2c0d291a020f0204003042d80000007143c0440c80c038406902042c0114216002489024002101140140c840303030001c00e29081544e00003805814210a0080321072000e881141c440204040d55900322181070304c0744041c1702c004188610321030f54104406c101c0050102c0c080c1001212114540c02144100a070400d000b6803a887c01900b4040000a840e0b4020b800c62400c880129a1a000c40d8050300e00f110081e1040e08101c1c20300602d0000c52041e001920380c84401000002c00d40294400d582e08110b54400c100400240310501c1034a00c440460943c5181c1d170000c0014050b01d191050003c0304060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 798176582 1250 798175332 798175373
    0x21306020111030c1b0d02010c02010c090e06090408040306021305040c1b0b130501020d0f2a03021c1401080c030d090504090f02060c0a060b0a03050a0b0603010f06030f 74
    0x196042201000c0d90200c9070450514640e075030713445c0168100d25042c1601041070170014060a6015a003040c3c043d0000e0300806d459a0081114502054050342c09100c1402000c61010f00d50002510314103200e00c8a54000d401820800d00313055581d0f036418180e90041012103805040c1000412582c24580a20440210181800591140703010f0411844945941d0b000e17195082e614040f500350803075080c880c0c455a4001c0029542d4420390f00b100006064006508400c880c03502d903144c1d0003202e600c94224014410795104129407a042c1001710080d40007490902284041403501e010b01c0314142c40f80c10b480d440c0c01041c00603107600d40401715080c07900b5074009a0107600001c040600d042e51107100320341079600466000580504500704110100c2e03c441c4002d400060004050700217410000d00001c46610407101800b2000252090041c1c1005070310000b0704551041214000062500c400c81e40e01c020b02400005015440c200000251203c7e80e10039036607081c65026070340c00d0200c1c0c0c120708070380c0c9540306 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 798177832 1250 798176582 798176591
    0x904060b07050a020d020a08070b1e070c060302030402181608010618050909240f060d02130b220b09060609180c0c060c1b01050f130501110d0213060201 67
    0xc2d00d03200c0d01c0e040040e100910030359048881408664405040c1c002900d9103001b21410151211540d482c02e92011220034400b030b5180d4402d00d41441e2000490700d606030f2202481150518003001035000c0d4001500c05c036401007511400c00312154900e0344503032007180c41d8400f80c2a02c001d0464054100b200c10303040401080313802202031401140c3d03036404804a1b0310951384000d043e0380e17410025040142c003e900c280c1c1038045458004160859a00d024040c01c00744211005079142d2030100408512900c00c025001940000308100c0c6021545c03010314280f0000d00079a048039800300c451603410707408034801282d0b656103151041e21410711840e1160f004105071800b502d41544100010316141d150300098810301c0d0000c00040360180000240c54018072040101c541a04051409401c0c50700400000714554081c100f2001c155501405030074098106110ba10200d5190300c0c652401c0100e0b080000e42d10780d902d5444e6050a0300005004207060b4041d04401a1504a1080519489010395001801b160f041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 798179082 1250 798177832 798177847
    0x40c0e06010311041733071b0b06060c100e0706080f0103020d1716112722060504020405010f060e040f1407110f031204020f01050415050904060b 64
    0xd034044a0903240282c05e05405450809000f84c035142e02c0f03101c2d070b105070180c6d600b03041c4e8068140f01a15000f001c2c28401882d0603650003000711016850b0103807240c6242c4001f90601c0c0400d01c150720581e00700101401d150300e81140014510714050001c0103055905907503007055228044c0500104000d0070051411080350705207030030403e09544040c000603124005441c40d000c10810081380410f611003c0e010345a4070345010b00e945d001c455060045c2503c001e440c0c002d1980f00e81c68603030320fa04811800c3c07511007800f00c40480d107008402c4800520015001c4501d0075449540c401c55003c0105080c4a901e010600d8a000c3c81800142c0d01e040e4040b41017000290750134000c1d01d81001c0c401c81410300c2600c0c00610348410392aa10003801001d800c0e0880c04203144240080b140d1f011088020350550311048960107080804d01c01d90b00c2c820959070f0766030042020003003001403400d5107107841d001c2c40c145003843c02c0c69100c1407103404503c4590900c10201c2c4000cd0152500d00f040d001d1803000385031003600d26041030036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 798180332 1250 798179082 798179111
    0x10060306350c0a0b03071211030f0c09130e010f090201050d0510090501030308040b15030d0e0a09050c0403110303040e131a07030903021c0207030b1e040c0e060103 72
    0x70100346100d6445051502a4004000c000d407000903034000b085251421383d10840f070125030340b040d18282c2c005025a5403060a50103540140e484009036035a4003895a43c07a48050f4003a0003010304001034031002042135401650380c0d26001c04160b00c1200002500f62402104036007111101c141c02d0280905102c09400541e07085001e443c1188090702c4041510355070081c41201400054002c151100e00e040b00101c180b56110264612541c032a1007081c000ea03e41404404c000d080121116900d50b1204c42c00543c0e441c403414450b500008007610100426854030007400950b04100c0306080c074840042010418132100c5810f102d4001c4042c0c0c0034600d041d0410380440f0070703d40010b0060100c0140e48000c2c0003081741021403500703044035284041c021800d20600040160405103c00d400601c502030141402c0360300241d039028004920b400418100d481d5940300c8148900c01412f40142c851040107100401d1002c841d81c1d44101e00c504d003070280050802682d0303408200d011348110704140c54440e82403000702 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 798181582 1250 798180332 798180389
    0x506031c050a020f0106170c0406030b070e030c040501030f0318081203060f09010305100617060106030b01111209101e050c01021e0304020a2709020a0302060310060306 74
    0x20000d262a5940300c805610503032030030500040440d035561030f02000085080200b17071f0620143c0309842c02e8421803041c0d28108803c0c0d032864003000c0e2a0308108008207070303a240507040d00c0031001005019142e0702d0002e140028200c91b000d0740162a4400c5103029a41096486104440e408649465003080c032810148925a1140d455060900c444000008910280c0c1d40706910040264018610105907841e482d00d00d07100c00b50108401c90850030514003190148000f0f40c00c0040c074041c1c0c001060030360309e4080d044001d0010480c0940c140006885d8440c0d20010070b1081004420140c2c0c080c640e948103400a005035951b01803681c0d01000081c1c4606092500104080c40559502d80790940e2280d5802c60001c1c0207100303002000001c1c190750706040c3c00d02c1d041c4201540c030860088a0b0380c03620340c0d514150a000c1b1200031a043c0070103210060941c661456584c030403443c840c005020402c100f5100d501084144c0d00c1520129821101c45030304220199040c040c140250501d0009060950080b540c5c00c0c00b800d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 798182832 1250 798181582 798181633
    0x301290a08040b0c0d021b060c1e07020604050904120e0a0e040b070908030d050105031908030a0929060406080d020a0b15040c050705060c0a0e090a0b041d01050603 72
    0x2209030034040f44400003008107681807074000140c11544c7d41c0b1841c1c06489075103003030310349501c15000710400285034080040c1070740d1000c0c0400310040b115900903406003000d07501241080342d01800511020031940c0f00c0b200054031aa201300303c51014209842d002030002020840406c2c800c61500009000402004d07001076081a880030810f2020388984506851084098001c0d10349071001113010710010b0340d2608218100e031015406d0300d507290007000891390307074103a401c0001d400c80c0c0041001c90034003502584882c400782c0c060b840004c0c2140c10100c2d5041130b05c500c41c0c00450140b81010034018145098440c43c001030446600406080480940194442284010280007404440009406042c0c111060750140000500c10018510340b1403001c2c1541c1c2014038191800d100b40d1002030640c840090881d02d50f2020b68403840c032003084800400101180040ca0b02e5090b41e25640c49040e603441e640211645000800005070120f80801c003000d085400c0101a94425408031560701d03a0000c1c02d0290f01d144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 798184082 1250 798182832 798182843
    0x213050d030e04020307090509010f08070608070e0301052410021f0f060b03010602070e0f16050903011e0c03020306090c0a210501030c0b031501030b04110301290a0804 74
    0x540d03a6070030305807100c6a020507441c3e04030380000100921954002059010745204680c0781e44030342d0300c503001080a40124000c0c01501c0d40400303030910145006040303940d0300003010300d481d000c15221071010900b541d6082c0c5c2c8459100a06091002030401c141c480700101c01c1e01941c51208001d11490b0095440e103080c50548441c2910024480249150782c010318070003030364100e051044940c0c1d50035400b000d9000b40704a030014000c0c4a40482ca121600700e115010740c20500320440c442e1140034203c446c107220f4040034424040c0400c5511100e8400b800707051240d41030741c2c003504504080d40710303241e040d9240003001c0c0342014410010000e4030b0303450a0650340c0048244101c0ca455455020303041d10000100300c1200010844840c0041d8482e0403034010314140ca1251101f8102c50385d942c411200302c2e0200f55030140c88407041c0c0142a06a52180c0e2000c40c109a0040c00802c000b10311175428286c40d07000781c00508a030300000c0580303600440080c0c01180304c090418881860003100c4540145035941c0608000c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 798185332 1250 798184082 798184099
    0xb0a140901030e0105040b01080c09010f062d030b030c2b020303070b04110414060d0b09030f0c150114091f031a0f0108120d05131212050109021305 65
    0x1010791007940b100d10800e05500c000c10003814203040c05a40300800344140c4c1501c0c811030f00c0d480c20131308190312000c0c1255960071003000482e0915034151030044514110000c621106220506d00c0540808207254001440d10005510f424120030f150030014080c43e0071340244ad00401010800561400540075810404110000d56801d84000303811803045002c060490b40c000010b1000b4089040c4120540d0f0720111820000c021600050100617030046480583c80741c00312895001286803115125130003108071007528507154803050309440030b030080d9250100f01d43c04604469005a60484158090320b0130101c0381e501030030003100103202d4090052070132000703140700c0145c08500b00010341d9031400756030f1110306140b150010040070000b084007202c031408001107110001484150202d60400d00c9100101680d2800c0b10344042c200142c030001c0e01c8143e681030720088034000b06014840b4100d4039a0705030346000c66004060070076001c3c0c81042c0c015030041c0384100203d00301c0c114160404e5003101c0099a4560 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 798186582 1250 798185332 798185347
    0x50f030703020303030115091a1803100c0207030506010e09060c07110604030f06230a180b0403020a12020c0a180f09060606091205030901030e1c0302130b0a14 70
    0xd040005503400203415110200002c07907200c100d0303100f00c0040c840d81c0d910007516a40e68801e080e121000c03201c02e600c4210007040240701e803404a4000d4081450301a0484411441c012442001c0304e03000c0158130b0041c0c00404007801000818042c0304c1c01801070b03484c81c54240c20165459a242c030805402541492000500f040402480c030f06100244030b00100300b079441e02d560782007602d480c6a443d0070440310145080b03654203007440c8804000071518181107c0650130ba80e07123040b0000a210a007201d44142c00e0b0494082c00180000c16031505c607038400d5002d4010a00381c4d15006028070902d01000b0700395001f6441090403501d038490601c04580131050340401440c4580484ea00400e6001c0080d0321850030450fa10092284541040c4215205991400070f540d1762982e15030140031040d48010510740040003000074642c42500700201c54020101503d0610199a000080300d1007404421000710760042581d0841e00000302c00c0c400241070f01c03c0a0351034190441c60040914028000f080140c00d004180d64 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 798187832 1250 798186582 798186589
    0x2030415081524040e01031208070801050105031f0914130503030412200c0f01030606120b15120603010b0a05031e0102041e090c05070b0406020c10090b060a05011107050f 75
    0x252080c0c581e000b83c65a126220240030401c161309000503204a09014550841c1e03d1245108610441e42c3d035039400f42da40d0905004440f00c0e40050103410504400100703003c0c1001c0f0058041004000f0240700081c0141201c61610b00024001d1041d07001410800c0000c0c0030880210403280d006500a20300141c0e11880081507131584006640d54808101c1c898007045000c2e40040d40780d40d203003030444030b88180c640c00d20011030aa441d00d001d01c1d0009400c40c8541c000d0301e0501e40205010002c000d02c0d085580c1c11a0b000b011940d0000c03a00302d488094030005011007414288a2180202825641e4510081c108000f2954450300c80d189501d04400040d03280c584004294151401340c2201900700c0d4031000b404118041400e85400b6503124103203045403000d11035021748101c610345548003900c00815500c1d034a4802c000d410000c68440140101071020007400d1082c496040e819118164000060070f190081c0700d9000102c0c0c1041d07050119401c1410688540001c04804581003106e65a00000112012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 798189082 1250 798187832 798187879
    0xa05032e03060f02040f030327050a0612240e0903030c03040201050a1e02070602060a0527031e04230f0d0f0206070602220b030c0a030912020304150815 67
    0x46840701003440012042549c00802c05030f500030003011500e00403441c4001040c00b0030b118404c075513110200000400c11107004075000031407004800310025958400b840d1018084418500440362060680c900b880510b841d1010320380c0000b400e07001142107203060240c1421610000d030001c0d05014003c01da10095a1003070402c030510019040d099031203010041c10103035682006008444c0076000740c600151000059116041c400c0d10b0035040c4e900c1000a080c48400341014200a0a00724007003000358500043c164144040404210301003d9521407a00c0360040701d80310102d038501602451505031190395070300d50030000414402100d101c94500030614000494016041009400240100d003240a2105990140007a480c107400342c50f038882c000310448070480e403c500500d00035160610100e4443c0d65000003814204c0000e040006d5403045d80c0d2103081501500c0048800183d00001e414003107604041c1241c0c1641070181800c1c2d05905181c810700d9414176200311142c1c060300000808803914200803d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 798190332 1250 798189082 798189089
    0x30308070e3f06090304030f05120415030b0d030c110109032003071d160e0d06091203110d0b010215070f020c01051c09020103060801020a05032e03060f0204 69
    0x54948284a03008800425030002c0180c6508000700700c1c0202030070034001c034402e4800d04280015614003400c2da03845102040540c241a640c03445484220b038038400c0c100000f4006400c0051400e034035004420301c01410f5520181c0001c0c021001001068002a0000a58400350794826280d084100d55080100e40d01207151b800501048d44032048103004060461200c00c14000580a4032800f0b0348a00d005a00320400c0d401480140303142d140020301002010544038404041482c00001c7e200c2240001154036034441000d540e410703070f03414600b01003201890050f40f6400041c1428000421a40c0d00742401d80a4111103607544d58541c03000200c540c7c42808420b441d07090f00c1f00c11402505200000501c03000b030000400d4090300c1950b61402c2c8039809181901d01650608940e8094819040207103405047ca0b801c0c02c0741031580398000452515820b00140c82c0099507075403090303140d24240d00b04134854201c003002d140030048240d80da9150040d60700b03e20380c00e076508908080343d40740c07180c58101d000348902d03407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 798191582 1250 798190332 798190369
    0x70327030c030b01050a0803070f020a1a1c050c0706090203011805030c0d030b3007080c0901090902010c230706050306041b0906180819020118030308070e 68
    0x80801040281650001924000e0311062040c0e0788031802e10007409090300485865a1043c00018001030a0301d9411810b9480500780d5003010380d861800041d115074840c2c0b12150020041204900010244035914a54103c0e41060119082090700261a88900d0074068131482e00c0d607071908159182500b240da402455180346041a02c02e9003030085d12904408203081d80c0340280c0c0c0030180610722900583c10306110007031080c044040300d01c82d4440074038a00751100329008a984070080c415a8180000320040c40e0f844040c20303401626000304042010305030028620a0720b04445100580d80c82068a080c440d48243c2c5685100c140c8060003002001501040c0da4520a81070085031031035010b0050360103a46c045e2004e018200c0201140c5408145a0701c24400081c000c920130040248980c00c0c03900940c8421500800a41e00c074412241010180e081c0b500310403072800c14082c11960310044070340040e01c3c4c0c0441c48404a04540d0300a280b0303070001e0300550820003001e405168940d580c0503502d0303d070031580d13 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 798192832 1250 798191582 798191657
    0x30a152706090c0608060a05210a0507050f06030906010b0a140406030c1205041505070c0c14031507050a0c03050912011e060620151302100f050703 65
    0x600d0501c0c064140c0c0e40044540810070540020390a00035001d15000b440300503d4070300f03080e081c9820700001d40ba42400101803813211901054028000380110180d450145000c0c040450410091004500c2d1040c08140241010000c10103410004250541591490444150ba610010170202c526032100f024200f0b030300c040020300044c065059070295120404030f48071003800d0f030074100304a42141c400f180d01a203c0c98a41c00d929074aa000d9030b222640c4005182420300000000da00c070403280075820b82102041480401402c0c50707918003007042d01c000c4101d03103450f0141840c091000500c50701a400d601001e08c04a08110740400d8051026503544050142000c1c2c603000c031182e00c0301d02801c451000030070400502d021b00e00010346140100d900380c5015444078144100141c600d11804284525421518000c51070030f14920031607a541a40168042003031010000e0071401044038030380c0c041e0441824000c020070109802500401a108101e030141880610044500001c850800035180150341503405c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 798194082 1250 798192832 798192911
    0x80307050105011a071218090203060406140102030717071416050a0b160218040312110909070c0f050105100609050909060f04050a021e0f030a15 64
    0x40900425402200240202e03640d13501e4040491401d00c10400440c0c808114442c0070807400050458494094034200e10403040322444640900d4980d00691300e0346400100780700c200e28060280001a05807100b10f01f40c0700601c0170000c2d54138412070b18002d00e00810104031659110003c03007511100394214480001403401c0d140e5964403400c075500d14403e00c2001701004101820180801401e44412490161900500400080c681b0922204c226400b070302260000311204c4580942a004d60b210f0b4899600355102e181c00002642d41986948200c0340050116a02c140d851264680d00f240203420004032451007800c1401c1020034910010300f1a40c2084103102c003034a050f0081d4802c980c8103540b100025500c9070104400540240c410407207903806203011402000696900d541c01a00c100201e954156003036021400c40c080100326902a212804000b0120b41031405502044d000d08801804030482a40d5812140c1903403103024510b01035503469a0100b900d0380300201042d801b1041801009a02d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 798195332 1250 798194082 798194099
    0x8150120071211100e0a06030b030a050a03030902030607180e090f3408120a02160602030a080903070302061f030501091203060f0b03041b0905190e07050f19050a 71
    0x458204850180c101d00c400c080d00c0c1803040c0500c1e0034171034005001840e100d2605404a000c3c02e10060000e5048c0606000c00d00080c0c803c1101010443c460740700031414901d43e0041504044001300071b84103010307190358a0181d00703208901050543b00822a001c0181d00c0c0c010450f8a4031080812243c458403408400f516580d003084003041c1c0300c1030b41d82400d10391200619218400c100c541d20564500d94082030058500d40c5080f005490840e03098812164600c1c9404111100094180d01620141c0c20010718400140d604c0741c107072540141e03100010740c54801c0f25a0001e5440340c0c003c0c901c1400d01d08000d0484090500103940000030340e0804020321204682e070603c1030001001c00550000b0a1802a001071201482c0031103904a031905440d180c1143c0e1107450382c02e110f50120001a982421030132010403140c909100b024001ca0428144d186007c490f2084103040b540918948400e950100f1020446980d9003401c2c10b42400b030540346501030660f84060343c000102d00c1d4000070303070044d000000031030101c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 798196582 1250 798195332 798195353
    0x6200705160501030e100507020a051006051c050a111302040801020409050f01080616021608060604241701020408070e0702012a030c110601090c081501200712 70
    0x44201c0e5004825944000640c11101c5821150507140c00c450000750024965600180d0700089500580e15280f035203640b01c42c200082e0009a0452643c0c0d00428001428a40e07580d0044480f4601ca0702e01c5402642c0721141e40e038005800092101410400f501441d841300e65003882c1c1c0d4442c00100b0754545844450346800f0390080c1c020705003454585400581d4911445100b14101e869010140203651180710b04c00d0790b151240300c011000d61143c10100307204094500000c4009004050207040241050780030402030f942083e0a03403010380500d181d12511001c40560381000c40300340d0080240d118100300c10090281c010313940b040282d0700410000240e1a400c1c95a294410300980d40204844942c0300c0c414500d900c025140242e4044400c000f015146020750302245e980c500c2400c0000c4031a60000c451440d04000340c004d600c107151151707900300a8640218030b40e5085a4030060304055412000d000070160303001c207542d88c100031036400b091400c0d030b040078025038002e8801400d140304060f5180c2084485007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 798197832 1250 798196582 798196603
    0xf16051222080f2508040608040f020306100503300912060108060601090b0a0c02010c0302150c1c110a1808010230090616020c0303070c030b0601050f040306200705 72
    0x151100004c1d40c6104226500d0300e0301860740302000794101424100300322a5004006c20460301c040c6080c8041000d65400c0100302e1081440c00201012542840145401c050800c07442d80c02e0a10700b104902d20305210040d011007100318001e1455100c004003000900c08969002d034010050203142c1c00456030710004914244259800c0e01d8039014a40e941c607081d54035220300040c0500003800f0b00480c00043d840340100050090003031044480c40c02c103076032a4200079035090718507080d1080e001411514085244150082001000c8020000f54907015445c44803403090620000810042c540d030b43c00b50341c1c10386c81008081c00d41070303000319110307180f00b039040101101007504d45000a084948524500180350100d0b0f100d82008800381803d51104444100a01001849034055004121741c494580c0c50800260010a014564429441e45981440c1504d00005440c20b81040010008500140300c0c14048604817507011100058400e0b007407003014101c41c0724844142d50b403500025600144100040c03840c030b0301e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 798199082 1250 798197832 798197857
    0xb0d02041d120a020a03050706020d050708010302031b0d0b0702010e070f05010e0a06020d0c02031908190305061f02070504020d140109021e0d140f16051222080f 71
    0x665540c10b96076040c80c003d540f42c610050380040f074040e000038411005003102a01c11030026040034164192841603440c1100d840c000114107000402c00d5280c10060711030440c0452001c0b030100301001012402e40340340c120010380101440c0000c00d140900c00d506c6940b140301c0740c405507651175485401c0317090200c820b07200d0703a4001541c62443d400f081c1b500003540012a01150003d1003010121001513a600403082e02c1030b41d02d4050041502c900c000d8603104412020300c5030441950740d4406502a124941510149408040c5004200803092300c58412400c036114034803d03114031190070303814101d24002081c1c004641041c000725110100c5006500400d9550412050490b030a0b0703200d41c0000100d00540b1086407540c09402c0955a1410041c8000e000c00e01400402052021012981280281060319600c01408101d8104011020031800c01c241c424982d141151400300601241d190132600078044203030184422020750440740903039100420301c6600000e42a113601c10382c408441b0780c0d000405c00044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 798200332 1250 798199082 798199093
    0x6071a0106020f160b1605071e180908070f1b0b0306090f06060a110f010911180f0402130e0709050130060207080d18020a0503031306030b0d02041d 65
    0x540713001900c807090a9406051400381811410007000301154001c8400350f50301d0044d03d0000c90030700240d4594085040c690041e09004910707150021940901e0802c0c1880203d142880000001e000039084400702600711420b07183c0d020050400300640d115000c806800301c4a00d1070000360003404030b8043c0d8807800c0c084914112030350303803c0d200c1c0d42c800d2011a241588524200003111050f80108030400c0d5400e0060201c9916204104085003100c0b402101074600010800280b4814940321002d00050074004521000b01d0808022580031500c0c0a0070017413084040c211000a0040650702003030030f94191104a80410380e9400981c0010304080c00b0b6901d99a0008801a01b520203400c681c010004c0101c00c520515411505c1b650000d41021400722109941000281c56050540c0164000c481031500d504920320440d00c104909604250720440c041d41003404664032410b00e901c0c0401c2100c03210f00b004100e41da00c040c000b600800b40b121009500070f107480c102241c4060b0700d410303021011802c80101d0380c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 798201438 1106 798200332 798200353
    0x11707120e01020309010e0a03050307140f070f050d0914090919080a03050f0103020d24020a0306031101020f0d18180c020d050306030c06071a0106020f 67
    0x20301d03603401006003c0700184c00c0c40303032002ca44122001452038100583d0041c186020003055101072200d4140c00001c103049100c02c507444410700c01e0207103565502e40d2400000d8000761402c140c8a500c9054200084c85000d00741c550103841074200050740024210f4100420041c2c000c0c60800c3c14041d070070000c070003c181030304025022407041341e9007a1030700b46c800c40c024201c410040086981c500300000410140e02d13900b09400720303640c2102ca6825100316001d02d520307610054608282185100045007a0950b900d0b40c496800daa01c00c00441d10740880301801281c0e2800c9245c078800f0744da04608007040b400c03802010400c030802d000310f5410100940d0b0740c0d00f41400d10882e080b001004c5495003182050385074140501030102d5124103015055040c8480800d0f56141c089000e50700403a0b00050f000244508940303104c01080d074946c00c0403c036684446009444200080036005540700e41150310 = true := by decide +kernel

theorem cover : BRFrame.Cov 798021582 798201438 := by
  have h0 := BRFrame.cov_init 798021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 798021582 ≤ n) (h2 : n < 798201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
