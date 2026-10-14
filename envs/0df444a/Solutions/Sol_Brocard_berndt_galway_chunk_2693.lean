-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2693
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:27:56.568016+00:00
-- url     : https://prove2.me/submissions/2e0aa0d8-eb0b-46da-b020-52848cc5bce9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 484172661 ≤ n < 484352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 484173911 1250 484172661 484172683
    0x18090e07090b0d211e0f170433020f130e01080604021509030a0804050301060b030c042603030103080d05060418080a0e030f01051b03100311010e1c140c0604030b101205 74
    0x80d01011101003a181107d2050b01454020f6030451b00c0310340c440f5420354100151403000c907a41181069480f0a403960340003501e0302009410400340c5178410b23000b200d4034040d40c90707003c04020040500108501c101c0403078041d400c6501a1400b4000e02003102c050b018600c101905540c0510074890314205100c040d00103130007601c0c0300301e00900c02c02e503840100e0b030742c0da000680360741b10310380e804020800000c1c81000c92030140c6c1d02c000000d503107510318501c4418207580099100751403000d80041e40c40e4902c600352007515440301080343c3c00c200012003511801c0c0502000c0c100101404000610751030000d014548400380490010100c0d94040c8030300c1c407094060041034549a9500a118580c801d400a0b048141ea204100300800c110000f403554035481c00c900c10889119060144510006e00c81c2e841c1c5006c07151000302440b0f9940c1081c152845d0400300c151540e01c0085a640019050040341c2e5030702c1c0200c40480360005001c00701a12404086000d02c605039020b02c0d0f1542512081ea001c00802154001c109 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 484175161 1250 484173911 484173917
    0x102010510030c0b031305030a0207090c08070e0906060d0c020c030c0102010c0f0c0c09020c01020a080105030d05071401060e0f01080c18040318090e07090b0d211e0f 73
    0xa915540d5581410300701c02e010041400040315018040b04000102950340301150721111141072005403250342c11507212a040b1030050300710040c11700001d190380c0500480d04046242c04e240d0f070720340444000c143d441c142140c0c80c030864411021880d10b90b41c81d0140d500d9101001801c0000032414040a03603503280035244140a8060309491940c198010312404e03a502c2d485071900440040d000b9022280700400c20000c8400302c0307201d42c0119803c82e1510161009a60017400181c0d5403240002c0035100d080140d1141d440380c3d01c488801a8600d40c0242900d01890f80158042020030800340d0350713405410541c01111280100d1000c2240c004110044141250015400c0d20925040b020510103214001403080f00d50748058808140005e1242002e82111f00a00c0c20718a8940d071942030301700c10b5400800c8210440c0d07100d030748148424421781c803443d5110344003140c0fa00e0201d00c65a482001c0c0c1d5003a011518a6a10300081803490340b40075409081c08800c6000111074101c1c1d141c203018085a00403003c80c000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 484176411 1250 484175161 484175171
    0x40f020a0e030106051810031e1a060609011809110415050a020613060914100c022113031b140306061e010504050301050108060603010b01020d08071b0b1005010201 72
    0xc42c20184035150641e030002d40194841e0030800f050f1700e0030003005004000400c55070003000012400c40c1c1091004181200b2405e0001d0199041000181d10b4102c80108441c10040c14003800e0342e12031003152507061080c01c1c88820340c3e014590103240140158000381d10507041c040da088441a0200090094074a00c0381840c141141d21841282c030741c0607000e183e101603400400880c100315583c80112181c40d1045034086500782081c2d4406070309803a8072815080b90741c000c0d860b046c0d10342154050460301c02010700c02007441d200c040d98200181c10800c12404000c10000858100400c9807881100103540c00071190806043d40286619131780016115010600d010081340c0c0025150114510340160300c003d0001d2140000410f03021450110003010b14140701041000050750b482c207014003802001790b04040e00242c41c11409250a591403001194110b4203d00d5840044982000e4041d0704101c551400691242c950700300001448520040541801e604104004001c2072103228031b029107130b082e802444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 484177661 1250 484176411 484176437
    0x30a0501110915070b1b071a0907060201140408030403140a0f0206010e0103030c060f180807060b090408040b0f07020a0e0a1406030d0c0204110c0a12020a080a0c0c05040f020a 77
    0x5050041c00350062a500c0030001246222415504101ea144604401940390034040d1b5503440c02440282d04860418200f0010490000c0007403100f50000c113213300091283d104070351682c1010910050006080c15004804070b01032500c1f540c4000100400c1d400314544e00c1d41300390405009000181c7d001001403180c0c0c0e0002c0707449180352130818100c1c0e50540b941d83c490302d969039814020300815141000c405a50390503154111080000d080d140a00440903595280d03404d0900e04103440f001c0702401d01030710510040c0000150700d070342101c04650072084265280c04213540300c0c094510400402079405103007124007144401040c90311030b01030704a10300700704503101c8200c01c012200c80f400c0710300c1581a0042c00408070160f000c0d2442c1c1c624280b00038000900441c1c1054202c090b9046000200c009903c0805410b0800c60051402005850780340001d027135640040ea20b0b04c1462280204900030894100911010841e2000691001d00b4004005016004218800000942140429038009007406c25108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 484178911 1250 484177661 484177699
    0xd08030906010f240c050601091d1b28030305032502030f0a0c0b04060518280f1515060c1a0606190903021e011d030a05011109 56
    0x80c104c981e0440d140c40d100c40103402207841d90100c0203c02d030600160840000000f6804d006581c06020f00d800002040d2a03000544503003182c9580030003804c0c4d4080800c8166800c01034040703403d2900221080e21044500c0e5480d0340ba12300030000000c0800d840408080201508580a103100d140384214802e680b214440324042e1150016510348050b8204000c4c15008401a400030040001c0034200803070340600d82d5580c0411a80115015a240c50791401030001c14042445201e000311803030402010951058011101150422545401d6549100c68410304020409032803d000c240c0080100740a0b000c0911350790007410900c4a00b600b80da4040b07401184590041004486031504030b038504a442da07041203201c24100d80a0042039200c0d00600080c0b8205840f510b0090200d517059441e901c0003480c41c13051110038501c00c6403005c0074001c00d5140860f183d03801705410204617000500381040d02c1e09c81001c2401c10089003c09040c650a0001003426a42c500340201190401070707400c0b04071a52841020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 484180161 1250 484178911 484178939
    0x5031207120b01090303030e0106080724090e2404050f040b01050102030c0a08030c0403080403030e0a1d070e1f080f070201110d05100e070f1107060c0803040503090d0803090601 78
    0x6140444c4114005001003071003544440044003405000141c041d8984103070f186011300c603911440f1042c41e000e040c4020003400000035039401c0c2040c140000040d0070064000403000008058604078045c2865410000340c461400008071000a0003c10040c2032550400540700012a0144c50421195000140d554400030803110f6400240020700070100e020380d1450581d600140904850840600000c0041407007070000304011803094a40070900b110010a00c281503440c0e60151884600c1d50490f00000000811801c2c0c0c0b000203440c04c88400e6400300005a10400d043e80004072641295411001c842d4005441c10f0181c44160001343c601c0e2364a080880c241e6003645401d03110101c080c010030003c6005078211782d810503041007103071910702d40b10151600084070072521000000d40c8640f008a079150411007410559215002600c4e8a605200303000c0c0174410300310382c003e01c104800000a01807000a0041d92107501c00106030b9825050681868191a001959031200f140242d40000514220303034090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 484181411 1250 484180161 484180181
    0x90f0b18060c0f092103041a0315040f0f0e0d02120306030c19030b191505030606150f030108030a1404060206131a1602010b011b0b060303070503120712 67
    0x5a41d1030300b40e502506400b50342200007219001003010911802c01c0e44240d102c024450305d01c90085403940d10301503280164031242a40000c100004109101910040a8030b001c000d4006071004119131051051820051981c00f81e031069141c41c141c510304103c000441c0d2000149102c0e82258850380c04900340c0c450301d100c103983d01a8507074480c0040d100d5500f800d0346604403603041c0450b800e01440c1c1d25200e00c0074010080342c00f540741d840e80d8400300c400c80f907840c441c124082c414001515519030405022a9840b50003515680c480d03d21500b2204000780301e541280c50080b02118072603103d507507803a2800c0d56500611113400c01f01d009a0315050b401080303042901d0840f1655401401580c60703808901d080310740f40560a40300c2c80485460604c2c0313010794040701c0d40074a8140c03803001001400c0510080c04c40f03410489442c100000301803140681c0b14502da541a41d40d4000b44054000e44846001901d18810100014441d00011035102c0b081d00301d14100502c030720102d4a600589110703086ca40b10454424480d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 484182661 1250 484181411 484181431
    0x2402040b040e0601051605060f0c070c090e0f01020408030a14130b090111150103051c02070509060a1502150c03040f060504110a0f09110c0a1104090f0b1806 69
    0x4100901030380070000b20b4000d0010b0400d9494119050490941044111829561235208509118160701101c400b19401113407a01d040d4107103a042c6e82d90004000107031080c910500d0310f504051808000501c60b01d0301003200d09000315540c503550540f0548940041c120b946c04900d00d04d203d00d04e42801c600880e0400461114200001030500740030604d0741d001001c0c09410800f400303011550350141081001c0448841e102c165074907603d2761030150718140300c5240c9600c030105800d00c0e80341c440c2d070005001029240102e03854101c50751303a10302040342d4040c03030303800304540c14015113142540c6034000c03c0788203440e2804d082040d00c40c0d9070781010801c240306c291801000e0107070008588000c660345600054006105041c1001c25021400002d0755039101c0360094510250260307400c01c05507105218691203540c00e0042642030050300b144240e00ca503841da0018010764001155180b02c1d56680e841074443d03e0b40300104581110b568245801454811202c504410380b42941600400c000052403503c2214a50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 484183911 1250 484182661 484182667
    0x10303020312070201020702090127020a05040303032013080f0102041508070903050f030a03140103050a0201080a090602030a0c0e0109081f0204030507091b0e0102120a120501032402040b 82
    0x482c901d07140810040c2843e0441d5070a014202c01680c800301542d0082014410030b0385c410360f00110071045022848040c21690f881008200e81d8240c101c0b041d02e040340e40500f800981c1004200d010030380401c008181c6407031100b000640303101c80106800d1140596040404076503550301e2142c2168200d20030743c0210506c0d808404105050103200d003891a0340010b0701e2501015896480e1f03a00c0e890f103d044200748a403908081400c0541990510030040b6100310480b80055130752440d2903075900e84040020103410040184001044002a40c101403007182d0b0040045640f8500f1440402c000d200c1075601c040003c41c2d0720242c100e10340c8a40d481009030b540c4440036100740d045642d640804012030a0121010903020710002000c01c40a010200c003c0c80070840100d0a102c102807814542c04180f0911424800803d169041c2030f64000740c1d1854589110203030b00d5942c109104140c42024102d080100c503981410b0010081164030b41c0c01c00240d403100c80c03101c1480d1041c01501e106078081e82c0170344000002c084c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 484185161 1250 484183911 484183927
    0x21207060206010b040f0911190e01020c15030f04030c05060901142409130203070905010e0c0712050a0306080604030c260f090d0f03050301051c080307200d170f0103030203 76
    0x548d001c10505c840c00c901c0030340303031005404a00e480c0860300b440030300105103558802c41d290358040c4144402000708642030b8080e1005602d5103203040c000034003050781c0400d1200c002020035010303592401d600354000c8100c880c10714101100ca806030901c5030380320450074418030225501907542c408008422082e9010091100c05c460144001f0f0f410003020a0700f000140c00c0c0d0640541c406012440150500800120b034a6061001404400c0310281515000c03240030030403e00865120714a82c89201098070b00075695807180041180036200c1500010940d0080c5d00030f03c0101604680d00c03a80e5984107034806103004c442039510000d881c01e0145009602c0c0010400341e08040c50080c001c00518070b00a07c100701580306511004800c507004401203020034000070042c072443c50504110310624002005010f51002259201c00e018080640b151040c0b000704050249454944025100c1040d2044204e40d07405941941c0103001c404100c01c00070300e801d40c100201b82e001003616002c034160780d01600294505484 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 484186411 1250 484185161 484185179
    0x1150611061b22232d0907020f060f0112030509030a08040b0307140301030804091508030c0115050306040b1f12200d03090909050a021207060206010b040f 68
    0x140c200a6103100b81c04110300140002c0d915200e00d01c00181e850381d9011075042c00c0341c01c0b205041c54510107604180d80b2800e10895036460341308200c450000300c120300340e0024002d00725000303484074071400e680301106004210301c880e8002164600d200c40f0000301c0b101a29100e084188841d000c1c06110088a41c0385020b2011902482c0185010302c800303401c07204021400e0325126404c0c0c1054002519441b000400d0048070b6a0080403a02250059998545154510fa840e003c10b44124400c0d90b8401d07484118034445000ca2102c802c0c000d010700b006881c1c0d01c0b0181443d0030b00070440c84290348007201c03021801091508000485501c03881d070001c1c03e85040e842d0841900022441c80710ba4444840d03c210021030b45401420b814003450f4072a81c0445c803490b022204c4480307114207040900340160000c61506001c25805003d4404680055400181c01004c0c0d003400da00b080b0407a50b01940142490149201240d00080c07403108440300d0358292502a40c0f00c000c03144980c0b1030381c0710300070071710042e81000d210500c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 484187661 1250 484186411 484186441
    0x406050711100818011b0e0d150213090e0a06020702060d1b11010e0a141018020406050604240324030501051005010507110303070b090115061106 64
    0x2018090070740071001c1c02800900b0012440101c0b00010341c00c2e00510122846205045000e04600f80c002e00109200015a9083d2001c07004120104a80540a1036054403071003403004601d50885600d5404005550a26000e0360090700002c81c80d84032040c00190b0715540c0c0c403404402d40c2003a40540001c0d140303a1100006500911400e1381e00503010044425650454407030003a10900c0c1c0302d5200c015a0b908800640803410f003100300c822503410042540b00240f40451510421540300c100b0070400c1e40b1034410107251881c00b0603c0313840301c0e2801171205502094406501011403003110b085c0040c41c0c13282c1c14005640103138420f000000c02c48000420300307a45250f41207640d0881d146030010300038030100720314001c410800c5400605401001001d20a2020078080d80350b110031450300c0f43c40c61a2500c00020020300c40c1031000307001d07031040101b0040303696024801ca403142c1d60006d010741094140804442d00a08290b00010741700d403100300340094018022641c0c9250034094a01a000310754800810400d04d131 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 484188911 1250 484187661 484187663
    0x40b0406140403030608011109101110020f03060307060c0209010b0309010b04052d100308220f06020d0e0a0302060304020301060b0a050904050f0108032a12091c050304060507 77
    0x80c1c441c0081d4007030752040056a8401d500a640101702c0d41d181051540c00c580c07900180d2591380100300f203e40c4180d100d01d0310350101c000e0306182c08202e203444141501d0402c11000303845440c4500010b90410b0942c0140c020303500034170046040e612840d0361414140d801100303400b8005c2d000090800104504410100031b140e02412040012655501c074200240c12030307000310303209a050080f2603030220080403103070400301c000224203900500c41d042c03040000e0781d40c141c14030009040c904001003040c0404018850b0400340c502002546c1141c548030300103070001e0407641c01901e0041c400c503800a060184070780300300850488040c1c16000c41d40d08503020300c525540010000d03030700b646d02c666000501001602c000c3c02e080d0195036134036032940c210404100945002074401503414041c40014083d00e480802103c0c0c1804010030320505100c101c01c1d55080c03842000c9911b400c14040d440c1e1920810000034001d141100701142c205100c0348241d00c3c40c00e1100f0400d02c016020b9841404280301c40c5000d0002000c0380c07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 484190161 1250 484188911 484188923
    0x5010f110d0903301b021314160806060903031908041401051504020c1609150807080c2716091e0911071b060306120308150a0905090d0210020909040b04 67
    0x8141e4002c42c5d41f2241140070100c140b50b8403045481c008280400c415000400510403041074801401d00421280000d081c2030301c11800041c1184980d9820011a00c190b48507072801511480381d00d5016180c41800c03102601c000000100c40c230b06003001032003800e21031140c155007800c010007d4000e100094000b000c0c0c120303091080c15000c0140c1410140010001d103491000455080c94646040c201590745070300140c215404035205100c45980410440d007250000c2e84c0245c0c1a039003040d04903500c801541000980b280e100c1061203c030611281c41032440c0c180395180c05407025580e08800000c0f81c1d00c01307003002c90301421000034400b8901b141c0084a0071130901c00b442d82000000e48a124181200c80703006404a48262005c0205039014060300000384040155407d0a0846842c00703003018200809064900010411413241590340d42d1070140078200060040101c1c1c5040c10180d85d80d504130702c50707410140c4520f01603100807082a00803a0505140507008810907259a0b0740c1c40c00e8428003030301c01c03518 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 484191411 1250 484190161 484190207
    0xa15060b1303120c0206030c07170703170f091528090b091204140d1a040515060303180303040306330b0405010f110d090330 55
    0x1040e00050103040034003426a50765030218914900010352208012072441401035840d0f03a80c0c0541d4074601034036480300e000c107029030b078810591404a0040b8100c06106002c43d03130104d4001c080c154440c0348400c800250100d004495114212400c5048004484001d60f9078400c41c0c101c040b820710b0525458001e03140140006040f410406600b0302c41041c1c81e0383d80b080c03569802050342401403048140d504895800003902500c8045042d01c0b80501c0345000760ba01e109044800003000b61540c1c01207103000c5c2d030003596110003001500072481e18400d0607501a074582c0304070b80e02401c1d0000e02001d114000d060003001589000c1c54204c104a00c002071040c20359042c0028440040400c50900030340c031004501c0b401c0c1201034074154001505000e4141d041402c03110800d0030520080100b031046400303031031090074406410050494100c0300f0030f03101647c41116002d1200b000960075009451202942e1240e90740d0001031040034403c0d404664814a020580740304030300c80201c01c5008924142c00c00b2111a201c0c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 484192661 1250 484191411 484191419
    0xb0c040e0c07020118080d080a02040b0f0c0307020d0f140c1f0309050703030201051603090305040302150714161706010512030f0a0e0103050106050a0207180b030a110418050a1506 79
    0x70340041d194460001d940180b03000740b4110b40d2023584140c3c01701081c14110304090500e001d0f0501401003068181d0b01e18800510303000000c01c10030a03580240e80c02440c0e04100d0b443c2d85040f1014103050f500466090794982000c1c00038401c08619000d2071540640070217070749003500c0c1007800042c441146160500d6511415440030600500030b15010758080d40001c95030b0308100c1040c1c011290116500000c00d4508054007000030340c04405c071011a60111146a82e1404115200c00e4a2180000c000e0005032103e100079210600840e030540b106104505082a241d618041d00454110880c00e0b00d8042d041840181b0031483c18980d101c040b809094108e90400b01c961681a001d980300d0700c101d9000c601841202e03640356074076000d07803409091603240640c00c3c0401c004019565000302c0c000c5100d20032114140c601c007070041e40e11440440000408036600c1c09030314182031485001c0210103034000c40c18000190441881a0071502c1c4107940b01c3d0060000e903020380c0314407482d08095800310203d00c0e11020006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 484193911 1250 484192661 484192697
    0xb0414070822050c0f0901180515030d0909112104030504030b0f04060510030302100b0303161a010e041211150f07121a04020d1b020304030b0c040e0c070201 69
    0x45283d220300014600078091108002207514036050240c880d2660743d0050181844040707105401c0c440c1088003160342d80301c2c2c0c0e03080b1014154141c41590584685411075400700da00441c608110740043c3c00c02c00c41d0008081d83c906017031003181d01191032003040c00c3c04041c1076510004071950181c040e241036800c0a84039541c011824005035240c1f03200c0c000b03140504c41440030b5803241c00d03005884c0e1140260f07118a10355000c6c0d1104005413000141c155540c0c401750f0349403814800ca40d00884070107440151003007540350540c1e010322400102c020b4094204000315510080e920b00d94061500400d42e401440c4909001300c40c454510b58403620309015071030200c00c00010492105000307080000440100e441c100a0003031415605100c047e010b80d08040782e80c00c0402201d0032141d8802400e071009a511000b207442d0202601c4510225101c0c100a2441e50003410307400300150068070b2180d0031807000c03038543e0091141e040c080c0340100044412004d001c03030180c01e503602c0103022140c818100017107007a03480c031100b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 484195161 1250 484193911 484193971
    0x108122d0a1e0c17031005030d0320040605120a060b130503101413020a0b0301090c0914060d09060b030d09060f02010e060402010e0d1209030201030b04140708 70
    0x301d001c40c18031842d0142d08441000041034079140c81c50b00003610306660f00c0d0781072103080040d0140d00040002001ca4001c6410407010400b0b03144c003900b1201c238a854008002c0080c00c0340000d5600041e9149680c4145c0501e25044030708581c110350304d490803c50004407440d00b0307000c05031010103115030f02c0728005a0054a03201806d0340030001001d03009034a2604003494104071140989417805440d002d0700c62520a408030f0504d4020303030721650840010f20244003198070140b1303a4004450351500400002046580d64004182440080c0c0c4c0303103c04160340d07004084003182902d00c0c144d807010b41408403070620031099000c1d1016501486021a100118a0200c6d04004006480e1000a2091107062151329040020035400082d81d01c003c101000850141da910b860b40a03100134100301d0440400d000329580c40b54400400c581000c0b01d05444924080040c100030340510003207001c02d042020502842c03506210307403160603040f2940d58445a4501d40c003110440801032801c5c4104071082c810b00d80005000c800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 484196411 1250 484195161 484195177
    0xe07120303021822050c040519050315040302030d0515060d090506061c0213090804080705090f0403081819030503010e0112050a0b3c0108122d 63
    0x40160b0310030b5034822807914641c03880f81441c000c4440c04404d82c0d0000b0301c0041e03030b22203007a22040010561550300801e50140300300c0d8020750384460444100103050007a100000100c46040301101e0305006d698030540003c10381281e000c0d015070024002d1440c41202c0e90800c0d43d004100310f00010b0060041000038400b030700043c03c400c00499840301c0080802804120554000f001100d01d0321011080b01c071820745e92905014000c0c0204c58803114000652034941040341001e40c407000c0b803030300c6580310f02e8540d40d50311283c8102440345d82c241c0c02185403031640d10165401282c15540d648482c0d5100d00b00b159207410340b4015140d0f24401c5804520402034420040c80711284241c1e20590783e54500b194000c21120180c00c00c80d0150503800d000800120000303a040503c07a032140580301e1039502c00466030700b4440180c001010180400c00700841c04205481d4019400005c4c08440040d6603c507160f040d500c42c95070343e0500400c0341c100b0284400594080c40000d40d1445404400c45ca504541008403044d044106 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 484197661 1250 484196411 484196417
    0xf06040b060f1b0106050a18181a0106050901091517010603063210050415113d020c011d19030c0b0408160818030109150e071203 57
    0x80c120510140e160f40a040341c10842c0c0090000905100014005880910a00e002d50741204140300031103000e0740203000c03a00107412131444000b03010300745010306143c2e03900030000041401c07001283d0103010303100350f034003100040e500e020002d03040c14110440440112440801d0000c4018803140c108052800e1b02c0c040c001035039020422600e000c021408414800042d400551410b031221400c1d001404510003800c03c084409421100c0c1411054400d4811904401441c103000200b40b13010075008806803441c03048410449040428441c42e00b640c0c1d00300000420702041da1203e0800e014002044100604001a600149080b4007100340d02d0031111815603202c482071a140492142c0241440642101c4140000341c024010455400a20035180b10200400613200140842c05101c1010242c4001d0000c1021440d82809581400155600403060248513859251a1a0107504042c003603401c904c2e501c000010b5401c01411303a800045d001090031480c43d40b2032500c0000b480e0460b10400c00b0018003a40b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 484198911 1250 484197661 484197667
    0x20d1104090e03040506181903031e03020903060f360c03060906060904031b050619060e0412020a0b0c0a0914130e0304080d0908010c170f06040b060f 66
    0x940d40301c1500e111894140c415002880b00704441d843d0103040b80c03040b07403102c00d16440654144000a201030700ba10680790810680c440080101504844400318407003485001180d00d8081d030004809038031031601c0381a019041180454420200c0808083c0c201c3d800001100034184241c0d02200c4801c0c02c05142101307804a01c2c4004003000d01480340c1140020158060440380c50440c3c2c2481d070342e91014200b1401100303403500140602d4859004840c840c420140e0f100300c803410b541401680c0700000d54040c0c020303441d82c4425130a005403e104d20400c0b00e00804054a2030350329500c0340481001481180801c1d40a0b0911260008141154092141146003191a1141410100202440165003001d80703400c880803c0c003101660380302c42c4980e001e0325030703040811b90350b00f008021030031030103103510600244c4110b1611020554101c80c0c94015580c07104000c004e05501d251007104c0d00306411321040480805040419000719500c00403e51269025201107a51425107010600c543e04c40c00300b8042000303001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 484200161 1250 484198911 484198919
    0x6010e040207080417060f0414120417070b0c0d080c0903010e0a14060f010b0313080a02010605011b230f030a03020910080708061e041d0601120b0415020d1104 70
    0x160342c400c04007201c1c0900031b00303147c81c011452007205440900060240402d050501c010030004001e5500c1403100c00764841d442e180e807800000c8040420000002c168042c040001c1810030100f000d82c0c182c7c80b40300c0000c100082d410003090300c1031300d80a03109601030b9004204201542d1024081c2b40782141d080c0008114884042c20f140050301600c4040e01e51030b1304014180141a0300c80c8200d42e05403091100d01c1c070358035210340340c3e00503010103482e0004102d001d003c42c0200040d0b0301984902d040314800e0b2203001051041000703144a01d0a040c900914014070030314000400d041c0450b41c400c80c100301008442c0c521148043c518034580205550000091b0001a501058181a10a00041c00725410310210b02d0070100c001401018000f40218040c0700c410069a0451110319030410020304050310030007008444d164480300b40410b41c00e60001d0380c4034036000043c8050303c1c0c01e40c9008145c5c014101ca00b05488035990345040000d01c0c07040d45c030f419400340000c0000c0016440b071459500656905c541d603072490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 484201411 1250 484200161 484200179
    0x1030b190e010b0c0d031d0d02060613021911030d1b11010506010c0303180b0108070302030708120d02091201141803040b09060322030521040f03030506010e0402070804 74
    0x705812140e5200000e01075160800740000d00c02c1c45619a5060106009240010310002221003415000041c82032000401803550080f4140b4000c03502074070b110740e0142e18183d0000903072280d00290f424803000409130b03204103440341004010300480c10f41900d1400101c2c4481000b584c407001080110382d540354040130035580d00590086402000c6000900c07d6103021000030b0640044280c014050584403c00048004031b24400e03000c14a074407082c030900301e50b103450009a039078805000c224000c0c41401408100340b0700014580b50040c084020306440d02100312613290203900314800103500461084134402d0350010a005600c4401040c0012104d18945050b0722081d0500c1e043e070754440c0d030700300304803e204030f4001100300e8004c088280c41103035594854910540c448143e02ca03142d481c001e40c031100b160405034800d00074102902c00c00c145c14500b44003000300900c0786200303403002070a15400c40c0748030700061301980086a000c01e050520506503d0101c003c48c007a40d0115504450080c00090b003440300341c403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 484202661 1250 484201411 484201439
    0x21213090f090809010806040b06040e0a0c020316080d1401080a0203150c040e060a050607050d09091e0f0e0303010609030c0821130504021201051e01090603020901030b19 75
    0x1030750009005145003500e0301d88440c45203400c501e0401006400042071908c890b00543c1070a140034010944d07690b0741e42049089681e040d03401d0b0180750b08161141c03036100d20000c2600c84c039481400000c03500c83c2d41603039441c0f01540407020461142d900e46501215488081109500809410025100e126110300c10141050a58042c82d4006441c90050200e00c8031040150b9080d00c5154910000f40e032105000070b582c2110550285620003c000352040400c000410703954000041500c480c112070351103225500989804108408005540f11210020703003010707030841000359031620700005091101d44141c90950744260407040200d1a604e40802c100200417454000410841004d0060307070021100126601c0c101c01c188000d08070020071051441c9412070040001031000400455a0f2603014860b200d4040d030910070607119031644d0094000c00300c60400d04047c5c00340e05039100699942070020580080d00114569410540d80d400030703003896111030f0a8500c806c00d004e0202d1f90ac0c146000100c0340804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 484203911 1250 484202661 484202681
    0x18050f070303080a0f09020405040f1e08070b040f1218080312010603020913050109050109050601030509150915090106032d082b0b0306060d0c03110102121309 70
    0x2a10562007080860b0340500096042500c01030041403108401070f908010348080c4e000a035110f4070788000d0004000300c4141c040446441400110040a040c40764038801c0140114086d080c00400c001d00b000003003030080700c03641c81886039140c4000e030081f5859800c4641041860382001c0717464502c00000f038032602050400145444402540341455444000c0c19540c0c041c41500c092640109803103285070740d0000c040005800d088010800c945e03541c04a08003500d801e20400d0820751909002c14819403203400b40320b00c24104040280902198041c52143c015030003031603440d25000c1c2040303a9035410000703800c540c0039003800000810f0490550030104101114134490260301c0316000a1f000c00242e54040300748019400c080c0c41501c0e01500c84180d4000031040161220a4201150815005600b13a1001c45801e00039411100c00e07550b41c8041c0040d89051150140030f400c0030300c000704005000080c28031407008042c8143d40c1801300c000c51480d800d1300140d00e00240080c0c0c40034140002011845016441e03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 484205161 1250 484203911 484203913
    0x906050a0e010e211209030315040b2808030a02060603010507080105030717100219090503160b03090a02031e0f160b0a0918020a140f270418050f 64
    0x21400342d00701c56501c2c0c0820031004c920844a030241809000000300344c58902081041c8010180340c282c2816480e0740c41156000640c0316040240c60317107400c00307118410440742c010b81700da080300c040c1d80d80c0000300c2d0020812500d1414420007000c24140d02c08e20140450102036001003600c4e0901d00c040600751703080117144c2c800300607000e17004101030760740000c112045030001410680a14442c41b101402c088080031401400c9000140342249045981100584030740c29a4032500301c1921601019260b50b1a02b81d09040e8083c909000c1c0001c08030701c4002e40c0c00480000445080060f5a4086401c1007450340c00c50805008400760043c00e06424014249074080d01c1c000762112000b5182c1403003809a0074041e504140d440070645030007490145803218040e00030b240c980c6000c800c11004030400b9500207140c41c0c00003407007135052200a0302100d056405054244652609001d4940d01241071101d0310108100041442d104c1200551114801c540c462045800141038010090622900d80840344100300c001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 484206411 1250 484205161 484205171
    0x31a0a15080307031d060a0f0302070204090b061e0a0b18100305060307140625051f0c020106030c050906060f040801060501030b030d0206010611030d02041409090f0a23010906050a0e01 81
    0x1d86e4608045a402e4135103400d244010b954040e074124001e020b0b641000b90042c0c50a4180c0b414404468546441500110340326160343e000d55900c1d1070100d0b0490b00306504aa5018414001c0412003005000d0714520500441000b001310f20014158040610ba0b90300420303524014002141018821140a800041200b41d0441c00005c01300e01c007072142c4600707842a00d840d8021090740c1022224200030141c1c00600301d0b0500c1d1608000401d00e40b250058219046241c80184000907006008a4088a8000300310b502018900018440075100080039298880b008001e80f60144001030040c20140141d2070001503c641000009001c6a0400d01e40d24441d5111458054035142c0c0000c025041d03803050320306030500c2d8004894403841c40c00f41060390b8102d030303002042c04a40c81443c0c00d00300c0e16501085404000d50f03200d0034865500c1d420b85000610558004032511000b0418410801140d40481c2c01c2d0388161800c0b5900749170846a9a49040300c0907601c030b10601054a00c1ea0180c8414207003a0402001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 484207661 1250 484206411 484206467
    0x1113090c0503130b100503060f07180e180c12033a09020109150809071205030318030706060b09090601030605060d0b0d0804030b010816031a0a1508030703 68
    0x38020031203d4010010030310140050480d003040e1580d04010b01e0040c0440b032250411301503540700c3c0241110041c1c00220312030346040c070400c0c8480f0760000f00c1c0c210b9010600c40340c81e80c21401042100b030300c621740064450280001503e07100c0d8071500e05a04502001b031915850a1064155000343c100001a01d090b8021460009107030500719210101800c0c5078001240c4201d0301c0180c0e82110281d01c142e400000405800d00c0c110b800909141c4105c403854265030255480311501215414412009000d81d4000d100040000088000501052890707204807818000c195544c40b00340c1303149401142e205400422103003d0f905041c0c21454200c003013400e00b403101500346404120075004024443d031800d81c45501428050b111140740000b02a04080a6070341c0d944c990501880c54482031241300214030030340c900050205a0304500c1c1050b242d00401200e04814004603006a0913000740c080700c4160350700c50686a480368002c103070b08001d00d4985e000c0c5846450310306002d04040c0c0302d4400081e41c8403101075410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 484208911 1250 484207661 484207681
    0x114012f0607080702031c020a0c02130209090f040b070c050a0c0f142b02042009090901140a1a12011b05091c081201060314090a030f0806041113090c0503 68
    0x754642c6107d0760058481c0c0340c500040b03d140c03c1601000c1c1d0402c3d143c091010108045400501c142030080c0e50400c0c540d02c5030705445203d00c0e001c4801030042c48411003c1501a4440c40c0c0ba002c2281c080d008890284d20191155214021035610444103a514600100040c1c0c9144680c2040d02104a4403821010200380c0400d160f941c0603500740b03000d0b034200000385003150340c2d0358400c88940441c3d10964000c0041d20264214139480000c21340d2056002400003038111005004041c001e400351110340764142c460800f600c015101d07001500101c0140c0243d14130513920748809204d164005a00041340c1000c84003024544090740742100d40c100007042014500319160b907101d0000419040003180c0c420b60301818071407080d0003148901034070a08007030000110f05a00d500600211194000c0886c000c1e01c030365000d00c5d6101d05250005001c141200c081608a500820780254414005000802c0d03c540d207841c070303814540c0406804007034041d40020a021120043c8168104c49141d42410362a50501200038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 484210161 1250 484208911 484208947
    0x1060e01110c090c1b0a1230051003050f15010f030201050f0a02010902030d0306062c1210061d09070f09091a0106020a06140114012f060708070203 65
    0x74000c10a80000c5081c1d0340d001045c600740c0c80301d81e42400d59890401501e049807a00d00d80c4041030000407511008403a14100302c0d14080500c6084001c205070007848450704601810000b0903000c4203503594403001010400a02c0442c543c0c1c90a0f00140c00351902444070441c80301c50681000c525107011076401d10060f41c0020450350358020000d41c02c0d444100c82031781240500a0002c009405008654003082043c1d003681000050390758503142c3c00ca01c0301d030740300c0844401c140700b42100341080310251100c0e20300e0400d0880007203a410802d0556a1241f0305140e01415107820758000d902050b50007403074401c00d101079100180c001c50083c01404800349840c82c28030b040a0240035031500c0955402628007000b20001642c000c560100f03607502c500790b035512406515545244410360303038181886070506e4106000c00031039050ba02d4038460700c90002d42140044514400d8200d4002c804e040d000400701c82e000c041d00002c401550200d00403d86c80ca01110000c0000101070040400c2d0350062207440c0c0c9400f514041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 484211411 1250 484210161 484210171
    0x290a020c0d0825050a08160c020409110a080f0123011a09030d08060f150406030c0504030816030f020604050c060703020a150c110705100c021801060e01110c09 70
    0x39200754851100320503040f1028902d850030144031100c001600c40e080005011710404a0f02c4204295a840429030200075840c0c0c07900d03002604103480c820041c40c1a82c8001da41034094545000c0c11810400410012402d0f9001302c806603110008010550009011b4080b0914030f00c410361403c4480f44480e07071805c0c4418021901c030301d80300d00c00703020900003d281a41e500f510001c0413a01601014000500b5540043c1d5407103000d80045105505a0b0414044040c14810680300070b07842c0c949010000c40040a61003515010842e01b00400004101c4240c042c00380c4c26181103801c01020300900c0d015041c80c50400031a01550001d100b000301007103020a0044c04000241c400310f80c2c4403c01d140407410500034520041099102560700b8180c681d10f40c1c444e41e101561520b500b2410341e00750f101107682c0d850034443d5542c0b040c4040100c000d12482030010b0681140b015144074010b0f819130342e00703012182c401d8000c00000394125810b10f4817580c1c8400d000310680d50b69800f0304007030380d00e00010034030007400181 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 484212661 1250 484211411 484211417
    0x40207230c041a06030a020a1103130e01081f0b03030d11030601090501080c03070f03090b09011a0109082d0f1f110a030506030c28080309031c0309290a020c0d 70
    0x168521044c0c012045d0b1849840514152680c2f81422000740401409070b014000341c1c2002039001141400001440c0c5003c0981d02d102c2d480070300d0000402c4d0000e0314000030820f4060205020b000c0c000c055a02890108003501c0031499140e152500004000b041d07942e010504128060060100711071240c01100d130001b001e40f074080142c00c1a00300940180060881c010001c0c0c3e117180802051410642c0185991250700c2d426114840c420001112241000d009a1445400c45610240000c0d070698409052003000c103c4600d0049840d10302c40c0c101500b18540000f541c2004100c80140001c498070000c900c2da12203020080045240c03042800d500800340c045083c99614004202702d940d04011520001500a0900303850f80d25140c05400120381607803038088182d01040c030110f266040802a03544800000d0010100d00d207202c0f00214280b021485060289035507100c4910115044400250026210820a40301d16000780c1841240c220300820b881d180d2071050045c0c00300310300c001c0303100100084207103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 484213911 1250 484212661 484212667
    0x112030e032a0a1a0405091b0a020d020d02070f0501050d060b030a020408150103260403050105010e09100e06151f0c03020712030c02040207230c041a06030a02 70
    0x802080c81c15039003080c2c0544004050400b0b0142c80d500030b01c0c0156104003035031000315640c2e80b101c07841c80d55400c80d160354544281c00e102c1413100c0c1c2000102c40e07038031065901c443e007003040713000d51494607540c0b0417151040142c100c82250140c07581c041000b9024002288020030307100e0719000e14182c84080a0241604000c13002a081c0d5405200340c00000181601d50070065690170b2009404000354810700c0398400e50300580d54610100c404401c01070741240d801591210420080c8203207081c9620b10450104221031041c4001b10205000344240c9000c0e1a21461126040c03c00d104000c3c41c04c1580321074601c0c0e25040902c40c0700c2000d80071414681050220018507030008007080050350520309641044401e18100701013011440d880031540034028029002d641155480b4803007020511215600a07000c2501c240c10070005040c551b0041c03140b00c0c061207000042d861424520b1401f991540307002c00183d4410505401a07107030034840c1c074840f8401407420b03d0003000300340e000c43d140303000c001d000d0b000d0281e000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 484215161 1250 484213911 484213937
    0x80a080307020a12090501020d050f0708031906060305151207060e040605060705010f0509030301030c12060b10080406061e05060c0109020612150108070206060d02030f0a060501140405011203 84
    0x200800c580503070f4031094070181c021605000601c2446035128880c0103104274144591580d020b00d08549450b42c05224503890002283c0340d04210b940050114228003680918494188090740b041002070b052503580428641000b00c040e8105503025000c092158000750310203417491000080103403c481160901403022280d480002e00144210350242f1782200002032040b040201c19405406861440c6100700160b4603002d40f420b680f40000d02000700115040c03481408013004c00280303151031a1085002213a4a03109174040f84850381c017040f0794000305011500340800c101c120b02910020b040001035000440400d055002810318051188070300454000404080c076400c00e400080034560080d1402e40c0d00c5505441032000e100045401c2c05041401d1201884250321424815014800300d6000b0890343d1690002c204044000110880c0d240c4500c5040d0b0701907410501001d4505030149600040c0d0350b14180c02604078020480b0b40510039032400c001032000440e01c1084881c8540c151910411400c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 484216411 1250 484215161 484215163
    0xb010e0f13110904060609030803070c08040302101106151810030501060b070c0801060501050405010e0f10120b09041a04031b060207060c0e0913050a1704031b080a08030702 76
    0x280101c8007201a060030010950090220010301000c80240c8080224075a40c010807628070742c06000081c01e55104001151403103114840800b00c80b80585519442d06541e503000075030451102d15008086030041c60351a81c0e80700c1c00e10001e684201003400c11580c0103601c00020320b12600c4964240501c80c0403001003492444503107412400307580e12000810142d902d401e19414541c000700e000702c0707600b038030781102250503070045c0a28000c441c41031711210300301810900156100511010003d4000074001030112990b540c20f4101d8640c010700361035211726030b0401034108040e6000e02c00d41c5401210070005120000719421441a0f4400c00ca1641907542c1d291441c08907124241088080c0300822011001800e1000c1c07580100ac64910801d0100100e0344082d000740c80c40b41c500607a02c2c6d032007e030900004244040b0214000340b5184208142d480701c440c3d964502003100407120900784160400b2406008105c1d80c0342e0076030541101600c002c40c10b2440c000741e044d901e100f9100018030080c0c001c4003207621680 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 484217661 1250 484216411 484216429
    0x105130b1b07020316180c080f1f0b0301050111150a0c0c0b0423010b0901090b01020c1905041d0a0807020a03020306070f030c031808070302070e090f010f0b010e0f 72
    0x70b80142030303590100f90308000d04e9812815000c0e54000c1c1d5984054100c0c400c1c1b03d80300e0003000380015261922182d50f042c0b401401e001d0020703e24004d45a101a01c01e0f8440743d00403200d006000102e0a0540325410040010f0180c0c0c1e100b401c02c411603001031195650a5100038550358005100e84c80822a0044404103c400e00500c0b02c0050180b041c50080c4801c008840d000c4900d40c5070501581e0300040310150f06142a0345149100640040c1208018080d201c0c260f045881c01c0c03001801100c0c241010200481d550002001e20308615909003c001d204a02d040c3c02040c1e00911403001c0da0240a9502d00100e448107140382000b402c08a002070b40350110740791000b85100440e00101550494545204040c183c107815009000009281c0310b401d8510703500900c00c030300c001004110405149c0c230181e41d0300d803a15846048140c0541c1b04030740b400240c04540c102d40a2050322810068604075440c200b0300d500391007120400041b128205031401d48a80da2024400004d050b0854000701c0404449000c01c00610b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 484218911 1250 484217661 484217663
    0xb0f07050604050102370806010302040803040f140103050c0d0f0b0a0902070b10080a0b0a150f0f06050901080a0f0e100b0a05090705220b04060801080105130b1b07 72
    0x1004400402043c0001940038101c08410f03982038600f102c1001040382c80100001403204851040315081044180c800e01e0180c1c0d01c114181401850a9110040341c2e02e980c01c01e0b40844292040a00180084480142e500340020000c0c24107203d2420900201403040c01007001d09610645c0c3e460140940c84000d03003081da0a1070014142981003911401080c001e94844941510291a290003103560601100c042c0b00884417200040c02250303040f941c542240d0b048c080e02c2e2580140d2500010050410030b280218005e04c074a0861080e0a850602d1030005111246e000109003c4117210702da2181e42c2210100368045019200001d0180040d0407840080c46c1d042c0c014070b114400e100340f90108541d164050400c042e01229224007642d5250101f2030094800c9810000041d02030242000084012460f41c0440000c0702c0924925920b03006540c806800550012001a80078801049044028850603400c1003500000454110845e211740813002d00107848202a0b0702e106801c82c1110b00e08805940300310b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 484220161 1250 484218911 484218913
    0x140a02151608060f091f0f060203040f0b0f0a0309150c180b0702060702090912030c180f0f01050f0d02040803071a0403021015030f0b010f08160b0f0705 67
    0x241c1010001e007105440c10303203074200c04a02d156020407242d103418465100006802080e5241d155656411482541250503070466009506030000c40c082000f040340340c0180c10329900468a031072a1a840751000d11440d8085903c1d5142000380070a444d80d014202e440d440d213181400304403400c0500d8100481071202e0300c8002070914114411541640c411807050401c40703403025100b6043e4465030311031442d2243c964020b5004200300070800050410054881c0c0c0258000c00383e9043c10f0202c144607209070f04c103d40c07041d40e600000540e0f00010400c1d11003840c4080d0103480c080c8484003c0000b04000c120000301c0c10307040c0314000c0350140b086ca410208035221410620019920307560382c0d51140b0340ea5042120101c1e000214861120004844500c4951159804d80c0c02040140a60018000146104d40320011075515a140110102e00800c0d286440c0d10320403280f100329580341504101151045030030211658104c5074840b11903076548184035080c0c030015200d0f41e0351161044480d001a00c54568000d103e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 484221411 1250 484220161 484220203
    0x305030a0c0201091d13080909040b0a0f09030e1302090402040b0903071508040803060402120708061f09300812010519090209120615011e140a02 64
    0x4a90340c46403414501c00c0c400e8845150b842d44546200317550683d80c03117050700844071031030010703800c225079500d400009070040c40c0c0c41e440d08891801103400c54604079410b03908015240180318400e0640d105001c4400e0000001b0043d001c071682c1c1c002c3c02c03200c1c00714106120b9100300c2024140061194120381d52003d00402c21940d807a50343d083c1814680010700301c3c5200303000c3e004000038007894050040102c0c1c0c1d40ca03a1008000c0e0345980c2c501c02180c0000c0c2c60260807681c284490141040c0710020b250007050641c96221081c03501c44100044641501d00c4546551400200509115001170300001510001024803c0d13040400490400c103264081403035001ea00f00c100c28105001c0303444024440d84e1002114040d15030b884038280482084030f005c00782c00402d0f06080030040c90585a018101144004146200c0e800e40b01003428545107040e0346201909080120610456030017140d03184240292103e1070151010304080a8685c4102c1a0002181800028002d480303900c2809412101d6071296010a2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 484222661 1250 484221411 484221427
    0x61b0702061c0f15030b0c09100f0e040203040807110109260109083c0706020c0a0b04060507020714030309040504050715090e09030915090d0204110a0816081609030503 74
    0x4d03102d440381c80107031400c0f5505404030b4562003541c812150880b002405640c40403a40c80030480321083c82d0750501c0104031904940c03044c5039999000a501890080513015119641401c0440007800d03110a0103060086040040080d4603220381510101e180550000035032020041059024001c141002040501c00041481c00c9501c40681510740546809852043c9000b14441c0d94954071303800e08a5900710801e00c1240d0002d401500200000d07001801034034072603602a5520035500720305540403526551184100f280c01907041084000030013140286c10b4031589600c0100f522485401038141c0926220400036041c00400c121040c0100394042039129030200d92040104128014010441c0340c6c0c50f0326020907040c010001c00d4491a401c000c2c8200c024280520780c0001c1c3e54008000f00d41c01c200003805180142c1d0700c82c1300f00107400391600c40d0243d8908418030700900880c1c0c01042d146041e01154240c3c0758a9a121050541c8036450600c1c0c40c800da5003142083c0c0300c02500d0b900080c8a48000150a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 484223911 1250 484222661 484222691
    0x703060e0f01050108070308090d0303110a0c030e06070804090507050415030911011716110f03090405010e0412030c020109021216080f0c0f04020c010509061b0702061c0f 75
    0x1210341c41c6580000c104a0b42c948005607100d9650340b00203801c2e04020f0008482910342140070000c464400c0c140000d5864100100740d00ac0d4002c6414030303020866105002c1c0916401c44200c450811080b25080e15000c060b641d410b9150089010f00009640d40e60001200785020b481101d014001c06000d8043e80c2e101c1000090141c000f0800884280026260100b6154024803541800003114076071441560f40751aa0400105440e215a0301044400b85005201003014024a0b01064140c001b4555804442080c401541c2040e80502ea0044004082101181c030046980314250360360300d400300c0d0740d800042e0105c1c00f400e103014000c0e602c000159403040d0110f50028a540c000100092015011079507102a20349a50000308100c0950300b00c0c426245880c5408842c1c600c0400c401000103081204429200c0d08644040720580c501e13502060a00514011078485015050340c40d0400a18100c0c00e42e001c0b07030542c003c0130a0409010031801c4c3c412014504d580250034914a40582002501d00c030a40760 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 484225161 1250 484223911 484223923
    0x181a0414060408070807050705060d060303020f060c0406050a1701150f031104061b0c030501021308010c090b1b100b10180512030c0d020106050f04020c06040308090703060e 76
    0x4440140a414603800e242402044262066400890241c2018000d49400c403040d4071a44003150303a0700502c100842d480c1c0e1440042d00103224a41c8001922a0441c80e01915000100d036a00d40c150303000d4420010f03901d0203013084034140c90003450429111040d84e8401c2d02c58040a410b088200c2000c8000440c0d15191255802c1649020750744100c9201d050740026401c60304150303000881d08104002c180003d0f40101d44040c046500c140303c07100114003030384800903198841d40040b101a500055044028840d030200f220140c100c60008006241038102c026040c1c020074814170750a008003144000020000800c0d2a0751209841c080e00e004500d072901030002880346001e258811280803c201403054401e44012805042c044200c442d81810a0104540c420749a20b254a1622040017040c08003481401480d05502e41c940000c43e803541000208010b070740e40d980300c85000341e00c1401001d072032200000301c05401c16050300b00640980c0f00e40c00e1507401e04a40f500050141418148030488407a400104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 484226411 1250 484225161 484225163
    0x4050105070311191101170105040b01110105040f032a060c031b0c0c0b0f1206030a0c03050a030906081510140a0801051809100213050418031106010f0306181a04 71
    0x116017165400c0b840103465828082000045500c40f1000520003420698413048802c5814100a0780d0555680e038214252502160101c9044d54200d40394010550800c0600314007012400d0b11200d25006811100d182901e1818050100758641c2d0074400c2c040d00a9121444011800441c402800075890000c0e0181d0b480040c2251419050000040c500100006a0301d00546042c811890800c2c00100003805207006000141e150041900d410005007100b001c14000303504c0b0f40060300d110419410050040c80e030507485601400704400070020030011404100c3c26011b0101c076085441c41d2014000c0340c0a910403058030100c0c12b800507840d2086078000d04440d0480780c045500c11545041000340f0103131000d066070050f1055000012140104005401030800d0904500002c200e207656a4005410355460302c880702c89008101d6216030905601c002010111410302d8000c00d150f52404941d00c040035168800600007590f502c0d9050000d00c4050110b15400e42c209840301c500181d0000308060b05042918 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 484227661 1250 484226411 484226423
    0x9010647120a0b060d1527060e10290f09190b12040305070b0f01170105040c170a0c0b130e070c080903032116140405010507031119 58
    0xd0790403066014101d00c0383d6001d88a1820310720702c10010405060040c010651a0019034408204c540f58211046007001d8042d8071030590304d500c1794070002180c009821504030341c41b4080c104204d40102c0040d9100316400107022200c2080e070003c58540281e109400311111550004140c1103070074854000d4820000b003241d261240841411055440004274480c240440205104081c0400b20341c094499002f03019081041c43c2c58559601d031005100111182440320120000510911000b50300842c1201d10700720017000203060648800c8180c0d101882042d1440302c84600040280c00144003c00080d039105402460007510b5004107451a000349801503100011001c00050130414507060b84c0c0603405a0715442c00c202c4040d254411035510801d90160188400c03c40111200348090361100c01c2c038480c030300482d69414061540150744034901ea45204102c080100d450020540750b041300c2c219482420100d1340c8145503d0103403904173750b0002c003001e18014685185803418039081c000d00c0092040c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 484228911 1250 484227661 484227697
    0x2109010f1107060f050d021c062c0603121303050d1d010804030c02090405060f0a060605121e0916320406090213080609010647 56
    0x110441d80a10303401080c0c619030340101c0c0200031641c01010000c0900c5600e29240307113080e1031515134506070390210300c12038541d84c400f0032003e032100810300c9144081c11007980203500c4844000207502c022643c40304405041c0300c046002c65041c0d07504204c0b445003004040c000b15281c00300d0041c5401c070030000b48819140c034080c1d41000c1c024035116003401030b0080350075050b0401c1469004011140d00400400440611101c8554440941e48003108144654030401c02030000303140c5412494513180d00544912821420484103000c019044020340c3c0c05540300080e20300941c0d8030314030040300c4122041141ca803035004410500200342004a0a8110148074403031030408180d450040014003802d003211500140c5d08111000303103541c482005192041c2d0014004600c21361501d14540480c0e01c0700907070984141a2080c01c000c101c6007400baa56000c0707024802000014507000503081c9401c1010307120300050b010381501c99049542c0041d00c0020340d170212080707401940142c40940059003d5500d000c1c80030340c07417 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 484230161 1250 484228911 484228937
    0x6061903050901241d090622080f190e010903020904080d05070f03230112030c0507090f0f06060c03120e060a0f0515030706050f04050402030424090221210901 70
    0x307001c505d0301454054006105954642d1110400c99180660410050490f0015a00810302039000b03000310340498803403a6500d10440350b03c0e036902d82002101070140b00e15080300140b16030f00000920112501682c0c44030003a03a45151800c014805d1540140b42d02c4d2422041c804001e9002400740c40c02802910708100800d255605020742c1c06c490703060040c2100c4038030010b001e03140712800c690850134030034105517426003890354400d801e00c41607802407690359a44d0580d070580c0a1950144905400c01014100310550501c64010b2803200900380c0034051006900c1c43c000841d40a0f801341c400300f9008002c0d140e0b103042401011000d800b0320030145c5030b01d500700030100340c090351762070b62468a40700000c0c000c2410a14101054410360000107070210042c006100c009100e480b180021442144100e1289020a841d1072000da1101c41c11b80c1c03d0042c0c1c43c509101c0354010381b1009003840c142e01c203001003140038000c1440c409150039040490400711000f15a6800b0000002c44090039809000341c03120310301076081c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 484231411 1250 484230161 484230209
    0x7030807032c01020702030f0f0c0109360204080705280e0723070b070f0c0204180501021314010e010e0405040507050a0b070303050606190305090124 66
    0x40d01c40c00e1a440b4880c84002c5400c0700c07041c0c520840c5460301d07600160405a10360006030030508002c000d41e0302030b08480b102031503040e000e1101c021020001d0030041c40540c10070303000100c00307203081c07280e8860b80049421300c241d41d14030b07880880c500071101c0b98250355032a101e50141d0b844502c14403404d40508045122158810942c03400e12040240804850741c074180b4144004071014030141010003403107481301ea0340d10301c1000035004428030050840d000c0e40d1030b02c0501d0000e0180b04010315500c108070203c0c043c280410340c001480002660116400b050f54070002d0504090f50301c030490000c2c415880001c8610a03444062074503000c9900c031507190740004030100c00554040c000c0562880c000740c0905204400317458180c2c800b68000340548101d0b08815158400310b002809650441d690303101000c640b600c101503150003016404901910340c03600701008224106100001108240c0905840b0300014120810035130140b161040c414070640781005180c01c0e40c00e4411800d005140224a514910100f0101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 484232661 1250 484231411 484231421
    0x905041503020f01081b070c140609012114090123060a060302030a020f070506040b01270905150c070614010e0415020f1305010305070c0206030703110403080403080703080703 77
    0xb4001d44100301092028004540c0c41c6001001550382d00c1e02c481c607221124010f1000780844e184140307102c0c901c0d9030a1541d0545010f00100f4a0391240504019a44007a40d01004030b104500ea91040809040085000c54001c1d0036402c00780c0c12226a4802004801e840540203400e031510006021404014031a141c8440c42404541e00e43e0400402841040001d211740d005661280b61080018109603080003401d405a01c00401603415911000511040c4811220418014414002c0424690500004a408030f4041c032800080035552080360360140314040c8042c0d4507040d4840c461010741c0c83e1030403521390f503900144025174203240f905d00000a0a4030000425043e42c801d07000304076441d617469440c4020241142d1040c0c00883d004d02101440e51078a6001d4901e622024842e11681da090100040031901d008080382c00700000d0717034803510241e2540030803290800b03d103250120b00c9150051003a00c2621441d4030050018a0000703000041c444020060b02c0030600c03a5442c0c0780c0d1925419802c40c1681c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 484233911 1250 484232661 484232663
    0x504050309060c0304080a0807020112092001110114070909022502010507051b0925030b0d05060408070605090d12200c0c040c18030605040804050a03030905041503 72
    0x948200507080092a120000d4110145400100ca140c00d4841c1d2480c0d04104128800310f40440d00401ca920440d0b811500f054800c283c00c0d0010810001c8680b01d103481d2241280380381c103842480301044c001c1a4801e803040d9446005510080c44035218641201c1e507445c2003101c5410014a8030000824900c040e4021294824800300140a0700c01000d1703c00091010300c860100c4c144142040140005001400b24040070614000d9221402d20800c080c0920414014800f5020b4602441c03407401001d52100c1090610201c2d1800052080a2074040307026802c1c03503440035090b4400c60080000300000540145554ad109840a100544603c03800641d01da210f8400d01c0080f0341d1002d9401030310b100680c04485100c955404c01010801d0090506007035501c1010b5440e45908040c542e09200c0c1800e0050150030801490001c445240314500700c101c501c040c0c08014500c5441e480801d0511500030151741c080c0000501540300340ea980d00c0c01a003d000f0a1103001d0140713080c03120404000040a072359208903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 484235161 1250 484233911 484233913
    0x18010902030a110301060317040503070f0b120406180609150c0c0308090111040305010b0123092205070c030305100302090c16080a11070506040b120415090f03080a050405 75
    0x1c0b5666910842042d03482c0c4010342565945000001258195040c20749040c111559a65190706000030b040c182604c07604034824620311030f0001c0040f00307418000c64030281e0040c2c403e4a07083e211031500c60058041000d103c502c0d400d0400760842400030a9006821140c80b45843c0c43d03840d000c110300c0e0415a88203898407004100313100306001c04070780980605980120003034000948402c80280c080000d400c02c4d01b041e40c0d560740d16403030b03c0c03800e580003240e0215004403c0c02d548035894014400709903910a000500d40104400007900d1000b0914003e040ca440901e0001400303149040c2400901624200000b40d00003030502001c07542132030604c01c1c80420740e0b401401240540e40c824002040030342c0503466148100f290280c0c40c80c0450603170005400314952036541d60054402c03611895152075519000300e8861181000100a80c54541c801c80e01c0c44880741841e00c0b5103640f01c0c00c0901c007680c0103515024209007055100c0302005403043c1c02034100c074803e8036401615181d25241c6411140111002005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 484236411 1250 484235161 484235173
    0x13050103051501140a1701031110081015020304182304050c0103091a2e051c03020a0c0305031201060309121404080f0102040905060d1509020f06121801090203 70
    0x5901e4001c005d01110700242000b24050352a1000145000d01c2680203072151003001c40084010f14141000c440c0003529490311858070300f81541200420303603291098001120090780c5002c0729034000d10650f80203001186201101910060030301020b040021541c080748480060b1801400c00344841c1d06000c0e907000b1000306009060000190001c15442c4c0065a290590030420402140154510307841944107016401441954280c40100302c0d40f20042c400401260540500a0751103510040404101c02104a44035000f90b05080c1e052100c41d070340240c01401c0c1c0250104c00d000000004160440203000409000da90b100d2040381140c0380c00d00010400801003200102951003403803849900f944007000b207494644d0380c2d581030740741c1500c0b4098124940d4005c201041510700a200b81940100d05907981905d21000d03544400890544400701800555640c01c80070541d10b44800c8a2034844003c0c3c2000e6451520954150000b4000c03070341c4c1404002c19400c204015201070040804003030340500200301c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 484237661 1250 484236411 484236437
    0x210f09010b01052b1d1c0903021c03030209060d02070b070507021c0c0915030c0f0503100c0302190206040203121305041109030706261b030a06050613050103051501 72
    0x544990400342213110340e440c1c0c95500f0f4010240e03244507014850520003012449544100d00c01c1c865034080310081401507012007003016032500110780100d0034042c400c860490040e850194024080c17005050b4200b0008a103540d4941000d40c01814424000c651640140d5036480c0101c03820320a08800a401043d0020481400204461481c001500c50002d0350056902e40d2024401c81d60b11030761940e00707086200c03c20070a01c8071600c018005820f20070078000c40142447d000c281c0d2581804400e56015543d005030944072840b0742c1c141d91101c030701c032007444003a403000c1c101c000d41e181001da500b41e110703001e01899115210700200403102c1d003200306903040800503c2c040c00c00004150f55481c00003120403c00841e03902d69002e00165010346410b8940e0341d03c5131400c01d003104001c6d005040029803080c3d02001d06c03c042c00d01c01c0c0205540240580c00c00c0d0380703075588917181c4040e1145510164010f4004504040060f558400c1d02d01580e07030070390b0104065901c0d05114055200152032217804201e444910360 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 484238911 1250 484237661 484237717
    0x40e0a020310050112091e020f040c14160b070305090d020c0109090903030b15040312081005040b010c02030601030321110301050603042117070c05060c210f09010b0105 74
    0x41c0040d40a0760000070300040a0301c0d8002c550607100c0c921983d48901c030003c0d20452030007500d09000c0c2703142984c08004480c0f01280285c5822541002020400d802141c0c656801c00304c0000550919032014912070039061041025000d4201500d030405680140c8441d01c0100d8800103800f40d8100d41699000c20441c54102c01c3c600030014008142c040545600708415503460781c80d0315090100c03403020200d42e941e1544c00c08003080c003502e242100c1041010801d002c00d0494203500c0b00c060b51412100003942d8910880181c07940303110349034000d4041c002d8600000c14582c002040704591010802d003249040c00e45800302c0700311036401441d40b180708024001401a0305000011b5a441486012200700340d41c0e900c503102d86012074642e1424001007076401034910740c410240100e50868007504142c480080c0c07e59171a610741c40001e1615038081c0e008108244402d54440140221414046441c1c0407403d1100c881c003035143d411180544190f092209102076940700340b003152074502c0c2080c03021a90400b510302d85 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 484240161 1250 484238911 484238927
    0x506011b031107050306040f11061201032310060302041a0607060b01182d050d121e081e19021c0c02030d0f11090d020316060203040e0a0203100501 65
    0x2480c01c2d4424a803021416031410003095001d10301034410200c800a6520342419276600b0340040138000c5805000d0000c4a00d803107240141500d5110f5a00c01d00624010486504507485100400c080e206e20804500d1040c51980001c050302e00a84042c00304107001c00588204c0360501c41c0403030700520304000d80e90218146038800d0f2240e84c0149054101051442d809820300401c1c1d4210345c480400b04654402c1980c0207070340d6a101410842d034040e09d90b0340f404c1c0024015199502c0003601150850080c0000c1a2155045040c143c101c41c880724403001101200400c00f038421900c81c3d0740668110580c0740c65406241d4090302c200001c11070719610f80082a114006134002c0c550284914900b005079200002c01ca00840944003070550003161104c5000f082201541e07e41c80382e070840b8500c4c002030394240e0f980d49011280d107008141c4038001210f0027440440c1c0752418184049210703405040700812100e0340807000340b0803154640c0c40308402d6120410010100e00c42030b03809010051241008001325400340402c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 484241411 1250 484240161 484240187
    0x50306011a030a110f030a0e07061e0c0b0c041701090b041b0f0e0f06100e0121050c030702060f0f0711030c060a020406030608030f030106031e1109040506011b03 71
    0x1002c6543c131190301306824650800150340210090100400443c5001c5100e41209100a1802070851610b04900030300060024416217403a00e11140440325007500903c43c3d1811315621030307460f01151a01c0303c16101190024000c1e003141c0d03542418440d01828050280c80d08064200e54091031075140e69039011400c41984d111a103c05001000003d083d0701041a80801088845500281440c000e80c0d11082218028891440780d11028688100254084c4000c1d00c21542800d0601d0710300c40e08020b04140604c1d00e000805858100350130000c0605d8008003540c05114181c0880b106a29000c41c51816030500311420600003100c40c0020303000da8490400d4401c40003026040c1e03850524040c0031789090400071a400002070b5000102040306c2a410700c550f5004022a07406941030410307807407400300548818400e0008140d110400b224070340303441d411b0b149640802400d040115103914404031005402c0f00003031790303c02ca28120010300a540100402c42290420350409a1410304650342515101c4c15000c1e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 484242661 1250 484241411 484241431
    0x91506031909030305041223090d1b0f0b1204080d021c09031115132f0f04051512071e0801150803071e0602040e060a050306011a03 58
    0x15403608035007081c1c8a820b14090103070b5800301d800c1c80e050600f29680300c0503c060800700315040d552041c0800604411040c1200b0214031a59100300ca140082e0b8260b071000c10280c03070580c0c50903082c541e070340c1502e115004540030501c00c4202e440e5907a101c1d00050040d0740c0c0092040d541a400240014403140040103100019000141400b0202507020303911010f140081907956a10300c0c01c8420305d0f411013850020030234010000c201082d000160141010406000d000c151102e140d07100c0d040054080c910410080658041115100c0d0000074510702140100034502440c41d588000282d4101405410310544995886a4000b0400c0c4240107500d82c8000071071070700e4001c1d400049104002080c1052080c41c401c2e040c00003013803d168010382140d080c03854034165049440010080110b0110688055981059007042002900c500240351060a0764000700f0180c400580400c20300d40e5031a02e60700820040e22130740d030f0032511030003803590b035850a0050441000503400116080c0420000659118080813 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 484243911 1250 484242661 484242691
    0x6060307170106170a0501110c0a060e0307020d2003191b0e0c0406080604061a0f04090f0603231002090f15090306090a0305030705070302010e072309150603 69
    0x580c04030f01c5100141c1c000d1416009841700c0b800b8840240603c0752030b0703040142d51030303e440c0341044095910429400001c00306515aa5542c403490000d000b134a02e213030b402800444200806d4600b000d04000b840d0303179036071250f05029000100c904000604800c00ca40c40703426040009c41c2c58071258440104101e111030076000301a0701191500c221030803540101e02d00d419180d12141440000390628600030204c1e80a00c1c90220704101c050364031018001d8003502e1108076990780e850840d5103611842980c203c100007034101851000d520031143e200b2030884c3e0054560301481e5600006608900e0003102c2c6405481c1e010700460120391015a00074244000300901c01885020309502050581c8840c1503240040a00450005d2841c181403010b55480040440581507240159070042d001e0300028040e5000c005001c07480c081094002d6000600d01c0c08250129203806948224140382804581104004042868078000e402d0902c00c403028000c00541c00e12605000c201c00500426805c000d0030400e41000f20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 484245161 1250 484243911 484243919
    0x1510080403092d0305061b0304050c150c0a030804020f040c081b040302041b030501080a080706020d060503011e1b140901030204030b070809010b0108040308040311070506220806060307170106 84
    0x1150f60440194442e8016000603e4605404c156040b81e140070140305100803c20040080d40100c1c8800340c0c03000445400380c503044070683c00742040c01030f09802a014400e60a02c4000d05800522441c8600d100710390341c43e48003a10318184016507107107001210115840d000800c500074502050100368980851481d4102552500007800351607090303015a2032150300c2d0525050166040c0070b054007509143c0c0081000c04019a10380d10030384259000549501d0703000c40c0f10303a170b001c0164004070000c1c00c0080081c842480e0f6113007210b081094940241e42518505241028240ca1100d007011070180c564403845811025403903101d48580c4455901810107a0810000c800580c40015017409901666220070301480c00d10149401c40c0e58443c0c1890600401c80200000a03a20140541c0d0050381450716035122038031103405518042058000e00d0b481017000c120f50f41546a07403d481ba40020090041c40c0d107040d6240d41c01622081c0541c3c441c1d0b019042000e051081310b01319503003d81c651008230b000240d401d0392 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 484246411 1250 484245161 484245239
    0x90f200d0602120912070305180405070e0f01090609211e200a050609130e030a02100e0712051006170c010806010905130b0603151008040309 62
    0x103801161107079800305101e0140003580f400e05501c115040010328400048600d44105405003000c02002c0083c0040c01e910130600d00c40d81306580c050082d01c14803103810f0421015040d0004920710751300074401801e0084c402d620a91046088401c10b4030b40320511802c0081040307465110721180b003d000b5040c540100000c3c10b140e20030342c054a00c440403810900581c0fa1201e0f40c441d450160303003c216040ba00d0302c182c5950354400c101c01c4602c1110b10594410170100483c9035a0344004110075018500201040510710100003401030030016420340c0d41c116441103400084a11840300f400c0c03e0b900c01c100030320100e0040346240348102c0c003500456610301455040d54040d1442d981141c0c6200107001903200c41d00c0001c20004441c0402400c1a08031071400c0c40000340a800b480c8182d51003105012604024001564803a0b820303000081c0205540c0d28020b0303242d80c481e00c0080c070501d0090146c4518460799034840d4078168019941541c50280c070310314000680b50400010840502640003032440c144040d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 484247661 1250 484246411 484246429
    0xb010c0209041109090a050304090c030b0a08010b010e030f031602121903110d140f25020a0b0705030a0e2106090601050d020a05090901021b070513090f20 68
    0xc850300d003003016150510305000d0713184005041c9284030b502641c0318500050303020003601d0a403542010002041c0d0b1070a01c00702c3c05000b160b0703c0a034000104403400300342c101040d00b1202e200402a29504d00c00d10104003415514a29929001265042440036413000984004102d241d680000c082000c9042c03c0c0f8034050070038074441250254119041c900d101007540041c0e506210361189005001c100a804601818040d502425140c8815000604180c03401e8104d00361040f004840c1e500d25110104000002410100004140d204501d99403001801e00f00342400c8988181c0c0c400084c5003031003441941910011078211800d5070191102c5404600040445030211090400b503006003040d08100048a00340ba01c1170300003600881c040220080503886001604080f40c03400d83d91140690340c0c45140034024043c0a9998505070315068511072407034400a4010162501240c515000024100c8640100c600c03581004010061203151140480e0b0742c0101014804e035100004840760f0882800642c00310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 484248911 1250 484247661 484247663
    0xb0705071202012006010603050a02070b07080601031104080f1b180c04030213051006090609170312010b0703030612210e040f0c0801080c0a0b0c0309150d050f06130b010c020904 78
    0x81d000174010081c0640c1800341e25000303612041c0442c42c04406403900c00010600500420600203e9004a0300d243d01c20b0341b147c100301c80344582d06901d4648031080217445421400441000f0302c19141203211180000810071a02180200045580c0440003180841c20750010103508648000b880f0010140e112052003001c25401032000203818542002c41c0b00202126402030b10070040b2200080c002c2c2c98000302c071441959244080e0303020740c0b440340c02a80e01c5d521401e40285c000c1030040000040c0c0b441048060000e45120303880c00d00c2515180c1840d54011142c115003c3c0209016119000a00400a47e46620791080d894030b458101c03080004101541c1d8401842c0d489541c3d6000800c811642c0a60700c07030b0160825102400e100303050034000039100c0b00940074103444c1e00c80014520f0381c0070742c00b00101d4002070005800000d2800510f01100c505030480000407a0300f5041c480022307402c070300c101d075000d00c80c1038001c240c52080b21a111040c0020314602c80010305004801000c5805139842d1040d082c800c0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 484250161 1250 484248911 484248913
    0xe0303040f0924170a060903020c09070f0e04090219030b150303030c121f0603060e060105090a0303030203220602090a06110613020a0b0d050603070b07050712020120 73
    0x503882c14960720201c601d014014204901c410398011042d8024042100c11181190a884403141441c6121810207a0a14000b41064603207000442091780100e03007540c01403011502c0001d03d0362111403e40d0408240d02c240d40005000840104a525290303106910b0361780090490200a0311070010030804501c075070000d07100d0136050810003140c800a01c20b14112010150061425801c1c03240a00e0420b00404040803182591007002825032444960030006403010203e600402c04d42d10343c4d01400030032075402007032002c42d0220000781165020b00d0850701e0903074000e00340740115032454030b0880081d040074000468050002c101c6941e810440070305800501d001c0c42c1c1c010380c0c410305a400c10460030000d500850a01000c1c820400381c540b400716960780d00c1000c02c00030640d00d1025200045000280e5046212841c1002c42d046007241e40395444a07109000981c1142c03011a05c40400171110300541400814651200d00140021140c40c03401d03062261060408810150f504070b054400188007502d0480c3c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 484251411 1250 484250161 484250189
    0x7050d0315090b0d140f03030a0f0c030612030c0503041502030d0f060e0c0a030603080a081006051603030f0e0106030b040b0a02180405090c0a080d201c0e030304 71
    0x909030316820088000c00e901c502c01c10018003600c0101e0307a000403409018002002001d0301c2e400c03841c400e0015000300e800910640e0b071f5a00c1e0501c100c070010141d00f0180c0702102c2c82c015442076041d00a205007410f440003e20945044201503a00b10780f0b0382c512603012240c5000500c0b00091042004e00382e40d425030200d402944d221105015283d086402a80c0280c90413810544100114884481800c0e041641c03c105c00303645171140340085d0080c017995440148030480c000b801c1802c3c1a40130609074002c0c1c03c4009894100ca0391003608070340600440e80700d2550856500e08400010340a41d2001d4682c05d621000450481403c402190858506500c00e0300d5408840702084100b0613203104160740300407501e1301103007030503030240104456800e01605280160742c1ea00210790820f034100b10851503103400402120703040ea01d0350b803c292a09015044580072800b07280c050203041601c00c250040383e010420050101d0485140111346030600302d032402052020225016403162018030007800500303440c1c0880c886d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 484252661 1250 484251411 484251431
    0x609091b0503150f070c02310c0c020d0804080604080c010510032f150309190809040915060306060f05090411090414030f090f0f130b1c0606030b2a0a0507050d03 71
    0xc007114007405108480b80f4281c0b1a45000c0d03000160ac2c010b40b0b80565111005482c286444a401d00c41c03a00f000f0f0151082200304030801080100070001450044001c0c4000d440e009642d1030344100500006040380a1003121100d0130401003400590710801c1c0c6070740018901e425000c18004480e1801030804110000304100e500702080000c1d00c0081c18400d850000310b00551a50344160140f5520203100e55201c5811009002542441d83c90b4858180010004503a0700e00d00f010041032144140949207101010000345840c0035400e103032180e034202c3d0182480e045000c0805c44546030050003182c416104854121041008202034929482c09490003652031400c0c43c204181400160503551241e01080c100807000d1316228a0048076601282004c85c26112500008014103410b01d0310034a11000400b0364000e0100d05c2d0805070460303001c1d030b2103140c2684807071001c031403049424403e90080000700c14141c6103034855000188500300640c40c2c81c60902509940c1e41d41041d03d2411010000794460242c0d03c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 484253911 1250 484252661 484252729
    0x5090f0412110a030c080c031303050111070b011403071211030c0a080d031109030109080403110607020a062d0314060a080c0f03010609091b0503150f070c02 69
    0x80075015800c0c040d403001020010603030b4415403014020100024000340f0802c00c03d0150070f4070701c0c1c075812009032921903940d02c00311507260781e280c8410f4a0660806013030607500c00b92081181d03a11600119a03002a07801c085100503441411f88080c0c2d05071068010000d0880b01d241d00904406c0e00c01d80000c0c1c481c0c804442014034000c40540558496a000c0c08100510b00d000510454400f040d805d0100c1d0400f401a0070030354038020078a1090f003550a003003400040010290050080d6480b42c4040b500034401d80c400e1211501070260000d4105404020502415028494020211071410031a4200d150900d070178410300c150205042c0046600c072020500e00c04801d800c80c550016080c1d40024003107242c1b1704815542c40400c0360040c01108440c8001c141903c003034000e10003a080b0501e05201d14003843c81c0c2158022140b9114543d0b82c55040130116076450041020f071202926544182d0b026250703c1048088198064002c5051081d6107840b07000588492098494144000ea003042140c40703258018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 484255161 1250 484253911 484253933
    0x10b07110303041d0a0b030c01080a180c0b0c250302192615091c0504080106030c0503060a020a050d05060402070c06020f010e0c090705090105070b10030210020c0a0e0a0605090f04 79
    0x45c1e0700c08d0f0003807652039044e642e0165010f9030062048601240b900907000c07010082100d0080c01a02d01c03210b80038082488120710000b000c0100042d022640c110703803020380d040d0f04c8190300050910324a82101040001d454070120b034100012194001141c0c4903036914001e0880d030146002d20070002d4008010211300700003444035800015200151100c03034540707800041e4a49003911081d5603c4010100485202c501c00c00658000e005120b0081003000e0301d034248915250094481c1034400e100300c50009080001074003d44164290a407585818902d000c900380b000f41c01c008101c00d400580c24070603c00411126030441c0c00401c0181c020384081c203c408045800c0d43c0e80a550707080c85a02c58074450546488040e139865001c5906d10700582c03210068030040b00d8a200d0801d01030903582800d4140700341103058070a01e104491085420090071420400281d8640500c0ca0445501400c0301c0e0082090340700f107480d103592050980000040440d2180300007a190403043c4c0703d0008041d0040100410041c4000d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 484256411 1250 484255161 484255181
    0x509010501230c010e010f151a0322050a060b0102070b0702090c030621010b0102060609010303230c010f020304020a050f0a120302031b03070308070305010b07110303041d0a 76
    0x2003007800901026507a0b400700520001d009040d20005000c40c060039007940101d10440c40e14000780100c080c010400c001804c00c010500d964812040f10000300061580182005a00e04010050542d612140003030301c0884c6039010302805440c6c045042d400680300303206400801e8403031840040c000001c503000a01d0200903410000d0240b80422400015a0313411042e25804130341901810f95990303800c0045140011116002000c80140b0140c01d198180c0640009203001d00a07802c03202e03681c0e0f88a04001c1c150000b84000340114480e6807411050f100718001a10001c0204121b41e4a01001c0d00041e508442d1148102c80b821743c1d000c42404110f01e42100048018801114448400521400020110b0815101c0c6c03001d01a0b10b012421f042500a00a07510710b0711240c400c000481c5401d0402c03c1e213a90000000b1000a601c840c00944064000e2069506803480d000032141003041603900e0400040411070403503030503c000c4c0030010b84c800001c619003001058074186000c090400303506d0b810036100c010326 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 484257661 1250 484256411 484256417
    0x70b041502130504090602040b0403050f0f15010603050402030c090109060501090b0403020a060516021c02040f05011a0702061306020a140606090c0f070f03030b0307081c03050c130f0509010501 85
    0x3003824802c4005078151015110101c8000920f050b036494a00020f12480d80110b520f62008140003050120108400d5824200f82c03054500c2c42e40248061a00c40c0502d03040a410030182400500c003940c1300e588159885440030f42294051507000c000a04020380c00d070b0042c103440d5201c8405010a5a00c0400d000040081c0072160b401d1600710360004a1220f0103000c2c0b0402c0080c003085072a4040c20b030318103202102d80c02400c98011962074142c0309007800c404bc4026800b49041c0003580c10340f03d2140c41860b04803414a603880c500c1c0394401300c0000f01da07404030034160381c402410300081c80045d04a0818100900640c2c006041315072082c58070301c64220030900c000296810510070007010742c40c1c940c0c01d03541c0201ca10011a82e00c0211603188807040c0070301c0310040c102c244409550403c01d6095030007644112002c070212440c155a6109079a07032000c65103007031100001c0e040040044a80039030080c80d08080c484200504100311340303107141006070307a070f502c4802c00141d07220041101d0b04101403a94003420f001c0c0307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 484258911 1250 484257661 484257667
    0x20616060f0509160b031303180906140f09060f0f0102010902040204080d020c19050d02130509070f0512150606121306112701031b1d04201e070b041502 67
    0x4851050400d00c8010188c14480c2c6281818041e590b001c614202400084404204140d15101d010000c0300c07212194a004040c03100c451006440e101c60068850310300280031841080070705007804254100300800c0340c1950348070054040169903d0015201a00440700188282c000030302e40203142240d0350305458024140c2c4419040d40d0ba4074542c03444240e800948404410040c10320104400800f064a1222207620746030a05c0744c601e034042003000440784e0005003400021703114800c100c0400354003000c5070b109a102d554160058181c3c00c0026030702032001843c45050110444258241c208211005400d0a8144221900300706070351182850403182c4603aa80d0a003a41200c9000c070100700b01e0400307090b20a5002c010a206d0b80f103a0080065480005000b15074043c00c440003504c0c00c039400315116a2500c14968140842c1071a11030410b050060f100c00780000c0754001950700030340d44000c10145050b807110b270503058800f080038001c200c11441254800316a24190405210012107502c1a004041c010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 484260161 1250 484258911 484258921
    0x509010f1809090602090307050a0f05090406060801090507031a010e070c05160605040611010b0a0b07051203070c061a2d030105180d02010504020616060f0509160b03 73
    0x410380000000c0031038103102070901841c052049020400e6070122507424186803070003041043c59006800108000e4003150f1040303440d07074108002000346001b02041c401d81da90082000d0b00e0541460b0780c1141c0074600014440d0744520b40c09003521503a43e8240d4541d80200c400b0020031442e05030340b12208186140c07032011541001845000200c000c1c01c10350801c51007005040620805202c096400007440d0040303c40c1d107550f07482c0907140b030b0010b02c5500003007040c040741111102018016540b40050090201c0d480a06080514425400c501010b807164400c81d400c0c91030503210f110082d8001d070100d07107941000303a00301d140c074106881c10513070a02ea44407100c000010341c0f80c886818240301106d40700c00c40e10700003060080164180c0b41065101d5450340c00d002c20b2005c9801c10320418076020401d00c003a1445606400c0c005d900303a54043e83c0003900b01e101044003508501189244a5000d4412500450341c04a0107840308255041034a00c0b05458005420310403171030320445010002401c071078214900310700c0c007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 484261411 1250 484260161 484260167
    0x90109090210030b03030c0d0e0310020c0d050a0908010c051e0901020d11010b030a0b04020307080303150d08040308181f021902010c0c08030307020c0d02030c04091112031306050901 80
    0x94001c800c0c141504d4203e036541a59040c019952540409021101c058041c020002d011000c00c031060f81c003a0207000203001401440d4002c540000002c41c2c000c000035402c1403800c407010f911110309001000644180811a1035007800360404031406a61110384030f00c10711030030740140c10071300800b55a494810130a50070186d0f000f0480f00ca400307009041c9289050f0400c41031502518103c040540d040c040e0051000400034540c101c940603d00950403a0b1200d621000a41c0e039a103c00d45007200415400088841c8030b1420183c140c40300c0d841090540d06042e520740d40e080c1550407155800960400300d031081c03401c0381803440208040c102d2480e071020004440d018040d46079640711081e0240c00b01101003401c1035902403011484901e50010618244503a070f5000f0903141c0d00252601801030292412011041c94445110602d441e0002d01a0034070b0459001004014500e1310700c120741c100c9000410410f256601e00c2c10035160002c04c0007655464210b500d401d540e000d0309803c8030050010903c02140c15980c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 484262661 1250 484261411 484261429
    0x70318090e0c0415080d1e050c1f090605010e041106030610030b04060b030c2d0a0c1a0907050f0409081207030f020f0712020c06031b040f030b060901090902 69
    0x682d4001030713100504981200a5901d0340120403148502c1c0280711005900c4046000240954420100540104c20040350b05218108071149a5404803801400c83c009440301b04240c060100d00000f0380c0400c03540c41c81c0079038609030700032102c0d202214100802d01501d02018088244200c0f8290703e1890040c00007100311400c1c201c0007082540d039035414903c540b81d83d40010b002d0311711403018548a1a00901c04c405c02c6e0300c065000c0410387d00721040d20f00d24179840c0781000880c4010700d1031a0b0a042070b01ca01161030800400301612240c20000009420f6502000707043d000c0c8242030080c10f9414105000e101102c401c401d01d25008038549036683c0b0101c0ca911060798034414041444104540300d81100320060314803c2d1108041074400500710040000b604010603da9124030801654900285002c1e61034013480181c05400100c1040011030a48050111500c4261f4040a05003010b40780c20b500c03070f8961403c0c1c0046a801c4180c0003804010715026070014010141c01c107051004181a60200e51409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 484263911 1250 484262661 484262683
    0x5060708010f0911041a0a11030a05040e1306050405070f080615191802030109050609090a03030e0f0f0d02010e0d0225030602030a0f050a02070503041a040506070318090e 75
    0xb90344804041c3d1044c404001c0320005d03e03d09035484032240c4d076000030195543c0810041000f15a026541e104680e0021007524001a210f484107410180b0780383c20400cc0e820f0007800e01005140039503107034001900c0d6201e103134040c03400356004021803070400481040e4039841c0d400003411644032904201c8000020107803030043c140103907041040a401152610104502031f04501c2c1d0352854103c035003e50000d2940034504072407826400b8012520f8131010711005007801d48850226030401203109010901a030030007050811b100d001c450682e003421042c6414404c20007214002500100f0b10303484034642c240034000001026030081c100c10200800d02070350722080c12039266800d21000f02204002c0300022580c00c021900100700b99074070304c0c08440040082030109042c00c6424034200104004000ca4429a903440340c3c800015840c0904011401c24078041c40c50142c4c00b070312010000410760761502c8000d4203085219882d81522240107031510b840050f490341100c45c00d54682003450b1051600015990440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 484265161 1250 484263911 484263929
    0x5070e0901150207030b360c04240b07020906120d0f03020d0504050c10260a0f0216031d10030b030703021f030f1a060c0a0c0f0305060708010f 63
    0xc0b180d4980070307801e04a2503800503184881c000c08000017002401500d90700d4001100e140300e4103400f481203034094801024038140b00c5502202506c846410280d1100340b4101107203010450341e845002c01c2100359060342d00105403480c8007140f0310045040c80c0c0301075034200c00104c1c0d407010327801e01d03135041039980b03001403203200d010429000c0315043d07118041d034111130818010040c00e01480c0341c03505010356116684076107203000d8070803c0001000c451080744100c62251010122445403100e51030600c408000c090949200b0560710640e03928840200c0c80102030040c0c00c1c501d4000072894500740a000c01c0312842d0b152840c200c0e0701d994000305565100100c024808217040000c1c0742c1020760042864007100e82c000941065020b103050302c00c0b4040040480d0a20700030398090107182a000420419103620f0419812140714025428031030749803240182049608482c101d844004031a1141d1045d4907540d84094000f1402c201c09005001c001d0040d954400f0741814001d002d54500f0a0700e0301c07012203070b01c202040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 484266411 1250 484265161 484265189
    0xc16150806030f2a150408160602120a020102040504060f0f0b03010b03160e090c0d0f020c1207020102120f0315041a040c110109050106090b120d0507020f0405040c06020105070e0901 80
    0x4c580c50403050504016000390000700c1c04481c504071110640c6c13040c0a194114030804100c0307045442d41401790016200c1c2e03603000e404410740c1c1d4030034151507412020344c0100750754080c4000301d034580341c611641d401030280e03e4078030080528102c0401c00000281d0025204050200010b1000140070300480f50000c5011080700d114101c400e000300d51014214100d030307074825101d406100044030a04050131300c0c4003030207008010301403000151030124486c00c05800e9180c0c20008000200080c40306c051f140c13183c018010740e9445240704000011705d42c0091420201c8140100503c24145444109620b200d9010b860801030180000c1c4641160041070358a42d200300d807240004003d082c4500089e58018003250024402000d591900364007800081c007030078000c107240203e124503500e0034212603c44441400b02901e02114207070012121a400b101e401d03a0404000300502032140c99500c11a44103900070520100d0079814018000d09441002e410303401007005840b2101000da94488005044554110500701 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 484267661 1250 484266411 484266463
    0xf05030615070f0f02040c02070e180115060302070501150e06090a061502060405240a02090d0221071a0406110c0301050405160b0304030e060c16150806030f 69
    0x120500c40d081000b0110318100f4a02c40801c1440144511118804c84d41442444d80d8070004a96441e1280305035141190488007140b0424400300303a800b070440c0a44000300b007411600c8a07601c0100001d80c0301c41c001030b500140344001e01c8030a2103080c81030301d2191500503100b80744c125501201c080c0680136511540b015000b08440c0c05040d403008000304021011062110142c0001030348030041290180c3e6180110850854464180d01e030015200040c0c0c1c102c4180c544401c0b003064025003020126941201c0b031055454013681c0c1c1c07101414001c1140c0c07502c00c240d05511802103418889141e0221071102c44004c001d4a1129124094a0036244540b03007080d188209044200e01d49042d103100036405505e80410311051000c041000c4440e00c05c0325038a80800c50742c91040c511540b0044501400003103946030811060b00c0c294004010301c0400c402110000008980388042d011203da0241156800b45648000d203030360041251030303220904802030000c0700b2944000310740b1a5281d0841d2035550501c082205 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 484268911 1250 484267661 484267699
    0x901031506080d051206030c09070507330c08070e060906070614091b03070e06030f06010602101515030b0d0b010b12090c0a05010e04200702100f050306 67
    0xc1c0244005012210001c1c0942806815a846600e1809819511600151080c14000346c0741807824009400b81d204c3c1d54440404031810b4105010881d07031049910011451447d09102c4c1201c40c0c0079041d184051100f02d8024807044a01101d060002d124050b4100070000f0b4000c4c8800c40c8048060b91740d0340da80c0c2c4115000640d14070403106d00500310f80c07810b050071800600306116180b08003100b000300c40d14000701c034503101800072880c0607240c4d0503406030304188840c00c0c1c4800000d40202004d8100c0c0d1510b0740c0c07504014202142600182c0050b402225802c070420720358000e003c40c00c50480c0c640f241e00c40c00d00070f00082c450010541c8400749a1500406042c0e61189081494015000807030346420396180c510a19036a4013200c0d5054000b001d08022031710021001c00c2c01156488000c009c032420a26180040d29004c024204040d88169280403e001245100e00040e221020700b5900c559101024410040c004da5181a01405c00a401d0000324185400804883c0c0009080300d545d074481103500144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 484270161 1250 484268911 484268921
    0x210402031e010e010501030f121b1509120c020f0f031203220506010608240d030302131e08061014030a0816260a18080a030513080c09010315 62
    0x1550307605e0140000240041036442100700fa2049518500d1100c680b031003210314180709035401848541c1096410005a98107085403041040d85502180d500c01d1a241c40c2441d00c00624188003140005402e0411031030542c0640d800c4440407260f0001006001c0d021a60350342010740700b203440c00c40002c04952282821540240803004480e040585000c1901e8200c3e141d03142846440b010903030b000302086900c00300d008140c103440f0304a071a91841800003820409440c0c001c21007501419420808064005d28441c1d0300406811000c1d6568a130404407240c007601d0034296400400d06802c4901030011400690017203a04585009105008090f05000068182504210020010300700060052142451524888011801240000820380768142450720500d9240d1500d1070303007030f800c01400113641d001c0d124034184440c03041050f101c0c4585540b4514500b0183d2007096000c100c01041e2200ea00800c94403040c043d20441e0040c1a4a501c0d0724003150101c40c06001c010f08850b19007100840b0315003203030f000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 484271411 1250 484270161 484270181
    0x114010327030c0308090604080a05031f0801020403030215041a190f0c110106081c03020706020a020a1203090201020d0e030a1b05040b0f03030708160605010902210402031e01 77
    0x881c0078490014600641694490f582c210041003800c000140400e5011030740911803500030503001d1404900010864040d40000c02d507012030104200110305070064103c0082c080e024490005035200d09509000c1d02d003407a40d800a441881d403820421000414480d201c02c1d2485c00341c050780e242621540b08141d1101004244c0a05151408810030072101c11604090200003252720b03195960000c4086040c2070320424040c2c5e6800740d00944001d03007502186001d1948600036490010f0620165039201e5040e84d01c02c40c00d58006a01819540060000800b4880b000c00624141002504130b81d5001075114801c0130ba05400348504d410170848591414000a442c496002040c01c030000030255030804240b080303020b00c0b80070328540100c480a900700010300c001075001c020021800c1070300c0792791608429440044840448003116080314000364442c0110f50107170401003005620345001140d0002c40801c2c0300f4100c00450140414007003d40c1300071810424404007808503023444404c0c1c04105000d4581304c50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 484272661 1250 484271411 484271471
    0x11060f0a050909011d07050a050f0c0309040c1701090504080c0d032f04050d06150605180a060f140c07171203160c111e0f060301140103 60
    0x2034144411030344640200b061440c1103a110141e41d03250300f80940e0f04417030031000c012a41040360108000c24028800f07482141c549240140c5424203001c0d20302c24942003030720109115400410095040c6c64203004450b0414900d29100d540e62041e03a0320f510010707034184940301c042c43e5207801040c140f2403c0c00c100d880c0800d0510440b44503500c00300f4024010640e0500704c1d81c803054504803a21009039000c0e00183d0712076180400d5410241000d04100c40641020b80455050703a803101d141c0168520454880d0042c2520b864254441c3e9000b801e42503600f0907101e04610840e03203244c050044c603401034840c8220f001c462402441410031900031400910542240412520601d403001802ca1858a201e042401c010003d49010650100514819000030750703051455100540290071020320450508075881c0c0144c001580399980b99001c21110180d1700d00000d445803002c0e000d00141e0400902903804100c09560075495985003a4020a031a641004001d040540720070580d40710340c50030706030100a2071007a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 484273911 1250 484272661 484272667
    0x30d0f110d0e1203090f07090b0a03140709090b09060907030804030f02040605060d06060e03010510120309090c09060e0a03020102060a0905070807141906020307150e070b0c0c091311060f 82
    0x1704a0381d0741d0317100d03108181c1c0d19071180301c002081c60b04003030041e01c03a00e0b20050703d940d11040c11035690002121100303103120b5a80c4181c03074001032000d9007405030580c0f003409100c0707010407424001102814110000c106c0d24140d48410820400904141d00f281c00b169045a0710032541c1a9610006028020b1540165406400410388910341c0641fa1305c55001ca86007a00c0f40d0741c068480f4420716081e101c04a65280c540140968100704240e220360200d04040c0c868504658401d13100c4490004440f000c00c9404001101c0c04410300186410100d55202d0b21401c484660b802403840d03000079940e100080c001003502d521404080200030b402c1100d2405484610140d940c085e8640381d01c0012440c141c89041d2254000c0111209000498100300f0706a806540c084d52a01e0303c42e89900035403503c1c0c00110582c00d942d0310302e41e0301d80c08000c1c13012401401015500b60303924985400032520f01302d04c50303c065104085050610904c002d9440321521025402524042c0308d03820701002030200d0203015062107100d1800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 484275161 1250 484273911 484273921
    0x3020a0b03190527010c0e0904110d020105071e020108010602060f0106051809090307060b06070804210b09060109051b041a0c03040303030509070608072f030705030d0f110d0e1203 79
    0x103400c0032456007181d9440122076500360341000303070112040c0d030040c00103114181c2b030902a0400d10000000c0c24018103000c0d203003a9144c2e40f10790004925582c01b180100c4859005421580d00144075801016144001c0c851801c004030340d031071044010b100b040c082c001c1c0000d0b03010750a080ca450880c0c0b90000103114640d1460032211854483d030259504980451a00764440c46904e4a10b083d80d5010350031034149030400e4108000c03402901240f080f1588204000c840c541d0004201c440458810408803025149030351401d1100019101c0240c00814400c0c0840b03200c1450720310314030540e4111096180c46120404201100340c10702c0c07058450003260b80c000003402005154058100c1401607060100315107000e562040c0484030800159040320008008a6543e51105041070303078403205a49a207001d6070720517070320381f062032540e400081c1c1124144c1010544c4010611248074a00c900786005401f480f8000c0d038a4810081d903c180c017000b03010f042c2d03158140c80388840304000c0007990304d1441d01803541d64201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 484276411 1250 484275161 484275163
    0x2120d0509060a0606020601090b0402070f1401050601021b090a0906050907080d05030105010516021206071d120c0108041106030a0222180f1808030103020a0b03190527 74
    0x407101814188900004106402a14842d402c200e0710075601810150742403c2e111006013030185c2c41aa40207400384224004142e18030607810314107118040180c15901c03954606402d4410040003c0e0541d000858036118030304021012074503400381200c100402d030361003000e030000800d081070026000ba4600780412030b20b000000344250664107101e040340c1d01c410030700600b11440d101c00d005050001e0302c20f00201e1500030031084003000c0706200900b400d201001e01092189040402c039840400a1032848030700200080804001d0380800d8295a80092180b02c25503003513035618030080c081c1c10840b40400140600c80e003008010a0b801b002841b8968030304008841c070010b90000310040faa07020309450340a005518195120301192881d4030000c0d841407607411030340010500c860030a010251540c810b09041c01c00c0854030360f46107104080c0b0355169419401400719607200b45e000b0005251341001030118810200004000000c0c0360745001c43c0702d640e1051502c40d90b0270b200c107910f03240b2400b507281c528001d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 484277661 1250 484276411 484276421
    0xc0111030c061f0b030c0d02030a0902040f0605210c010806030a061a090c03131b050a180e0d050d09061107140111070206161106130f060305070e040c02120d 69
    0xa0308100c075040442e100c03200e6590500c000c0e50b1b04800c07807104000b801140070607034000d1a0300c401d10540c0065940d029401080a0b580c5008203134006964800b007d001d02e143c0b131003400c0244001801c80004804c40c80038455640c1d1007001160781880045000504a40d60801c01e0245895218000307224883c40c0d0104030080c400b20303103146882504a080000d03035203503c1d44141c900ca000075000500f5018a5600c540c10310321000d01c0d140c9100500c802001c11141c640444c44001001024803800a441e628104901140c11500c00780d10203401400074001c1680d400415108a59408200041e0659a52034120002c0c075940c061070054140201d000b130b09004203860000b5000d0044402170140d4a0801000a000d2241d1103000394055010700c001c507c42d61902d050701078018031a003a80d05070090450001002a0011000c52a6000740e0107814001c00040c000940c005091a05050203142014000600f001c801200070354004e42d1f56400c6210300903c204451003c41030030000a0303a50b00e01c0160840c0c0502 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 484278911 1250 484277661 484277701
    0x30f05060606070b04030804050f0106170c0306011d0901021911060901061206051005031204140a0b094608031303080307031e0b09180c0111030c06 65
    0x40224800181d107030030100102d512060f4801c40113261507446070340580748044040c0084d1464850700c004110000024840e01003d4032036008a0003a955030b0004044c80c2c0310308910414001d0300320900410881c0300310a43e410a4280342084407405603614800580240181c8100007110350103071401511194101c01c91400038080c072826501d0681d2002056800d990720784c400c06145510b50302c4048081202d5a00041e0814000760001d80e40b5a65940000e18084001c1048041c1e01c6000a04000903064400080c85410060b0b600c900030307600d0214103004a00825117901d005804030414880100700844562000003e07140d114040050103680009920b0855400f5051080740c4620104501c1000001c1d1442c00b0001208001d030242903544440e11a00080c00e03c100741038552481087d804840b1964011401014034009162660103042001d40c03000505031080401d001030340300c4003090300402c407030049140c2801c1014000b08110200b0f4903520a9400c0440c00b40106014007005110468481540e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 484280161 1250 484278911 484278913
    0x50a05070816110f03011116021201050702072309061201020c1617011107020f011404030501020712050a0f030510030c0e0403090b160b06150a0806190506090d0c050a030f05 76
    0xd0200c0d80c1418220b4100b201481c074800400c0c02601c0050a01c7d23021680a41d2026203c00032800340019854255641901d408016801c007210034000300800300d00b003192030707011041d02c40503010a0001040f100c400140000e4003d030070b1b00c0409500e001007501129500200700d03040b91080a50320303a140c00b0078800d07801341074001210300c1c5500440a0050250303001c15106005e225140c0700342517003000002c0764038910180c14011190359041c50040d0340c4025100940c042d800241c0d45104500e402e204c00e5000e041c14130b00b400380911080c042c855004266a84100301800d0008031500d400c110045803500c1548001d10404a40c07002240310b600d4102181c0c0110b11a4442c00c898684500c00c41280e40036402032640d0b40b0455050742004074895102550708030101802184200c8065030540c1c09951082c4111800304965006001050500c007a10030000c802c0c050003403017241d00700400904284a0900c14621844581c0c3ea034005210000001e0001007100410130484d4954038500b0400e0034020040039126 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 484281411 1250 484280161 484280179
    0x18040b0c04180519060e010b03060f0616060605181303050f040602070e01080c09041212022205060f0d050c0c0a030c05071e0902160507080a021c03050a0507081611 72
    0x51341e45103024078800c2d601d541c4018404c980c24099a006035400060009a200b41c0d03061450702140c64400040c060f0790f5440404c04014200703400e04c00165140c0e0703030003580200300401c00c0e40200f407079411149410070322080001200240900341100c407030245869000902000040000d1140d400190030000c0716007241030045141c2c3e030303803510030b8450300102d40e031a801851880002e80000c0b48121001201040c40c1010300e034092001044904981102154140030f40030a03d400c60302640212101e0000e100c2210440d24102d828601d0003014021501070a480540716004104588001c405407514152045e044581ca0b20150500500b0703181204019901c80c002c05001149840301d540c0324880807401d41c5c034650321062801c1d162200a6101c418102d031020800c44906000039018407a6100805400740200580155030042200e601c0700464010344000b098041741000903000f8040e10402905410402e4840102d81030840451141c240000c00b101804018801081a500c41c03882c4c4048050300e0a080e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 484282661 1250 484281411 484281451
    0xd060e0714090a060506070201050c030d020a0c02030610031e0f15060614041202060304030e0a0905010501030e06091b010c062d0b031002090a03080304080306090618040b0c041805 79
    0x41358154011940c0003d410070a080c0035500a10007000e100c4d8100085905c0c1c181e880e150f0200320b070024040040080c6600d2100002d619003000131940248408420b011050714503a14070060081c1700d03e82c3ca450040600752042400b1843c0001501c090300208000d2400940e520464000c0409014807004180248003035140b803264101514107036000c1c501000d404155603000c010b0785410040c0220304101417032441d00740325200c0412100c000c0c0a480c00c041819410000007501343c40801e5000e0045500840802c03008200005807a010b2000000b80c00c2a807008a20049a82c0da90005001e450035042644400082e0b01c03040c1c0365511043c400407a2690300000d038500c94140d46801e1006a41742e80a007070078801c1c1c880b4550007003c40040040a41d6065541c2c0d690303603059500200d8041c1c800c3c2c0c001000300403003806e0445038994460070440d800000702c13032070341c2018010081c0030744040c095035403450024180c2c0740c030b180031a8060990422076a441c5a00e1404800140004540e0078200d04c40034025030f2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 484283911 1250 484282661 484282681
    0x10209304912020c101a040209090412050702030f0d0813022107120c1d01030b0a1109060c0d0207300c0506030708041e0b01050d060e071409 62
    0x2040c01c080040200014a28a00007220030039103000020840541c2001600c00d003074403c00c40e0400541d8040c4c0e001c540d25444002c128160080040414007907801001810310ba5039a6000751070388558094482070044080b060211154025440000e4142c494001000359900c0d000918800c81642a681c4000517a103081e90300203c0d22410500940048a03806800c0300c01c0009440c1d0000240d5080c11280c541d80da8582460742c04500c1c0d00140c8000c85801c2e4107104003d41c08210100344224490900c801d940340d980c0300c1085000080c024a440c40c1e4621040d5030001a4000f00c8040081c010111a11100f0b15420b0b1743e100c0000c0d85d03e03a0302602ca10b070310015816803102c107080e140b1025400210440030081620090341620784004842402c02c40c0ba001c05c040e9208005140201c0140d50307440050b20301840d20300c208180079100d5405074031484524000060240f81000d0658205a44030030070b208040c50180054004c4001083e079034003030944041000e07481102149036080084800121301d0300c03013000344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 484285161 1250 484283911 484284013
    0x11116030b0901050705190305090a0b0a02041707060e102609100b01050301120312020a020c01140903032a061612060302030c06090109031502070c0801020930 70
    0x302c010707c5400702c0c501d01601c3c041e42c40b0300c0c4c2c081c0781c0c001901c8541605a5030040800d904440074040300794045410700003003409008001d0642814002094010300742080070300f500203d5220070344164510382d42400c400b0301c0f0740c185d034400810b42c0180820b0300d1401a41c44030307520b0023103904c0880d910910f84440341c403003420300541004510603125a460369007001c00210b9890320382c880036001d01113030845642030516288001c00303c0c808182d001d00050000c0341e00040940081e0764450340e41c0703501800f42111950300801113a03602081007000c90603001121491488050b02840d10b20703114040c100400016034071340c034203c4804815035074403a540c0c0c8032544400c504a070764501010390540e203d0241c031002424041c0040030680414180405125034a642d518000d0500c2920942aaa00400d10f141048081c000490162400c88004d50814160401081942d50248002c10040d10441d26480140d149031109103041e850b00e0058404451852050b41c120982403098002045940b1810021240104132030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 484286411 1250 484285161 484285177
    0x903030e19021003020f031003030e1504140f060c0c010e011d0603270a030810031a06060c0307030c0b0105060f030408220314151005011116030b0901050705 69
    0x703104180741940a0000200050341c0a4040c1a404c04c4070000c480e50401c003651261041000038145541103107401070000112880c850301409403a43d0364030541100b03100365070030b0b9121075681b0403000000000203400002d8800101e80c010a0010b291a00c103000810074010001007030322121b914a40081c01115841040ba41140107101002c9110390b191600f600111307000640e0f03c560070b56504804805034038404000b503400e103c603408600000200345c1c01c1101c3c3c1d1742c81310541c03d00c008007601e191a80880c0100c003c1403c1035443c1b2100001d0741302d580c0d00c0e00b92203d202c0c002007203c0cbc80d000c9038075014200c120150703019500480a0400000e103450300030100c0d26140c0c603c6a0301c42c00c0d40c441d50b8543c0300640100e4500041120103c07550303010b16a040700031100450103120750900d403404034041103041140d6841e40c0801d28501d9010040c076500a4000b0701e044807403e180c8040300e9103000c0c11345802d09102c40842507024005203000014041140c01e1030b401207420383e0080105444200b0150754500c602c00e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 484287661 1250 484286411 484286443
    0x306020a1e120515040516090501030b0f01030509151501030e0f030702010f21060e0901050744010303090e090a0803040809151c0e250e0403030903030e 67
    0x98507250000943d0007054004500068400400d00041d0008060f900c0c00c07501030480c0034054548030405039001d00f000009101c00e0030200002810500800e0f440d4030004029070505407039601040010104015448049008011002150400c0c6100c5800f645450480b580042d0410b0846801c0e50382c00b003140919000c1120086103001c41d541d006407145c0300c0000100701800072003030781c400301c6185040044a00200c0ca0b0400201941420055014001c020b482695168540000c0140403500b103140d480e08140280400405180034180070b03a100c0721000303080c24810940c90f03c070001071807412901c64141da10075140c090000d61035040c40500d480040f128100d203648401c154402040c030150095802a004020305458030080d100400c2c98909500c1180f9401c400029003220340b802c0d00b11803141d186211500038030148042d004c0e0310742c2c8c0d86004282d024400000c8000c0c0d030408c00503040900018400c040b900c14072031400e400c01030000c040e0314108bd00400e0910a0303040c0705403070100740007090a0807c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 484288911 1250 484287661 484287677
    0x3030509010e07150e06160b040b15090f061504090e0d022406040204090e070504060b09060405120c030604050303071e0507030f09081e0c01110a0b1506040306020a1e 73
    0x404c080300c40c0e0065158580d04901d00f00603007207881c1da10403c55801ca900800b0071510fa0304003880c0c600c0c08010001c0c412090b0b620303039800d031414590319207000c1604080c2c0d842d036010383c688070840002c03140c074002d00c08007001090000340080c2101107500140c0c03242c44a08166144515856401e90f2101030100d494030301c06611084a4100701034940d81075800c090080c00050601c0d03103810f201001c8a10300c20307a06080e40d0001d10100054503090080801910900c403031681031445080101e060340c043c0e4061030707215101c0c1c09546095403104000b185039031040142140c1940c102814040d440c0e81c8140c1c1c00c2c0002500505840700d112600c0740e0031810389000c40c0d581c14a4210580c8044403c2c4101002040070003240d40030000d41c0324800c10032a100c5218000043c2b10005411a81c6440c12480741c40c1c09060105056007000c0c04040845c00030559600400120110b9894100043c01c4030700010301540c2c4418081070200a016040d40a043e400b6540e0303c2e6450301d0011031a08d8040d145c0c2c280080000520b000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 484290161 1250 484288911 484288949
    0x310030318050d0605090c030f07050d060b0d03050d0c0813030c0501060b190e030c0f060f190e031b10030e0709020d090314071505150d03030509010e07 67
    0x504650481509554028a03881d40b66000107a012001040a903400f40c1c55800303003c1850000d00c1107080019048008190041111a0603500e4090902c1050311808529125074140403164208500120004010007142079107864080d02c3c40d0004131105403214501040081a14003171291503006007044000721489c0c0e2419030301140c0c4144540801c641654a54200042c2003500d080a00203040c00713808840c030b64021005004100c1403080f203000c0d10035400000480a940c40c0e03003001c1e034580d0a081c0c0392590f407019051402d01592040604070108010101c1c074869a00e62700c100801444d104c00c40950707458401e2040100d50305480f40103600d501c001d166107000c110602940c441d000421140064880059a89080d84200d8021001c00b10b021a00c82480c00200355000e1150910508406001c50804015446004101d003070124080320250740c0d0341c08270302500e4100e9944181441d00074800310b20a800b23840c00401510003601c2c484150341c05c264498020060201e210020741c1d990411040301c00c848 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 484291411 1250 484290161 484290167
    0xe060403060c20071a0f0a140c030f04090501150e04050a0b090c040e0106020610060e040f151a04080c0405060103141e13020d03210e0a1703100303 65
    0x82d400d024424401c1540d000030742404a0340074145003107000d0001c0c1c0812840c161109103810a220f24240312120104000742403d4461002d0390b90703200b524a4443e501031b41040740042148030b415035100390b620001c141c03201c250100c00c00030002d40d00240381c02c1c0066603849004110000d1103000d1403010075000080b041c618140750744410b500c5102ca041c0880d910070182c003c501c4048055074020f0000200103414010319140303464050041a1360702c000e06d02450708001d40c424070040c60290004100c2c14040841069840345c01041e00228445401c0140901041c005e060000b01803040382c1e117048100c40c050103450582020307607007103494180150000e10068030400000740030092000741455501c00c401d1800303240c0504590700c507500403d14000104680007202501e800014880208901c86042c0705c0c00589a80c203000303c4859160800d00010100b45080b0b03100005c0a03c212200c45150003401d4840f4580040c400081500070409815801d4100b6580788181c8011602c0104d0040492010400030b44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 484292661 1250 484291411 484291421
    0x5060a050316180b0304061d0a0b091612050705010504141302040305071707151209150f06031a1b030405010e060c0408010509060f0115180602060f070e06040306 71
    0x60b81c5070040030a081c01585004000d41c40d0400390b5000408002c00c410450580b140f41c15020038400d0011044042c00031155480d40d00c1500203014044040200e020038a04209003202c2424101c400c40503161500c41c010a2100801c5065030719226084002405500400444003940d04690b811a010201e0f03001744485000910000d11a040e42000000041003042c8031072405401107880300040f590140000d2071400b420b0b40c00c0b9000caa1008020700c42c501e030f0410300d0351a080180c8040442c060b0003038100151000308a5949008150038031794881c2c08004294040b0085c5c91040c90341d00c00031340b6540505c680041040b0f5000320503130f20318072142c440c0d9601c40001e183d02c18855000400c0216000200a08100c400c3d50322441820001c1800c0c8084002809420b0b80010000c1c0240b410f460000300703403044d00c41e06100313102c90098444c0191072641c3c4507080034a1002c11084224549036a00d90300259a41c02c21244e01001751360b8480401d0015200340412420b801005140b035040600310b4942000600c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 484293911 1250 484292661 484292701
    0x803040603090f050a0302030a12020f0307080606070c08060601030e030903060a18200a050301051b0a090e010f030c0e0103031e0c0b09060403032301030f08041208031005060a0503 79
    0x62211000f18002800822516000c14400d5014544601c01c2c6007019100503e201104480c0380d0041c018010b01032041c07030680703034800c00c94507145006458807404100c46110b40384003e442e2558540000c81da401c2c00045c40c038040c046c02c0e41c0810071588180741503a268081d00a00940c103030404004140c0f880d01580003e804e094401840e2889601d0f56503810384c44a2140000d4030090440c0137610089103400402800200419002880a458140200c8050a680c4000c00c041000e0115200131850321032103010010300080c0004018550311440350070481212072004071447d0641d00d0011540c5900030701c4207030480c3d51503252074000887d0600b044042c111320b0203071f00080114544c40320300031507620b14034240144c9015010384114106414010103680030501802141481640c9082a440d80704001d281129004861441d8101c41850720311110b00c901c0d80b100c07402103001c410040c10b104510000b14096900c1d2801c1440907aa00d0702401401d01412900002140c0107200298800d928250701c0d203194 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 484295161 1250 484293911 484293923
    0x6030506060f0429010e01090303050306091f08030304060606140f0a0e06040b0d05060102010606210204030503120708061009170106031203020406030b06072d0203060f061306080304060309 83
    0x241c0d84c005507890720801d501078003000d0349040781c0e2600783d40d5800100000701a5000c0c83c00304c90311811500c0280c103500c4060a22801101c0c4071000984c4556901e00100000342e030782e800d6660b4190b5801c0c5465480e00250383c199981c1e0720740200010141d02442c2804002d581c840d90181c10603845c2e440c0d400140c0c00181ca04402d011084180d00704c10b0b59681e0050001d8441e040900f5107800c130384840202114030081106056a00d462014412990841543d0700b0940b440c1c2217400010440901c1c140c040c1c011030340010440d1102080420f42e60300150303500ea03c2180e0b541e58140181d520071040040c4103030500c0344103020030003c00c428810300700140c000d0040030100100100749942d42e6a135505004512071201310000740d0209040c0a0f01d0340c0350090710a410030454101c2e003421001e85501c0d030050301d03500400c000346007240c105a80741c001c0c4080a0030b0464004080c2d4401e403400b4914003582e1b150032600c191288903100e9007411081c1041c4104000d9425640c015410f103170406038140c0042030038060035111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 484296411 1250 484295161 484295171
    0x307091a0c0a1202100c080c0a09030203060109020c0d02030306010512040609020d06020417030702030c0118090213051c0b0103021e040501080304090c05040e0c0a0521010e070306030506060f04 85
    0x11201c100200a0348074425403100c0c0d01ca9880040007804c2c000c0c02080640c3e000e041492605280e64080041900600501c981c1903480802083c150303620601644000d4140c00342000000c1c0048503a405411754000c00b00c10795107000c4100070f0498032413104544283c00f0920921400d036888040820460740309114840c0040c2e0840503030002803c9402c04103084800540014080c0560a04901c035040d8513038250004504000d00e66000036100d0700c0c1b2541860400c00c0002d2646c06100d2000d914000a103007103c81150758044245c1042013645940c0203281c00380c04004680300c01030403400e60b95806075400040c144111b90a46e400c01089000b81e5022004d080c3c102e13000b20a2596441c440d09000701701700d000540e503952914a144054852001c006070510800b480300308007101e45481c1a0354041010303210789031ba45441c02825140b41c050b2008074080070840c81196210000140b03002d906892406c441c1203015900d1003800c4096480901004202e5002580403489a0070004480030b26100c0040002c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 484297661 1250 484296411 484296427
    0x1101140901230f041e050d030605011107030b04061b020309010201050606041212020f0d030b09011203120b06040902040b0304170f04060c1103031306090815060907031e0b0111030307091a 82
    0x41ca105d42507000b5159074006d8401700e145160548079110042c0001c4c01c20300b10340590481e0301038840d1030340c1c030000d05a040078800040811140d944138484150034000e03521010050243c0c0256290001102c1d07502540c030f0000400d00c2d40c90401c1c2036a0880b0403040e401080f41c0300c9559050a51300024a0071015442050850707008408244600000a10380303550010317000c00c10100b00041303202c043e03220340600500307154601c0220340c2c080030745109240e40c0764020602d5104680411080c0c07040c0e0340400080c038808200425254002c00045001c0c0740240c901d0343c40c4e8000581409110b01c24450110106801000100320030b5004241d481510ba000f0f00f00c0c180412022004242142d102c00103070329009000c51014024150003511842c040c040a20080080141e01803941d114a100902418480e820400c00241c50610070740004505c1611403c03410305030070b9000e191a0240a41c0004540485d10a14500134092000400e407403084a0655510910302d141c000c528018515116074010300d5030003001444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 484298911 1250 484297661 484297703
    0x90d06050106030212011205030714070e0f09010c030b0f041a0a03050d1409060405120307350f16150504050a150c080c0a1101140901230f04 62
    0x15008003070030b85000d170341c41641060082d003d80c0c050b00f108200c5585a03d15034046940003081c0c451440d4881c0c4209448a007500e03a4600d000d085038400410941d0200422031000d050509803801030203030034001e00c9410011441502910300e12008580c0102c40b25416030528609900b003080032001e841080d07117150044002140038942d00e078000340c03441d0340314001440e074071680201c02c10000d01c1340c0c040040c200350341c04002030694480d51084520440300000e40c80d08a5800307004403080c00707510a030340b500d004a00303091740740d03e503500700040c40440009000000b01c8000301400700c03941140b135008014a84001c0c80c100d442500044103080d160005401000443d49280e40304040c000c41c0a00010828000140303015400e150400c0c8a003200e01d81854034454025420030091900b0600031040aa243e50709800200c858030245040d84100b9800d01a407407003500c3c1d4451060b4096403159000788400d040050140066035003003c1c00208040342c8100140d00c0010042c41c03ea0058403e02c0b1400c40941003a02d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 484300161 1250 484298911 484298921
    0xf03021605160e10030b070e03030a090e0105030d12020c030717070b0709080615150406180504020a0207150201140a1a040e070e0901020d060807030b0a110f090d06 72
    0x101c1d00d40e4021071070501d45040d40c8040b28024075036042807140519268030000b44421082c0710007090f860100c070225854a0080001e004c800502404076a25010440402441d20f8810b100b90424251001e0021619090101d9480f035510b00d280c49600c0e40071200c16601c80254000300d03c0014034001880b10030700207425503444c403c5140b44490350301d442e22070608210341d103d08098145410720421847c200844007010612a92007450481c00460041c1b49101017420020603102d681c0003404009004a1b03019003044003003842c0b03107407820101206ea450b0782c180700413485030420314400750380b2502003000110710001400d882d0301c43c64030001c211040310300d45132507019600742d902d440c074503803100c000b00b82d4051f038005000301e214001c60341480902030780c01050351900110702521a18801060004013100000d40440d000ea500041c1c040240c20395540c005034903000180000c96281c0082c4c070120310b40552501860500c00b40505509251500d43c0070351160a911645405070030050903000e600200e81c1c0c40c0320b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 484301411 1250 484300161 484300163
    0x8131b08150f0105010305152713060f02071a1305030a050a02062a0f120109090b0c090901152f0f0f0c040509100504150c020a11010f030216 62
    0x45550a2a16800c1c032660302c16045241003500e40008c00460071110881050559425111207803080700b80c40d6070300c1c020400a00700443c0c40503804140842013110b0318401c07004502541c4200044a04c810203403040c1d126004000d01840441802255000340034086a07030004032420b8400703030003001c540d519800c60b00003403545404580040f441c03180c0b01d03405004a0703902981013031451008810b40c503001041003048d02c00d42c00456001040007000311100208417801d4020740401c8515039a5228500070142903198002c40d5002e0b01000422a01442841a03403a2840c00030500501d82e82403101c000041e4410b10760f0002040b0b101480e02051056101800e8042c85580803a5241440040c2d41d007442c1c036441072000381195102110385010603d000c601140a81302c00c903030206194587c0d4119510302042030014413081460070052008100710301c8400c210491004d8800d0206620a071000e0b611400741410240c0403402c00131281d882c0398854040c0b84100c0d9040c0c28018145800368100c0d008691903500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 484302661 1250 484301411 484301443
    0x1011031b071e06240b090111030409060815102709060c0e0a03081602010509030d02070302040b060c060a050403020717060a060e0615070303061a071208131b08 70
    0x6401d0910419010355001c800300c210b110041d0351404038400104000500c1801080040800c0e100d02c6c0f0b0b0b218100444181030781c032084a86070f80c0c80d00c0301e4900070002c0d845401018454001c5d900009100c5c2940c3c0c0d8807a200724852606a603180000154110741c1185100101c12045241c0381520506803141d4010140600320020b600b4030004800360001c81500c81851080b00c44100030800180d42008442d40d00c080411200015601440160380c80d004030404181d06000f410651040c0300d82c00034001085a0080328207014600d084001c1c0f00a80c882c0703121514030794002e000040c014003100d030440ca40091191044030409980c070983c141c002e011040360b001c001e400c040180030b80007809009a501404042c500e546036030510000282240c01800f0315244204000b090346000c2c140603900040081c044c83c840056000b07000c1d222803615502401e41228810314240ca0458018800c0e00024440d502140d200c4000d00c0c0c050325240e40405c1002203680c01c4584102c0007040c1024103000411010300044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 484303911 1250 484302661 484302713
    0x11407080c07050603190e03091f0921060b0f030d0201060501170f0609040c03050610050414090309060702030109061a0909010c050703080a1805030c1011031b07 71
    0x1140d19003002e240c0d6101c94030800081c810700c450a56510b1000703017002d1030711500184008000c8901820340c06440f5126600c4030b03180c0710260403607a50340041805552030341e030b80300b800544a80c0f407100c8201e50245c2d440903036881c00c82030400040c00c1e54400c49401d00700506d4400d104c0d54402c0081d190070009030705000141d44a400c01c01c40c41d600700d51881d04071403081002002600d80300c0c0c911544020f0080c02c503807081d01003e000c98103001c02d090b081006542c11409444bd140341c440e1852074281454401e41d402640b40c99107008440074107594880c0900706030310107140341c0b40846007001915044550103a03810b541c1c2d94510b0300041e055204125400d0385070b450200b100a110801c000d28014001d0107006264144003501042c1940034084410041d0316051406058641703208000c001c00b8555803056910340c404401e00240240000900f101d50701c050f089820840d0810134140030784400d000343c3c600c010818008182d44d14081c42d10440e00c00e0f00c0030049e42c1851910f0301e410341c800b0b00001503084020100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 484305161 1250 484303911 484303927
    0xc0501060b1e0705060a022a07061106040302060615090d0b010603050f040f080d020c0d020f010614010816141303020907140a0315120b1009110706090201140708 71
    0x2d41022401850030700c000b0b0820a1940b01e9030340340c100040c000c280c0e41e03a0004030715403a0300007201402c060318130301c081d05400c4440d01ca42465950310320717006030004030311204606480003000060442c40b60354158040c0c0718603210101480a81c010314074401c01011024003200d5210b490342a040c02d4118001c2650551a514000340075046500240c060503840040c1420440070801d8425031410481c0c2c0b044401c0d44d5101c0009800d002405181c29000d001e005034051407032482d90014041c0b0310000c4c9480204005551a1540000c1d852250812401b040c041e0b0b00298007a4560704441605070102c0c20401c200c0b1980c030b1019401544040074000103903440d031909201f903041c4440900d80c410b041341000e0021494090900440d40520b0364160201500c8090a40120007600c4030030000342901c40801d42030036100c0c9402e90343c0391022210200d554182040000d0050b040380070320045480d102450903c3e29285440b4a0007501b000c200581c10b0126441404c00c0c01007903c80103111181c040d555254880c0c0345 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 484306411 1250 484305161 484305187
    0x61902010b0f03070510050706021b01020c060708090703030e0414270102040b030103020d0204060509070c02030105130b0615040b070c0501110a11060705120f21040b160c0501060b 79
    0x2c0c0c0c0e000c140254022032091249441e00c401000300005141001d586600841c03920340007a10645944520001c0100241d55500e031054014050320818002601c0130f039030f90414101c1e1910012a80244990f111150030004240194000520060040d00100b50a00701c03121101061100307541545240c8580c0b840d25462900c01f800301c0309111f4001009614140c60601104441c2c0818000030384107603405e08140085503210b034014001840c0180030203095240182c030107041c0840c1041c00b03901039420040080d1801c180c041d40c0d0004650300659440729a16044240200c41041c96409618190300b0800882c1003544440503100241c0300301011a11141464001007400d205103800e01a00d03484103034900001034074404000b1080d1002d694160f00e901450408510307140769441401c00e60200012240c1c1002e01300710081c103000d0f02040e0313412801c0198450928000b18102c17000303000850004040743c403203810120100001051440c2094805420391915400c40e0100d80c000b15820780005014111660 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 484307661 1250 484306411 484306429
    0x1508010b0f1b01150602010209041119030c0c0c0e07260106110307061404051603050a020d03211a0406120f0c0315020702040506220b061902010b 64
    0x1a1080580e4180015503600300424010728030060100c2001c081c4180c51003009500255019880f42c0e4205032195a1740d002034000c1d840041c1450085080c411451249104e410032200346c2150b000d08210964880d110480c0104400b0603500100408001c5040c0410442e0702c01c0d0010340300405003404036040040000d003185440b03038003c0c442185e68000b0b00c10010301ca076031800d045500c2030404002c03070321840c407a090461041c540010300e014544440000080b14440c80144280e2240741181c9401000702e5207402c188140d4072005246601c04502440181080c3c480141c0c00c81c42801d10850309901146100d0f0810b503c3c104481c08184c0c0e4480c4c07400803da100680101980080d00d08001d820708148065803860300340400540701980e91030241081003664009603004541080b03022000191185401c0040c0d40001416446142010003185852030311140f40d034400d050190f55480e0050100ca2040058007184040a622010a00801400b0000180501d108088560000a400000c5410460341c68 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 484308911 1250 484307661 484307669
    0x50c070803090325020d0f030921060b1203030417040302090c2106010909090c0503030f0c01051e01050d240c11030a20010e07030c030201121a0105091504150801 71
    0x4001c2c0010030f03000d0380346d9040d22003495801c0349050700e00100c141000e40700182664058a505800c95209600108800854186d41807080780140070540c40070041021101c20744013002410340081001c100040c415002c041001d840840b09181880c1c0d684e0001807002e0000c42e80a00c11980009022003184507052030f60603400074100c600f41d100d0500c0d4000801004040c010184070395079511a5005119501064500401e0010112507450001e940c07980390640042440d040c0715170030070f004501d64214900081c2c503000780c1002101c03d0b583c6008c0400116400013441660a2110500042c80035200342415092050030a540464101090351004181d20b1402501d8946134100340300480c40d03a5031000101000070360b00c0d02d002c05c501044444450041c5800d00300b00d4542d1081c905d0000411080074020f4085078005d8a0350518207481c1081c140075100c00d0009404800562002d15020350b0190002c1c24070b42c900035000da15090303203804440a0a40c010b03000b00403009496494001841c1e48002454058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 484310161 1250 484308911 484308967
    0xe1506040b040e1f0902090102100504050a0309060813030e12011a030c010806060304030305060a0b04181803023004170606122109030102220b09090109050c0708030903 74
    0x810302062008031141342c0142d03843c0c00d8000030306203e903a20804c044c00c200751a2030020041c9081600d0025a203400004044020911303020001828074052000c95116422422803400402040c0d942150381c6614411065405824507001c80ea418009106980704185405007140b044904401014a08040300301d025042008017810000640c0b500c0b81901c0e0400d61600340444d4603114880014104902030304002911000404d000030001d9600b02802c00b00d1001c0c270010000d00000038080d035101007810a002d00560321480c032031021108509003000c000034490088101541482d0750b60030440d406a80185180b2103180d003104901c007028412140c010404a4074004120841d00da815203502d401246c81c3d1003155074403a008901040c1004036a48084020001c40da11540b5400d550b06101e0300c01c80c030049030362034481c0220700c02848108480d217000f0001d0007059168030300141c0038084d120090803d0940001802000f0014541e403020b540074401a60142d615540b404804050324400800c9003209 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 484311411 1250 484310161 484310191
    0x10306080d0c080d020405180403120b06070b090106090e03070b070e01080c09040209060a0f020114011215060906030308041a0114120a0b0115020c1503010e1506040b040e 75
    0x1d064000181c1001294001502030300c41e0030b40d060002c0240078035800b00e41c112140a1045500320840b0845501c1140300f034603016400c0104e01d0501c821241c9514145401400c100720340c038046041203009a41c4000c00d07000100b40c0303a0b103444032030043e03885404c0e8a074140c1d840403540504028080400c240d0211051030007490040f09100024600080900102290200003d41c18200d0700c66804942c056200548241e03030324000000d00410704110210141c0040d41ba1580e03000207020b40103100c604a85920fa8015400300180d1510b58088800614441040703580d92800145040300d4029000214000d0702c4500d01464542031500e440d07190744404000c10040c141c0103100d10400c40c54882024101611518400c0516000d618644010181d001d0110080c2030300001e00e10041c0002c2520b0081194243e40c1142001803c3c4030740c1b04040e01414624182c01c1c001401080c1072640d40c5540705081d42001c5c1801303040741010400d140c2c4150001da94058001605000b40600c0b080c40d150411040211000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 484312661 1250 484311411 484311433
    0xf020f010506011b1106040b03010914090309041a030a08040e090703170c151f0e04080306012102121024081906150f0513120f080a03060501030608 65
    0x2551100840c0c410b05003000f482850f0a2107501c40c4405c0f420500500850f076115100e80d501160b6030424858413400301c0c14161144102e0380c503d01198090b113500d40c0150b05180110003088060010541e80010540a00050003420307502040700000d070034026400a07a44908290702000d01c46001000f0b2400c40c0d00c0640100700003803400b4001020070645200c1c407911001c4550016082400003003500a0440c15007050160408081c0301c103a40000c402074070061503a507204151001d14104880203002d4120510000b001e5501844914545421001103a0b141c0010f1003007120403070b00505000602018510b003004804024004c1c8a00606080443d50f14201b500c180c064841e0403a401c5c2d07000802401c0b0001c10b0150010240441420103404400c1c051583c5440c056400c54901c1102d10f4000340310080707104440743c080d41c00c44520090119801b03d0f16820180d01c00ea03100640c910440340700c4204180350002c11510005485480c44580d0f0100700303d854800018103490040e0050340e040e8120010400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 484313911 1250 484312661 484312667
    0xd080c0301030f0c120c0608010906030209041b150e030c01110303190e010609150f080a0f030e090411090a110a08060d0807032007030f11041b0f020f01050601 70
    0x41d0440307a00507000c00301544146007000c0840003540c0b0110b0701c0c050059031002040149101342c000e40c0e0315a0761f00e400341c0ea43c40385814203590040c032029400c60403400100d008203040c01090001c0d40010344480c41d80346d56030b40000d080034007041c0350b2034000b0f8007c0028601618003403140581041d4240b0744002c0002072052100e40b2440041c00145610602d0880c01181c06000d400c020b803590302510003040075554038118100035107500d4005e041010850540441e00e1140c0d0103c3c1400d44200c0d00c024405521565161000b083d9441006c0d000d10600313201030a600d90b40c2280340c0f40304034131a40c04061442e136100c091083c10240980300c6e0700e11300e0900b4a40480c004603442560421707612842e000701e05440381004100c012210749409020300900180d86824185c00003040c140d0030b1040c1c490f25080802c03007002207480300b5043c08010011f40d03120402101203081110200f41d524030003480000c04200e100c002100b441022603103080442c03580700003a510749805105107204614007030001d200510f0060002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 484315161 1250 484313911 484313917
    0x181204050907080405010912090603200f0f04180e0607140910050d02030c130f05030a06050a1401090c03180b0f0c0c0d02010515011106060915040f0507020d080c 71
    0xc600f0456500005018804250000703125a07410000103540700c101c121004040d1b8005d809004007003420a042c03003041c07406007400e80b4440701c01c10800c0c0d81449413070300c10002964072480c0c281c610228240008078280380075541c85018840100c8002400307250340c0070841d091030790041160061142a0b00358545510340701045031040d14088510604a0700da544040c0c500c2c0c0960a030184240e4400300c20001c406001ca401407103161100b001512003a607949803100206110f0f07008064040d00b02c1014540000c14981285803c0940b11001003200325060074140070072002607100c22051a2038012244886416200e4104418400340d00c0c1040801952503000b10444003400101281c00120002681d886d24101920310600040c02074455000c05000001d003c2d00b800d403155000c00d4107862140560b0f40c0660007003600400540c1c090300c4c3c50781d6008100030103004010801035000d0344040500d0700c00d03501c81c03088194100c0741d000c1c00502418900b400078501640f0954040a024401050100f108072090507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 484316411 1250 484315161 484315171
    0x10c0905040b2b140708030d110415020a020411070b0f090a150501050108160206063001090b010503060105031b01170c0d0f060f1701141812040509 65
    0x101065024880000c01c00d031a0700144070022441c50071000001840d584000c2c43d06403030148071440c5050403810305660b1503003028803030310720954420009800000f800c1c0d0001010342032400a4241800c0d039500000c52902c151481500060f00b10280030307000c6241c00e00c1224199850500c029003000303201c1d554804280005401412000307900310024000c0b00c010003040326410780c080206030300c0001d1500301074040d00080c0145408a880000019541507240201c10281c0c0399940c020102c0f5141c2405010940c0d6982a030750303403640c103041600c52409080d418008680c1305448000241d800b014109041c8244041e0802880381e08031303100404c100d9400040081d061030f4008207040b440f610791070040e15000030b00c90340c400b0300c0c4004030108055030303600101401e445229040240400402a4610012290709016000c0340e0302c070b5010280301c41d00e50140d4039030704503600e007000007000320984006044500d022102e030f51511120000308105444203015900c54004943c44040c1054107000020f80e0152000304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 484317661 1250 484316411 484316419
    0x303050919030b01140103091a040c090204170c06070321150b03010e09010603031d1503090a0203100e03030402040f0209040507020102090301140c04031b1a1b010c0905 74
    0x19045116a00c032100c203441c910301c0101d01c41c0c00039500c1c901655030301424410303089400c90810101e0800c0d4040c1c002d25030520b41c03140f160201200b00c90001d192509000c6c00c142c0d00d0040c190b402044c640b0755840100301504541c4882c5c01c4841803444560700c1c240400c032500707015260034028840001e8100c0c030b07810440d00002c4101040d80b01c90500f11401490810496400100f204030f000580781c8107100210b0584d401400c52520507034564040509894030380c400140081c203010b140040c000011041201040f0340213040a0800b03601e1903e40000360000d4441c2c1c440360b0401e41c050320843c0b40c200150a00040401d1040c00400035a800203510790100610180c001c0340c444281c5095191a50304403501d500006200700701906008400a0007034100f401e40c036002c0d602c1c050003a0080303d1407078800c62066030991011480c040c03c1d5903d03040c413007181c8190f071214802c0241000c220903070215100039030054500b640075101d90f640c004907aa106490324083d0780c1d59252409184249502088540c25035006503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 484318911 1250 484317661 484317667
    0x109060609050618060f0d0b041113031217090609060f091b040b030118110406030503090f060405030f060a1413020111030f0703050d0e03030c0d0b0d02060c0105041203050907030305 80
    0x140100305288607200386c40da20700d0740009581c2c00c01074865104c15146401030ba070030080100401094845442051003903d00c1a00450080000501201c02c0c0181400607140c1500d04507690310040c4800642030f644c900f850741003082006088001044020b038059000d2001d1419800c014803000d13200d007945c08451403c84040381c201d0b2600e803280d41001e403d0803000f4000300b08050240c0a003200d0320a004030704580d1109603200802e00c92800e0300400e070960350800041c519200d2035204004a8a40340e001c13042e0402e00900c0f000940f03640506c80c25072110384c1040580641c1c40c1c0805120100e4100d1941d56a800600c04c06002c11240504800d29400e6820b081041303a003c405055030740340d8003031501100c140d407000040303d03070405034800c02a25142e80011028007441c4c00b94031003180c403800211514040b0040c180b00488501c038007508072454000c009460800c0294040d0086001030340725842c280c201380e440c1c0092208101c52094010048410741c03404002d94103207800e420382c4031034047c4400350400c1004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 484320161 1250 484318911 484318957
    0x3070c020f0d1202060603010606090b0702040b0901080d121a061c05150a0f060509011b0c1508090c0109060c0503090901090c0f030605180403020a0209070801090606090506 76
    0xd4821950000c4000d145001d0301c0300c0b91909030b1400540c2500c040c010f014400c013042803414140130f10400e90301e060310f82c2c0784200d00785442d41100b038200503401d83e070194441a2140258646207070f0709002c0c01c00751020307242d60500904083d060f411201d0b24240854940341c48210301c00440e40e0110f0064808a0301555a110320880c100c001a541c0d000c008003546c5001c0030302082131040701c0300f40c208100640f000c0986640c3c074600c0b441d0281c02d5124980111f20104100308056210f880281c0131040258210902400d054070f80000c403a1580e00300c0d4001c42043e400002c41c541d0060710555004030804000c00c1c40910020000301000e00070301c6010140f10124840d14100102401a6901200041c02c03000c01980c0d141c1f880009012440c449401050b01010301c11020b0748240140419684080c000030040303c51001d0f40300101000800c254118051030700030b0b03030041c0d80344104c150185555030380e02d00e03055051a8a10013212038030b6102d28140305805004206540b00c4d0010742d0210207d140540244a00e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 484321411 1250 484320161 484320169
    0xe0a0f0902040e07060e03030403120302070203032701080903191124062805060904060e0403080f0603010e0a2018011a0301180c03020405130e1b010503070c02 70
    0xd1104025489414040012030609002030794074121082c907500d90498030905014140c43e4400e03404080d0415200320700d1003980320b0003600140302651001d011a443d0820716014041e8103c1189541e5580e040310100240c265a400f40c101500014a8000b561408410801c561002d080d582904e9050064840700e0030302e102800c1c0105035110418001e400418243e4a130041008481102e10030710a495600600351140c6004151a03038841034800700d200a203080c4010010190003c0c10b140d81d021742c803000c020032610001008607010b284603840f42c90b09402c18484816140d80014000b0b0f000768580312a15448110009441c01c1c00c54000600c54010303900c04000d10181001145201d0f0001030f0110308013444d03694201e1082c121100c445c0100d49003074050344041450b200c20310405201c0801c0c0410001c2070b01056024101080050a0040c03a0990700c0020a86428950020069482d43c500314000084414040d4103c42d09900725040e080d031303045000290007070001825000400c03d00e0030244c0301b117480d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 484322661 1250 484321411 484321421
    0xb011106060f01050f0c060910051605030a0f06081e0123041a090a05070501020604080909070306080d030e070b0a170403020106081006031b03050d051e0a02030405090c040e0a0f 78
    0x614160895580443c003403800c0e51042e0130380d508d45545c031030090080500e540621401d80078080b601d003010604490040119210381000d0003107210996038110f054800105441810014201040500b50f54248158078024a0b0380000b106099a4140800c410120703002c403840d400d4001201e403840125031128241a01c0c0081480341c1411180216418480d80000018241700050b1007001140c440715150401240c50712019600140520000d11061256103010b00d403060b8403407211314000031243c3d580c1015030b140c8002002c0040c0802e85d60420041032140c02d00110000d41003880d211498060349a00041c440c503880c443c01d40e800c44003080446d0405100307400c880000c00055003103a050002d1044198000c00103440111001c0b60391881d00000004140742c60000c03030f500b120103030800e52503502c41940d5941c0700e01081c248001034001440f10303000302038010b041626841e500558403541003400303101a54602500c1c4250f0030708140800c100b80e107070034003100381d0242d030b81100400c40440c50618000540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 484323911 1250 484322661 484322677
    0x70e04421b050d02041a03060a080f3315032503020d03271809020f060a0917060f0903071104110409020c0a02010e15160327090b011106060f0105 64
    0xf02819001e008402c0c6086c3c0a10b01500b412900c000d642039481c1c4080d9980d1403807110340c0050b9004444034109403080b01c100740c1c412076541e2041d9550210b5a1083e000d1201d011a034120002c161031a41c400d00d41404c105000c1c004503a40303410440303148120340402c02850103200003071007881100702d0182010720030007016120044449511100d03a100c007003c0b03007000016000c2c0500c002c0510320141810344c200e0044111590300035004640c140518824080c00b0391119900409100f00326000080560080301c02208405032180940505e0801081d580640c0c1c0b4080e052401c10b91040c8881404500c0c00821005410411034001846240860008286e0b0160780e00c00007580307101060b4410b184c080030030600c001c103101742d944500380344a15040140f01a0030901c3e003e10007109000d040d1480250100460801e80641010400c42861104200300c075840b090481039110003640003000500414061148401402d08007400301121f204201595031100500062048041c014008806c0c0d00680840c0d60403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 484325161 1250 484323911 484323929
    0x10c020d080c1507020c09010605120606040f030b0a050609070906181505090f091905130602030c040905011508070807140409020403030917070e04421b050d0204 71
    0x48603000900d10b565039007120010050700401d000c1c01b4003031825020b0f86051311025101c041c10603c80c84506510f03940b004001a030010380402c40070401c190754117401c0e0015485030300b49420626020460405a0700050a0035005603070304024042c0c01da40142054098666602e0710b02c403403051481048200d8100307580310310310b034a21082d800b104090b8040d00820004505403183d041d0466810248481e000381111411b95000d0507407400c0d11095200e8000c0340c0c10840e06118908403d419840301e10881e40306031108190ba2000060802c641180740c020725005052900310074074245500071014091082c010800c20400281320f0004030541d00584190f40e00c6442c204005803a56100d0018000a500502050300030503168400010b06003070400c0da042d2400c20120207004000d10b810b0362003c81d828040d01c01c8443c0c0342101c0885490071030000d00c1000d042040b00074081c1c80f1480365003e124030702c020350760041c00c00c0c14074161260440780300b00307000034500c8146445c50f0303100311100c42c00c03000340201e4200c6003071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 484326411 1250 484325161 484325173
    0x8040302060d0b0907080a0c021218040b06120417090d030c031e020d03140c0f03042414010b0a0c02010f11011a0901060228020a05060a02060106031a010c020d080c 72
    0x1050346c415407080c450242c0d540200032412113040b0a07641c0f01d222041e99410071004000c4107800010201d02c0c03950321100940049000c0c081040000d483d50000c149800303940444204000a0203251040011549000b503ea1031400c003213100802d8460000d890040c080c132080310000800c01d8465070291a00392104249680ba44a591000a444030340c175a41902c0028100700c0d00ca140c1050669a56000300c1c554401c0f00e1422108589550080d080100280d603a40ba80000044500d4641c4440d070f0703000601e00c80002105014000e500340d2070641a0020246000188125500f00d6000180c01d10040c1d024280664960010201150035110020059003903500f0840040c0300c111500b85c02c1001030f0700c200c40b1402541cac0c840c0ba089940368140d5a0360b00755100c40c011050710042c0e00e480b4030b1000d14009000c6c961f880e604d0303102103403480c1e00407112007005034000b80040140a0341032107134100b110301440555412148041c00208041e03840000680f141c00f102410808100000c000c03206007181d030a041c0c0344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 484327661 1250 484326411 484326421
    0x40504060e010b010f0905090c09030d031e050708042607030c05060903030f16053604110f1c0c0c11090420010c020a0f05040f0908040302060d0b09 65
    0x2015081400000740c9640c00d001c502e0986600405030820a000e083e9161100300e4908010070802c20300c0a400b2140301101001401c030580c90a01c40320303e0000403a00c4c0840c40d03210f04100460301e124000c0c0f040c80074a140038140070030070b13034803450275500950400d8410344070100d10b090303a982c004100d02c0e0030ba0b2075210005482040503004510761400d18003400680703482e0354500000c0c0b0745a100407558840d400c0c00c1d0f58000788002e0120003012507880441e141c1242402042e01069000c0d4064504106e5418680c144800c0d20f80484c040c0a51030340c0003550301f0300100100c0024640d440c040e00445c222005004103511550001c0d000215850500d103100034442070b001340201502d501000e64003600d0b208510244910740c3d0800d851494047c6500c005001032600c040720462000c1501201024108000d0306d46080247e910350b09240090310300401044d41e418034000c208021160002c074071a0352282000058804244200706803801c07a90103603001341e520004000140001c20140c4a950350200d1804180702c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 484328911 1250 484327661 484327673
    0x721021201020d241202012006040f0b150a0b1e0f030907080f21090a0b0307020d02010917070f060606050d0f0b09010611071a2a0c010e0f040504 64
    0x43c0c4c1c42054403982e800442441402000461800d0013000a03001a04403440019407043c250001c404c10303191f02840c2614a00e070111783c1440000e540942c0d60aa003180381c0c60901a1640d9402d4200c100100f16401040101c8003140d401180d51003581ca0080c40492540d1040800d102584e16604070072100e196500c00c0210304507059001034807820b256109484012890210024891007003100034002083e420034075846074000142d00e82c101d24541c507000e00c0041c100e074071031400c860301501d180000d8507140d01e0020402850010810784c1002160704001d844004034003a400f070b09103000444881c40c2d959200504000312119584440204094074110b400641598003502a140d01880308005112601c1c000b56120296400034115560010841004010050050040d180003190800a0b2440303580d580b080ca00b034181b00082c02d441404400501800c0c00c0382c66803d182d07481100001d0607151881c0c032401c000c0d640d82d01c0b00724250501001c80144080d55442100122507000024004e12403440d081c90700c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 484330161 1250 484328911 484328921
    0x40602040f050d0818120607021e032b0b0d0503070303050106031a040c14071b0f18020306030c121005010b0306010f050904060302031507020607020721021201020d 72
    0x40c141441c0c1c1144080303914503080000c0e100c4243c0040c00141030544240000060b0410b8059150b8000b03045201000000814003602e48200b800d034015103811000015403032052840301c421465035400420402d0010305029603d400100111a50300030000c10307520440d002002c1070000141e211030399882c00420060008000d02080d4841e036800c1c000c590341d42e42c00340d041d1400c00c0c19002d6149200c0d010b401c15400c1c01c1d8000c0c14040d4691410130401051820104403940c004001981c2801c1604002800100b84600010042c0b00540d140c6081034078010280e0a20b01543e02c0d010714664001012030103a507401c003c400c1d000c0000a2280c600150020f03100c1c2c5e5284118410045900c1c10070b0b0001902101c8141682e11407201070311404445808110125441e038000e86110b640565100008805a10100308142c01180f2442c0701c8d48003800c00301c4000c0d00c4c0c10b0000704120210740c45618244085a0b8451400b40802400000c103114100740d0310004a041c034000c3d0030240c0340c2d88080f840960242d42e03508a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 484331411 1250 484330161 484330169
    0x319231204030f0e0a0312020a1e020406120b041211060c0a0f02010b0102061f212f1521060f0a03050c0114070f03080403120c02060424020304060204 66
    0x2403541036091100f05580000b902d803000c60344001d01ca80208045584201180e00e0302045205554914a00340e0720103120495000d2001c200c0c440c00042d00045040c0340c8545005401030507940e44684038240d80d942103004006100038440c1d0005044054071034051101c03480005445400e41c0d40c03625003d400c0242c65040308800400090340c61000d0072080b40184900c561102c0107a010300340700e0b50346084c0403c01c0b17075a0000100031003040c440c00041c0e2690480343d01e413003050107140b50400d0359107901340002407441c50754030300ea01d0b40f41612011800201055140030071080541e007007400e030350200709000101e02580d2110f0050a8411303958810f21100c41c01c6062289804480201544a000d000e0101c211840e001c0106142d0004a41684030340c00398645284880c100762049203840c0709591401c034100c2941e00103d0102d03494000307001c00c154005203900001c01180c1810069891030900080d5100070150003d4411010901c80f00b210300300d420350203a03131101110310540d41ca00701850444000c2d4020701c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 484332661 1250 484331411 484331417
    0x5101a0a0b130915050303070501020c070b040807030213090204050a141308031f0f03060b0414041e0507150207170312240a140a050102031923120403 66
    0x300c0860048414030940300031200c1001454a21420b02020303000520070701510808410300800d002601e40e90400090903114404e900140e00c8203162039116241450980240d1a1101d041c402031010b10300000ba10001c881e0110794050740c0e060645c5520300244030880b03019422074100300030403292004a40090740b014030b000540c0000780daaa0300a0070a0340c864041c008140040400c00300d010500340c4d00102c0072610a00d0825140590384515612031080305900c1201c0541c0c0300e00c8503400c070703140a06c01c85606a91501c6a80350502d015900c106080398102c40d0030000c8445080c407a0184403042101102a06425441c040c4090030080042c1d0745c1c003018851821030451030011410302440120580b0070001120030341c22455100d0066907010812a00c040e000f0a4161940302c07511680c072700380300700020440c1d03a030300c0007102c5002c905000704030840c1d40010f8150b40c802c11040380d543c0c10f0000091010f0101c0e00d00701d410041c1c0142c245c00d0b04142d140100f079103240c01103401007040c0500b40c2c1c2640600c0c8030b52 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 484333911 1250 484332661 484332679
    0x1e090809100e01020c010c0213022b0c0516060f05010612182409060c05091306150309080702030d110601170601060f110d0f090806040b0c0705101a 65
    0xc04101c40d101142c0c012507005030000050106994080c4250554052004110030354400003c00d140c022608031003882c0c00c054400121642031661446429070050045000030b000038442d41d100580544504240c0b6240c200500d002c00c8107105269000707c514105d110828092035030b4a400c003c2c0580d0b82c0c034024842051401103500280318908110410141d4003c01d542800d40d410b14402410340c800165982035952aa81d8410020311184a034082040d81515010b031a0341901052000718400380600700500c40c42c1440501c0480104070320004949424500461614510300d0100c0d50b600600703500940510030310403941d0f200381d001008581902c1421003140c0c1160790b80d0490f0684001101c000902d290051401840041c0c8501455401c486613410300d0043c41248107c0315150101a10f01007000506044200c54001d40c4030b80500020039007130b0001d10040c00c0c1900d844a0390b5001401e100e801400001d100000c10000740310001c00660307590020800400c2101e072010f0308665600000303100f02186 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 484335161 1250 484333911 484333939
    0x31e012307020c0f0916020a050f01060e060d0b0a0b0301020f03040501050103110a150e1c14010608030c0309060c1507081902030108060a09140a0311010e060412031e090809 76
    0xd41040b071300f80d200a05590b11350f1158031420102d081c4480c0e4042c114003070a02600007040040001b00215204a030000034501c0c1780101c218143c10380070303006e0ba201d00a501c0c00c041c0403603004030602d0b410180e50300300000c0041c01d40b13001a0082c413030502e10f660080d02c088200802d210040d8030040c100c9024010034074203030a02c10104450310626008440c40c444031880144003152040c1c01008504030060110030880350380303030b403245002ea40c4070000b02c03031940c44c103103042c251060b0a000c1c1100038010800114145590001402d8480c000d11040c2c5008030004030701221100410030040f0003034000c1e8040d400035402d20100040c6011005c0780e071140c2e0b00403602c00041786440e0510880e4125040d0314080c0566482e0f02c84000042c0005040a9034003320101c07011325808814014030005501c2030700c41700c1c414004040e43c1030035a0f00100801b2001e41003502000040342d18158058200c80d11883c001a01100f1405c0c83c0c10710900f9081e96168030792500c8038600802c01080c0050480b0351b01140c04030541c03500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 484336411 1250 484335161 484335169
    0x60911090307030809040609090b09010f060503070e0c0415050703143a050106020a030215040b0103150e120c06241203160605071409031e012307020c 66
    0x1aa8451074050740030810400210b12038001502da9490018400b0880b95998240725090b01e0f074142040e50f60302405c000303100420100340300d034035602d241442041c018649000c000a44901d0030b44142802010b84900007400c120b4040111400b80c8103110032444108462075006103507800070a000c8012034032007043d0860142407070b400d56044060000e45002a6002418058510b007180d4410352040d03c0e2003410102d40940a014060280400350700034848030300c503410002d10f4220960610b80d1140c10309030500c8081104038080707038107582d00b10614952444104444600034034500c81c0e0492240601001410752500381c1c0001c046109800003220181d8a40f1508010140b10026940f036000c0c2d14020007001ca42444c50141800a141d4000d5070300301300700d02000114446c00c1c035200b00c0d040b17551386081009131030300496815000d400b40c0d0803290070941d07440d02180d5174048030303200d4041c10384c5c00200905840300b0940081d501043c011125002c0442400002006a00b041d10601c0c00b50041203114041424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 484337661 1250 484336411 484336417
    0x90b16110601060f030f0c0f090923061306150305010803091e0a0f09061502070b0a0318051903080606090604030f0201020111070809040c0e0d0605071b0501060911 72
    0x3454101918503640f0303000701510a07aa401100310709154a83d26031701122013291040e076403800c0c101e0721180d094000b108402030540c0c4460f00021041031414268101e600720b142c1c901c9112403190f86503003640c0e40700c100015220301012020f0804032800c180d408240c1c0f900004c41c0c1054459140c0b000c3c4620f91b21009040c0e1030f0b0064001240e000b410f518000e406107d1070307103400c058100c0e01500705050117845840040107c1c8090b0032289402e502e0703030420040000026180b004900540c070141102e5401c002d0041000d2041c40503a00030151a94000c0e40103c620340140c0c28102d40c01070484425120b22514139140c40300740601500452002000a1280d0400100b01e4803690001050349113400e05598800308405080402641150f507500740b4601c0d0480d2a070f005000d00d40c01848155141c1d0358000411040e107002101c4041084030703942100070b06032502c22240103140d40c4010301040542d95440c044914a0b040e40709070105170040a03040c01030240643c020760913100500e2043c0300180080c4501c0381248 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 484338911 1250 484337661 484337687
    0x90f0c04091a0a1b03021305060a050703180b0307030e0d03060f0b0f040506130e060105070309050607020f1003020d1112040b09070302030a03050901020c01142b090b16 74
    0x51140c441810910342c407101040d03001c07003070480c0042c8120250680a021100480880340440c0e400140b0140910350284114020f200450b0901e01c0d01200780001031150140c0d140007401d01454001c010790030340c1c203854450b024003c5c0d545000d40360724003904010080d04851040008900440c45440c040754404e0143d002941c448008030346c0200d2420743e0b404000d41c4070782d0381a12050414040440c440d9608002807489959000610908604015058141540c050002c0e070500104000c9980026009240c100441360304036070254a0720014000300d42488a4607130415072100407880c1401c200354141e0f000d03020100b0825002c03c480c0c07010040f8041c3c2231281109081c4080009000035000a80f030b40b02c1d2980c170142150948410503525404240341207c5114110f010031004120b000481d40c0c1000400041d00007403070000d400107400050760a15118120034040c0e0b40c08040182c01d5100315040301c5401d40c0c0b411620170403440c1c3c40c1c3c4c00c1c0690f4603a4152110461914441b003881485881035060540c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 484340161 1250 484338911 484338923
    0x180e0102160201081008071701060e0f1e0708180f070b04080c010914090402210307120f1d0d0c0b0405010e030a080a1803020d03090f080f0c040510030209090f0c0409 73
    0x3603040801440e4240010f070364248896403584ac001c0b403c0640d00001074064100b51024003894102041d910309010002000040d9007529803003000700050f400201d1940046da120751070540031020703d100c1030900b4420000070f1054820b0400002c0c0156905004000b140e000e1000d8491070322900c0011150510341e40301d00303203039a01c000c401c0e00f0662030004481c58100e40700403d16103041c40c40f40c0000e001c140d04410300056030340020841e181400480c288020305000240303040802c001c40d06101900c030580f04000004002901c0148540a803203070440d200e1407940104483c1661660745080d0500c40c1e005005660001c0c81119501400f4203001030b078111200d6025650034101a04264120303541020102031240c03002001000001584400200b041654025901c4c40041420300032045140e01c0c2552090440c0c0c0d00c131903042c44000d03070041a4102c1001c030449000c64541c42d601d00c15030306c919080e0400703540001350100307122810600003104d6401c00a00425103107040ca5500c00c01044480051010f409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 484341411 1250 484340161 484340173
    0x5010f060e01260d030b030705011115070201060506040b0c010f050106080a09050307060905030a090509010506071b05060f041d060a050f040f1a0a08010e07180e0102160201081008 79
    0x10000d4a40d9a0000c1642898500814026400c207213860103107000c0ca03000120796151441401ca06040c00b560010380030030300340f01100206a51840b651603030104000c0b444800c0c01000300b0042c5100390454001040300030640ca8445032a894400395a030712600e0000d5441d8604201000e9244035802a64101c81d00398035884007560b510b51250307014225005007280e203070200700034100005000f44540c50300a4090030003551100d11801010b098205a07800c00c92048000100400281c0d07a11801c45083c40d6008080b00d07003110000400118010941d042564001b501107040400c04030780c500076104840800d078010011404000039102465411b1790741a800c0702880d60240420304082c000607800d141c000d400010003007003103000301701142c1c0b501c15210400c0000c1005d0300315528000c0ca000010b0a040030003002404c0025008980d81c41151040f0681c0120000600640741da50741e00c519640c014000c000d5644d020380d070301c41301c04184a44404a000c61240c1380802d80b0000c1d1a258071003515417881c01085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 484342661 1250 484341411 484341419
    0x1501060503010b07080403020306010608150d080f090d020d2604230102030d06030c080f1207060c0903050303040606090c031406040f060902071121120a0c0b1305010f060e01 76
    0x42c1584c8194029290710804200010050300d00700201070007048642c1d251045400d068110850440040d5a1244114001c40703005d40410283c4c0200c4001c0d841d08089169a40c041c04007251080070031680113584803104032682018401001c1c50800c1002c0902500c1701d590000225a44150195001e1030513001e0b0000c2c04610004031540d042c5040e02c83c14011a4107002080b085801550303c682c2040741e031200300301d404004404c1c08010b20300d608690744028040d040780d40d02d20306170303a800744035005040300d510b900d60340311240e0042e076901020356000010740340d413440c06090040240080342318001c03640b0315041108581602c00d220b0700003a8405516080010703284c139070401025180c144414080076650b42c200185002c00740c8014541c443c800e1402c00c140300181d0040041260382500c1110300c0f461055107007001032601003980078500c40310212240d200c2c00103110440b83c4059603400180b49481807002d004401d80c0110306454003620400007030188400c41c50303d075800d45241d8030500480c0589100184 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 484343911 1250 484342661 484342679
    0x150c170105060a09081b01080606040e0406150314011a121519020a080a05010b0724150e09070807080c06070203030903010507080717060f1905041d150106050301 71
    0x1001250076413800307078042620742e80001d0606407801881c4600400208000a1958101d40241d6004008844840c00c0910b44501007002401c003c100404a0350368401d89098215101d0b000806035810501d2644800c400c400c0f050300a005401d100680868102d645800c5c6d460f00207034001a820f0342d4000380c802034041c0c0740c11607600c19002e8840700032807084c04140c000720130b594400780c6010002a56105000e051a074421400c50388103801050b11b90108100010110701101c4840740d0b011000c01c0700040782c42094015100602990800301e071618000748000a03c1c645519000e405440c56400355400b082c3e42d106415910000c031b01c64030081340c2000119003824980303500130389081400541540d1070400900c0001e801c55a0494110020030007200034414926440b5001c1c2e4258a500000507140e0306100c80098080000900d80d50711801c1c88030000e0b40d482e00070803802001400c004c5d209102d40d90180301c2c0c1c0d00024003e14000c40d181e00c920710b000640b0112414165040f11540c0e25100d15613400e0582d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 484345161 1250 484343911 484343917
    0xe0a05040f031206081f06052407080f0706050a0b040b010905040c0905040e071a0a020a021c02031c030f0b090705160813091d0d18030b04150c17010506 67
    0x800c1155140f4002841000a210702d90a002c80f03695007807010100c006c11513045070503a030051801600003903088070318410380c20b0100d2125940c80101988400092920340030702e01c14800c80308000800420918100010340d00800e00a1003101c10074004c25007010140000c132200310100ca80043d10440c402c00c1142056405503103211b02c2881c01c10042512400401d090310809450224240d0240703000b001032400c003803980d02c900039481c4003651500e13459400003580c5501d01403003c0c1c8070302851841c0c4520790754402c661a200f01e070b02500b80c5102e5003409519011070a481003031070006c82e0814400b00100b0310325201e0740700000c1c4000d15a01c49030f00c070341801310750366081030003071003491038400b00030502068015001c0e25030011205001d2000340d003800f5070030040c1c070109820a041c8a495030b016408444010494445400701458a80191100310140c44151652580050300e2046864144028052102d8007405402040b1400b8450403511503022960600d504200040101051005001525200c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 484346411 1250 484345161 484345187
    0x1b03071709130e060609070906090618030f05060106030b0f03030f07080f0730020309010305070221042c012c070c05120a05070f08071b0e0a05040f03 66
    0xc5901400010340c42030b02110740058400485034042400c0004510b001da541c241c0c0300e8994680190460b02d440b401070070f20390141c002e01c41408a082c0c00146485c0d0080703d510011904140072040510392410b120344c0321007013801100c00180c10418001114140f01100b42681a405401103103440d080c400d514020703070041d0004907045641000908401980107010b400f000d0700440f04600c0c100d40800c2501d658030300300c101854041c40410142c051194011081c0d0708520820300340403a00350f44005040381401b403180080445208144e040380240c504e11406442914055010155a070070f0302405d0005100c00305ca142180c8180300d0700107105603820b00c0c0c00714644136101e003144000500c00d051486003102040340d4040005840c600b82406018041000d13203075104035900d4261a095129000820310300c81c0d024003070321591004680c0820052038104440d40c0580082e51030f0f11810740c1203403000c01141d0304e02c00e201c0d01e42180404121100c1d920310415000e9540045400c442c2c260079a42500c0055135456 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 484347661 1250 484346411 484346419
    0xe030c010c02031e03040f0501020a080315030c101206140d1b050307090506090f06031b0111010c0507020a09050c090409050102131701060815010303081b04060201021b03071709 78
    0x10384c1460f00c503040800c04124200c0c0300d000d1503c0d0f40c01c0c1032180003002c282da800141158801c000d0b01c07000c1040c4a040303079002035221380e00e008810701b900e0100c1d103000c00d001304040d0008a4024825200350b40006601324009007200e003400500d035604001d50742440c41e00c80c2564450354041001c000504168100080752241408040619aa0b140000c0c1801525484449038a44440c104181c1385492002c0951005004100071000d040980c0882d0f903401882c0369441e40c007003540442030002d0b8000c0619903601c1c6040c400a200030070144e0001841030300700315000c81c0103948046010601405074050315110b9100351003d241000c50340c0042101238030002d40141c8095500300006d10741648440301c444007600c03604010100301c001c0a00308500f15503240d403141c189030b041403811149403405180580d0440303800d0f03d000b640720746580001850313259a1210002c011100014000340b01341c2c040d00605146800706d0158680c1c0c0c101d00c48081e031070384100c1da070082c1005403500b074105010304000098126000050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 484348911 1250 484347661 484347673
    0x90b13060306061809391421100b060d020309061906080c060304030e18010305100c053a021c0204031205090f18160e030c010c0203 58
    0xa08040440303890340c0060b107080340c441005004031444504d1800c0c1c101075541c000c10440c0050344684072440c407200c000112a84000566007482c400e00f890709196007802c864403074501e5503207203043d80c00f1442440720079010303019111034007001c1c181100380a0074010960300640142084c088103c00103018822000c0c0e03025006000825242c440f0748007951068441100030310311410b21030f26002c107034100103000001041c1000c006011070b00001c1380c03c02c0480c02c20b80d601c0e916501c03540b400382d4018076940c00190300910300d240425201001c00d003004d41240c0c000c4090700c1c0100d188400e28010754140101a00101d0408c010480b0803c8441c0b0440c0c00301d00d010482a03042141441094050720040080300c80c10741d0b00803035910518420741002c10203581d112242103203000c0c5180d0314151100d070165441810300c0008a0303403209a4941000b20000310750010703e01d00c5101c500c08030500513400b09852072481054181004000d00d40160580e0395003d038024002c0182c0b40640b0011510070365098400c0340c00d4061a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 484350161 1250 484348911 484348939
    0x804051915020409240501050906090609030d02060703150f030f0c081207150c0906050f121801180201080a110c0d0215160c0b04051504062403020604090b 68
    0x9102800c0039000540000c511102c5d00b040c498080100c000c4048803002c0c07415000c2295030303000070032141213800079141c668484a00038005a030602520b200280c040c0a20004040d41c0c550106601d03101c0c080700e403001c11149000714004a06100036008242651403a002d0070307c042900c900c0d1200083c0d108840c940c030407580342c41c0000c0c20142c540c810303410041c00100d6410104030030001c80030768000134201d0400919500e0180144201020300c04c50003030150001d180901031910500700c581c2c071100a95400250304003149028079820300740d451582a9440e140c071441d410355030031580340441501607407a4084c2e5150b000305000241030800700301c01c0009082102d001c000009104202c940e4010381c02500c80da80d1603856141c00803000401c036200c00c10540c40b003440c038103410143c0040701c0d5400c042000225516031414901d0019444d080303104a007501810041003204580124090300c0380500021013001001c8944111640750f408002c1d4040010300c414030051500782d1000c0740c0d01000501160450b81a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 484351411 1250 484350161 484350203
    0x902040518040206030403030905010b1206070f020f070909032d03050105121506040905120c06010e070c0f02010c150603020f031908030601020109240b06030c0712210f0c08040519 79
    0x4070b0dd404007003981004080007411038006d00d10414a89450003d0607002521400c405d450364043d0003103000440ea5688141d013411700c1503643c140000600c04500c0ba8080c1c0380100302c1458062102c490001909102c004112400d0003240031041d42c041070001c0400c00c1540480301103240e8010065904281d80d101004046501044804030200985510039600c150a50905003000b0707050b0480c03091310030703418140100e440e0700520703122040d0742101e0700c10049801132004030381c141d01002c0003500c82007880092001e03198096100000703c0b482203901d2180c051000c01456120307180d4400c1d036044c500d440000c0700d0204026600a6610800c14400080c81c08a03603584c414000d08008064500840041e4100700700c0c220306d10540c41d03080d50899008c0d0540c03400324484095803140000c0200f00c80c001520039002103000f550210512480300e0340c0c51034100c400e2200701d40140091104501c0140c00d1070798456403240114040360165802c0005000999a0302c6440340082580310000ca4150030810106e0b112404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 484352517 1106 484351411 484351429
    0x10605030c0403081804140702190507080303090d09060207050f100e1002100f060e06100c0b0c1809090d031a0a0902040518040206030403030905010b 66
    0x9244000e00407180959480240a80c0022a000b000984034a40da0700c001c1c54151020440303407940e14101e885820301640e01c0405078018103844080a144c00c2d01d444540b50061741100c00c2c80350383c0c0d000d6030b240da40101c070a103403544c00044c03020f0080c640c8a581d80000b05641d1006081007403c10002400d00024400030038441e2000344411800140a80c00781550070100400580020302592806500e0710140d005901c072851400ca141e640c00c040c07500c181c5090b01c8502e0f080b5180c542e504e10a00c44a4034195028106001400c045903000620010400384030f40c103001101a191080d080c2d24400c0390085901c0704e48546c141d031040080c0e00100183c00d0540c00014603000c1401c1d1421690f00d001a1175070850a0307040304150101084d4038183e500244206c842c142c8800c00c1d0f13001054070908001506030750007035001300100045800300e4440d41200c00005e0281000003240826400000c40c3d2035 = true := by decide +kernel

theorem cover : BRFrame.Cov 484172661 484352517 := by
  have h0 := BRFrame.cov_init 484172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 484172661 ≤ n) (h2 : n < 484352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
