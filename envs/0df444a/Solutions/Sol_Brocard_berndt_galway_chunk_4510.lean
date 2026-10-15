-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4510
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:51:12.360954+00:00
-- url     : https://prove2.me/submissions/414d2343-be15-4e9b-82a6-85c3cfe96dad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 810971223 ≤ n < 811151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 810972473 1250 810971223 810971263
    0x30501121b0b03070207230906090615032403010507020c0d03020f030d1b030c051b0a020904060b01110d02060114010216032f0d0b220b040c0503 64
    0xd507460565040c0311404281070001e00c24004207400307a90303002451146103aa0002c29420b4101003601d00394407510044916004500540c64009440c0c0c007140a0300700c0019078403804070780c65150014404801350407907000c80ca10701104101c800098030070007400c44805e05441c400344450400906085e1502203980c440940d10402e240172150405460040c1214002c0c4141e0b00c1c20711840300440d0555000c45001980c83d0345811554014800850140c0043d00a0341002c21050385000405452402690001044510f9005c4501412141404001c1c0c21a80c0204004014a000e241140040c0048421217000441141d0200e0581c003000a01407240052500209480d0f803030a940c00d8408040059414118000c482c070060300c0d010346400c0308025500c1505480424a00ca482500030359403014244408100747e954800d02a480b00e00030700011a40041c4004401d645482c680b000c028441100d1142c034a030200c0c901014001c1d0300043c6405648940304041010707030ba404c01c26942d4520a401904817200c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 810973723 1250 810972473 810972509
    0x905010b1801051308064503090301050103080711010815131b03060608150f040e1906090b060603070f031a03030406021501060906020d180e0103051c030501 69
    0x940440707810480140350032440c1000080661a003114154000302059210400307000c80c0c0040d62541800d104650380300c600500d040d024200505043ca000307401c0b076245a0088540040740148100c441c4844007034024840c559480c81c1101c0a940080fa0640e243c0100881101c495840740c28002c0c0181001d1515105140707400e01002055005484400011a6a444d01c151030641c41103000c034401b020368030001451441c0c40d1000d415200f0007469450500d000d06403500f22a65001004003643c40d00790b80005500c14480c2000780f034154601346c82d80740100c5400700e210400c01690810304000e4030904104d641900c402040c081d03036000c207603244400300d110400001e81880c800e03407008000f94213070b59120310b00b000c81002107410366126410040040c5c00c00d45140b0034480e40ca040080c01003400d8a8410704003071038040020740300c500c013081c00f00400005842014080d2214000a00030b00461004032030296581e1030125540c0000c255047d0320220000c0c1510b02182c0284250341c120741003565005411340d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 810974973 1250 810973723 810973747
    0x50604030305181c050a0201030e01062d0807080f070b04030308160c02040f02090f1020031903060e0f012102031e010c121e0b0d0203010908090103060905010b 70
    0x482c51001031381009415107486124840a200102079a000380090250540103000040a45844030014206681060000c01032a010a8060200c04502401010b2507030303a0072f0070890420101e5880354510303100d600c80100d00da070000b1414004000080045540c0350741c0e40c0803034000500480c400030300801c00c14400220700d00e400031a5014081342d0b0380303803500d00c4409640c0040e045803110b403850011107a02084070314041c03c1040303500c0c12403002150528a0704c000080003c04645102d407500e84100049004102d42c002d007041035850b800c6000d040c1501c4003520791001401410300e03101d100810400361020600c0d01c01030103d0581a0b8030781494452103a52120340f041c1713030244002c0c012038140c440c822841d12450340d60f5070a078000300c04100002c103c0d803207107210003001784503010300400c2d0892502c60888000c200048180840c00310b00d2001103042601000060984451508081c1d01942400c02e4042003200500c01418030200c00d0300c04000c580c1e1581c48950464200b4041d48001c200f00300445e9120003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 810976223 1250 810974973 810975007
    0xe0705071a010e010810050f13330b0d030210050601020321070e090c040608100518160512040206090d080a030516111905011112060406050604030305 66
    0x180075000c0d55105010800a40c0904142640007289004070000144508075080c040403815591915080c4003505090124849014019142d240125400940398042184003803441c203e102c000c44c00c40300101070179201c6012915402401c50345262a140d6141100d00e0140d41a1138a103816034000d241d410001090a00280340291005056120500c4400d0740103180708030070b9580003103140c40420181880c4101030a081042030072507105950301004c000b1481407010903541212110300c0c080b092070311407034a51340c410841a08025005080c0c403000200503149081c8a500400d641c3c43c40d0400c00c508010101c0b4640511002c00820b9030000e408a030151a003000507004814004190a551030300da556000203a91100c1d0560000c00d4850080014003655503124403140a5182000d000f80402d49003126161403000c9900d03c96081800c03000004d1100951280700803008910600d6510462002d44c82c2c0d0600d41140e4071840340e800e00344085040c3c1040c600b075a0451354076443d414200305541c001c1c15000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 810977473 1250 810976223 810976237
    0x911090a0204051c0606091419110c01091a16080c04050628090311011d0603010906050a05030a11060d09020a0b0a080901060b041403010e072705010e0705 68
    0xe103409200208165035402080300c4840e100d00c030741c1c054a5002d4500b07001581c1141d48064441450b04031032154104000180503844011000d40d00d03441c0030342d103003040c00501c1c100410302c440e18008640030481107015806100e009015404040b501c1c0c100041001c1210703030450b0465852b0044841d400035080c0548035003600480010b401d00c0c2060f40f55400328030503411044650440140800c8a904400d281030a00c0d100b40c1d100386024000f1a0030341e01e490f00180d08080446040184c0e540d40c0d6031840303040c20002c01168000400c1e1503601d50752180d941010b4013840c001d89100f581030120001d003624000800c0c0741281d60103244808000c50340760821240c0e400102004900071f071a42e00140040e40ca0305007200140155100081e1100801c0c00000c00f0300c40002c100284503894502d05001d6440c0358001d6230109c40c851502000411403003808240501165401c60307906219404020410b615030140710040852120b580c00e480d014454040e9080d10000c0c405e080c030042664011500c8548110700a04407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 810978723 1250 810977473 810977491
    0x90f0603170d0605030f21031b0a03090c090e0d0e241315030623040b010909020f04060807080f0402010e0d051f0f060302010206150406211203091109 66
    0x2444c0e99a0046070070003c2e455205c000b503411000303c500072004050344001403840c840303140c4ca0452510301c04406501039404101d111500e00032440d018032034480c1c1c02052119520401400c2d00d255900c00c59005003902d0900101a030158030103000c60a44940d5080701006002400d40300c0f00300c0780380314000c458001c030801140d07840c1e4104000065080c51181c400020180f06101d640030409180008044603110740180303410b0000901030011130740c8031f001c0a11645400312000100c0c0920000169440902c41d407018100c0c40c0082070f0070b40510108c502400403602c0c030f0b4560f04c0700d59072060b5046801d42030464000754011550404074004d54810365480a20300005000080340700100d44606152007400e00341c15146c0c5502c5103c084000015000f4518610b143c0030081c0040e508550010b912458010400304444040da0356040b800da0342c0da04024000c040580b03911221140541c540d0480e41355a503003c0d1260811811444080e600c6442030412941c0c210800418048800080005c2004090001c0301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 810979973 1250 810978723 810978731
    0x604020412030e0922030e01261504020405060a110115030f1407060f1209170406090e07120f0f1122050f120a0c0f090f0603170d 57
    0x68880006241090040d0090b1075107101d62001d4810000e04c0302008051810403020b928071034412080c21040210341c5d07985402d1560714104814012075108505080c42010b490b0305101091802401050301800b5248070f2600499a10000003448141e109500c14942c014104002c1c0c140303070600c00c1060f820561003103000424090200480c0c44003069068106070b4003200c070303509500e0821944140345030b0b03400381aa02030b2095074a442805410403103038400d600c06102c04080180740300c11840d4800011035620445002d04851414650700700354100703005002c0031840d03071100803c241d01c2040645205030324940ea14408a80380d61440d0340902503040d034400006480d6404c2134410340460041075084150309131443c3e10380c1c007210418103400c06007114001144080e40d00900050b1115030445c4a03503074054410180b8a241041b200d464401110005084d20b1981c001c081500c4030366540ca14125007146006208002102d03814400326001e83c44000e00c400382d1080c0d0b15800d02c0108025011307010340e580c4005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 810981223 1250 810979973 810979979
    0x60f0302100e040f0209011b11040e10020d0209090a18030e18072303040b0c0c070305060a05101e1701021b0105091608060f04060b0d03020f0606060f1206040204 71
    0xf41590009080424411740101d188140340d648841c00b0348841c00c0d0700c100b80d06402c80c0354440c21210765000300201d0040c2d40300c01e5009410350b03040155407840d0150883c00c5550304004401d90000790042c114080c8148504000300307400140c18000d500100c00180404425000240e9003620030350390289051760403124845400c0c00101d101d8182a201c3e0456807998103515030107031010340e050500d000441500d8602402400301045e0040d869540c032841429800b40e540e801d81d40c8131840d051840c0c0c0b004060784200001c0188107112500428068210a0350140249454118858803001908507075400c1226170071040110b28000c0c804e550404d08040c00040c40d01144800c8031084500001c0c2c080030681d1564140040700c5410410807040c01808010f250200b03044c00d0b012030325104003a0014042441c00404034003030003c0c036801041d0700c20b0020900011f019440c0780182d251601700d0300400b038500a03200084e0705802d108040f81d40c0c1c8019041558500001d80b411079015010207002503070056400d02000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 810982473 1250 810981223 810981229
    0x100f1803020d0c09151a16050d1d04050702030324060c032a060a05220b07030f061401051803061e07030603024c030b0301060f0302100e 60
    0x24900324003540141000c5804c0000c1c080507a00b10100901c0080c21034078041001c060143c103500068400b039400d19a032802c0c898141c40c1e02c3c0105102c007612901840c0f400d02d880c9500b000307407110490480350310176610a000604020440b20100ca2003405a0802c00005075491040341021084503428800d482c5054907420204200f90450030029100303078000101100c52100c1c006001c0c00c0d2041c0000c05000c21880000d40070b840c2d07034018201c41300868851010441400302c050002e10b0151448070640c1030020681003030019004299480800710f03140001e4545084818090306040d1810800c6d100c400c1c1412000440e0290b0001c03d41c41c030326281556003c001681c0901569001d0301400c5d543c054120340c0d9002c00031801d440500ba01c02803601c0c290b0200010f0315048081c0c0c50305030a00110754041661070f42081c24494200b02402440e0885280e5051022140b91100541010955040043c1d541b003405060072580c140c00b40704440d50f06000100011b00d803486840d60000440c0c9404082441c5042c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 810983723 1250 810982473 810982489
    0x111160b282a11010506060403020604050d060605040c17070906020c010e011e0521090a020126040b161716020708070602031206030a20010c050f1506100f180302 71
    0x28942c0002c224600c4820320001c00d000e4203421000481d000c501d0145141d00194480c80b95219241c010400040c1404c180921540325400908003c0c0c824424204040e600404032448000d00c000d40c0e04491000c190114440c140f1401030b5212030700209080c01d034880043da41008488460350401900034800d402c1c0892841201202a01503100d450f04c44e034815002c1c02c0d452060107a0804520340c540104100c5580004150205e141c080c2441032a40c25070400c80d110081503c0c400003017586016040c0000c103d2a841020b125242e01c0d9050040c0b480202c01c221a101480700548040003107801c0071820b00d000c0801d44541c0b8260500458070020b5941c4211801e04000d0391024001d6000400d0f4018000070145285a2000c0b0860160040000c02d942e00501048288108041546280c1c4860b24590244a00c0102150080e04075032b404c10042c45520340c0d0301d41002b131080c03480d2607a402141c803908102418902d400c1881c2c40d1890210b854240444650002107010800c0d1064040c001000d6250455 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 810984973 1250 810983723 810983801
    0x30504150b0f2706120601060e0d05030a0815030f0604080c15090f0d030522051204090501080721060e070e0a1a0108100b09030111160b28 61
    0x56501941407640c8002480b4080050104d130007030210807020748064001051480c150390803402c080b900c0c0c3e9180d401140300100d030134000901d80d2200140040c01990080405403103500c02000c020500c940207c240750311400d4140f8041750940c4483c010400081d4050060801818920f003207820344074000c003181120401c107032040e4066801003080404006802e2203240100c0001d4207050240d030404400100c22240b84100d058250000703250240c0400400344450704003035010000643d15561511450002400b00784103c011520403007000042c1a103840b01106000b9045100c003081e2001c1d20b840320b03000f40100074105a01801000008500703c16000c07901402120103030000603038024a24552032503c01000710850500610328200b021100000385050152050411000d403500e100b94080303409005140d001e1096010040b41e2500540440390804823031500500200c4134a40707031514801c003c0c3c040c1094035500214030b4010360100f0185500140c00c0c03c2e1182010700c049050005403550045c04d440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 810986223 1250 810984973 810985009
    0x1a0d0c0503010918030c030e150301090b0a080d0206070c060905030d05071d030709150b040803130b041a160b090d020714090a0c20010c0906030504150b0f 68
    0x7200500c1078111030f100d9103580202c0c030b102160090501d80c40161030380040060040410040398100c0017691680c042960317584148281c21071300d0b5615410362201a00d0400507a60040c26406400608900700080b07103030505034030740c000c0c082548454400310b545450880065510686405850340000d20810050800c84000003000a081c109044010301e41d28048900c0d40781000b15034030900c080e07580810b100d01140e40b407040c009040d02c2045045018440703203502c50108500c003c540010140f5011004050303139548080c05000c0513403110513107140c9016600512800010b8040b13805c034203100b240c0c014480075108020341c0c59031001d50b58506c1045107045915000c240c000b029a03801440d01013045a010b0b20003602505501c031051808205148001050305124584803240d071041107004002503a1401d8031501d400744d02c403c0314040c0502800ca0201400300103140c1090002d003103840381c410f290046502000d081980d410994003c1d0151007804a180d034030104c540c21113003455490400001401d1040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 810987473 1250 810986223 810986227
    0x9081920030d0509031806031509040c0302040e06070e04090309030206210105011d0402130806010e041a0c12090c04140f0721110d0f05090c03070506041a0d0c05 71
    0x107000365015500e000d000011303698410b20400e40c044440503c06d030080c15040d00e5494584d900e0340013a041d080c090360480ba82100d40c01c2c00780814004201142c20559000307039030038040d2606816000d55039030812030366100041c0200c48003440503d0607400030356810b402443c02500840d120f40010f14103601c0801003118903900d045603050141d40c3d09a8445c0103150900b40307107006404000000341a00b0007500c1e8548204d03400918103586465a10804008c0c3c03202c0304c110b8075950785501203e40400c1d401d072000e40d440d4212140b111515042000f92601c0365645109070b40c00d1040036a82c0400c4006e02403d8040e00e070045008601d103e031210300c50700701462490000d420844c02c2984c4445458000504020b04000c410b440070290340c858054060f1503a2140b80000a42542901501d4040d01904440c2d0b000e55051100e06203852249401c028002c00107542940c0680714504105507450000d0700c24650007601c1444104200400d400f010700115401ca948a4130309a840d41c000000c070ba1040f000d4001040b40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 810988723 1250 810987473 810987487
    0x908030c0d0c0203040803091903140a03081b04030f0c08011a090f0126031c0606020c03070609060e040603020d0b24060d050601020a060c091401030908192003 70
    0x40c1d0244062864490000d50b05c1d02d0305040304641c59214584105000b03110705a80b00740880130100300c00c402540c0143c0501c00341802c100c892500c0f8090390400390300180801001c03601c1004038040c0144d90300c1d03e842035107140030301c0c5550f10007100090b22410313111035483d0000064080d001303004980c0000c15052417000311000d10701c00c1108103a00a00724490095201c030060285102c051190400c1055198043c01c0061542100310b107540700741070750480301c40c40495460b00e00780019008070046e101c5175000d030b6502c410544141640c40d0345511400c030001d4003012082100034040c0b0640c107032160029001044494a03038020480384c2c030300d4110450f503400d2a401000400324021600340d01d146480b00000c400c200c14000003c0660260740d960387c0c0c07001d0755a00030a8286e03008002c0d00d084c0c568406402d01440882c6440a0007141c803510500a180c84021041101580302c0d2080a10180c6d00400b80c509244900d9084510002c80e0b59502c000c0c000c803080d20a004c1e10301003a401405e04080c6009540da614 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 810989973 1250 810988723 810988747
    0x130315020d11132403090c0801021309110309100507090f03051e0703110603130b09010b0411090612070903020628031b140d1a090f010303170405010908030c 69
    0x80da480130300094550980c40c44c0d6859400f2142ca4452a40c1c58082806a46820000c440440e16880b030102588009649442402d0148400040b590901400c00051660542c00702c0c036031208a8010000e6041035200000c40c01056020030303007015541c81c0543c0d90310b4840c3d0340342815074116041a9034a80c01603c94103038081c8007000c03901414a10002428a007490b503038400303e2440d0790001e00d9120360380c04000124420004c405429400c2e0300042d0b4000c050501c1088039000f80318540c40180140d04000c011303500420840211600d0304005404c040c6400c51485600e0100e0700060254001c0058203480080580d84410140c0403040910448020316850000380d07036448004c50310020b0a05080c02000249000c1140700c44031103005500780007099042c440d038001c2c0070307224030b0000242c40c0c0d00e8913294007240c1c5800122110060426a030000264a4045002c504480c09110080020706c614014192a40c1648196030304688101d0011500c2840d035510f48689420444190150140c08184480790342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 810991223 1250 810989973 810990007
    0x12040e0a0b220504030318030c050601060e01090b0715150f1a0403060b150d0c2c0d051504030f080a1418121603090b130315020d11 58
    0x104100d40904100102c180d481e4081c1d0807490070060305a56410002d030605001b0b405c4071100a000b869010703e10b1810b45006891140000130940c0e0910038640082002d5004840d07603007032007a0586520303101c0f41c81d02d0601282c5900c40e0034101e640048045208000e105170703000d41e21840e2400550008840e0400390544601da15950018156504100b207180c0c410345e04c8812075083d40d800000208844404401240c5140e0280030344054103400028800c2c50150150b1081d20140e201b90760f030303a012088100c519494094242c001c00d44108241800da945403403d02d0b94241e8051040702526560a01e513410040d1420003107a0945c04511540401c1c42c4d95540001d00c990f011200140c1080b4108105030344003003480f8000c1c5a00b0074a031108082e81c8141400b0010ba004001c0400300d015035584070302040c000c07814145181140410107404020548001200a8803a000c0e602c0c2030b075074002813440c1c81c0d500d03200c00702e581d01e07030300c81503081002d812092014010000c01100050009030341c2c3c0a14141c44d4100d0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 810992473 1250 810991223 810991241
    0x8090d03021905070f0203072402010902100c02030a06151d100e0606040b180a17101a10020c130b0918031b0a030e0f0904030c0512040e0a 61
    0x341c8104003501a01c80d004080300b2900b40366103040d82c4c0314041440c0c1840a00031210001e07601d0320924000140002001901d003004141d42e41a5040210381600d05078240e59440d00020740c0710b6068a01c88001e2032091000b010441d0001701100d40046407615203004a0346c00e0b44005d04c0c098a048014002080c210f0707000707050320221103044001454184d1064145550501841603c204080080390a65480c9000e5801800203120065503842c0c000d0b100340d104034014403855026518042001400748210982001c1401101c1c1c09403800181f2884410300030302e16055818400180c614451800f4ac0314100d0ba9194400e09800402c400b0803090204107484480c80d808841d464180751001c4203545610349056080b0a8016086aa6819040901d820350040050025010310024007035000705000081403d0303054000e454a415011040d0244030400031a20030544e008410b040210300080c0c462a20403418a010301c05035000c60149140025480e4015800000a0780c0c1103003d202508042d1f00ca18185 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 810993723 1250 810992473 810992477
    0x9070201060306050c52021207051003020c01060f0623030c0d020d1d061006020106230406030507060f030e0303010303021911030d2111191e08090d 65
    0x7008103040c02001a000d64000b0f40c050030213010300389801030550140100013100c000e403001400c1e00c02c2c510200480048410107a100e480c0ca00071484c44208c020030001d094680c05000c2840c82c50403228103601950060001942540d62400002004001000c18101811295841540451121400300c00d106c5030000b08000301c4600f0003e00071515a200b08850050900e81005a01c45108048280c0101040703905800300100c0c0e820000d12415000c0f0b445072044c0034000311829200d488076022070803901c0e1409240384140714179040d85116082c0d010032000d0000d00030700115090703840c0d0b55040d08002886d885103000c03908104403410f045824cc010040300407003080c029400c1d0761540e00c00031350f00d8007049000f1030040d4950708804144501000340c0b08040744090100c0d2010891079800800130b070f042d000811400c0b5116a182c204802040c0030301fa00c0d1750014482c203800e00c080742c0c00d004112051880058248000c1c0c034601c504003905074140000c2d074240e6440e000f01504c0c00e82e88850520102c01c1101c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 810994973 1250 810993723 810993727
    0x120108010c0e1c1a10050a140307120206130e06010e12060105010302092e0e090402100e0111011401050a0e0103050712080c15040203192a0509070201060306050c 71
    0x240c0c4030343e900c40d0540000c0c40b42c10500074140c0c0c18079904130344010281d4a0b0200c007440420111500940d040403c50320260740e101c0362142e880d40100300d81c0303000026065041c0c200306001c00c00402e40340c07020b80040b4001011607280c8051801807651108107580300520840038001045807968000703440713145040040d00d02091046580513100d8039418140285410305a01003606442520780d00e180b0a445241510240300d01c1034484d480391001c500c1d83c400382000805603000c11542e420012540b03405103501919469254a032050203847d441140d045d600d04010400c03440a21a01007400b511055400301d2030300c000194144030622204001f2070300245a10003a2a00400c002040002c82804941c10036103640c50021240c034004025110340508100c01d44194440c00301072000c4060542c1c001c40c422403c072407080913040d401d0703103000480c9000941000060007551003601d068442040f1200000b0360b002c084036483c0c0000921a5105862200040c1c0d03441c0710030300070800a407223550b0f00495002c521074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 810996223 1250 810994973 810994997
    0x150a1104090212010602070b040311040b1e01300c03020708120f0109060e15062101030b0c0406050406180312020d08061e0108040c03050604030f170c181503010b07050c0a0608041b0b120108010c 85
    0x1c403500c0c0d8215038050150e03540c3c40311109da0611a606488085a200c8030155441506e41031301a543c1d1000d50703190f801041003e000080d01c004c680f044034100c452050010106036103020410071030382d030141d119039041102000205010a02c0420352207181c1e50b003130144807080d411800d2420003120300409640c00c1c104208428088590014159001c4580503c1d10b051079000b900f403025040b0090740c2c00140900001c0e00044c0d10290003040580062566a803200c140303941c0e0310204080202c1c5000c0f040c50102540e03081a0803944652a4142d100d4004c140c00320300b41d90b076030742c03141d10b003200448040d00007410b1255100f40b4154414000220303000324024080d140c1c141807071a070a07540715104040031180c9a5a40740c10982c1c8543c0b00b5152951621400603031650307507503400c2048942c0705850840d554064601c5c403011a24103414000d06076081680c501002e50f40d03507a10b00841a000c80b404402c4a1030349000080c540655400400498018402400845d45082c02c01800c0d02c0c0d4200300c80040c030103104114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 810997473 1250 810996223 810996287
    0x1d0f0a050303180a06050705030f1609050f01030e0f06040302060a0e06010626010609080c09040807020f0607150b090f09150a1104090212010602070b040311040b1e01 73
    0x28070b4001c4421843e034401c0b446041015450040c102e040103214608213070800800c41d40100c003441c4034004450b1a000c140da282a065102c80c1e0700861036030301142c245801070180d818910a46e0f40740b0711040c100003480b0940c01030900d281501e00080111560b0001d400c101c20181d051000c0b070f812503d544828490010f2004a05882d204140070b101c0405c484072040d501009442c841d060001d605004805500e035868201c010008612805011028411054641003e09119240c075100e560096003031810b0007185c0e0308120200c9005640307550f0044091011381c010a00402910421a0004100040b02c1c1d101030240400080d00a10803080d54010310100016030b00041800c07095503032808141141c980d12017800e24028401c01c604207000c100041404150281d103070380103110040d842d04404640e40c0c0d0350001269640741c030740280d908891040c0300801c00191020700d10160941c00500c007040d0840c0c00720104000c501101c00c0c01c0f003103010851200141c1d5801050300c82001d00c5056200342c4810344807400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 810998723 1250 810997473 810997477
    0x306050108190c03110c01140106020312010b09060715020403060b0a03050307030309020102030412050307211409012307020906060a0c020d110a0308030a111812101d0f0a0503 77
    0x10550b40307032190800031050b40302e58001c4503c5a030002410391100086912a4001c2891004800c3d0003041d01e00003090b41800001600e0580090f03015440c2c17281e0030801804482c1c1c0050101642005062002e0400620305041d01c0804880b8807a0040c1c940e403444c03c11005654081c0e0506010390f00c2074509101048021081307942e2103800d0b0401050001691004070300d0751085902c0040703540c402c08007031810083c0c0400141423541c003c1109a15401c04100c131111801c40f600d950034049203581100c100749447c2c02020b03044040050504030141481c84860303409203010340c0c4288182c11170000e4042c0440c030384440e01d41d410903c151105810074503c0007000d0500e211600020b4412100c01541c03001708254800381c501c41c41000380004022598902d000e041580058481920940c10142481907440c803080c280d40d20410183d0841a48581c00e005110034280070315414083c134016180c0303a2040c01c400313015103000e01a08a0070910100000b444480c10080400e42442c070f1600080700d004081100001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 810999973 1250 810998723 810998761
    0x13020d0203101b18030b010e15030105090109150c0918090c0e0121080f0f04051305070801080a02010503011710111902151501090312170c03091c111c0306050108 71
    0x1080c0d40f100d48440321006000301c84881201c1cad066090508203c001c00040d040002e07514030404810981c1086400d100050306e044118200021341203000405c100d004078003141a0b51140f00c0030000e013100990310740350400400d0f500a002c10011982c0100001034504064400d0845010030803044804150ba8001d800c1c414002c92600a03c0b001c100480700c5641001164001e100082101e9680c951440004001d0305c0111058004034003220000078801102059121641d43e050352610301e583e08211003001d03241070b5400c00c054a4841c00f6010344403038032144240012980d008019549841c03201d01d080241c00204a000f8046400c031200a000d01d0388010340d010f40082c030619420b40c2c020340900049070142d50603803014040e000b90f0291035003a00e41203840d46005040c3ca500115844e43d800b54100e28600c81500d20001d2a80004e8201c150008200003441d4420729500c1e010404900401501c3d1800d10101e440104021810426103049500362042c5001000b081c2488001c40c40d140805403081c120381c10b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 811001223 1250 810999973 810999989
    0xa1502120601050306030c03010f05060108160203122e18020a08190216060506100e0303030a0c030605120f2112090304030b09010c080702010513020d0203101b18030b01 74
    0x12010031111b681c2448401003019001d00200301480e02c800000303000e40000e403030050128440101240c1c0c0d0011311445445888400c0c0c00952800310440c032032801802c001070414102041c0703108407040403401201d05119440a00100000b51800c2082c1c88289400040f81c18404501c10001a84039940100702d0030f51003042025a0280003009002ca00003034420010444030f100201c0c0d002000b0403a8542c08180500401d98145d590b031007542c01c0c142c4500c000040e480d50701d54030600c0080e03503504090f004115101303d603140c0403132611358410110f581000072840d2101903402003440754030007038410000c0340d1240a00000107801c1e21f032180e000b00020b126071403580e141d8010602c0014040e11040007260011540043e0302030b031600d42010454020044030500c1c1001606410209a2003441400349034010003040d00c800f031030b030140c0c0d070300700036001119140c100c2e018043c4403848a107402e034038400c80030718500301517441d84491210b100082c81444524000c960340c4a11650600100e49204905810f4179869 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 811002473 1250 811001223 811001227
    0x80f1206041a12030d0c0c050c0103050f01030b1b03130303051e01060c2409030201050f040c090207030e0d080301030c1d0a0203071b0510060f05090a02070f06060303020a150212060105 81
    0x14035803c2e08500c80d40203229100e0f41032000705901541d120000c10280c034040e000742d41c2e030048031400440a45405840c2850515061001031020030740d0780044a810400000c2006181404000010020380045136204d012981d41905201891780500800e540302040c04c04040b16040a030920115511041c0215020402802121001c1020314072510400d240c1c0b52681580003000c00c10307000701408902d6411001542004041204503503000100c80c080c075800b210f100ca841d07040c10200b90083d00306200a400b000460300c803003011900d881c100d4413501c41c05103060355030b00d42c11814855a03817045a4400059004800c5c00300360a00201c9100f0f40d0041340040e000340e42c9440e9070408031041d880e5061010a20040b0000060400800240e9014010b014210600100b560384902c0c103210700441c8541d45d007183c804070000e19602090740c01080914421010002600103c0e101d0b03000b2a00d80f40c0081340560f00105050040c042446403102500c1b00c10a0294901806d1840440b42d4003c0034007064144040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 811003723 1250 811002473 811002499
    0xb03240904030801170c310e0d14030f010308090f0a03061a1002060705070c0b1b1006050312070f08030f0403170702031911030a051c020703022503080f1206041a 71
    0x104007004c00c0c000c2042008c0c09500141c20700542c807101024480d1000c00c03541d001c0d19458030102415a4403c900c1d004000308242e02c1e41c0c0fa00c10703060348000e079416030040c40907184800c99590000c00704c1c05180110000100210031401c0e6403000c071741d01a81a4407407031904942001d0a42d0004100e42c1c0841545444da0325203255103411034050380682c200c10090240481c00e506c0181c5404140344200f032040f170455258070711080004044a146001d1160541c00c6101030310a4200580010400d05104416039202a4502c1c0c0740d116a40e041035401d0300700c00202c0010311041c0341e88003140f46020381c40c54403c89140c0c1007111019641c0d01c00c40306250110145850640c8009010f0381d030002d40b0000030816207590384481720000300301394044105580d4a00c1c1146090400175070510945410b07c0c2d1540051030385101c680158000c48104517055010070502000120000d4200b00140020309042d00c4003e403180350001c016074440c2c90042405020703528103420140f83d500400c2a4800034901504c40c0388900034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 811004973 1250 811003723 811003789
    0x14060306060304061e1a03010606030608030d0e1e1b04020909130515070e0301111326160303200c063118060b03240904030801170c 58
    0x1d01d0754100e172590f10b000324a20f420150051103844902046000704841b0b61a1402903003190300780d00402c081a07000744030642c502c4515a000418494101e8110b40180c5c07401a020003044032503542400c0141c011080e413101e200000801500d041e03902321001d40c20480d0b003402061541000030591498034240703641040a220041c1701c12404041009030141080c0360204000c0c0c4000c142e15591402986002034005079075028600342d420244042d60034030003142c5441008440d802141c0c50307220001458240e03e160b51002040541d0024540c619040d103224a1814040c0a02c6906442c0000140304000c070581a04000324a21045150880d00e840d1074141c0840410905c1005144ad0200d644e926501e03d40115250054030088540420a0300c0354804c060b0366010603990548a800c00303259042c40802c11a01c0c4440c9011015282141c81d260000030b18400160303280d50075142a030100301600014401d80a03661481c0d803107007205100424040d0343d010040b550040000c0412480110b50b121041b81c00c4d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 811006223 1250 811004973 811005011
    0x307021b0d0b100f170307020409051c2609120f120103050c0328021c02032b0f0e090a1e0c0e010e0d0f170d05011406030606030406 58
    0xd41080c4442d00e58a000d2a0580340300752140241d4007000c0c2624000980c5a218800302c00c1c414149102841c01c00c01c441d400d02c0054400030302d04076030074081d40c421000904170300b60499980075456502e140303c1c0d189034948520409252030551404485e41c1c0104180d1580025405111030a100b11007542d0b4512078154858a0007480e03580d02150905200000910100107401c1c86400310442c00e0b103078503505040d541c90400794007c0042c0403138000d03440c2c41000351500308109c024181520401c5003911a0580c0042d003400081e00794225444e100c080407841e51a040980e03245a040a800c001d41541d000f02d0300503141b02c4403149514811166000040c1080c2c10b40d1308a413842c2c0000c0101c41c526410b440d540c000241040c1f4104000113500180c101d5801c1d031145031a000c2002024007200d440301215108d414060b03519020079030b10102c02045c2c42007a06251401401070060b00c0b080002c00f0350408001101040c0046131041c410032003803080c00240e42e1400216600700354050400204040000403c401903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 811007473 1250 811006223 811006249
    0xc1b010e07170d080f010b0d06031406100b0313151d0a030215060a0506030403110d090e010801090b0c03040f0f0803190905071707030203070605130801020307021b 72
    0x14041c004000407010030084454240c1e440440a0720301052240104440d003c1d000c030380c07805100c029580100000c049207002001080c4a03030302c0100d01d05840381c039400c0c1c0c005000240c00c10540d2107035040041c50101d40e400440a82034a900b590320b0b5007800248a590b0007641e480c09400107413aa100552484d03400d038007620005000ca48124031a86000b89015100d000c001804e5000d4090152602d6804d5440580c1e14402c840040000b0845420401484400d40000f00300f1801d0010f004480001e8410410081c140b00845e642c2da4503100d82402d508016014041e0711000d0168180303082d071000200c2294056501c861041203c0b0784a944d0350a00c0d4412940c01c0c40b024202010b186405024412041c0007184504414071016440d1900015200b08440c1e040e40040c1a82e00403000503c0810240d150458001c0d8086040703a4201b40c49400007030408150380d21010104a00044080a8102c0a500040201040b01c021825031030845c801070345075001d00600e070400c01a503a0b0b0b450602d545506880c50a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 811008723 1250 811007473 811007501
    0x30b061e033a0504031401240f060212040303030b13060e01150c0203060f150402030a0507140a14030601140d090c08070b07060e010b09190b090c1b01 66
    0x44451050b000e0004940301507200360441d641101c800b18074004240c200d07101e0001e581d0380c00e850b0900e1600c44040c060345403509555155260000c000e0f501d60342c03040300d1889000c6c0c0d07040e041c0c01c5c928010403000c200e0000e9022a045d900503a0324110b1614204058504981e0103007000b007450030803000006d404000700c00c0c8208100b450310743c0c00b0441860311105075040e1505040550b8281001e4202a40c80d0705020b18000d51551040b030000d04074040100d400b07500310b011851240e00030004403001905a070011036103c0c41c42640c481c10403080030b50142802c620441d000e00d805107481030000005000b1b80704d0001e0202070042c0000402c845921071400ea04072900c14441e01c0b515903a125082d0006000070590036610b401c84080080f541000205d6000111000e0b110385a24201705a075950010344001c03000c00b80e207950307032340c4000680d615540b12281c800c11102c0701001c14440000e10b0f5104496000e501c1074020b1090a041020524a120440f1418070b100c0c5208101c6a04090600c1d001d40803034052124 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 811009973 1250 811008723 811008733
    0x1d0f0f040b12150c0304050303151f02030715020c1b0d0804080a02130e070e060613031208012304050402190b0a0816050703051308190b060901030b061e03 68
    0x140700e0045842d03401c12403580c014129070b865604c000c4550b40001d0300c024000c0c0c6c00400c040380c1d0111076440790504451000c3c284003000100c80407901d941a44845c071201c0036130000901c900400c484030201d6030241d10b02500c00c40c20410715141456881d240c8a250f42a144040a002d004590f6030104901c10703240c1c060b00e2195100e40700c4541588601e410207040307001d00d1001c00b410b20f418100780917a40710000c1190007000140c0c50901144940c0402034121504060100074508a1016946022002c1c41c082d0011407401504c01d80004d02c16070050f80440c203542c200c00301340c10055051119804428000b2100413030a52030703500000b00e01001b0070182c1c00051000c82400140001000e0123095031003080d840307603511703541c410100d01202c90205200034002a400c102000009001d603001c0c0540d00084140c1c00b40c0143c890840620300402c010404500c1e810360754003e41000000d6140c654071080c252600400b551441d500c145c1000310141c071061058200c00c0c04000c00d01003040014000080040c02c0754 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 811011223 1250 811009973 811009999
    0x503040c1a0414090601020d0e2701080601150e210627010b03060103120c06060f2d05010813020619090f0303080403030c1407050c011d0f0f040b 64
    0x40903a8410f00c600c80d19200b0002c03182c4103e190801d0b2040c42054181c02505c1254886a81111101c055081081d40306a5003146580ca00011003569102d5180c000b04011403075060001052030541d05902a003e041007100b030f0740041d25400401072070307015001d03a90940042ca050110140940c0fa40702130b07040078400c0780d08200320325420f4030542c0c0082d26041499010519500c0c01035003650354441280383c06a001400400c0020040201048101120318100c0b0150702e05649140a681c7c86600840c81c0d00520b00c0b060203550010b00414840104092220701c9100c507a6181801440fa00e100c4c031414414618009920252501203107982194010209555903050301142c0c0c0103903403030a12417400281c60841c0490039801907031412007a240c01d03480b003002039034503a074081b00a00f02028420040040103111310109000c0c20001d0858184504040d14100b251100010222048580402c1c0d691450044a03e11619804441c807403010080d11500c40c0c541c0a0380104020b0311520300c0140c3c01483c80c03d80c074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 811012473 1250 811011223 811011269
    0x204120309051507021c05010209030d02010e07050d21180e1801020a0912150501080a0209070206010b0f0c0102040e180f07030b0f0912030109150515040302010503040c 74
    0x15000742c6008030380020040c400540ba109103402880c1e4000e400440c44284004804070f1503010100709482480058034201e127140c046401e00200110f03000c0980e445607e8101c0308402441910054a02034604450310702442d21410f034109004003032068488a0100049600c9201d2403520640c10203010174041c44580d16400345030000700c201c034071043c800d404103030048601c01d040c002c607484c040855035010755240c03c02500b00c1c082c513003905044a0984403200010b001039810b014860007408201c025110824140c018000600c100400035821508100c005000e0f84400c2d20958901240240c04162681c1c054981c0e540244100d03040f4812600440c1c0800c107503041c15944450108441c40d0946180800501505aa07801e15002c01080845100009128119440c014a500403801c0742142d081d850010401191a8400c0e044840010f456120f120101455411480300500d4181d820420050352440b0551103070156000c02810000000082000c0c000003020802c0070340080e85812041c02d6440740c00f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 811013723 1250 811012473 811012487
    0x9090406090f290c0906040302130f0f05270d0c020105040810050403020d05071101030f02090a1e060e060f0c1501080a0b06031b0913060203040605010608011212050d02041203 77
    0x40c107008203c540001128501c1080aa0703034585400b81c000d030700309800c41d800c01c6002c40c2c0602c21070034880d580d44118525400d40f0300698203900e000e600001060b00b003240700040c41d0369248c0107000301c507411782d07581c41c40d03240d00007680441200302d601d02031080544602c012583c0b031140d03901c000040e00ca40c03116007000b50130301d522560040d03109070201e440a04c03074034800752906d02540d40043c00241030000445807550180d0010340300041c640030b0061a11181c7c030009810008a500040c12103244481d102d0104004015054003505007424242068200100022210700ca800e2406403640c2e4041f8200380d02d9041001004040347c8000c24000710381d0b84032100c003030303072803001c800181e230a1119000443e8180c02c002c035500205240c01a80c840b880b101030014001c020b0009891480e05c051660040340c00701d50036102441c0220b103e08004203007945880d034000d1103d0f106806c0340c0e40034030020480f40001085405400804461402d0098455401c0d030000f80c0207000d103600800d150700824035013034201039002072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 811014973 1250 811013723 811013783
    0xf050a05010608060d08120601050c030a020703290615210f070801231201020f030a0617190c05300601080309060d181a0603010209090406090f 63
    0x50b54507103a40d40e9004021000301c0c00301014006d10800c00c101e000b05c01c034086139580d101c60181006441d05201c820000d00c3c680c4180e41000041e00007203c18001c00400038040f6101e081440b00e118810000d0901e40d001901000c0c00740d5200d44610a0002c90310002e0ba003d6550303030f9881820028a0444044d400704a490017101e50005035031054000907007180c01a0800790507510000b035031040c0040700601c8031010b03200703941001e81d2150036091000c40b82c030024001002d002480640051f104c0c180881e03a40c3c22789800d600807102841c010000a0700c13000700001c00e40380300404024240c200000c01d04144c01a8603554000c01c1c0c002c52022130340807181d480b0b03000520314654240089485403054192841e10b40307d080c062408603400400c47e008180c0703442400381448159015001594a08103e1254000c840018003110042e0071811040345005200050950104066009503e4103580a0004581c2e40000f880100f25a503200880c0d420b001c070b980d0040200c5c950160b8040c101c041c044507512888041c242d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 811016223 1250 811014973 811014977
    0xc0b030a050a05010614090301420602120318030d0e0f0a030e040e101802010810350a03020609161d0c0d060e0103030e0f0307090f0f050a050106 64
    0x100071602c2c0c0c00542c4120b9040b924030740c0d5a07043c0700c152010007071015840528040d40c550348501043c203800110b44407175904a10402d45009804100d04100e0900380c181040078044c42650110400c0103035000b2403005400b00b42c509032590342e0f981740c030b885034541211000c3c80006440b001c01d8081802e5510342c4400340307400403039048407004100301848a036900d154000050009200f0b109043c0725041913009a4000e55001c02503480601c4e850038182c0445031811034111000816013500c1055581240c079554024880d090b03494012410900102d40500c0c14a1003800f640c000200d6494403000015003403540c40c120801507406c2101c00c0e05009548807001d076424041806000e42300005070710344ca241e4400310303119502c41786010f000800c004075200200408401c0d40c0b180c01c00101180d00307103e104200142107071266210310781d4114203006040c3d00d805885c0c940100340c4006644150380d0005900c50131100501e9011038406060800039000e0b000e9038101000c02410318061250210858200e18180e410903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 811017473 1250 811016223 811016231
    0xe0a020411090f01030e0a020306130b24011409100801030b010504020408064312020903030714030904090609021f051e09060703020610061103090613030c0b030a 71
    0x19110481c21031240d024103d6200000c0001040a540641c200001e80d56440d4151002075502d50041703801c244c0c2c01c03a500f030542115075085e40d0070000c04d8015981c010001d20304c0085050008072102e03021403000c4000505010003030b0039801c0049142000c844c1a038902900100500314460005807c0000a00007142c041007424000b161034140381c400e42e030498074440c0c01003541c0c2c6c6504446101000440e05049004d080c20303000c58504d51400c0320140780b20104100c0a141040329403c0091440c0640c200c1582564010006010b0782d0354000140e032107582e00070003030703013840e184000c4494a03604c20400e503a604141001074000c14071100e588030192160007598034440b13880a0b40340303244c5001a640340e00c4020400030b01c900d00410a0510501003641d2500d48014a001a54000205550040c580c200c0050740306004100500c030300c104035100100902e081c403440030a000301170580c1701d0092010650003210302040254040050149081c004c507003141d012569a610303a400c000c9103030b00440d5006072603810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 811018723 1250 811017473 811017491
    0x706052a0c0a09020f0414040204030807050313080a0c0e070201061a071509030912151a0102011401150e0a050402040909020913020901030f081308010b030f01060305030a210e0a0204 80
    0x1c503000300c50007a10306a010510b413500303040421401c10018181c41e03401a9003840003000040703c80cc018500503025800071501c071019060b5095118995400000450700135280301400900e580c0305210a13603031114450030795540c6440c4124010090782d0f200c4281035030020031980c0400055402040c881c1d01034603a0313101c038140a4844800355080010020009451981e0421821528080c4807503402e10030380820400c3e101c0c0d002c1000c02e0b030b00100c144110602e0f10b054000e4980da0244500c4100030707880035017031111391b2600ba00c541c800e414200a12043c0700d07800c0b042007002e41e90500008d024020050085403201d8840c21560020301c1c3c3c01c5001c90243c01d80340b01241d4081d40c143c2000c1e1580da402420002c0c56800e44d40e52a00540810400b00e880440522040407203202c800c0c00540500059000018000300e44001c040c80d00b4003982c0140f40d60f0749408002e00120320003004550781d00000e4203200056183d1564400301c80c2c0100300410b004680b41080f070200c001e001103401941c10380210303014005159 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 811019973 1250 811018723 811018739
    0x803070f061815270206071b03060f0e0d020c0915030a0b090c01020715030209060904020d0903030b101b030509060a021c031404020d0201111e1903020706052a0c0a 72
    0xb844d12405400102004502c001440c11400400c46a40700d4644041a01c030721160f9441280c885820848025840707030701190200210744501000d0389040e10007444030766a48007000c1d40761100c6009460141038520b00164110065004d403d040b030743c0c041c1c00c40d4169551800c0c90030f0103441c1542d890b10f4034012240150345640c40000c03482c0a6420154900354900400d2500760000e5102c0c41c007040c1c00c5801800030b034040c3e0703a03140b02401c03040c65407030408551041c06280c001c0841c0c010201080c0b2030f05e200803525104903400101160401c07084d0640303048000440c203081e0303100d014032404150b000b640040c912400b00d60115070318190114801144500a00c00113068040d540b9842d45440080c203480c0005000d46401d01054070220300605198408500c4884c00504004d80715510000355120078003c410022820071140070643d11040d42081040401c0d0390094442c8428030803101040008256039540140300d9100e400e10303c0b8114525128203454441c10350b29601c0c0030340202d2080a0784e0600040b645 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 811021223 1250 811019973 811020011
    0x15130e010c0e152206050c060919150608061e010605120a0b0111010204120c050d0c030b0406111204140f0607050d0b030708070e100803070f061815 65
    0x21000070110000100300340052820f80c0c0140200d04140c611413501503400356a8282c003100940300c542e903400c1c0c1e00d0040c1700581d40391040182040d030055200d1003c40b82100b003103480d6200c0c00c0354004070308140c003060000c0040c00b8001d56040400240a00d0003845002000c5070358155242054102c41d182c2c9a9840c14166410700546031045d54400280b03000411840f455800289400c005040030214210010345c1c103402c9800c150002c0d60f0f1a0703000076400061001415041008010403031380c00c1c6031050541c0e6030b002040c0c00c502c001014400c120b00880c00700000340e089158900e1403c60305584810400b4004040d16009035016901c06c4030300ca803100004200400c00809400c481c4000b0400e80d1185003084034580e0000e41148095960744440c400340303a40c10300c0454002c1401c90004d0988038203190300003060101c050088444041c03482e900304403031200070099628540e04070141d004500e230b8900b00b24020f0309202507400c4400c5c141660134001c106d0207811003410f0700ea1140c03080082005550200c00f5038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 811022473 1250 811021223 811021247
    0x105090606090a15032301110706050c0d180b0a0524120102030c030603060711061306020403080a21060338090d02010c050403081215130e010c 63
    0x40e0446000200710703040c180303040b42e00f000c80c2070400521152000900c00300d034a2250802c403800c456010101c07101c603408102d008407844c01c00c0300030809900224500c180510030070380010b00c0e080d151f00004032807030b815105407000c0c4400003074144482c090444c20209019401e0f80c0480d2100006070128020802601c82c8510580030400b1446050f40061510740c07500c01080d900580c0001c0381503d02c6030288081c000303903000d0408240d842d900c03030401004041c10014010210390401240e001210307016000006e0070f603040b200300c507035142e00c006490400d18080c2c411508054603000b4002088840f05510219100e0b01c0d64201d1845a00c1501010a09040c0c908621020303011f00c6000c0b050901d444400c15884014000703400b0390000f20b100807002104e50107411036450400c0e80103007030044583ca4080c0141c40742c0f1445460403526050459640e880d250155400403e0301107000340c0003801038a40744104549184000304030b1041d9a2101200b0b20182107006403012055080403419041203024a07038006035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 811023723 1250 811022473 811022491
    0x215161a011512050c1b010504140c0105041403100207030c0c14060d020c0321090d05130e06012c0406090c05040b030c16080301030203060f150f0303041503050105030f0105 76
    0x114903c559190084c100251803034060003000c210200050400444491891004100124076440c0a0526081c10620419810140c1d0080050f40300305030f034454112400e030b030454090038003015226004280350035445071340d2050300f82c40000c034041890381010803218414411109048408e031516418404104070007c00d0f074000c02e05011030001411076030003404010004908480c00c0403000140c03080d10800d02480f140c81c603200e020034048070300c1003800611340400040c2019450006840ba02001d40402071003285141e00c01e140c0070600304c0e03104090b10f00c100c18080c500c0c0c50001c1c40480300e07220761709403208400303201c1c41c9014000990419a402040700988080d01c07518185031401d014000c15910007410351405000401c071014428240181a0081d5806000d40350b8881d81984145840e245018100c80115400c032010403480c80481564140001d805441101054000b000800d1440c0942d0f0405001c0d00300070b041c2c503011907915030321090484508404a641e0045501015422030341c060381e1900f2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 811024973 1250 811023723 811023737
    0x608040b090a17070213052a03070512041e080d0c031b080709170c01030b0108040b04080f0403061407090501090e061e0d060c030e0f0304030215161a0115 68
    0x440f0100003009025400e001500000c4020522002ca404542d0103c40c103c0f558440001400715030034040b0f10b03c6854100c070020051445c1000507010349103005095404c8450709080001804000307507140074840b1001d400310f14030300c00b9405161081c2d554000702d41400c0454070301580c2440181c801d000b2030000c1d004402540c031191044150031110480c00511000c02c0c0b00001000142601c050f40d05212802e0501c005092609036410006003502d9040c080c0310704200c0c0620070320000c506d4041910750000d51080b0050340e510b02c41d000000c0704d401298000351030149085802810280d40c004803c0c42401190b131188800da88030310040d9000c00a502880d00250083c000169403800c00c0c4110b42040300301960351425034140400081c0d0740d6208030100300c820946600c56920515018002e259034515100301510700c030200c180c4100c0d41c034000c0e0700c00030b48160007048800c1c0c4420400000c990f612050701031128503520650130200c03280c403640024000b00709540c0c4000074458807462101c203144040342d80e43c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 811026223 1250 811024973 811025003
    0x60b010f17011a040f0308030108010b041a0409020f0612061f0215060a0f1e0e010b070807022b05210f070516170601080601030305030412090806010608040b090a 71
    0xb5140e443c0700810b07824885000c000c042a500d903500c55000040d03104908040c0e4a604000b440c5007500c0400700000d01850030f040f205504907007009040080c100042c0c60008000405000080f214100041c01c1608410000f4005140c049440c807820300c01c01040c1c6010600c0c1024044020941000c0450000181c02c1652090000d100620305035800c0781d00106512111034540007045c8400900d51310003c050a2081c07103104100c001003021000608441900d89410b40c0b5100b6200882d00c620f01000f482400000360280841d40d4540f4000813044405400502008100140400280b141d0400755803521440c5003a003440017040d0072841a014407010311138204000144444144e4000e644200c4050060140782c14902c0e40c0850241c0060000510300601401c111401c0d40c141241070700807000c950456001031010a412000300da42041d07201d90f0010811b000181d084840328826000042203000c2e100000038515480010103004601910409206840343e4450590b1564000d000030400b90f0411052 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 811027473 1250 811026223 811026239
    0x90d080c12011e030507180e0d050301060f050c0d0306031a07170403020f2b0518190b070803070e01080721020904020c0d030e0601060c080d06080a060b010f1701 71
    0x5102007480302da84400d0f1984030381d038076810803545400065030301020703503091003690034140102c0c02d507043c5201c040c012402c001c0f0402000d42c803050045000340142441c8220310b851140d01100c500e0541d0000f66001200e808400030054a540d10050b50015400d01c0c810308100203000c5130500844040c3c840c0140021682e026482c030020040003a0103501a01807900480b2105104ca0407012540341c080445164450032104001c9842034000b20800c8400c0c000c5070743c0c540c06e01c0700c1c0c004041e0045803c0c44507040c02c4403002c0f42d965019040b07528902c80100f47ea4040004607400340d03020326203a48030800584840001120b4200048034088009240f20b46648224401000a071341440c904000151416410602080680c1e210641c0c843c1c942d40403d03608070b1804e80c94841d03040250f00c03aa01801c203d5140c800000c00a43c10003401078420580010506d07103030f0307455602080c02003000d01c06803000c0d21040c1c10004014120020080c0c08512503841c84042c05214031524900e440302c10428105d035034241400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 811028723 1250 811027473 811027499
    0xd080c070f060902040c0f0f030e0c1c050a080d11030f060915030d05070b07020f030d0b0a0504050c0910051614251d04020a140406050603090d080c1201 67
    0xc00d80b18030b43d9030100b160150b00c0303500034510500159224100e80703d00c10800180040525209001014504590000c0f14040407e0310040d0740000c0f900300103d000d021900144030904008014024840d00103d9010010444060225481e01800400000703100e40c106400900c800c0300e8540c04442c030070b00020740c1c615080703d10a40044c3c04a0020101001d07c0c0040791a00b008120a40080b810120301c2008100d40c82c580c29170f01c05020f1000d0300a0351038441405e6941e0040600e50a1455140d0f000c04846031524080640100340040061000e401c003e000e01499038041d41045001e5260040000541d6000e042268007038000c032000421212071780c0c0c840035420b01c3d4075000110300c0d004540100d4881c0c0d400009186400710229284040f80d413801a280050389581083d00d08061108000c000140e03032183c0580003210800305881e0302c030140150010b4000c02c055004907601000c0401030044111000600715400c444903210700c0c9407a11201a03550160140c90350300010b01c0b82c8180144030801c86108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 811029973 1250 811028723 811028753
    0xf0f060605030d050c010b033007061d0d020703020102070b0c0102041206051f0e0a02221518051e06070609080306090105061201091109060f04080d080c07 68
    0x20000030150344a5000a007452207102205000030780128102c42c928000303205082840100310000c101000c615602c0c40b00a100d440148225004480752034608900b10f4030441350301d50350001041045031003c1e116504158400d903000c1a262040e070055000c5c290000070104141ca0b0140c00400c0b0303807841d04042c0e030030705c0c0d0140610414030354090000041a80300180c0c0b5001a44c80b030140811189040c820b4126071002c65110881c1003403c1e41420044107054a10980c0c00c49036200c2c01690b528803041411100028a400300503e8004c05503000568600e19105141c01d0300142c1e13505001043e5034a40c840e40c00002d40121741d4007030b440c0300c444060340c88021900444050007400c3c4601b4241980c445900326000f682d07003603031214400404c01640e4604408594090f180132a0420b080072030340c5100300100901401010306103a601c0404002d41c060010944001c41401030217156903148904e44027131250040e11850b10903205104260980300d00442d20382c0d00c0360365081c031081d00345003075030b1200c10f6204803030780c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 811031223 1250 811029973 811029983
    0x603030324180f06012309010c020f0306070c031e050409020d151715041a04020a081218040c1209031713020906101704110405070f02060c070f0f 64
    0x5400a500b000024002611074442e1254081241c80c10300000743c1400c4032580700c0074400289800490ba0b05501406403264000300381ba01e00d442c500d040c40800c00700307400c0307804040d0705220382010040407952100200080d28401d98411501044041c01c48035a800042e14050209506200601c1026803d41c080c1c181c080c0c49010209881c8042d440d10941c0c18510380100c4020061031010300ca124504001c036000042c000203041c0120318181e00c54030201c945544100c034000c40d443d07001c5030541da240c2607840050301400b82a80c4c4101900700481d42181d1103505105031072038141c0a1000e651925104044648200391500e07074a1810020f0304100038001c1074002c60a0044002c00e400035465903020a80c46182d440842208607002ca004000d8109002006203100d04081300b040c0070b066501240e607840d07580128801240c40d8407036280400c0e101c0c200247c6030350420f03d458104907881707902140ba4554140f40c0e4003a01c207103071107024444000d03104500d000f03031010540142c090300150780c0742c21079420a0702030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 811032473 1250 811031223 811031239
    0x120504120b0c1308100c051806090310111b010504020319170a090503151005150903060f180f0307030f020a060608010506010314151012020309010903080603030324 72
    0x703905140c43c4082a41c010001650008a185121940502c90280c400f241820480e061001060103018041c01c000c2c0354501811020405884a40b0f08106054900c0c2c44404103104004481c403401c00260002400310328000908500103401d80b0b41803080500403a0094082c0ca091000b60106c03d6614034116030499201c49a451000a600e1207400501040712450b0f03a1403104515010415107405520345080005500c28418041401c00900e8404c04440c0180c80402e41c20340a18001c115a00900d2100c94050160600300300490302c1c43c480662281820300300e643d402c0041c40040e581d445004803910f00c400c2d07000300022408240035207403444400409104031030100c4002c0e941c0c40c0548020b03034084005a034440701440210741c0c05004c5e5048007411803604c42458030384180710590103c41445568058804c480601d201c00d4484d00303c500e050b070017005055680e81440900325000380704243c0c2c142c00282c10980813441c0d525001c0700300c0340245403c55480821201c2213400c80320585940c0f12160b032004d05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 811033723 1250 811032473 811032487
    0xa1d0601210b0103051f02091f0e1302040e0c0a0503070e0a1214010f020a1704060902060c1f140612160602070f06030b0a060e0d060207050a120504120b0c 68
    0x1c80c2e25080c1c041c52003407025081004000c69041548000206d00ca605580103225000c09521081c203500b519101ea801081850802c0b08400c2d00c02e241e00c2d02c0c000e40c0001074070707150519071001078008104075070303142044c1c4820fa640c48042c20b10340d02648000400040f401c2005c5007440e0b2282c0d07a80301082070700401000006a444150b55244440e801c021244c0300e440488000a400080c4911580100301000562a0200080307005242e03070f903031700c00b181d1140012201117414407080758000e03c11180e020341040c0c0d032003100ca41c01175a200c018804124001c00d81400c40c2f000c41c5446d000340d014900202d003258900d03450b0207003009880c1c50303440402d8006100d6482408200c2041025820007840300382c02601d401030806101114007001c3d5040300c01810b080001036540c903242d1070030b104101d4007207181400c480f03021040015030840300c0030b00c050685400803d1070014080e000c40d0318440760f8410310b030040071420500b60035070b180d0049200304098a2004d134072301004901400f110a511004030400b445c50501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 811034973 1250 811033723 811033733
    0x1009020414070201050a0c0801050a090504061103090304170a0c0905090c15040501180f180b0d03211401090b01020a0b0406090b010e040c091d0d03050a1d060121 71
    0xb1070304040142e44034030501c01d4284107032280d803070501d0051800700150b60429002c10700341b0302180b00b0100419a40c40014081c807419600011070390b07044254581c0e0760f0901c0380f00c0d256a5005030091040c44883c0310a403641ca0b400020701403c003981d115070000c1c0103514050b01e92005110040180c4014098050765802e41e0343c0c1c0040072403c07420710080a5458604140005101d100f203200103030040c540e10801400180004030f049011190444003449555525202044c082d14140680c1a0801516000c4504140d0000c0c0040d20401c0d540c04400d05071080084000c0c2982d000c1307005001910300c10710043c0154081c50b008040c0420041c0102c6880070071641e55810303050b034110340980c0c201d507807201110708101066803031500504410039051200d0415803503028003400a0710804400e980d40d03d000003550f0100781d050060041c0c003141994600440684042c001c1c0204071031030f060725884c200d42c02c40340310318108401c12455010001010980e00301074840740300303802c0403a100242c01c030402e1301040020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 811036223 1250 811034973 811035011
    0x3021302192a1e032601090525050c0c0909030706050c0a020c190902070605010602160e0a02131a04150c020d0b0402040e0f0307110102070810090204 66
    0x1600303650700c09a5a41964144035800c801107115212034200c414405408a80b5100e50520790443c00c0c2c03000c1d0351031003107880d043c1d03420445c2800c00c03028148920360000064a10304421412201068400e10096079284118040500c241d41142c002030b40030104103028610600250018000d5030007142c5404192000199088208445141d01030384000f400702c081013550701810741c0011101c00070504200015201230b40344c40110b54503900945440340310804008051860900816211208550352802070030702c1405020240110009440b820401c0781ea101c141e04039202c11a403200040303c280351614001a070180d80542c40c00d5102401010340400e4900d40e406845603010800013806039030301d15103e40502491800d00c3c269040c00b02058208000d03894050150036166409450302800e681ca61000400402020188a020b88202550314031520000001000b6460040355511312034100e800049a940ca810b0084640c1c98104180d40f000d40c1c041c0da00015100ca100520200391400b5901d0124800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 811037473 1250 811036223 811036267
    0xf02030c0109060b0f01020d1b03050d0e03070c08062a0408150108070f0b1204021206070f021507020d11121602011e02030a1209050d02150106170103021302 69
    0x4907542c02c4400300382d01e030503170b0543c40e002401e001600c0051960140903108412580c004103044900c00005001c040c0300c0c004944000307040c01000c01c41c405481c3c240d40e9480e0041801150080754482001c00c82d5000002c4e5248580c030451508c8400317410608660410030901441441940e5007440003141480040c840400018514010300100790701d05141540780441c260b0040620710761020084c032204010804441b040425681483c140382c8441c4082050880b198542018601840062010003079028010100b074001c0c0d40d00b03c80c07000d070b603032205405019001d44604015a10200f4030369012070180c9500d05280c0e00703500c00d440e80000c400d01c94145d6a804840b500e13a480c540c01c031240c4110761700f29100e18081c0c080090308165080c003660019540784511803a03001400b8000d445440c01d982030b90030155005900c4800e95011894110f800b81d621b0035034000710218004980004240c8a10400c4003030303040400c84001c003c0d580d02e10340078080280f40b140b80060010b030302041203d14071505103002c1c00720 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 811038723 1250 811037473 811037483
    0x80306130e2b0903050c10210501090e031611030a1a0109060b0c060103030e12100903080c12130804080d0207030501060603020a02030f1305131b0903030c030f02030c0109 75
    0x4400750318030b10901070b00c2c02d03203001414058801c400f44003090000500c0b115a40f01628040300060b0b075000103503040c581d201c01031301507000001d4140d652003d480d042a8101c80042c0004d0084100345000c0b55200d020364043d462600d20100700d4400440c502c0341e80788444110207000e60300722400303d80380c911050b0419049111004044801000b00c08500d03c074400050084000c1a0b0400c000d61002d140c48171018071020342045203801481240d981c442030000001000c5a0403601d440520120100140424042c1540401c1c282c50000d40f1607580102160f07045108031001c00703000d0340d80e40d020a02c012464101941d0106040c40003082c048010001ca1400040c0c0d40c00a000071481d61400d2070a48000c1c0e00014109401484200d041c1030b00002900d4802030301c98440c9440d003000413411042c00d051030344620740c05895520039106680390b5504c000442401a8100c00e0001300c061029280c2054521008001441c0c804040b400b00b8410079416030000300380e20540707140040e804500d07825a50b12000c1550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 811039973 1250 811038723 811038763
    0x411010c080f040501181d091006171e0a260d0e120a05090108130803040803040605090607080406020a0908070b0a020106080705010207061b0501140105090604050103080306130e 78
    0x42036800c80340c4048086001c1c210015401c0c01c07c07a010300310f03124042d00310070000010400b0446201c0188031284280403407010030404d85940710450081d940403a4000390789405400c6c2003012a03a2028803800007171540c1c20091200341419560590803801260f00d01031804902000c00c51240d92a0707006111041c4c180300c0c049050080446074504201c044000d010038141e042004900454004042e90720047c804d09001c22260380740c111405450088100041065000000b04020000d00d080610302940c004e0004200660710700030420f0740e4030016605203010610a071b0000b000205240c000f400010060302d0481c98081d17495020324501281c68003c515210740200d00b0b06111a424032590b401040110700408a0a1a060010392640c2ca1401f0f5a010090140085208041d85003030180da908d034400000c0181184059101f180d4200a0045a1045070b059020501d00c1c0f5060041a050301c1e00300404070300d1a19280b080111040703503071414003402501c6055401c9096000c0c012540c4030403540321929 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 811041223 1250 811039973 811039979
    0x9040609062d05220c0b070308010e1612020702060702030a0302100b090411010f021f09020a1203020627070e060909070b04061815110f010c05030411010c080f04 71
    0x1060301c03000e101e004100075150404000444d100084006155000f02c003403015415001e050800349034040d0341289001d5480000c04400b05503024214034101d501d80c00403004203481d03040d0359000312074070355400321b001801100c0000b0200101d0f6000b058000e1000717088510741142035001c0782c102a80340e101078015802c1134007104000d0603d0b00581148140440300600186059520320000007031984c2d025041181e0440c1104c20a402000091000d41d4008070301e01940d803100d207040001d04007140c0100d014105041c8005104420328a18882046e495000f820b071554852000c07011845074000c0040365824403010741e0780c0f5103405020201c060f041001040d059850140f0621a03034060151896002d940500d00810038010003206a4055820500e40345248401c210301e0b903d00e200041d005802c041011040c1103014982003002450300d030400c08181d030905111081c2041c203d4491000400100700100000340018200500000b0701081c1410040d0018070701d92241002500291b0401d03110b00c00000d828 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 811042473 1250 811041223 811041281
    0x711011a010f03231b19090506030108032205100503011406090d03030903030209040e0a060f0b0a05040f0f06060c0c08010501060f05090102123c090904060906 70
    0x18001911840c10244004c4103070703a072150650119688104107100911002c5903c1c40e0041071005045e00e11504800c1e25880c840e110500704845119824010a2504070b00158a00b4108281c3c0d0407905202c0245041900300407200c110311800f55181c000c541c01d400e0001c42e059950780314218030820302c0e90b10303c1d0b01e81d810446114620031016101d148543c000780030038140c943d45c01c1c000c1603146906280104032600640360a03030190091300582c581c464107240c0403211358100000c1e82c1040d14000c0805000c6000031141080849040e50b9000360080303d038030390501460074180c0142c2071903640b000000030340c2e4448a1800089480c030350080c0e000550000c0304007040c031084400c80320140020100811055141880244c44a1300800059050040129032110385a000b4004103518840b0715000d10340e601414003001800300c4050b003000c1c500c2d410100f0004210a004c21480b0448030b45035001e00d143c52420801c21092041c02841111001e440e6801c030b000192b130700c4c06449018401180088c61852030301d081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 811043723 1250 811042473 811042487
    0x9030818211305041a101103030411100e0109120201090e07030926040e1e0a24080a3002100b0402030f0c09010302040902030f01050406080a031202030711011a01 71
    0x801413145003404940704000c207401c8241c1354110411103060496803c00c03070007514880e940c02c0c13000080b400302104005c180704020304124090101100c0c43d5248092021095070000c602c0e4803541d0014031808414888081035503164082c1500505200b00b40a69801c80a18000b0003200c5201c0080d440380014000c0240c24105810f50a072004132241d03100c0414044c1310240c0c0220b100e40e149245c41200807c9291032b03001d6002850040c103440c3c092440c900320b030441004d0400c45202010403100c46021401144401146006403400c40019049031b044688503003034111190419036400d6103e08400281e04600e0b58540032906900350050203150321042078500403070308100503190299004008004607180c18402c1194842400340015440780600d0340101c0c000d0180d0f030001c9050030301c000b0510910b80e218011050480c2c9084030280042a02c03000340f0754450702030400040c04a82d9040b0064413041c4e60f0b80246030f00080c5440c0c403810305880302480d5825204c1c482c2c0262030350200000b5082c415640080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 811044973 1250 811043723 811043729
    0x92401030915320601120204080a0c0608010f0f1814090c09010b0c0c012015010503070b0f070303020c011506031a03070b0a03020306032e0b0301090308182113 70
    0x10940408848414a0b0103d80c000030042c604200d00d000c9202102c07040b5505640c05492a10100c540b81d2040c0e02e00304a00301c03500c3c09403c0100d0040d03c000540c2ca5040032500e0309030b4040c5042040014a040140d0800c0300914641f03810590302c80c1807440708a00d04451082c0300e000355200400101e06004148014280103130025410030710b01708604013807600d001924800c03890f420300e0058039192402220b946401184c5660604500480c1c10b14100c085003d10014142c0d88110162142d059035884201154403680c0701c8614502c0040c8400c001082c00303075018006501c84000042003c030400b80f0340c0302082c0740c590084404aa9509100201d200400d549940f242205600500d0318078181551000c03507000c3c440c00d800805400000054141c2c80502078100455569080d513040e01c0f89095026054403100c45058807403d04e003503030007030940c5014000c00f201160162a80000341d01d031032a19581c01213840c0340c0150540320b80ca45400d003030aa00b518211071a508003200c2c80d103a40202c540e0350040342070f5034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 811046223 1250 811044973 811045031
    0x70e01020a171b0106120c0b030f0403112107031d1f030b0907020319020106050904120c0b0f2d0a02030601201b092401030915 56
    0x3204040040d840758076001c1c0d5003451074001030b25540a0f00400c003c00b10b40e00d40c02815075003022000944401c84c1c1c80c050483c0d41c420b2000e411642c0c0c841a42d400d0a01048a040341080c20450110300400d00840b60710005491150650391600c0d05d5400341d03200300818400e018000348002840c2c205042c1d10014020000000302c000141c19000840043c800c035104210754203041d10ba8807111840301e4000c1d4070905c1f040c8006446c45c0410b1914410180d2603800c1034691404000c896591002440d01c18411103054860080540b01c45845549440001142098495040c440654292008984003140441c030803203412851719000e1600c502e0510620340395041c144054503204621101e0aa9040606584079084000050322a944e490048a1000000307110440d03984541d0b04640012001090140c0d0101e0860104504d5205400c1800008582282e42071160041002c103120f00d040c2c01c070481c1c951103005240206208502d600c2d0041d22080254480200c00c0d603561080c124080c0303907000b03072940150030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 811047473 1250 811046223 811046233
    0x18120910050c070e0417130513021b030403051606051e040801020d1d07081002030615030403170f010303051b3a0c0209010e0402031e0d030b030f10020304020f18070e0102 75
    0x20301584141d81002c0c1c0a2305201d0000c006548840c600e0703c1e4151011404c0c0e00780c8054181c000d81e50050f4695205000541d117500444410b1089005250710450489449581c2c00349410640e0716000c02544034404104c5040300200070000b803450090000d0055080c1c10900010600d042d1518010132040150f4a403501c0c0c2c2180004100c1800c010443c41c0b0391209414015075a03540300d034006060f582c1c184c0c0302041c0325070001c424407040c503904c0409031a4007000e20001c0d0a184d00d42175900c80d043c41c800d20000b00020810450380ca841c2808114141c1d41d40000000c035031040340d002240440c0c40950054806480b90700754030341d041041d04d10820300102e25882c01c0140c2c14203030340d4022070518141401582485940200420119182049000c5802800b02d5994154504044110340c4074100541e000002030308061b41c00c0340601d00456031036012000309000303210800300d41d0a09006904024026030307104003903044443c0a51540d100c400307150944041e00c0d07109481e190501401003038402d4005811540700c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 811048723 1250 811047473 811047487
    0xc010e0f0109030f02040209120a03170c0703050d2c15040f08030c0909070903110f032e0c030b0a091505130b100818120910050c070e0417 61
    0x10100b8010b882d04440458594035880c00420f001e0b200340324915070402401218000c20719030104403480254800d0b600c08620601810700404042015a002801c0300820041880024000e8009000c2259108804150700c2034a000440b03210000c040d0101e000d44d91078a800c00c280707a0500200b089105103024012150429454100e00c40c15030607002441e188000002c40e4460703404400356450407100401d0710703516140080d4020007510292204482060030700c240c3c010b03070703151400300c0640b040320240051100c040a003101c0301d500b50741a440709114528501c40d601035001c1c00d0145031129201d81d2030100e00010420280642d41e0082d5104c406118601152009001c00220400044580440d00d41d0100c007810025100280a2040701503030014941e03221840003504080319a00c100c10303003140102c016510701e40040d03e400215070001440ca4013008441010f240401c103109183c000c3e80740482c04c2010440c06103280c418603800034401e0052220030001000300d01c2040c040c10b202c48941c507500b0140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 811049973 1250 811048723 811048727
    0x2040e0412050c10020711040b0f061e030903071a1b0a170a0603020a09090c120309081213090903230f12220c0b030606070b090c010e0f01 61
    0xd800108030700507006240710301510900903a0b0200c46440300b0b840c000c02d92424107000a612116049880d02c1d03644c0000d0303116140038820500c000c40f01a1200301c0c000610410085103901904a2048612022408a0141503203001a5200321a50b5000b15070782c810300c0c1001100c4503d00900f0300080c0303044604100c0d41c00107141000c440c0e41c41034402d1030b172244541c1d0400d4070f405c180700490006200e040802c002118486410200c01c4a00a8030140045610f41c401c820603079404142c06483c0741d10f80780b41004600208001c0d011110f000f03142c0700842a03280c4000790b05000c10a44001700543c07010519040050807649a1001421100010000307a403040e5070242c03082c101c1e1144500c0099031400d0300c1d000d2144800403103203004010003109070344540f64454280c14440a6402c0c214040b02c00c5011010078609055001e01300b03421407415241c0031302c4c20344501c1d000e9000800c07980c0c01c40c505002a800107040e54825600403442280688020144840014071100f580d0341c01500c01c05602443d22003d036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 811051223 1250 811049973 811049999
    0xa0f1103070b12190903020102090f010e0a050f0a03021801060323040809031002040f0e0a062909060406110d0309152414150702090c090117190f0204 66
    0x1c0842c40c2d1104070313a581e5000c01c81a2150b101140b4600b070400c4102d4081540c19401400e8040d0b080328950000b26500004590708551407003001c0c0c12040c0d0b90300074000c81c5442c2c40760385020f003801031605c00b400341c583c0d0100b85401000c0300000c00c901508001440201c1c4c050181c040c14050008600c22000c2604028007a2408040c2010b00f030100006121580d81d1814043d0000204405209550310b0740d0720300a07541c15100d03510444803031200308008078200c0081e034007488d01120643d80910003a220352440040c80341e640a0b8a10796040c0007002800300c00e45899002e44001c00389511080d80346e98100080b10b0038803600a81d00c0042500d0f00268500140820407902c05185002ca4005480090107220540c040302908014401c0c080100340001d81c2c10300107042541107201640c2c1a0024240c04645035164010040001d40c00010303034002901d0300358204090480c0c903005240503c0c003d0680a07aa20a240003610464425600c9050b490301c210002d00907003004200d0390004501e03041c03801c40312030102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 811052473 1250 811051223 811051237
    0x30210030e0606011d0d030f0e0111100b0303250c060e03100e07090203010f080c06130b030a1b0309060c09080703020f0411131406030609060f120a0f1103070b 70
    0xc0300c0e0803900300355804042804407002001c064000406c1e040e03070342006002c0643c040030b4400000c3c050050700d005035101c0c2188590395820352000307111401d6007000c2d6001401042c81400d4043c0301c1402409010100c003103c1d502011200c0802d02213000081c100031040b40300e190010002e100280840c141c0356140018181da40d0341c090a400030301f102103011020705101096200d800043e00200010803e0382d05903440c4001c0300d03a128122110344040c141403000500070000aa041c2000c0071030204801c201401c0107560040341d5000006d0440c111032240c05401444c91f0603140007070f945005007410020300d4400c01010070850300b40803545c545030100041d0b0742c040c60b002c02402480203000480700b0361910380002c450100041c441503102c140c42e40309500028214840c04200b800c2c0c4802800c00d81c10400e080328001d400180c01c0702e069540d0710040c03254580501d2880d6810201c5125401800e00d010f0104581c0c0901c00c004102e144286818240000004884602d20a802c015001c020761a0150111614 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 811053723 1250 811052473 811052477
    0xa180209150c1920130f0e010c231c0908131a0d09150c081905010b090609030f073206030105012715031407050a030e01180c030210030e060601 63
    0x4002d004240503182c170564010226044c0755080c0c6045000c0e801010b1a181510000c1004031a0080105c502d0240e115014520b0001b8110441e0f0700f081d803400401c4400242202e10582c290000301a0045403416042030740c40c050003186080365500181d0b1141c0003001c12400841071940c0300d259800c420f10a400b0084152540c0d1700c0c0417000c102c601232110b80384034840981001802001003005c1c213040c3d07040b00c00140d640683d6001d80184011446890305907590904141d041451080901585900c00903a00f0351510981c01d0485000d1000c211020103054851100c21300c03c01d80700c41070b80095400034450800110811a409200d1715440d05590440d2024613103809800341c00c0124031544c294446048900501620b0045490380c400008a46403000c0340e58104480352071140d15248651003a40c090b00016420000c501d40a0311941280a5000026000141c9a240f50188000c160025542100d0403a05c0c66010015440c0c2030104031202506402c0a201c80d4101d803102503100c080c01402c0781c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 811054973 1250 811053723 811053773
    0x40501030b0d140d02071208070201111603050f0f030c150408130305060105120102070b010608191d0d02300d1a09150a180209150c19 59
    0x4000d41d01c1d1070b114003205030004098004009070403812900c600c020100080944a0a0780010310f1441c0d40381005c0e4242e401174242c03070514000e42e0045841c0b4411044005461040c5624010b0302801c81220000070362060006010300300302000e0706414084881c1e03d002442c0c100344203a41d4800300100305600c0804610803000295a182e1508500e28001d482c0d41c00e242000d1400d02004100c00025100c1c16980c040755001050304405840310300342d00c1000301c001c2040c10588010041d4070301a86100c0e8002315108201c096180300b403c00c4a0465001c18508507038490840e6072013100b01c00c14801c05070078a0191021701414030700c2c8003119030b403034040103080311940095040d331755000c9180d00c09442201c0c00c0700700c05003c3c44503000380031500e1501898005110305582e0b008510b1511103045200c07499003010340b80c1501c0500d0021000100b440040300c1c088044c1c4c00b0080002c69036101c10020011080c0d10303400035141c95076542c00f6440d061008030500c1140350740c0700d019400704000016440000a210b15404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 811056223 1250 811054973 811054991
    0x90a05060f0a09080d050103050601240c051e2506020712030e0d03030f050c0307020c06030a0f0c0801030b090102030112022e030f180b181606200105060604050103 72
    0x24008028056000d0072003134010034050384000080d04502d040380d000e8801c48040380d88030044030350201d0031070143c0e90009042c190010300d00c2d40078610188c6410701420a649180400426458815500a0000c11160005402814500044480f0080c0d48080c501a00d090605000010b9030b10030050150003140c01c03481c041001050f203d02c49608040700043c00c80b041c4080c4501e00035000d4111090098007007800d1a00040b0742c5084941035a200d210564002d08031a05d4103800e000c0503a00160100c88200c1d115a55040e125400740107106035408142d850010561660a2030650060041c2c00c0401e40d03401000100002c4190128000601d60103c07040071200e83c010166801c1c20480f258541d031407244d03403c00d03155500c1e0181d0200501030b00000050254014000104002041079800108443c0070080401c1072000c011914440031640c050481d440d501c05108003403c01d900e07592141d000510b85403000c0c0103400e90710500d01003a000903c000d20040c1041c6001601071b0041d405901d04060b6186104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 811057473 1250 811056223 811056241
    0x70314040513051816120309030204050414060a020a0c23071e080601050a0603050c040807030f03120c020c011d04060311011416060f11190206090a05060f 68
    0x3180201001041024000c000c10100c1000d4002191007010801403003808940740400800ca1180311103080302c124800324145040c14584022040c0180d0800181e448080300603142d5109160186000e08040c1241c040e2152901b0302e846d038010030a01c0094018008540034a800c6864140c1c05940000c40810048011000450714071500d401141c581c82070041c00181c01d00d007064405c0034190078903c1c076200ca545076804140d48060a204032030b008200790108003c41c83c0700c1d074481904030410100e4680760036a0340015600d03000941c0c00c1500c410080c1600e0804142d0070003401c0341c2c014640301051001207034120000e900d030b01c004082c2a040c40303d10f8240d5121042c50325000c0011710380040c0204115516803c02081c2c40c654800501e010454001c20710220751140c805581c01c0100c080e414100301861542c43c240940215002440401e03140c0710304c14003c20820b00503084504929181440750000342000a20f0880e014080000d20780002c1d01901c003054001c103034103600c1240200280043c0e194003880b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 811058723 1250 811057473 811057477
    0x71706040b06120712060f020a0e01140f09120304050d060609050109090b070e01050903300c0d030207050c0603010e06090105060f0d330609140109060e0a05090a140109020f070314 79
    0x5a87c4640f0002d0389410854100c21380d0041d1007020307620220000507080c030701103940c0300b440c0f4000117441c4140000d203100d10707040c050a0364551115040e6402d00342da400c0450184d10819801b1102d40da11403005200554007881400e00400942d242881001b0860f15603101d0041d0242c0f0b00c1c1d080081c103c28101069010324221401c880010b022a0840048515517507800310b03c910341c50201001143c244020010b0003415940c02000c0075000d0203800d02895019070007903004010884a034044c28035855038942d01c1102942c000c1c400c522207820541740000800c40781140c140c1016120f0704040c403030791080b16001e01c25580032408035440042c51040a03050541124048440100b146000019000c2541030080c01001242e40b9601c44403002612660b1340316112a420f00e415000440c624800c2040074890442e0b41310200c400340c820701080e904c40340469003294044620040e00c0781c0f03406100100c8024609028010003d0040c00c500701100514860000c2c42024009010400e05520000c01c5001e0001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 811059973 1250 811058723 811058741
    0x40605130617011a100c06020307110d020106080c150c010608010903020d0306060c0314092d01080c040e04081c091a09070e09071706040b0612071206 66
    0x11244840c821a8004800600164000c0303070790180600e9503840640c001402000261680780c09010540241101446102a0003540120410000010840100740305100450184081e030b91450710740402c41c058985000320052000b021a850b091081216030400318601c0c19054007180e02458201c0c1030780c111030103405410104e581d15480d148000070344a4055001e03490f614407a03029502d05140d8164240d048075114410000481e10389008540001e1044030403010307a40520802030b003890f1100700440c0132034000f000c2e07001c01500c2c0c40f1000c3c4450303240b201002044000900c1d0141491030008140482806148180400b4140b1500460304100d242c0381500d041c54040d19100030b880c0b01a0507000b0160042600c2681c220000d110402c1c04102c0c8003c5191048180600502c5814a4020301d2580100024000c1126000700030780410b60403000c00911b2250b10071180106503038101401c000490030405084030f44100c6450284418484002c9030f803108a65419409641082c01c50030060b02811000c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 811061223 1250 811059973 811059979
    0xd050a050d060e0f060a140906180718090c050f07140303040f0605221101031806051b030103020a170c1507030f020105130209182407021f0902040605 66
    0x10303400315001c8003e400451103640c802c0c008103841d032501d1092000740e605ca401010340c00f18420940f0850b80c20812201500114054994448081c0d04240400b00400a0754030310006900b000042c80c2c135000c00130b0b0702000380c030640400308007002d84004042d203030340b04403041b25880c400b01203665018002e990100406c103191000650382e403480c00d03240c0541d0400104004650803403512011031111580300c40394041c022600003448100300480d0b1501c20b629003805114078101a200c50010114003150100507400e50710a01c8085503071305214100041d074236140c038150102c00308140010805656007100180441d40c0c0c44070600100740042c24032605066040800f50f41110070f1441d07440131101240002d2400d41e002e03030788103050744102540490990704d00780c894401140d0104816005854040701c219040b015000a4041d902968012242002c0380c0411024404044001040d620070720388480c0d99004590348007426860140f80b10504070046450f0200901070307a901404011901c6542c01240900001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 811062473 1250 811061223 811061231
    0x815061f0f0207060f0806040209031c210c0903030c2609040b0306010605090f030f0d020a0b0c03040c030803060d0204090602130603110304032f0c010e10020d050a050d 74
    0x14140140001c1540300c040c20041c0300d00040041d005215182003291041e0a42d60507106894500030400a5042422416414080c40401540000300500304108502c8581c4a0035000240c410610800072034a0501d8411203051058841001364001c000a0907250702d13080c030782c20a800074101818290410403072049031102040c410310b80d0701c0051000d00301117501100d09100c5150880e060580f5500e0030321418000ca10140305500f1140391200020040c06406000ca806508074400c0c05d5207413000504038840982c01411140c02400703030502c14503500200545840c0c2c554101640c41c41c203143c04038480a031441c0000700205e081580d03100038503108160010403d105030100f50174190006d5200350400300c840d058986000440500074011039000c45001c101590540c0d58507107040d500054403885480c4805108550100c40ba10b1030002c41100782948001064104030a0001600852401014501c0f035181c10180f1910785900040162401060340340c40740e116000c07580266864060034a12682413428 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811063723 1250 811062473 811062529
    0xf0c12010f051f141605010f0e010e190f1119060e01210c030914011e11070f140d2c01080a020a09120803090c030106081506 55
    0x109450841924003c0f25400040310907000300383c003844248104507010584000010052401c1440648203401c14006030310a00800f0796a000e00b107582c09991070000682d41c40c82280c00e48824800e003646880c0b044001c1c540400b4601e4054110008000c009066035016280310341080500c03c07507007200386806004000203c0c0c04c10000107100486020b401d00081c00182c2c0e1211640c803d00700c1e100a04e10200d0b00c070070741c00803008182c1e02403d603c125607014180c0705d40e4030f01c000486440406440030036280000a802000441b2541c4001c014a03400d0102814405031f00c154152038411240280e82c054403801d00c000d15450031740340800204c040c4010a01500948980a80d0001d00b0150300e52540c0c8182840181070500f5031310b80e58000c4250b50f0004e002c200000d090120303e40e0081c2010340044c245449041da403801208048030b0703402c0044417082804014000315003401c01103000301000032802401058100541c95a49980c90805d01945260b10030114031070b0380360b6645440303092014440301100c00c04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 811064973 1250 811063723 811063739
    0xc030c190c2609010c050c09040503120105010509060d0f0b2709030c1f18110f0f13020703030b0a06020a03230904020a0e09070207090e010509060f0c1201 68
    0x1111006840d54050303548252100c0411140914821140c2d610550800011000454110300c0c140021922440f0321501030890355520302542d4483e5220340300031a65a4888900010001010303803211341401410300581460399a0081640d9414072940400210311080c0e000803c090090030350496000204804a1132185c400c4103141b806118410400d10f01a441d520384183c0e59105d514107a100e15008070b81c41d9140e010020548031010122070780301040d08107145003100c1c5000103414007194080142001c2c0700c000d00301004000c6611108030784015000315500b0124500e030b41070395100380701d09900042e110b0030103000350722030b40785000e014041400780c07500e0b52000396035031448000c150081120a8513860500c20588038a9200b403098a80c1c43c2d081c0b41070102404083d412210484080c05844100e25105032500d0018031301c11a000d500034490135181212a4023103c3d650b80a4000b5039050004101e400740380024500c0d0005402401103501ba5203007224205103000d04020860300801030000002c07105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 811066223 1250 811064973 811064987
    0x90a020c0a1208090111070807030305090715030606080f040c03060209032505090f1009091713091116022110050402030606060a0f0c0602250c0602010b01080c030c19 73
    0x8984d40d0004c0000703d8201c031404003140101c180c000e01004041141e280060b03c681c00183c1c01c0082d01d400c03200c01c0d507291484102280d40c0d1120060000343d40d10403c005240d40712144c660480f6002801d006541440e4403202c001103801d00015103080d03000205400c203038604108070466801c0840080c03524200e04100003030090014461f9510642041c0c02040e00a14002c264a0140e81c907055101d281da03150140341c0c07000d03240000d81039450341100d800000a01d42200014603200c0300f82d41e40d079503403982000c4229003159940903002c0c801007000d108010485003145540d0b0396054045030100d0039241c09240114280131080744401035400b5840c0c50b00783c00c0910307801075401140b00b01c040e0707922651440280019402007106010008040d1214121454002d0440002040c05a04054a059101a80301441b030040000c40c0c08011002c40300c2400b84400c4c0301854000c0d101920007441202d4107200000c0440801900142035880c1c00004219211810307402ca0b00310240c55009802c28030b06007070000c1c02c15 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 811067473 1250 811066223 811066231
    0x2030402210c22020c0c12070e04060b0411030c0a0314010f03031809020c0f010b041505010f0c0605150a050a0f06050f12010b040303261609080a0c23090a020c0a1208 73
    0x7c003d2589010110711002c10b0000c02c4c0c6000c0800a840f9a45544848010f4505184442d80140d6249281c6000d07601d118002c1d44100941b00420b42c0e46e0040c0c48009085030b0000040850000c100380051020319440300200040300d405262003620340d50403c0c0c40d400c40390581d03441040c0441c4002001e48142c100805c07409040d140850082001040480500c016148411100c11240c0d001b5482484998050a62103000d030307038645803425103801c090b52501c0884e20143c84000054462030b107662914500b04880c1c0000d404240d508000d22440d2011441150401e8003401003400404144003c1d07a00ea84401c0c0e40444403840c14502895070b444170101a580d0240c04141c0000354000780905047d909c103014100510407001a401056070b540c035007030078907a00340e80303002c41000500d80001648201c1000b0400e240c134002c3c3c0c4009100b510301001804000ca00700302404055030000d03071030440f03a59402256075000340d0420340503076280a200440c0d0f0801e2094040140b84580c0c4001c4510504e83c0300001c92300c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 811068723 1250 811067473 811067479
    0x18051f08010f12061e09060b0a05030f0a020d1403030c04052106040209060d171b0604050a080a031b02010f1107050303150a0f0902030402210c22020c0c 67
    0x15988520b801c542c0c0c400c96000d00c0781c0032114000ba041c0040c015038080c4820320300911111a001c05030401032401c3d80d00d62002179810710346980d503074043ca10b00070601c44002c01c0110010140414288491740e11100c070030350046d2041041c00c05400c2444804580c0341e04443c20303c41070b83e54038640000080d01a800c070380a064066460490300340000e1600016003191600d1040050100b40d07159420411003603401098a900803103413000c85000a401c00201d1400d08000c0f49020f07454040952410340c0f501c6909200e4025540b0a4040c80003052021548000041d001012590784421007a400d40c040e2060442105122150b40b441815255040d4008607410701c02e210244001c60131180080420301800c0d1000d00960810804642080d90400d032010030640081c100342d048580d62005c00c1801402c030f500c04020503800004020440c60a4101112000321700c1640f0207440350380c1c000c0c0030365070001491854052220100c203040d007a41e8140b10100781c1105035400395695501c007142d03a030f100d902c58414580 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 811069973 1250 811068723 811068737
    0x90a0b2206290316051c0501090c0c170919060c02090f01151101150806040308011203170a0f0614090a0c0e0607030e0907080402030c0d030f18051f 65
    0x60081402c0a030703420540c400b902c072030442c0c444041e803181a03902c041c0d81c4d00c01c2c04000c001c9140304483c031815008100d0b43d00703140041e6a40c9058800ca094a00701510300e010482049050000034400c055a40d81801e0b145d0b02039502c52514002241134284421552680101e51800c009403c1340d00160b40c5010a209440102c49501c03441c40a040745031081c0100da050300c041000f032062140c07044c5800080844103000100f4032400d02131001052000e00d070032500c1160029005c000c14590003c51580c010a82c0102011802d103682e1402003001c0403c0300466444141c80005c5010600290000700700d0a80010007080f2440c0e035030b014080c01ea2030301c1080c1b0707000391406d10000c3e000e03480c0361250300072540c7c40d43c80312204039811004100d1f8581c4000e034114248200005405c126407240c0c08254441c42c00da4540e061582000c1c0105440c2c414040089441a10501909000294044019100c1030403038207005a007009941d02c400d64801d003d400c52900031003140800f400940005108403094280c54035091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 811071223 1250 811069973 811070009
    0xb0309011a030601090e070e0103121805131e0e010606031107320303070c030306120309030204110403060f0b040e16030b07051612021209090a0b2206 66
    0xd04614041c1d84180d03410380080e401042101c0a5401403010b564200381907134111603c84002c610140001e0f0070950310b80c050014440c80c19074001d409000201071044c10301c55458a03040c00990703102c0303681c10800b84454468440481096800301c0f03007904032003002c1c030a000365420744030410300a242d00c3c421180060304044440110540b49421a50344541003d48901c0c1010000805010100841a44c0790440c0c10102c5105a03107a061002c1d6000d18100c1c2d541c0c0740401d0300c80c00c0050a0395078075004428410b04148400c400a600030f1b2030f140803254152404501c181c081008009903000f6503101030540d0341061410460040c05078440c89460204032001c12002002150301d96440380d503400b41580015001e10140081250b49000540c84200c03440c1c2203250480c8402e001c2440380e08103e084800700000360b10501d6041d0140302d8652500e001802c9a8285003e9900198101d04080c00c010352495490039400c951b511480c02c000800341c0402401c01c0e041880301d070303110024100d40c81031152150801e002c40e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 811072473 1250 811071223 811071251
    0x5060105120c220602012408031207020102040b160b1501020a0605040813030f05060121110d06020a08100f120308070905120a0b0c0301051c0f0209010b030901 70
    0x56405010000111600c0340da400415212039440000070303005901d07007940c0d9000b0901c3c1500720701024100a40c00032a416802588194071541400d028600340305c810071080c400b002e0000156420320900781040c401c6900c680c50143c0c02446103800c0500210f000050580025040703c0030b00c81e100b8032030441d000155442045280c0a00741c46a1134600603009100040b001c1156034004039082030080d03400a29002d0629908031030301e28903500c121740d8220b00025000074003c080c4007042c01400f00d521701102101203e40d0040c8a52210100101040e05500d8880c1494554180307110500d580110215560b2441504c080c2c0250400c03a11028070709011000494032a40c40410070040340d26501900341d0142d901c1da000d65003032500401c940c1c100100c483d000683d6544020407020504000006030031584010705000199400040003041d02c3c0404000400c11910b540c0c544100400038400d00400340f8940c0e10703010034a407805000c0654400c0c0c03a1000401c400d599400218054203e03100204011a010059 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 811073723 1250 811072473 811072477
    0xc0504060212160b0705040b04060903060e0a02030d110102070b0a0605150406022d0a110a0806040b04120212131403010b0108040212070506131406190f0c060e0d0305060105 76
    0x30440352640300d090751800a5203071300d2440d42002141c1800303800e00d0340b0ba0b2144206a00039034000340010381946e20070001d0142a21444801c95a240054102c103555a00071a83c0e482c0525141c05c10070103030218102050200b941515003072380e40003000ca802d81c1841c0b1046400741080d8000d0310b00c9040482d00d108160540142118210b030320640103005100020b0340c06910110390701840b460018144000c0030800c0c44107010070b501440c8512011420788003003509110140581350000c0600d54000400d01c07022661102920390310641c03010607840c09141202040b428160f4140e030304550000049003510a1108801e024030a542c00c17122403072500044201010300341d0f0b80c0a170a00d40801c110402080140c1880e00c1d500d000c8064540840302d0455490380483d0542e48119240c007980c500c1c00000380b10302c00c00325101e03240d4600102c40c003508084002c8038002c00b921200d1740080c28046200d502c2402d8074050021010310742d8022004200d232120224007a52500700c814502d00000f0720b40303000201c241d070003202 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 811074973 1250 811073723 811073737
    0x512010e06130e010911010f1d0a08030a02010c0306050f0303160f050a110102120427061806150c1709041116050601050301290303071e11090f0403030c11010c0504060212 75
    0x6514041270302011040c001c0b42d5500183c03190002031103040403400d980c0800043c00001555400083c854030076003002401c64040303800003842400381200c0143c0710b66000090700c1301848040d40c0910100c209191036560300950100081090080c5000d600900009105280d581802a020740304030320a9600030f40b04901c12400340d4044d491286415002e0300c90440030709826041c150705e00040c4d098454248481c620034000c41c070008a900c880e81441440c1c00b150111210b4585410842c082e10b00d2507407403040c040260044030b803070541c000c544c10450703542d181c001c0e11141002000c8035075107031422451803a40701e42e454010f40d150302c00c40300006500c1c20140f08020b2002400030306103200303900200790036103540040c10380107905210501040c00400c54109000041810030b025101440d80c8520f03100c10744248a202503407051075036a0030000205c40054038140d01a41c145000100d4a800e1941504c4480302010302115541c81d00e545288401c0d0450000e0042e54441d03000c0b9401c040945021001c5442810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 811076223 1250 811074973 811074977
    0x2006071205090109090e0d1e08040311070e0a0c0e03120901180b0301060302040312080c070b0601020f060f150d020a0306020f0c0a0c060f0512010e06130e010911010f 73
    0x558020500c81c40341001d00b000c2c000c14540606620fa440e01d41800343c0301000b8071901107421200c80301c0c41140e00400c00c050003031060a40d01322000d007030305406800c01c40010310240c14420124a4000d1402042c44440c0103445410303048003441c18507415010060024850703c00206000c202c071100707d490001018824100d42c81c0c119440c00340b0381401100d8000d0303c03104a1101000b421000300d40562040301445c081c201640d40183c80d940ba5092080c00c0301e1140d02c54105104070301d801c3c8550403240c0c0088415140c2c01c80f1000080780c880100403454002c080343c0502c2d850040c0d0041c451510444d0303400e640242d6507212169000100441040070301c80d40000002e5000614800410000d541500500079482200e420b1a06105140b04042d0500584440803184d011580c001403000541100442c40381c107541745401400c1180c80d13484c180c0002018060305440c0b2016000180b55940da009000309804000001480840b8841e043e45029026400045034841c411501281d090b5200e00e1031452041015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 811077473 1250 811076223 811076243
    0x304060f05130f1103070302030703080703020d0f020d03020f040806150a090c08040b060a050603010b03040c060309031b05030906160c080303040b010320153109050c0c0a200607 78
    0x1550344c00307060340400c00500e401d409181e00c0000540d40c00c0c0045001140101c189560781e40583c50000e0030081048461001d001a00b02c410588070350009401c524803141e0300380140e0b1a01074080e5003016018562100c0d410780f1480c0b04020512503200d10700c1070069400e0301c410580c0d644500c68041510f50340819600000c0d600c000041c04a400b4405464002c44c002e040c0610750350720340e400714280c0d134130903003107200c102000006200030400300c9e1500b24000c0c4140d01d820030580e892030340c00a018001062603100ca40f4603000480c028800d043c4101da021b802c00030f0040f60b0790f5080e500e0001040c00c1c0ae150035560404040741c00115402c4c040300f1a4801c0303a001b201c1440a03821a0340e003140c044a29501410030b0401c0416a01c0d60f6220032101d00460043c076950643c13506003501c1400310a6107181c003008682c841800e050900c580d0000c040d041520524180440c250780c80c000420030354000d200041c5680c2c494100c540b024402140a02c283c000340300b00c1301c1c2800b140c0c040300340165845103260041c446810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 811078723 1250 811077473 811077503
    0xc040f02180108040c030606080a0507050a0b0909151f110102130e09070b0315040b010e0303030a021803150105011704050303060f12010e011d06190c0c05030304060f0513 75
    0x401c030394841d80300d4810620174a0054694a500d02201c6090708500c0c22580400e80003428481c0405c20362000742000c6a0368180c0754105000c1c0c40c0c1c02e00a05202c58061001d00b0042a15120080e400c80540f0b00d0140110b80c240c6a0300c50142e89002910440401203950102c0c2024011018002c03078001c18a4603040c205014584161804c6240b002490012540140d44020500850490042d400340c80c84c0301440340f590401c08200800c40b65143c8845040c070a00c1d50f4101181d45012080d03952150401e040141c490307110030889458402011040c3d503160250f90400038210782c98060450688a00380e0b6904054240124a000350500c151000703040c65200303100207910303032610090500706110060000d8038149203010b01c02e804c1d2103500300300500f03e0351512640303020694224030107600c00809000501107400c140542142d1034040002341819651114103041c826400382c1c0ba42d00066a202c012a907a80c501420110000c0261801c907410b580c1c14080490300c0c038051404224180c80e0440d40408020348 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 811079973 1250 811078723 811078727
    0xb1f0203090a210828030209130504120e011812050616050d050c0714010f0b03010c0e040507110a03021b15090d0606050406061d060c15060102010f0e0c040f021801 72
    0x20555042c115505d0542c003c02204526410b0680300e1140c540300035841d41030100070888070924542607018020700d000100f0001c1b5130780400b00700f020708840c100403148a074800d004030740d209500d89080c0c65013220040d000451000c036220243e00580524143c1d40e55868951510030382e1103802540000190701800300031112015a44030030342002030a05c80307614000703c5648030402c10b5603644200d80581d6544c808890044c1c0c1500599242210440c003c02200c440703590094030307280801c00082e0080c0d907500300041c45a4040d45a515815423100c048a02003402d0f40340c001d5460304600c15140d06030b8250030108115081014031004000001203005e4180b0788004140207607084280306c180c07804e42d141e6400042c203442d20b205500190101d603554200c5016003c2040c911210401003d50240500304240341d000a8081409494603a111500170303040c0e1512030040b400340c01080e0300c41c50307514036050070002400030015a080200005807000c0c0b040500201c8c0300000c90040d03180c0c2e00b200c80303c5400e81040c0e641c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 811081223 1250 811079973 811079977
    0x1e0f0d0e0102030301061107050916030c1b0f050705040e03131401092102120c030c180105010f030e06010905011401080c0f071b0e07171003060b1f0203090a2108 71
    0x3c8011004c0703c0c181e5032740d040002c2c80700405441c0407004034a4942040c090a86c180103140c035541c1c20303051140b60f42a2904804110000410025003403000c1456a0402c020003840058010213004100f4484003444940d070b40d4895010002e00320240c145501e000410790108410020302000586401684602c1c1050031a4005801c1003078616804401d40309400595076070381c60011074030a2500800012404105040c0380080d03100c07049100300001c1c40d5a00e5581510302885040d21405c3ca054002040383d11025000f404400711012131601500c1c001098035181e5034031081c100d070344001701e01e0421401c440042d5000d000c10b9503021008407080080c0c00072081c0c0d183c01000400d2180c041a080700035a88040441d805241c1c01c500c00340008142480b2685a010a02c0c40c4122030202c2441d0090400540c203400103901c0d4072009080544445100d5400d94034110300e20300031b0445201d0703095603a00b00c18000b03440380d0000300818800e10402074003045425140c508502c900c54103d01a80405245895a04190b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 811082473 1250 811081223 811081247
    0x7140703030b0d03080106141303081c022b0b132d050124050307120f05090709110a230f0d0b0109060f08060d051e0f0d0e010203030106 60
    0x4181c540e0040e00b11070300c03100309040000d030107503886034a29414804000c2800d80008211445500b0a0001c0c641e0891400b0719001200d5000182a555a0354444503200b094130405da10202ca61001c00c3c017080031111810340d009000e00c1d440300e030500984214200c804459040801d6904020020380d174031501407003680024500081e000a40d8420350601d481c054190b035042e881091f11035191001003082c20404030784502d0002c5005184852000981001807082c04001c000b60204407075902082512400e50340480380040b0741800a0209181001100e40d89444501c01d902200e0b00d04020040713142d40e01c4007035a20030540d50340d640e400c0d01004204060080c42c00d210b0290080400c10000500b8100c00c3c000b4440b01703c4180700442e1802090001400a1045a01c8a030601071074080200c0490b50100d94076900c8941214000b60100307250820529100741803607005034181d00700d0540a4000710000b1f00b10400003109003212405889280210b41b055400600903000d070384148014007800d4001c140801078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 811083723 1250 811082473 811082477
    0x180b04120f081e0c0c0d0206190302091002010516110a0305180a0608040b06090709060804051606030f060f1505030712050c1911030d020c011b0905090f07140703 71
    0xc0c14040b00f80000c580c042041a108124000501030308006414003c2c03100c0c4660490305802d15081c0c507008920240f142100740c04448440c20810301c0380300c4c000d40c140c41e8862005080d241e1522290710b40680240410750302c0f02140031000e844003080c00d100f40f54402c400b201d071601811a80c007079540c1c295403a13009403903484001500c1c801d81ca0004d0315504050b60041040d0344e14500c0340d0603e070504412a05001d05080c2c0141c5900c0100061960071209500c200c0e55a07103444299550303180ac1150605800b134848000c0461458000140680d06030044604003051081c00c02403075030ba549070842c5040c024824036001c40c00281d030b20345204d801038000d15800034660400d0401d20f142c02000404568084404080444002c00d40548032111410903a25004190800408005001c1141c03946e0380551980c03081099000030724040d0092080d041140e030b1064121a103180e0783e031041c50203044400349001d840d0180121030700080200701c0740c0741d505011390215180c0100c0030140341c0c40071013154010310007034007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 811084973 1250 811083723 811083727
    0x160509060f1908150901212003010b010306031509080705030a2f06010e070c080c0a060b010c120503040809210c0109081f1803180b04120f08 62
    0x7421650000003808446200d80012801c9050107402074038284010780300c102c2e001600e4550000d541c0fa98a02d40341915946180340d1942ca4040640788149244844020526002070154164100d0309440038032070000218024030520301c0c14001181150554440513111105c400395500c4030015580c0980b880c18081c803607240c64941d00d500d50b01c0c60f56002d903004d100001c00e44140301403526081400168031720b00a0316028038140348071034180d54994042c001d000140a0b11004a07507138a00680c10a07098543c000701254440d103103048529140c00125030142e030788174184403800d592980304010034502d0f558803040100d40258220000c85079034100030005c4031130b00010401e1804035940c0510343d03460140c10700c1e1240b190340303003002c4554241a01100d46c9030600c600d1800612110030081101290350034030320707040306441c2d806c00900c00182034010750034100e12040b02e1210080c10750086001d480c1d0400b14a1051031a559001d02140c01d20961090307054041c48081a507000850a982800045000713400040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 811086223 1250 811084973 811084987
    0xd020906070f200916111b0a1505042c0a0b0a0819081303140d030e03120a020c0c03160f080304060e060a17010306050403080a0516050906 61
    0x142240d10500d0140c6031441000c000b181008510240074240466070300074800003003480c6002c1410381c0d034080c041c14645a10365030f01e040d0143c89001c20039610f80203c4200d0302a6000c02070341142c0040c89440950250400c0d907004100c2100701c3e1502e1a80b020140c4d542403a2520f0100c1e1186070801c902d8a0301c03c40582030280c3c905801e8056040343c01072000500008a010010b0104a0305010507800442c454001d141c50031690100b00070b01000182e00b09034255036400781c0703401c4050030001d035401c0184a000c84081c46c644140d000110000b0b414200c0e1020011014845541941c0340070710110701d5011400400000e2221107ea00070f8103100005408a821180340c607000a824900b190b810030b01000040c070010418558612907440040c00f101000d180780c01d0a0680c020f1200001501e218050710001881c0c0001d03521030b40403921086110080391190356124030705030001c0c00f42980d040d0002982d400105515000c0391089501030f80d441001e44000c0302c04d011083c1c0d542d030884116030382d020409200c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 811087473 1250 811086223 811086229
    0x1200c03031b061e1315090503030f0903070b01140102010e0f1c05032e09050403080f0f090a0204052a0415050a05070204020d0e01020a1e020a0b04080d0209 69
    0x2a2080c03510b815004800001d8010704a4070788500100514201c03000c0003010401801c4807113182d41c10014500100155610303600348441015484000305041504d08100c0909000010020b03500600c0c1d03000884800d40c44600002c2d07620b015141018004d505600010400820300c201c3c452442c901c107000200300c0d81c103d2001141040150b050000039130700941e82d9a1300010001d80410f0b0400310302d007042410b50a00301a44c4900700c480800008904010b00020403940104200000080c20050400e114030f14003031400500c000c9003a200203091101c0000840d040050004599204601c00c5000341b0b40300d01903401304405000094074900740180c1c13560141090488840510b0b1004030320341d040e1940c0f140341c141c1d507980b6001c0031403003042044000e10000160550220848100d0b58040790302589a10682a58030010442c2810130010756200040054103650456a000c5000000903c4c244020070003800903030301d07007212100c01001c0034142800140085c1c0c0b031101a08071241102001402c100d122804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 811088723 1250 811087473 811087477
    0xf0f0402071a010f1404090f020a15080a0b0906011409101707020c06030a0e07050604090e01060e0c0f0c01060e0f0411100f11010b060310030b090c01200c0303 70
    0x1041d00c40ea01840c040410b6211031101c410b0043c600305506003000e80c81d0944042c180c4801e0081e5501c12510f4443c504240102c800c00321710384540003025204800c0d910036812071420501044140452062000503003001c0641c03090b4450060060f000b41002d0340c844004603200e81004003100d44104013400b10041700c3d1240401030a001d1095140c0c01401c2c0c1e040c8035075a6644100410000455010940b0718441e51180c0b03081e40c2d00b02c00c800d0400f1402d240f000c101d003400d00c9055005190018004030b00080c405000750000741d0174100a4000b04501c50301c07018507031891081100c109080081c208030310740e010707035a400003440c4c6016003074000a000d13919080c1c901700c68101a5548071140e19243c0520080c000c09810603503000340102d90515891025000240034400c500b003402052001c0304d607544400900070b402880410400405242c0c0c0d92405044080b00868140002e940314900180002c10601001826a1100310141c4602001488442c044042803090003c020994001e02c1c804890b15282040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 811089973 1250 811088723 811088737
    0x7081e160203100b010207031203020409140103120e0f190506030403110706020f0705100e030a1b05060414150c10091106090a0b0c030903071401081b03060f0f0402 72
    0x3440d5040340c10240101403401100300d40e1010400c1c600a1200203076070300056145c04403503212809103e60084000b064000340a0341c0d102015841c1407008854070b0203000d0a030181030b2031007807810045800e04200125940301c102541650840000d1540d02040d14104a051450f03d2691140107061500e80c40401e010f500306540803004140000d28842c8001418400000945414801420705500030300801e44d0703810891103041c3c0955030742e03200c108240e4820290085850000740403a000304a0a29040d5015503441c240e4490320840c0300008201490710b030741203404a0300c0c52255090048205d500b007100b40300a6440781c0d48a4001008003810139942840640c44500402c480040c28000c41d040010b05d105040b039500344a0b0a0401148415990780d108110a07280c1c0c0049a64a072181a507425296212f0000c886901d8803600100260308840040300500110085c1d8549c00b5580791504051400c501b480b12481110300c051002502d94241180700c4002d00c0401043c1ca101500508041403c90b80f040c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 811091223 1250 811089973 811089997
    0x3060310091a160c02060913050403090609060e03100e010e120c010f060506160606080312090706050c0307060b01052b0e060910050405070302040c081603020a0507081e 74
    0x10b004581c005540307103a031044101c0810724440d0b142c2040144039007112038009118400100d004070090711440194446594862010040e909050030043c00305d5400d4402c5d48001210704c05d000c2103162180e41000405103003d0001d04107940d60a005030040e10140a0b000d0a0b13650b6500c0500d401d080821440315802503004146589911900209094540c00c21082141904000c4100520b440d180c045138101003030b5a0090054800304d2400744094100c5502003800c51102081d410031b1007840c40900c5003d901160201c541156403140280c80b54000d0306074090f0160010701001c40440c00d41d400c802c10b8204141761491910713a21a0000c0a002c010601b68503d00500510017041c60f00648078551002d05c8840051403680b401c00d0f203055603088011481e100c80c0d52240007082c01c0080c10400000a19030040c810720000345120801004400100c035001c1d0080c4544118042c010300a04c219a200c010030780c0c840b0300d8110152a0041154445030b40d0008002155850a01007401d01c40640700302e1242d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 811092473 1250 811091223 811091243
    0x60e04030e010e0105030a05040f082a0106050a062706030c08240d060204030204022d030108031e070c030804140406050d060c050c06100501120203090705060306031009 74
    0x14140105072192480c811030612618108210f00c41e80c000040e00d5110000c5000440c0030743e25417400e40c1d18609480d00040c0790380e0b804615182c40c0c1984a0741581d0b42c4480007640ca0107185500482403c0c0c5105200b81600030b00a05018030070381d4032680c00f00c10079550502910302c00d401c10940034065141940e01ca20002650341048480081d84124903035002680703200c400e00401c80700b110700c0074082e040a08082c481c054019042d810080c041d01910b00650300108115180c000c180e0858216181c1c9405880201d400c582d6041d4060061500b600d041ea18a50001c50509400405100000700744140365003a0032070503c0240d000861034003010024610604003151110b1805440b50f110b04211034656204d01d00b004810300c01ca0300c42e104442000f6030400c0020843c0c0c0c480b0b076000e0740d05200e00c6142c01c4860081c10100110a540070521004450b0280d984020300b500b9150340c1400c0f4041600c2d0044940c01c051000c02c40d52030500007958110b140181940d00701405842900d0486440c031808443d000c4c05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 811093723 1250 811092473 811092481
    0xd020303120906010320150a03060e0c0910020a030c08032707030c0b07021f0507021509010f030203040f030804020112020a030506100c020306570c0c090a0e01060e 72
    0x1400c0c442ea140c0d458000d20300e100e140000700252403030384900c064402c07480d80855230b202070134400e030070001c0100030b003411f0361400e41040805031005600074809180a8a030144c000410184002141d40348150035175660841241d0b40d6035003900c0390f030001e00803d07000c0307808404441ca01d403911400c1d96500d15000e030040c5241c40c9545410441082681d11061000f0428050318026031210848000c011020503140948c18503400c200750390600941c2d4010303402c07103140f80b44580c02041440c0101410b101c02d0301c1c0c4160060442c1d803b1000c0e41320440c2c000f0040d46646520701f00090050180c41e410130320504041d42e01030a00400305e0100d070018503201d00002e0f03c500c103000d104c2c00c00d40c62124040b02c01e8500004008007513000b01c1d0751740c08082c2901c52780342001400d500c1800440481c8400c000600000100190032042e143c0c0078400c400181c2944521081454401070f41c0d8010031110000a400044c00003100d4030420000b400000400440006444085803a40d80800b17100d0500940b41d54580c2002e03d0030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 811094973 1250 811093723 811093733
    0xc06040606060305060109120501063b0105010e1009091104030201082a0d02160305250b190b0d062408030f030603030d06080d1103180d0203031209060103 68
    0x1007540e00c9107040c035181c072090240690b4809100d0703080d01c000900141140440f45061401020268400f844d500d02c0010a0100344a4142c0300101802003000c100c0301c03560a01110405007203080c8119404a1003901142e4050b00705001d0710041020b15040111203a07599800041c10380744400c2301039041c4980000e090007150b8104001542102ea03400c2c0e4040d800b111070808032808243c1690400c20a88040781c0160140941e03012505003499012101720041568a4090582d4010b6541c49040e1000000c046c01d1944030f808003841c610b600600d0750200707a01c2d02c02c800b000c040c0030942e09542944e11a14441d000d07031510010b40d4002441411b0003d4441006c2c0310194610b001a8007085460001c4842045130020000c2500d10008100e82d001e0350b241c4a8030000b92561083c82481501a401d1a800044580c00030803039a0f000d503100e44070000d592545044054892086628080441207001030b07505c1c182c185012601d01c02e81c4080d00f140d20b014803407504010011000c94005005510a6005000f005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 811096223 1250 811094973 811094981
    0x1205090904060e0d0819090c08161401030b1518040213091407021b060913060f15020312060f12100b1807121506030e070b03071409040902060c060406 66
    0x185e01d08001c17241880311031421007811300d100c8417022a0300c42d1443e41c240302d48400300c4001410000120b519405a441302c038468400749101e0706850740300e000c000b000254080e015400c9954070091920081c050541403035003894200700d5000d18400a00f42980c0360a07151840100001c055260360200d14618140900095612006e1140070900101050042107500051b981a240005203256203400d08210003240f11070107a40b5506a00c84040c41044281002a6016009403546012101c1480b602d800304541c00000d19003038030006034010060110241c040d903807601d8200c50b004042c20180c03010600010035500c0f40d4000100550841650924080d40900c1040002401a2003009441c1c2e508070402c1c3c4848402010b0701d00b80142c0501000f85002280d100c1d41800740d1f2011500700481d100d52000b0024a0b002203e5107847c41003010118241c0c41c0102034a200e0f1050f5071341d0030004c0c00404a040d41c0e07a04022030b03007500262205500c01c016070b40c44000d040440e0400b0028801e46c0b41c035044c240f041d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 811097473 1250 811096223 811096243
    0xc0525140304060503220b0a091719050c01062c010509040c090203070e030f07050306010b0f041802090634050319020f011a01120212041205090904060e 67
    0x10381d1080004018041c1c20070140c80d8003030071460951805600340c6484640000440c60300509026802c001c110400d0309030b80c00b1509240c0140b1041c4030503a80c15032000050b200b60b0300380d202c3c0070202c10440000140b044c4024102c0360500320000c1030540e650382091074800002c041050000f41c1030305007005450546228507004100451340d481050620307840b0a42c800c071841c01001c40f500d4001000801640c00350400000d5001d01900310703054502000d030308544541107401a14070038010400001004010542581c0c0c41201100e4128601403610500d0581004400900a0b0594080c4880307900c6079244409001058803101c009551843c10300c0f862039102c1014aa404001c01d070007038a030004140c00000f5507034001101c0301e032030f4002001c111060f440c00c010044010442d6080510011072200010a10900c003602030702d80740d16681000080100342d0151032280c1e41003688650019010404200d8402100c2e691802c1c002e2510b202b2402081c1c44690448080e2034040e02ca050a00d403141d01003203580a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 811098723 1250 811097473 811097513
    0x90e07081b03040201020a1b06020d080f0115021f0f050603031c0203190908070215031e0403050c061003030e0303090d2a0e06030706110d030c0525 65
    0xa500d4421152840350140c0300004003807503404000203003107900802809a10640041941400d208144100c415103500750041c0070060042d4102c418403540520801030052141c180c004e0400ea081050880d00300201103150401c51281c4400500c0e19502410791440c408034541000c0344400451500c44107442d40501414040e034400c000320400b61001d0200359403951750f00c2c43c0c0941e0b00e480e01490401d103003407104171880030f0310702e03080074141000000802001024801d075001c03044c141031100c1c1c41342c5a000840380210b8040c203070602c0e00c1c45400b07141c1c140341d403051007410404e050100005545150840072a480802580702e640b0510505405c01408646044114001c5107052201e60100b0b80c9603800f020020400110420f0b41880c00c40101c0345040940003490b10b500c1c00541d0351a84519001041c0c800d240207000e1201c000c01e6081c800e0b0f07a00b0643c0490300c8003c001c52840700360101c00600100c490041002000d01402d0021203c10071210000014603000d0703218008181003841e079a003956100101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 811099973 1250 811098723 811098737
    0x4090b090c04050615030a0c030209061617130e0408250b180d030f240608090304060c0201050903071502070807141c0501060801090303020414010801260a050d090e07 73
    0x40c03181e84140441e540319503032000100d100700380300200f27501a00a1206580d400300011802425440b03c0003408054607000b1034030250400700c0c015010700c0b988200761003100b0083c00000103100c540308641200303400a125004892401600343c00381305022400038020a0000c5071804400300b03003e81c0c00381c019000300340150590381e490b000c0340d0b80e83c0d03940b0040030b089002d040d180d5001c070032250415400855040e405010011545110040c54010b500d07141c000c510128224601144141400106840030380e011919032800b0700d907241d001520943c204100065051040b04d81c0402c0c0340070300d2003200f024518590014484d050410308414201038180e04030f440040010000d42c1c21994a44642504072079180096800c00c0c1a1802c016002d01482d03003010010390300f401c80c6070342050340c50340c0100115620000b003038018106000045506400038407411103143c41150154203442c1a01405110300355403407045602c48440c0d07588541c00d140211500a01164a8076402c01080142a041c240e1001c22071904003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 811101223 1250 811099973 811099999
    0x80702010e0601061d0d1214070f1509020d0303021c09050a11032a0f09270a050a06020706140708010e0a140907090606020a110603040204090b090c040506 68
    0x1542c074181446070108110458110031307003000c14100100c1201e03002030310b4402040c001e42800b910031140405e00600244030700d10f100d60342108240a88400d198040c0c107848002d9969141d00c1c49a8581c0284650250b98545e400c40041c6d56100440790030380d109403005611a5008039a40703481018240244070146d041500d0000054004a51025690b9025500481c400342040111b450000390b030300310101100c40c0c0c400041d541c031203c08140d145804112101e44020860406200784a401a50504401c014010314103d00840000003480ae428910040355402a01601c4183c9001515401500d44ca80c1c00074580c02805442d0041740804907954800018034144800002c0075100140700d006007c40307409000c5a1000b01e943c121120b40c00d2864040300359070801c60125500c400651091071107103460b08000054050001c5400c603800d580200d044075940e500101804610342c80103101b02d80c802e94901800c80002c41c855825800b40076058000d040d8500d0b44010301c000c950b4090304852040d68a0f040d60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 811102473 1250 811101223 811101251
    0x5070303320f01230402180d1110210b030f071d0108190b0702100c080613050601050d020c011104061115040209070c06091502131401051e0d02180108070201 69
    0x4004250000c5da00144c1e20b0244601e4400c098001030002e60b403240343c1d40a04d4050102404401017141d8084660380f9200c2c0320000e0a452800a240100c103c851014911015031145688220000500507007658151029009500d0401c000c03a00054501c0c102184c4a804da40a803200a42c0135001510080050f010034050400d10030300382c000000c1c4007491010000722001e109110100201e02070310802c2c45444484100600030750001c540c9580501500341d614401e0040b20300455001712010385035035140c00e0140d20240069404210b1602c3c00359211082214003951441c0108010f0a8603503500b0036004502c500036003080e061440c07807041d00c40380009201c0583da071041e213190411054185142070041c0352610002401c880000034101200040c054001211aa0024100000c104102c52405511942800c0da41110717215002d000502c1407122104110780d20040000700c61000c0001810310300c0d0358180000380e91221210303003014540b120b008112560825205600f201c4107000a0041400310284 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 811103723 1250 811102473 811102529
    0x5011a04050d0c030203010c0503061002061b0d0e0d030b100503010602030319090b04050d030c14090409051f0204030212011415040b150a020601120305070303320f01 73
    0x50306220b52081e8104034100003c41c503504000350f81c00380c002d1048814041c0c0c050950b41080b51014020040202c80301a01440071803141d06c1207680039440504080d030211741001d00d410681e00c202546503207a10184181c40100031890b05000369070380110701c3c454141c00f0321501401c11000c0c0b02c10b01c00c0c06d20041c07002c03a0300401079950140f0f882100c1501e64001600942c054812114080e0101040c681440180031020511903805203081d1400e05c5a5901100304035018840c20900340f15007201070002440364070342a000400da403030088046a4518a88100650324152450301c4103007580c3c1e0020b01001181404e0400c540c1c021108002082044044040d04810100c0142600512110b0604842860b41c40b943310102c1e60202a0400492003949589440c1990007548580094895032000095111220740000900c03070b0725076905401d014003981c0503005000116131242c11802004120044401202400000402201501d00301410001e40400e20200c041c0c0001202e5150355851249814100340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 811104973 1250 811103723 811103729
    0x1c05040e0402060d020c0c150a0c022107120204050f070c062706020706150315051312201204030f0204020f030903122508130c0602070905011a04 64
    0x40c1032445991144001842485072404004481e440455540754144000901c941d0440060700c0c149410441c00e0b644030410f010703240d0200c1c009142041d518006041c6078681266880501d04030440e0320300c00c048800d05241041e04907109840120f030303840042d0b02c1e20740180364000c2e41e401d1084101c0c4c00c00750300c010000195a580501903d40300c0b4404001c40d180700e443c214082100c17802c2200c3c1148030746000d50186d4414407080d9481d46c01c02c3e8028060b0084000081708580d40001d203050360446001d4400d01520005020320004d00b098030559000ca0700c600030303840c013070240c699070325150a8008151840704110801103411950001100032120180d040485080c2c1c0c0e04400d00722200005840080d001c0d11411150030011440481070001c41d00b0000050040921007080d00d501ca50384010a046480c0c40710741000120b1106080d01020301c80c052070042da04040c0c0300c80a00c17207400d041d0315041e1070400c0a5212600680c0603507005c04c021080342c8503080c050034603c040707030700d0328003100886140c2405180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 811106223 1250 811104973 811104989
    0x105042409030506070c1103120a0c080904020703051b010b0907030e070512070f060206070c12110105310203150c0d09050705041107020a1403010e0714031c0504 71
    0x4100c1020a025070414802140d12400b00c5401e440c0c140300c0140201c840d4481101c002a00f0914091203260100c4d056070644503001d00c070703070804010078401c4440c0031141c2004c2e100e081c1c0400020702c9070f072654002404114040e482d0a65105220700351802107540780185894240d16000030714a5a6407500076841d0800c0300d52501042e08114401a03d0421000c0c3e408598821b6106078080070458010610138108c8510f025804c08603039940f1800c1e41c55250840d241d40c0040e0b0408440800030361004424500c0da0407502c2d0003414846c1e4a5030f01800c54809640744034616500c1e40a001508a0905080e50790000f400c4401440c0c080c99070110741c2d00c02c070195040c1d88880c0f801c40001d10341018002031781c40c403140c02d004c2841450124148103407240e0144c010b09028600301a2510034900761002102c0704154013401080c589442c0080000b008030244080907819520b406038038550321030403c880405070240040e50741da0320310314404152514140c1c0d00c190711801c0204150307031045030300102a00c08550f03440d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 811107473 1250 811106223 811106279
    0x6030b0a150c03080a06231008160c0f0b04061a030c0303090f0f0907030f06090209011b0302070b0c03030604061d0a05040c0306110318010b030c060d02040302120f0c010504 76
    0x80f22006006d0302194200307411500100c19043e02900c00f18003003c1e0b0000041e42e10301184114404102c6140108031043d5a20384400144294843e03c00d50040c01214000c100f00c0032802c80c50b94410560707510548042e9400350300c6450f5080a003958080111812004800900440e118400469100c0c01407010480c85440409040c02d480e450711a503003500810b004010540c0f1740f500260240c010041d1034411a400c03450044d010a0003030b124070890f0f1003400141c44500124144201c0d00600e12201c000c201c0450252882c00586086907802400500f004c1002568880c07401c4414002120740e40d62010b43d410560340c40303030010021090b80054202405100200e0b03541d49500300b800030624141e00040c00149420441c0da650005a000703140641c4000d80801c0742c41922008a07404da41450700c0c210b905802500039044185404401401100315044015043c00c0e41d07600051003040b0131210000c1541c00448207407815030014000510180b0090800500f001d04100360010301010349000c0900d4a041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 811108723 1250 811107473 811107481
    0x604120f020607050f100b0406050a03060c21020a030509030307050f0c2a03061b04140a05040f060501020607090305030a11030d0e070f0501030e060f04020a0f06030b0a150c0308 78
    0x10b404210740364143c22504944a404c842400d003035403020f01e00000e0300240c4ca8096503079070600e010700403030f011a9401405008418159210440205404c0c02a6014442c80580081c01002d1401c0070180c03910a0400040c0c49200c00e100180540340010710a10a64104004101002d81c000043ea0402103c4074a4583c41e48540b1000318600490241c1d940c407102e07141c000041241e8a000d29850074070009405548641c1c842c00300b171400c8450240348001d80518241f02c1841041c490510f00c01c59260010405203996a940300403d040b5252404441000c0361650018171181d601000016000605031428880451444e2038681e01c4e8050410185d0800002400030100c03a9402c000740c54800009010410411f091407424a544a0491007020035140b00340342c00168940c001e00c154a6110085009400c065580a400032260700004004907031104075000045400307141c219081020301391035200010002041003c0080c241c1250784404c10001943d011404d001c1d07488224080447d502d400c112903184c817 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 811109973 1250 811108723 811108729
    0x31902030d1104140904050a030e03120706231b0706020405300c06070b100b0408070e0a0b1014090409031214070f180b120402030c0604120f02 63
    0x810014800149400d09110548040100c00144115800309400501d561440005c1c03050414003154068141d80141d603846000c80d000e0108401c41100050a494610843c5481139095810945c026100700c0ea40f000003404115445c50740300c0c549044012484103516000c50350210303a4400001089500b180800e030401004525015200500001803521803030800e07170445800c10380701020b0040b0107004103403003071100d030032010070b2500c500603006d00030910309045515003d410712070245c0a40390304855030000007401445180a000034065a0028045081c5400c0c410303225100b003e0704a02d0046c0c89c0030b018202d286d0326030805030941c444504200f1488010090345641c2d41c041c2100341e60b00182854030071802c0650041501007004042c150800100000480c0354a1280c1c04850100100326529840a1594000c14929040b060301e0000383c004152904541682904400c0445243c80154420f000c110b00e018018100c1426040e03d2030303404c080c5003040c421105440c1078005418508484040c0007592 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 811111223 1250 811109973 811109977
    0x170c030c0102010e100c09090f09050c19030605090a0b2a040f170a05031815130506070807060213030312050709051903020a0816080309030a15090203060f06040e070803190203 77
    0x14140c00100400300000d40500c1c060712905504403030314000d000ca010307800d260240d110014140dd50b580640b549085584000041030003608044c2248104010b00300010042491248140c0ca107024109440c0c860218800b042c008580c10382d40c810f44180010711600c2203c595410855201d00c0c10b20140030700f002c0b031740c070b0500c44c006d803001c6d0543c00005585400282c01d004042c5002d0030560325403551100d000031481c11401803c4980d00c00383d03801e0004004500d041c02c0503100741405400400e15201c07127640c501c003ca03402881c002c458488000c1c03040003816040600d040c048400036405002038900f800c07006002205a0280078490704100d0000707140d20010000010143d60702405d03488005407640a4260f40f80c0114040c80000361200001207042c4d800482074030014030016006046e666001d640700010000d003c0c0c03452007008d940d54100c00150340e0402181d170003490b4403000031800f03040203810312007a1043c40300510403e43c0b14401c1089294400403c54541003c00d09449810072040e880490a40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 811112473 1250 811111223 811111229
    0x1611010314010e0130020127081e010218041e11031f0e06010c03170406050103120f0c0f0501021b1b0109060e1207170c030c0102010e100c09 62
    0x95906074000704034a848600300d00d059072003131aa0001192010114005c6006040300c03030f050405546080d210043d400380ca0039983c1142861592000302d541031002015001c9141d0100040f58800350b40c070080840702c940381426004404000754500000a102d09541350645c0501301d0040d60740703480010402c19065088284491603c60034000c10040710f14180c0c0d00e4009039041000600000003902454110584000841c0d103000511030709680d4080c019544082c41c540e00f6801e10031450340c0d6602c03560803032200707622440c407405000895505500b45140418110b00c408014404c0c40300500d001c25810a401da8803c2d036100c0b40c0c11042a0031481c040b80039004140c114a00e0380d42c0325004200c00d001c041080d02d04446101c8101410140700801190042000d108540209580c00040380c41e508160a8040c62100c202c8201c031110b0b640c1c1c65084100008545044003a0f42080001400d5444d042c46003031a0184244000d004009110010030340f24815900c46012041e03895100940b4603000b0602071001b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 811113723 1250 811112473 811112501
    0xf04092304140c1206041e050d050906040b0a02030703020d08091b131508061312030903030e0d021005061801060810050d1101022401120f1502190516110103 69
    0x102d0b081c4c49540030364030790081e142101c80c6145d410f030210042c032451800d6402c40780c0020007051141e100c040240c5145c0d02c00003590760002000c10002c64840000b40c0102103030b010304d40c02940e1b99040b604000742030401091041c410071441c8001d100320450000f41c5c0707111a42c0441c282c080108a08000104990032030581820b0040c1082c80b410680b580c211720341c0c03084a00c090141ca110f0381e02e2402010300a50012030003844c450b06823247c001090700c2684400e14841c0309080003e035144030700d1038107890402418100c400503481180c0700443c2084a00400d0741200003501c1000765008104913000c180703001409020304101d00c000000c0c42c8410340710070500c0100400b50110b00b464240303052110150641d60301d640e015204200d00c001507407000300800803011400c1c0c0c2010300d1503401c0c000c000c01c000341680d0017507400c0e02c0b0f000003000c013144d008042002c0b0042200720060f91500d000c080320315460310f03d4180c042848814403031041744411103110704940b1070344002e166a003400d5840c0180c000700003540280b10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 811114973 1250 811113723 811113739
    0x1030503030403020f0c01091202031f1e020909040204090218010311040c02210a0903060f02030601021c0c06050a0f1a040f15090203090f030f04092304140c 69
    0x240100400154041d500a90a84030040130042c00300e940c4040514070680001d101c2c0004003d407000c5545051401440142a120011103680f014225400070300e003840741c156a40d0310804c1426802c600c2c1503a00c516100c005505008031a00001c1e5003040003000030340185c1d15460180b0440d82c1d400c8107561810007662006c140c550310f904020011180003281c0d42d01843c603002400d841d0a000168000703101840a907030741d045d14030783c03101d000302d07030700921302510600c03102c00f0001c00051180c3c0250484000c079500010b0b00e91810100092811441c110f4130601001515404e6441c036900c240c400c0c0045405c4a8041500c2c3c40b403105400c0205848401c1c1401c0501d041d00c000d4402c118081d0126880e0f10403501409070707150103c110300880390000060040c41c0303030b91081040084405d030051680415008103446122081c08161401e69215501101403010002010700140f0924803440d440d540201e006400b40501c1800714092000c00940050444a5800c60042c44400200079202841201520000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 811116223 1250 811114973 811114979
    0x101e0905030d0c0507050901081e0f070e250f032a0206060111010c09030b0405030714060907090c050a0e0f130b040b060306030307020108101a030420011409010c060501 74
    0xb0302910f001c0302d08941030b000f20500010745242030f94000f41651101d80207080c141c004101000b1100920309107076201400340d07a400300d600400c14083d07400103000855024041d885c01d44500c1003841d00040d03d54200926118516600716401120640c480105050000d1038010008e41030380301c041c941c03551482080e1101e0030780c0c00040d40400c10382d016580c00c1c0c8840758a07030f00d94100c06003a1032003000d5000c000703606014100003007042c200c0d0040e04680554252850b0011a85540c4d00c11055491034140bd507000b8801d200000e00100885401405543c10410045101c1c1c94014407601c04c0c400c000d020071408035495550303550354120080c0c40030001050b01c0d10b8a03192102e200080d240100007140300d6071400014405904040003140d120781c2000340551b1810701d0740d9005403082c03180074100d480302c04030114021a07040c1c1801e1030790380c1454117611030076180d01e09481c1040c0d00c0e40681d001e04902461907241030345541d80003480000c0741801c0d1001c1035251850310340100c814000c01c4c02d000c0c0600e41408000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 811117473 1250 811116223 811116227
    0x1b02060a090602010e0d1d1306080102041a0702090705071b1e0503010504080a080c0705061f120c0e15040f090302120f1c09140c040b101e0905030d 65
    0x100085502ca0b070000c3c0615201d0701d90060320788080c0507203070000c01c03103ca0401003040391040b031043d04100b009100c1481e014001140600f00c9001d9013244803140e6000070f081c404406040809018070403074007022031801e0115804180007080192005050100c040f41800802c89a2124044899004034490b0034065a4a5115001403054851458a8219204003054605060098502c120303000580c180c030740391403024225440e803002480c2c3da400c98030a00c9854000342040c0401c130300896034900346088c0c0281681009075403038560780c410001001584411000218804c4030b88048440620310b140480c4d480c415040300ca02c540b0281c05900c985002035400b0200c0c03a644c4070550290103682120705081c3d41140d00d540307a1044c940d500c1a011414024110744210a0622840f4140300090201d40b801e01c40d82c60203030011070001440100c1d00519045002c034101441a046c0e0502e0884003902100048030380640808822400700100601b800c0e5884c110600455446004280c0036084980702e2900320780c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 811118723 1250 811117473 811117487
    0x3131203090b0a090302060609070c0816031701030218060a27140906010311010c02041d1605280308071203050109020f04050d150608010c03060b0a02030306011b02060a 74
    0x11a080e0a00202050000161344915404254160010401c0d502e8803001c0001241008203600e0030048420116000240c8000140040c01030808606850083c5458050f00d030351800c1042502c00c0000800400c09030341d482007000320b15059100b00c40200d46039800820110f124070740101100004100c9411040d80d20300d003020005410f1524104904250b904030402e2605046e6002c480b55404000144003017249a003213903104a505060008900c1e820303074046030980e01001203c00c1c02001c02107408d03014038410710104201c4040119501d000300d00381400a5501084030189030b04000c060101401d0800b16a8464405150400c494686079000703864110810140e000301b075800a4100b00000036420503900030b036880d000c140286c060800e402c1c44103029800d5491401528044001c03482c0c00801b01481c4911000f03402030303100201320201c40340400f800740c0c0e0144c0d004454049040040c040101d0780481600d400040034602000c1d444441543c50548100744c0c10f0181d4462400255000001c0e00501c1d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 811119973 1250 811118723 811118741
    0x20915040b0414070f021c0f0e010206012106020c03180a23060a030212040311010e0a0c030204090302070b0c010507080603030c0703120c0c0305070518100b03131203 73
    0x2010700196200c007060200b61102c640f0140150041031004ca441280030314980e01c1c0426071441110000c806c20f604900511518040d070340080340040f00d0b0420381652050b98462104001c0c00102403035403400c009042c017a440340030000d5054540300c10450810915404903041c500c0258101c1c0d40703c414074203945c103030240d11802c00d51040400c4c010008032035503000405208000302d20b00b43c60140b40b218040c0102680f064100400f0940e0811031381d0a148508030718280100d0190785c603402c02400008210342100e5110038801920b0303100816983c0018174181502044ea83d06480100301140c0918060f41b500c12241c2000140f4400070905900d5032078154480d6204d0074241c0da940ca0140c50350320a060b1a4401c0c03ea0340c0300380d500251001e001090800f075030381030b110225140041680003940c6903001d102001350001c89407600403620810079807403d411942c00d2400c01c0c040084103400c00c0210a141020b1038400d110442001100152140441c1c05290240355000782144540241c42d070002001130680d20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 811121223 1250 811119973 811119979
    0x408010203060109120506160c0b160206010f14040b040605060d0b09060109060f0e12030d0f0b030d05160203190503030a0501170d14090a322b020915 66
    0x590008510311100e00140305c4a410002074049a01e425024130003144c1501d10700e101788440034008600241c0c1c503031501d0b442903544c018101030601102c0300080c24680c060780032051100074880144051200d8280c485020441181e0014846000c94003250190a00d644840c0d4444070100f1000c444040d036070001c4032885001c0700c402e4201d540e04001540d0958540c0640700c0015200940a01503074058042050b0510000780200500703900701d040d040c03940d44810000304140340c54800f20441e6a00a004030030815800714058000c010020000030054020060220903044080e038000d0309545050010207000050511007488801c2141030241c1c1e00c0d841176072407030906441c107000003540070039a85050081d10040d030054490a00d04010131205801c001c0710b460003c1f10108141c1d642556502d01d40d000070851200c19110103c0c0d01182020005145000103074141080d0400050350360b40e02c0b59a8040007200341c01c03200e6075131100d445580c0f00c91081c00000c2d002204d41c002e0000242c0b64150401c00d2640403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 811122473 1250 811121223 811121237
    0x1f0903110a0f180920040b030d0f050f04080303070509090718150525051207050604081c0c030608010606180e040213140f0c120a1e0204080102030601 66
    0x140600c000d07640c421040070100301c00d01480114051422411a14a0b2102c04101070056417030b03101c0c50504c08260480f21006071443c0b0101d604150240a560b21412000303090510694071010308210180c01100e0204200055401007401d8500160390180c8054000c503030f143d1400440141c2540d004480140c45200110001f41099100340cac0c2c01403013107011444400345c0c6840c11908a5030710580030315940038070100303110102d2070303c015036020901c0403104c002024591105040c120300301015440403880c00b00301000040046500000c4840d0440c0d0b108043c9a80c40511086105144480942004a460402120032022603141d084401a00c0040008201c0581e0b9044241c80340040b41000501380c030016882003011390307000046d40d03620600180c1a030b41c1d290032560440c0101c42d0110165501007048c0014820301000d40d080e15584498520680d910300204a0320701a80e44c8001850000e0072a202c403502440307154855651814400030120654855483c1c1e20458083c0d00b0450b103150008940c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 811123723 1250 811122473 811122503
    0x20108090316110301060b1602103b09180d180e100e040b0f011d0a091b0e2a0403060c21020702010806010f1d1f0903 52
    0x10089031050712825101905881c070030f0351846040c56541e800241d05550780c0600141490600300280901840d50510003100602807041040c01400b240303003503041040d030810480704503010742c48880d075901146000420303c0b08407044609400031150314072500304402900f030121150410a031000021410016110115100d0030211808003840c844800d80444642e0108400da108c04010783e002b406404100001d1900c42c0c40030304100c031040d02c0880344010b0090801c070009090b0f44400340542011480b90f4541020080c076081d01c40806010081d000d40c0e1484100308101c0d082c2791944241c4882211040143c5e5030700c0307105504400894906000d400303074142c0c1d801c0888005103000c000c2c20480c01e040f818107046499401c020b012442d0007105000b01c848030300381503101440380c1400705090503501594410382da1000504050001c1c0c03995060010302c505114401e80c000b40d0f0552050000550800c5250031080001d100074002501c00c500301008031400c1e040194407102240699004800c0e217410b0b500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 811124973 1250 811123723 811123741
    0xf06081c1805091e01030c060e1e04151502030c010e030405010215070c06090b1f0b0a03230a060e1f14030c090c0a032a0804020105160807020108 64
    0x70701c607505900d006035000d001d2005141440340260020898000850303031080a01852030300010a070401c0d180d075400c0304d5082041c503505c1802210b5101e0240c9804600040d8000c60800c81c03c04121003d1103503032585080b500c040c4003e10403a0007480c241261804000740d4260194407980070b007408040c01d50a03c2c01d015901c1200201b01c81c226401039000300078a801100b00b129101002a007050b0420000180340d0300417070018010395810301c1c00340d416500c05c0c0c2090142d0030801e901080c175000c0c901c0d480610820080341280c1c1070390003003422400c2c0422140d1014003000c011403542006651220503040074480e206009034480810703240c4049180949840740c1c5007281d0322034010f980404900b440e60902344016801e90890514903400501100d0425000c040010581d0500b2a00140c40407404211859140d03410301030011451041644010702c941c0d042c1140d0306260380700c1c48140611900c14080760459108508a0f1529603200a0f20400da96040c0b0b00044d46074000c101c03d0303000802007030102d40c1c0700f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 811126223 1250 811124973 811124987
    0x301090b0420070c08070303091401030b0d06051e100303080603030f0301050f0a0b07110a1202010215060f060a0201020405041109030d0e0105040f0e09010e160b030a0f06081c 77
    0x952000300d11020756038034000002d01c541c4107440440320454180c1d00041ca03800c003003080f03c014600ca9101c2c65601810007aa0b01008160b24032070504043c00c080c0188003c1e1104405001400e0300a00d000c00c0c240d13541d401402200c014200302002c00390701031040020341417a0000d8001500d1080c2e607200350580701d41040540c0ca01507116031041109003003004000ca490001d01036034074948003501b4082042c3d41c645440c51640c00005040d02c00d5a10101e409090345048007200300a000c401600807041043c42d00000c0d079803509004210300412404020495955404482c0d210f0100020004c944e10841c2c0e0000034040d4109206403409035050840c0c5240040740300041d201d2001e0043e00412020320030081c101d1300402d085040c503040c042c0400003c00d00d43c81d017906003400741c4081c20b01412141454900e0908440d2524010f100c1904029a802688101040301a0884403450561601c0381c941c101c070b01005140c410000d00e011442c0820010349048041000e511503903003400b074034240c4403140400359540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 811127473 1250 811126223 811126241
    0x60b1302040f1a0d020a021005090c0405100b0f0d0e030a02102003040605040f050105010618150509010809120324090402130e0102070606030c05031c090306020703031803050301090b04 81
    0x20200034008900d510400703170b002c2c00d134212080c4126106002d5440c0702e0300490340d0503a640855034101a5003601c050400740501c0d5000504004040b4000385818404031050151401703e60750b10100043c0800041c60316003180d0328011130740d02035070381d0b0360302c40600a5a04c03001080840f00c1981000c0303404400d61284480c0c020b40503201151245156140c0d620000180002081200c40c1d80c2c00b980e064020610074404d981c003030205130300c03840c0085040588854059026030300c02c1280903140301204030781c0781d400019100c4441c2c0a01f03103014140c4800700c0050810350410f40d68a13803c0408410000803000313410904030001d03522004090301c48460401c0c4442c02404540180d0002e40924945410303200f264404c200c580b1045000505020042d500d150548500b94020303036120841e19424019403506208400d41074841e500d8248011400090180078801148005031890380c0c0426120207250007500458000015440c090011420914026280d50020b0141c1c0300410310703008801465051a2190b040c030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 811128723 1250 811127473 811127519
    0xd0219030b060f0c100509010213120c0e06061605100605040c0f12020408031801031d0a02090415020c06190915110417061501090e04030c060b1302040f 67
    0x182540302d0505a12984c00740c003444115100c0d0075104540520b20b1b04c0358a020340c0c4a10000760765070045d41540c89401c0520380100300300050210405000480c60900070003107411004503458a65030740400200280104207000e02c101072400c9041041000205401071a13031b01203801000580d8440342072004440112000364080742140303000b40360147c000c0b8080e50000180000251516440c2c0074100d05507001000003103606008a81284415038250060003510012441040200c80d40e01c402c2a1351071407500800b9004141c1c2074080340c144a0743c20703400e40107241207010556440c00c910f00921381c2c8580403603e0042a0282514003100c241460195002c1150003200d981115658200200014034402c10803985503c000c100c001103940061580700f002c01c10400c0944110300d00700355050a03200140d40d456040110340c2c10240400319032685416003141d0503107011001c050b070514080c4010907030743e0540b540c4502080c07061206184281c00500584542d00d4100e298199603080d551440000401c807509 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 811129973 1250 811128723 811128727
    0xc030601051e0906070c0e06120a06020a020325020306071d0405060d0c0b0406030509070f0e06015003070f0309021806030c0a06050315030a080d0219030b06 69
    0x394028110080240300348025607001d240800660019010745e020480407200004021420040950003206003944a4400c1e14101d0309030680c1c901d51922007141c0c0c070001708000d0b4041070720508140b080003628010100f204d00c2e00e1903000c110069013140090104100c2c0310780b01e101d0000348450310403201004080103400101162044000420006d06002400705400102c040d0401c80414642c51640000708881814559581c0c100513005043d100000c0c82e000e1641e214140070800d1900748491601210810407818280c2d81f90310340100d40344460f0303004148080000d00c1c010303c0318103000c80c2c9140e0b5110410900b200c24050141d0300f001c4a145028000c1d0b031091040c00000c0000e80a4400102c22507110310b00011080060740c00034407507400d070916684074617030058104507960404001c503020002c000c45071f911440d442c0000003041444010003215540c200c1400c0c3e0001d40c0c03070400030b4101c0540c2c0701d03054685403142c002c01200250800b051940c2080d043d0403541000900a21882ca110074006c0d0043e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 811131223 1250 811129973 811129987
    0x308041205100c1d0d0f0b270303040b04060207060c050a17011a1e03091b010305041113062303010b0108070207090c090909110108010503030424020c0d060506090c03060105 76
    0x402419102000903000354010b0381500001d000000c1c49407400e40b2901c070459407030914082072484150b08480840388d80041050107241e82c00008241c4c0d51140d4851405961076540786003040290243c084010162420950261011034020000d48242015903950020315691003662040f4a80300317104442078080c0f480c0440c074112560b14000c00040400e89040d10384003500440c0d2803460f5000310b94071040c540101d054655101500c8002218604017440c1c2409941040e0311031041c5511174070600392058212f40e814000710605600b115008045083c19041100a048628115084a042c00512079483c2c05060b944660003040b105020750010b5009200c03031418110048010140341c1c4480080c0407510f0b500042c442d8890007444100d600c1913408000d142d001c3c000140582e54107811961083c0c10500c42401950700001c0389000325110b15941e0050400300901c1603040042c8001101e421203076040c00780381030200036002540a507100340d41c01c00701983c0c0c80500c44201d003c103450640c0090b01c204001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 811132473 1250 811131223 811131257
    0xb0a0b090f0613080c01140307020d0804051204080a1416090203040201031401060c1202010605030d14070f0c0321050f0c0106211a07020703021003060308041205100c 73
    0x350462070018120340e1030718440c2a0090503681c0c0340c0c0d2025840c1e5003c0d4800c0c0c0440c1d60b0000b200007040f07100005440c01c600700140c000c0c2d144c05420752008100040c800014041c08020400502100c040c410941d0351207803075001441c1c0741c0c10116420b176145417000c050f0f00208a40065202c0c114101f403c6000111414505184042e40c0042c2c0b099040503104c24848229400100844e070082ca4240c403141c40260103403400c030003480c00c418521825a494031304204507980b00403e00013281000313071504800d600c400d0a800e003140d0181c034030b01914442c1c01444000400c802084204103490160450400c590703421780042c5410441028401c1c00100c0a000c0d550600f090403000c2c000e08400400042a41a21019401c40000c08210714659064840c200c80050208580180c10603c508603640180c91500786800381d0390300d10324032009004078690002d55004512a5000d48041d550141880c3d65030f80e46c034682c000e01507882c918140c4843c020b101c400071104496120300b40d00b42c807841d128014410418600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 811133723 1250 811132473 811132489
    0xa050f030703080f0d050a0f290118031b06090e042f09040501020a0e01090305060f04050712030509010306060509280806041202071e0b0f0d0e010f0b0a0b09 69
    0x8145000c10b8180003100c801805c0b400707090301c40c44074020005200403101c02c1087c00d5602504240350b0581c101c04900b4460758501220504040081c24000390305400010602140040303a0b0000c1c0c11800000d0341c14031022082540a421504075660b0450341c591140703650041c1c1501a43c1c000c04100030703807020342d044448800842c0085000c5401c8203600c030000002181c00d042007181d00702d0300c0c0e95002a001d06100d4115800740602c0c0020700e00004690b04596425541361409850382d0303154a07071b8034006020040100038800180502091100c0c82e440c4c0340c1340141c01034120001c41ca0100c1c1c100300011556900c190181d1304102d00003003010122080342089081c1040030021100c00050404a021414180c10405640a02e1142009007550605604000d040040d150000040341c40b0b0b0301940c007440036022860006603400c841440b682d80080e55070b400001c0c455039031000d29150030308130406100ca4049d0301a481288509005004007902007080109200c07807400340c002440000d100914450500c00c0c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 811134973 1250 811133723 811133737
    0x7020f0718110d06170d2106050d0c060906030e0309040c0306080d090512010509033a1a0f030a0f0f021f0306090b01050409090c230a050f03070308 65
    0x1e0028003910000c1200e481a4090f0004404035500da220420000b00942d000c0a00210320202030086065054030060105c3c1c0300402c05040d000c078089a514504c04d0340d50214009100051844040300000d1510f6446070b4200c1c030800011400751070f40029800d010380600002d6403084406146001404820400101a001910b4003050354440001c1900c3c0000c000c2c03660400d10303c2e20ba0244103842c2c402001110346e082c41026005904100500c5031a0b0300c008107543c0821000245101051007800074041e103410120152651410340340824030240c5090f6101a01c4040140c00900752721448900b03010100d07130201041d54143e403003501e902c0301050400c41e581c030301184503d800c407013400b00e1900000c001e40c544000c460348100010042c0703000c598151166000a080c007003410711541100d41d0020301580900e226a054450706e49110200700800541c00744040c00109841c040b42c0c1400300c007180e0400841030a040c2c09625040c502103030614008030f041c0e0900d00020003d110083c05d5540b40341658100704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 811136223 1250 811134973 811135019
    0x106120e060a0603170c0a0f080c01050f0712090b07050d061511070e0408090907110f070510050702150a02071d040204050703090f02011110020c060f07020f07 70
    0x800d202169800500031280900b00c0360101141c1282541012005502d20b400d0101030140100103110031201702252001986401004840d0003001901307002c0941d02c00e010803e403441d460102000030803110910403c0c0101a00d64070914086840b0016030308462003070740040c015405510000d44040c0c440c400074119113413007010218040355104c52860341c0b00a140c0c503030000b248401442c101c0c09141003040c0002041032854101413420706849100051003485540b80c000c0440000007030629008146294031840c4441c2114041e000644015031a4000d5004444c802c90240d11504c00c1c5900c100d00743d80d48103030020241d0316610302c0031280c0c0d0001e601103030842040d401805c0000580b0704804d40203081c0c041129400124600d801d20400046a00042c0104c0a16240940ba06c0110b050501007011243e42030810400220300007920038a80a400002051030500000b11001e0f02803000c18040d0003205404840310362500c40750000c2e0784501c062540800282c0c006603082003144c214040d00301d03601043e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 811137473 1250 811136223 811136231
    0x2a03060c09051e2b06021605060f010806060d08090607050f0703050f060f070e0405100906030503180409030c0b0402060706050702031e090a181404200a030b010612 72
    0x1800100741180f488003111440007030821211689401d06128401c84007079101e07442c4032145184400419400310b40d200c007404150340440c080325500e00c281c1d036240f1050307041800c0300d68914000c5060103503983c3c00d00800c9418042d00c00416401d05098120f1015107034826581c0e81041000c0c0144407650704100ca09468034460540c03414490041801701c1c40185010703002070a5901d40c0c40c2e120318030b41800544803262417104041040803043c0d2001e12800078035011500451592140301043c80c0100c0260080c4000703914254001080120000c0140031005035125442c00c00c1184404002c1294801d02003c1e0201d40400c90700c000184401c50155170061005041c6801c0c60a1a22100301b10350303049034490090b070b00000d083c20702001000709000c07100c5030200402c0d242081c058081901c54401f40f00c0c00c1035500d03008086450504040c0c100d81c0d4240c2182ca4018000d10301824406008101e519510030388005040f0b000e1440e06040f50f042050341d42020005507140d00c1c0280441e459800d42c106106400e030343d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 811138723 1250 811137473 811137479
    0xd0906090618061407200f0f0a06050604020403020105040e0703230603061503070b0f091306030c2c060303070c03030e030c1806010f090902040e01032a03060c09 71
    0x4240310741c0030b0001c00a0346415140c0080c0c600318003191040600f0200e42c1089900304003260707611064804007260b8450920070001000080700d45003548004002605003d02d482007840100d000074039050080c003e910038081d0b41c9401e41800120300c202d0001900150040105001d800074480300c054105070180f0340042e21181c10b004450084680d80741005203103d074141404410720f02000a1904480b420901d6250340d00601d001a40d505880c0c81509440360000c82d2005d000c002d80710030740e0f603d1600604900080511100c142c0004c106074001150445240303072020800303200b034543e02206035082d1030a120914441e03c03c44003510750020306071603040c03104200c0398000410060300c02000310b1003520f42d0707212108158101030510000d18200c5000c1c0518580101a4ac0c009111146e0004000c0c00c1c400e1141e0742c0c48108a80380f10f41900000c00090000500040318841880c015048034000c041c103c869160400c400790130002e0100c1c0c020703084503403200140045002d541c40707040021001c0c1031021721030703035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 811139973 1250 811138723 811138733
    0xc030e030306040b03331509060f03010b061204060c11030403030518060c1e2a120625030b010507020f0406091107060b03160b03100308190e01030606050d090609 71
    0x30402801b01541c0d507a60031220500c401c4e10001d074014000820041e50f15080d9000704540c5d02e00100100e1055105c10714110392602d086d0b00040c1284000b8111139a140415841d015a904050701e0440d10149046800143c07a8401d00d4000180d043e0341010b10320301031075601d049840d90001584034004030b0700003041250741d07034513000103106407250700004e446c0d00007100000030660089504c07042a06d404c002c898045d46280b42500504112a6201c40040b80502d0004142d600781c1543d007255440c8118024404201c3c2c0329505508403142c081651410714003051070171006c3d41d0382080e03401e0101e0317130038403c0c5401881c1c0b0300403080741c156000c0c2000510b2661100d132101640d0040d5000700505100080c045c050001c0c2c0c0c0200c12181c00184d00600d031072681c01c00b001d62038807007620850006d404040041150b1144a1141500840e08005020340783c1001040890b117840c01d550150000c1040f5006403401d95004e40141022124151190740c2000e480307140e1030010301603d103412a4070903034916903d00010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 811141223 1250 811139973 811140013
    0xa0f090b031302010905010203211909051e0307020d060c0c02150702012a1e020a1d0f07020d20010c020106180504020d082503120c030e030306040b03 66
    0x101c2c8000d41e0107960910f00000d4a940d1a0f42c219070704541041046840902522a81000c0103072141d0a408030342ea0340501c02e906120410182024007414001c4820a00800240460a988160f0703040e504040007445860740d82c0c40351840003034021b069082e400300428030b5544080400846800c14641440141c1c0c0017414005150b10b42000306100401c202081d940e01648071078948a810f46008140518001462003c0e180d00c2c1000f007010549852400403071041c5007a450b881e507409056004400d13100c1002079220b01c150209595681d000c18001003046031314900c20340c0621025000340003520004081150744212412655440c003030050180d108441c0244200c0909015941c000201c0c02d042c2010500c0e0394007010b2041601034102024807015a0700d426a040c4050740c40100c20340d5407a0000040702442003400c003258407409011034104c0505411641c4034030b803880381c81c40030003e5451448044e8102c48441c03603141180e030310510010340e42d41080e80c44176a100030010100c4800140e00800d02c0b802e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 811142473 1250 811141223 811141231
    0x1b030201020c010c0f0c0b0429090f132c0307020906040c0212130905070203040b220305190b0901060e010506090102120d0603030e090f0f060402040b0403061b02060702030a0f090b03 80
    0x2120001400c000444065822200c02d5001851851302156058109e08090050101c1188540c0caa5049807501d52340700d52051510403080c4000b48403080d007946024140c1000c012490044212400381d60318050804421905015802801c000700b41d01c44005000081481e0050b010a41c85014803a4019026440107020039046155000492900300b01207102541c1c8082c1800003036500c240401c1c4090314003070055031000c14112889031600005c806501005d55211307800a00b00d401094104c14541d01c03091040c1500301d01400801001c0e4488003551400c0314400e103d4503003800740c188010301a40c544400203000704081441201c0d0351613012a9410150742c07150145500a42d902d078420000c058002c0208100c801c1c1c03c96025856190030b00e0714001c0383d00000c180e0441c88a15a000620640e1142d05440182c40b4540d5403a807203a4403850200000c000840503d000ba00407220014000c03440090303080c3c8160071035400703142401e0401e01c00b900c0e6400c0d12095607040c0208a0f1000c52581a040043c42c81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 811143723 1250 811142473 811142489
    0x11211031311040e01021806070c062a0503180915130b0a0e15220507120c02070f080706090b0a0c05010923060f0c07030309020d08071b030201020c010c0f0c 69
    0xc0c4241f024018801d003005034014900803401880043c0100712050b42c00c07070846005041c012490010f60007043d07203951001805d162491a0619040c0078418008090a4842c50381a5000318614918082210658048581415030400500b01c43c4039410240502640c1141d40741021821000d0700000904000310f50300007420a41c030031410095681c1044090700901541991404405010021702d5000307114042075241d5613a889001190605214142c0110785840784441005030182c4400c00035183d40c0305100d00c205440d000076002c00c80c898085049000c450350350b20342c289010302e00400c80c08540c115a14150902c0980394105001c40c200307024400020b44a515007803c1c010b4042108000003800030010256070f8010400c00020845048556402180003645162102038a1408501a09529500075040080c48170700104001d41980640741036441002c0b0a400c40310803501c035901039202803001070300580c0802d84080300355000da2000708044d4012201c6d058090110f40f104440c5032596440b40304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 811144973 1250 811143723 811143727
    0x10b0111070614121f0614030109240b0417031c0504080d0204030c030215071223122e030204020f041502060403030c0c0b06060f09130209011211031311040e0102 71
    0x481441458801c901801c11420440111f8001c0600b12032140014081c0654199542c2042050011148800c04c2038400758020148051b4651085081c40c0c0c01a100e181100c000007030442882c00d40100580c0c0290404051003050002d1502c40c0802800016206840c00c00040060a000e41524001040030310300880c0c030010711602d1342c818010b01c40e803400c010090340c01c000c0c1300c460f00240d04902400451034041ca002185c1049240143d1204c4201c3d205c481e4801000084a1249031403504a40c1d1081803140781400030051403048000703000c040e44801e11003603111720b0028030040c80c16a0281c0740c20036401c1285810181c03240b0b080440e05110613000d0016031f000d242044209a81030144000c1c2c00e40624240c11064000c1c1c2e98100e8810021f40a9485800042140104400c0c00e1056a00c9a070006088035060716041800707000a510801015000030582c2400f49400c0c9810700451101011500d0b609103150307116000d51050444842c4111101d44a034071142d40c040d03540e80180b0080003c9000010703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 811146223 1250 811144973 811145011
    0x2160602061506070f110312091c1502041707060302120c0703021e0105040b0a0b0630190608061311010c0803360a0213140a020a02010b011107061412 66
    0x1f51400051018004910404200c3c03e102501c0e4810030101400c00044101c40d02c107070a15180b07402403500c81c40380242c2e038400b190000700a00c117050400d015842c035070b09031045191118070407010703031051142c0c908142012402284070148000c5c0101600707030003841541e0f400d5044a0910742e076055158090010f0b41e4640040c0818081c6101559401503034441f4100030f50800360b0045100d9008050a00f096070001c1a0342081001401484903660802d00c510744c1158640301096048021b607104827508094600503010884010005004d8001c0d1502c0d8003403c040c1c42c02d0358840c808082200c00345030410880d5041c0750005400e40011b140180e40303211410f140b400003107840e08a004040403442e9803a86203072030b0b80d2141d0341e00401c0c004a10307170f0141c801d04030140c054800a800307444000c148038008064607081005407246130380544021001940240100003010004482107c44ca212204158211401c1008014014580c0310707201c49036070400c1170410b80a09a65030851004440b8506e01540350040c3c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 811147473 1250 811146223 811146229
    0x190b0403110601140306060d0507060e04090204060f060f02070e04150f0e033106030b0a030b0703020702041d060f0a0f1a15030f0c0304060e011a0102160602061506070f11 75
    0x61f6102100b650707003240341c0310107071a602d9885c0410720aa10510580001c48a440c0d2100e41065074200d40141c000c4c4881a03441d10519002da00c0342c441c0100242402c407120075860310201d00c22080350f000b03001c0d50300c0e182c0710764a4214a0711140b540d00d07281d442c4d88020703a00c00c00c00e2074050084035414800182d9203c205800d101d10110021001c1c2801000c83c204030b150605503041450000c0e80c1d060b150008011009001040a4810f80c0d0009042c625800042021190303240d001405218400e41d81840b00c0c080120003c0701542d880c03100d003200340d004400006c200144c0d030806c1942c405c80e94440881e2a58900001004440e00b160026010900d00803001c00c490800c10f00d00052080b1190b082c4d840c40ca80707c544031400100182801c6e40745100080801c0030310a558204000c01c4405500030402140031340440e00c2404907102510b4054019031052506800004d14008106c07030283d00500240e981d00101c43c0d81f000241040c1941c454000d028103070101d102500d08048403031082c4c1500040341510010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 811148723 1250 811147473 811147483
    0x10e0708130f0f1202151b09031006030c050405040f06380405010b0301150c080405180906010509090a030516050d080403020f0606060a030e100e010617190b04031106011403 76
    0x300304199032010000300c0c0003241551413158428043c42040500f40e8100c07090400300d00c0741d08201d40d812b1281213230181c1030900340d91220080324403402000242d941c3d80e50074403041d14800c4070003605018041c0c40000115510350040a00c5180320500c0341440300b40e040d480c43d18081c000b945503402c02820200383ca01d40c02c01d485100d0242001a400b203046601d0420302890030b07014a22200104031039801c48004002a180a42e0007815004003411006810f02c8401304548000311400329080c03007500000501410501c64107801003a0040c040c0a0302d4162b900c0070748040d0702c40e900400514a2000007000401ca050045c0304007640e5a45e030b952003505181c02d00030f140c940c40607004100b64101200707000203541d8103011210000c915040100f003003081241c866040c850411040344200e800e06144a0201742d065220406449944000114243c00d64011550700d6030044c1079411408070b9100e504001c241043c2856a00c24803a2600c0220420200e03845420002c0030f921200f2400380603050030850b49020702c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 811149973 1250 811148723 811148753
    0x90b0a0c140309121c060e06010320040536091b010f030906241505030f1b04030602120103060501080c010801140402040302031203060f09010e0708130f0f 68
    0x20155045040c038807400d0b0380740c40b104030201d4013001000907a48138180100c20010032074800d6840070800a9611020586088001c6511301d00080ca804048103d0b60031061000200746207410019042604007020310620f2210103080540206000c40b100580b400b8102e2a0410b01c040001d5003c210308050021900c3c000d00d007a01e09032002b0450100700c6499a000505070542d946624004c1544505818414020030520f200a4080440711020344a49820380300d001c0200c1d1901809224054100042107981d80025580d50280d00031400115049101c2c07411408500320400b410103141c2070f501d58030303102203070300281c03400c400c06818100420a01c64684101401000d501d8043e090300304e000400208000c0f414020300c2494045080042c400d61200e81c10356018503030107011122452816500d004c0d01e500115181e0348100c5124064000c5402d10800090484410540c120025203910400390f4007101f0081050070b0580311104d2040118020300f0354800305502801e8400803040c800c0c00c1c0300001412100b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 811151079 1106 811149973 811150007
    0x60a090812070804120905030304032907031505011706012003070503071e080703320d0b0906060d050405120403120306060c02010f0e04090b0a0c 64
    0xb69441d1302a40c0940ca5449026000800071500c0c0a01809425010b41040c0400c10000302e03045400d03124810310b4440745035807007112001103400e40340448801d0300007512898000400319101d680715010b00001c1c03030000417141d0124139400c041000503040e90704000f5a0100700054100c242580210f0014036402d4a5030b40d11302c0e042c0766580ea0401142940c81c4000e00c01743d0a0f403c0404000c1e00c52080d400891641130224580b0250f40c8845ca00c0089040400d5020011418645c80c07d24142085d405c041e4507604c1d01124000c2c2d10407200c110f0440c1c7d000e0b200780c90600c90250f50b031307006448010440d1080410f0550b50340c6041d9003001603a8904404840c00407074003004118186411145046480d6810080655101411214003080e400041d010420f001882400c540c480c0c6404203000001800204103a15190f640c814110400c1703c903440003541c0e45104460a80d880464440d41c0c082c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 810971223 811151079 := by
  have h0 := BRFrame.cov_init 810971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 810971223 ≤ n) (h2 : n < 811151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
