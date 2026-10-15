-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5327
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:30:21.484713+00:00
-- url     : https://prove2.me/submissions/f84bf986-c4d6-4814-9853-363a07d74bac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 957913669 ≤ n < 958093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 957914919 1250 957913669 957913681
    0x20030406021b0102010e120a0c2004050606070f03050d1103072a0507030b1503030406020c04060609080a02100509030102040303260103150506010c061d010605031f0b12070b031e0f 79
    0x4400350050702442c0c01e0440d8400c42ca9910105030840c002d046031203542440283d52b420f41054071959501c84015512980707052650340303d8440100c0000402401c000e000944162444020740001c0442e81c001e060040d140c0c1802e0701c002d0f082d1381100d12401c141c000403080701c2d410b24404078110342c0640e0300507000d00b5880381140c13164004070b80c006000110014506244600c0c5840c2040100b004040d0340d806002d60108003420070040d034006034427490030049071a60601c402900801c0403074840e40d0459184100011000d0159002d018944086030b05500c0410000285904100750b403103841c00c610340d07007520a1421010030142600030300001d41011065192119044c19651181e03401240505020041c151031395500401d4541c10400b04040c0f441040350040042e40034014440a45403c401509517442120860305074410030960803c82140ca40c484801c1e60344600d44800d10048000e810f40e207455480c5c840c810120740c4152104074010380c4985010060100d2500b0180c00352004e82e0305015a900c0344 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 957916169 1250 957914919 957914953
    0xc0112110d090f0209090a030e0f01080a0203040c0911040f0906060806130207050601090b040b041e0f060807082104030515071b0b01060e0108100620030406021b0102010e 75
    0x402e040350420100003620002d0b0740e031454641e10901564000304844443c501d4000c0806000229060044500514a00c05680c04c011304030760002040344016200d83d21800c210b10345001d5540540c1403a07141018010b0198075540040c0195180c82c068491280e03a2074014604640307580c86070350001003c030b1020030b10034a40030401e4504050301c1d400240c10917145072038190514500381e210042169554441079800d00303040c000c8000e2a502100e042044407152500f808800c1012217842030070a50f03a1040d1080d0344c2c00c030f600140c00340c60b448045030826525104010395a0441c40c009040341e1603940c03200302078800c00804850503607030b1100c0548680b81c80030b0910541c151300600f401083c0034450340e503102440801e1807017034000d602442c400342e01549080400360040f00304040c814100019041005600590f0354000c1080310071300d140404c041803038210000c8040f10b8900071000c00d0300000900152050b0300091032801c40701c005040d2043d895454005a00f2114428041310346078000e00800d003024084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 957917419 1250 957916169 957916181
    0xb130c11071a09011709030a1d030d050c03040911090102010509070b0702040c030216030e12120301051903021e09070504051f051902010501291c0b120c0112110d 71
    0x8181450002c0590764003145001082c11034500007075500100d00918a00d81c84107103858071271523510f501d000700d600040110703407140c000c0d0601c94180600002ca200781c0c0c10701001254000c00d00e94074104030418294403440c0c00b070790200f6140b034019070038640400d54070702c80807900d003080320041d8030854500f03d45030382030001030202c0d40380020500da82404080309400c400c0490202407486540ca500c03100c1483d0b0f08014a50009441040255001300d05a11741003a242c4200da05450003115801104041c07603e5034140561203030402074001c0b0b00114a1030b00813014009030000c0718800c44007810160703101d04048400380203501c1203541c40074508070a100035407500102c40d00c41d149185405483c000302e40540c5859140c0502c00340c00144c0d5160010001195501400c400c141510752044039008107000078462307503011f4869110201503012006511100f03140e4080540f521300074007031074021810341d003140b51070784820b469041c0418010072000384024072070304c41c04503c84c0c0c2007001c44d0300384070400361443d0007480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 957918669 1250 957917419 957917437
    0x210b0901060c051c0c020907082428080c0d03120c110303011203020105090c03070e09070e0103110f0d0b07030902120106090203071d060901030b01030b130c11071a 72
    0x1003005080284103c913403018000001500c0e100c4d040074080c81408402c15009007a00e0030050800c0078001010164000e100c00418072000412240e0401c0001413803900d0082002040d912413200c04400071200050030000b01d608100503030303891b5029401407000c4d500381014014000350500510320f003032242c40d600c0385004039000e2800407411119050000c2c0345500c20782169682c0c201e03103001d9008059090007400e40c00b0a40c079024044800849001c00c1d541c0f045401407504007000100062425a800c001c95402072a1a0121031820350356400c104510100c8400c045004d001c9841900046050584c861190304d6400183d24801c0d40d5900c104400828400310101d9018101340451800c02c01f00340107002c00303030500007030042c2e80341003031740019049080030704401031924100d40305540c0980d05c1c1025182d00705001e0030007042c011802d40040b0002e00400389016400b415000034466081d007241d01c05c0d0b0f410030340e81c0c690304104c08040300303101c0d558003482c45182c0c2135050846140818017001c0c0042c00f2840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 957919919 1250 957918669 957918673
    0x2010206062b031808070e0f1e010605090f040504020a0b0f070219080606010c050d03180213050406060f030c0302060903030702280609140d050c10210b0901060c05 72
    0x1400c0390b0588a0200c4540c0c4280c000071000f90307070202c01c810103002d07502c0103016140c010900f0300c1c80c01d1180f00007a1801031400440c2000c2c0c900050341c401c520950b01c404964a0702514035a9a120400540640c01c1980c4803801401001c583e01858101441810f000d02c0c1c0003812030b41407510703220541d440b690003880e00c221030030f0b4140300010050719a001e80400b02d0031001d83c10306401c1d082c0841a407500394020130003810424450b1100001c03803c0842c503280260a00c2c503020903840320f00e034440b244a0b030218100035040401b201a08120707003115030282c1d000e40e00c00c4134103100155641c00084c0034034079540000b40c100c8840050800061804100400b11144050140d9092460503000100ca9800d060340700b54a40c1409007900100c8821801160090040c0b0304162840301e080c01c1205034202c00900c44a40101e644c00901d03020301408224036071b00954020580351080b200f810000f404174246902c055850b00207454070882c2081c283c002d008a0725400b82110000e42c0c030302402142d52a141c02d0003507a082c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 957921169 1250 957919919 957919969
    0x80a09092c03041d0a0f062342041d130206030c07060c020114180f01050a0b12010b03030a08040f0209070c0519020f0114040b030106031e0501030201020606 69
    0x11004904c052420301c80c90021200300c1d13142003040c201c140da40341c214642c00306281c000d0522150826560703585820ba400c40d0381450050b08000400e400341c0b192300203d00c003007449040900313a41c0c680c0c90340992060141843c060213000c003d0143c603110b0140e8040c880124401901c43c030b040620004403198080d41501c1c2c4001144140d4010803800e600c240c0c0c01c00c2c0b00030b0f8002006400e00240d80500b821204c1144001c000070364004c000700144800203005081080e0079400c1840320b031041001854001d803444802080603050490318040106180b141c4036000300d03e0440b01e0b0900035410701c9071042080c0080c2c05580b034118250400c448600c1c009104860325400554110050786030994254800e01c00b9407103000c18068a401c10ba03281203040c200c1a42180c01c92801d08005842d502c0c01c83c44080c000b070820850f5414403039900d4945004075044071078120008400041c0080c0c4c16000100255500d80344481c5201c0300b410a502621000d0002a0160340b01101048003400d0050001c813488a0b018102081c0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 957922419 1250 957921169 957921179
    0x1602010b04020d020a090605070b0406052e0f0815011a160308010e06060705300d091109100b030402041b030f050c04050f04180b04080a09092c0304 65
    0x4980240301400d90383d0ba40032411116450b0401c0208010742224100a82482d800355031302401f00c100104010b03c51503c0b0b102040c00a030035001c15a08040c560001c0c00e408100e190000d441d00e00e080d00c10074500c690fa0100004008401242e64422003200b140c2c914104d0b030134440c1d4a82c0c1c03c051400c207442241c00400c0800031500b0201030341c0810038030a9403250103552420303004114007100170780000d12490b01003180100048000507100b070706482da01c1900c40342d00c0c0c1c000340000e1075008143e0b211030100720001d44248070030301e142e001284051140d1032544840e86940c0611400d10703400c841c040c201c004000c40034000442454003642e4402d10051002c52048100301140d00480c5410406c40d0100b501c6415204e84180203001c0c0d10361000c8000c4139582054a0b207030000704002180300809026030340d13070424030138102075841207940d2182e00201c51000c03600705840c00a071542e00c80048080059004800455896214050701000c40017002400401d900c00741c00301c0300d00049450504880b03110820001032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 957923669 1250 957922419 957922421
    0xc0c0c0603090b1f0e07090f0e0106051207020709180203154305180303090a05091003081c140115120e0609030703030b062d04083c03031602010b04 65
    0x1101d0801c0e07a840c006410301c0e0036032204801c0e023290090403044071a4001031105c2c0b64444103403a90156508540ca160740c0fa0303180c1c141c0c142959500918996410004410110681e942101409508c258200ca144481c159803035104203000f0b40b00c0011b91040894664218848440000c1c40105a0b43c40d540610301c0794031080a0400f0260300c10008100d0206041440030751081c0c00d01d60340b200590145150078100800510003101e07901656214044a1002c580300d064004040d40c061903010b982c0d03a039108900c840201030542c80180701081d141c00c0100850203402c00300e102e241200c2d2030720300305417050101da042a20034507918220a41019074445912005400c01c00ca6035004c0c1c4004070240d0fa4424150800030b0640300e002210b2405468100101d6180700004801481c81800d03c11100406039242000a074a5114550100d4103038441ca07040c6007120884080c01d40d509040c2e40445000503c03003458410a145c90380b5400300c185400c03c1c40000d1b10501d201c20084d228846610000890020401c0064 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 957924919 1250 957923669 957923671
    0xd03050d1418121b070305031b0d1107030f03020309030a0b013204051e0901020333011202070b2706090d030c0c02040c0c0c0603090b1f0e 61
    0x12900c0962a014815101c04415031901800c00700000340810350540c020700b0400b131140e22500c0240311a440c0b610001c000050003644041c41c2d11070280c1e039484891510109484001d100d800003075000d0590b0001d0244c1c000c0b01104540401c80001c0d01540e407454445104880c61020182d081d808104000ba139199010702c010385445104d4032804c110b6504240c0e21041d02c10f056040b02c400703400d0b030590710004001c6280e100c1e9038012040398013140c260b4440d02c218080c0b2000b481d41c00c0340c0381c0941003800000c04040d00610311480c0303504014aa806201c0d607080d440c403580184403044100c80403082861651080c0100e0703000c1e00644d40058a4941c00c0c2d0b03100501d41604803410342904510381c545046600740040700c02d1080c2ca046006051500300b04049a45074103040d104403090590b9400035040c440d018210360210700741c0003030007000502d401410251900302c40f540c084854006a0001203800b6000c0d204001c0d456401c079401d444503070341d0004100341d0628a0580a819401013545c005030b0302c03000c0c0b0962 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 957926169 1250 957924919 957924941
    0x3031b020a0302180a052809030c0506090601050102011118100509130f0c0e150a0c14010516020f0307060b040e07150801060c0206091e1e03060c030103110d03050d 72
    0x13181503032400c00d185100301c51000e081ca044d4000000342d9080c007030002d141480b0080c850584005225001c42c03a01b078940c1d41d030020b0010154094881081800040404e00038100c80c400c4e0020701600d10070807075070551481441032402404069a12817181410a0b842c1c0c40a090181d0520914080e072510000d052560003101880f101070b222209500c2c0c90040303024495003105107040c003020f1240c0000c00070b644481d80b44624644140040f80d034414a510455501c2e00c00758000d17501e400900c1c8040c1c640381c0a400c0480e800140d0296800200c0700c0c0c0351000501581111a6001841c145811951900040e1581c1403945500a031110482c082051051024500900c5074142c40b03100e1034941c1102500004050780303c1c00034800c80c8200400580c5482c03003280c0110304205c9003045030032904030707042801c603c3c1c0740c900903005602480b00c10b00b900044400801141000c504940540c1d0b580240c01700b003440309010051158415000422039407e2401c81c0120f114400c0c1003aa080c000704408200441c0c01d03c4030a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 957927419 1250 957926169 957926209
    0xc011412060406081006050f04050105101b0609061b0f0207060c0609020901060302130b030c091c05250f050a0611031603080a0b040b030a080901030e03070c150903031b020a0302 78
    0x4100012301d0050b0200260b05000c0d00c080c840c540c509000624584d0340b00418030b00740710b0303691550a0500d0100012481c01603008404001c00000740c240340008180d0041c030000000500b08842c0d199500400d101c41c0c200c00c20754020300b49642026022900c0c441036403003c41d0300589540500c00182d03954030324140688120390300141c807200340212610042c4100e90000e20b040360100140081c41410200720f60010300151011040c00001c010a4000c0c1d842c1c181018101d0300415141552859001100038402c12030441c1c40b084081d05c40403210202c0c03000f0f00c1100d03441250b11030704201070b9020b502e4107051800b040065034208020702d01d060301c0301c05514030300300d000407070344800c00c140c51840f03208100080e18180da0070407841248030040b955a40d402c42024150300f8000c69594901d82c8a030b0046c00c1521101016640c85603902d00d84400d04101e01e01a10200b01c181160002c0c0f95481000a0340441e80c05540d010416140750302c1540480481640c2a40c001d40c40710004000760b05c038ad103003e554413003d07c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 957928669 1250 957927419 957927431
    0x60e10030e03040b031e060a060801050409080d1e0b0f011e0203070c06091a0c0a06090203210d050f0f0a09060216030507020a0504060f0e060303040e0f090c0114120604060810 77
    0x31003010b0f4000800f01f504c105100b220a0040b5a4002c0210781515030030b407000a040151420300000e03902400a4510343c41c1d060400c0003220b0502401f220b822640d0b02c11083c00071408801c108891031890f0f48a45001541d1123124a000c513501c0c1a0500d402184c900681c2d1400841d500e801032214940d0b0081c0010600301c00c1d04001000f00000c180100307940150701d0318100030003240c640344c0355541e00c0700262500d42c842d000340d41595001d00407000060a105051203048210000b01100e03900310b2140811414a03240015648620740b684051080750f159041400ca1356900c1c400600614504030f003038401c0c0d9400e000c900100111100d05c889024001d44902d40c4031181881000000440ba0700321600403420100c007005101d40b90b00f00803041c0e0340d0088000601d07580b40c0000c20f1460141d94084600184010705121681e110089454025114141580c41c0c54900b04019104220070844660301c170700c400c204000b6901035442000b500114020303c0402c815035a0040c0c10700e4080c03183c1da8904480d035626 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 957929919 1250 957928669 957928711
    0x70b160c0b090303161a34050301060f020c0306160e060702090402010c110312121f0b0c0c09040c1a0406080c0c0a0507090f060e040c0302010305041b030f0c060e10030e03040b03 78
    0x11580c47d000361010741080c3c0d000700403900003411400188501d200741b1001903103540c1010300911014640403005401c8403146e20b0b00180b2079401d044400c2003000881c55003404c4001070308005c03048841849d0058500d80301501e4503401141c42500c1e1a10642e1031702001c42098100343e40c184008840300110401007615110301d200070b061510f4014043d040385012005a102420301c0700340b20351040740e14003003455488180d2140340e5030504200c000e085a00c0080103080100700903400c001e0106035802c00180c016081c148102034a16849030780141404202024000344000001600400d20026058140d0b0000349441ea106840c0500c40d4000c1c45546849415046444840d8480c071001444602c1070904035042030703210b01c00c0854607400082c0c10036855500260a01000c000704c40a40614a1411103241c1d949040844000c03594400031600321f003010200080103031040c24140304c0a903000b0f0143e60559540b01c4164004d10504560341c0704c50009120000b25401014040c0d4420039284200b00703142040f00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 957931169 1250 957929919 957929971
    0x50109050103030e0111070b090406030503040b1e0a0905190320091521161e060302030c180f0d060f060e040c0611070b160c0b090303161a 61
    0xf11384490401c545032000009200000505000f01c403000060a13580340d10800c04140a0161500050030a210000e400580303080e40500030081e041d100d44030718507002000c0d5094117142c481c190540340000d5203150207002c00d14100707003103044c46580a100e030118581c2d00e948400c402d15001d00968071950000c0c28414250400c0c92800758041c1d070107002c800d1040002d4000580110f40c950301401401500401202d84210400c51079004501d18050303074860503070f02c0c983c01c1c0d81c08038103003102107003101c01d601e002801078000d000341da0242d013415000c14201b504100f41d103400d0140e980714007503210f800e000c44e104880d00c410065681c9640208004111380341200d885c001030b107030207502001c00c40800001308000705084800d0320b0140e4000d841d1810780c4240b403007001840e00760035400908005d400096100100540c41e444000c02910035031404034407681d40c0320480000c2c06240b50190301604100020324941e21044400c070101d074411240c804880c2c4418a00e1a482c200441d84140100140c120310b1982800c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 957932419 1250 957931169 957931187
    0x3090b070507020a080c030706050f040806010e01060201060b0405090a0f1b0509040e06131202011e060303110f120708041701063002091e0f061011070302190905010905010303 77
    0x41710006140b1301445501203076803001c00d403044604001c0041401444000d401044a0090403c0401c5500b603513150340d41040c5e0f011080c4504000b661801000054492400041c0c500b1500003e024903c50b40c0c03100a00b01c081c2200c074801101d260b540d4451901012041c9070301d041d4481c0c4a9481c1e507111040d19081c4070403541c1510345c0f00082d5004004101c1032829640201600e103902c000403030702c403101c000c0d0140c2c090100300c0300f084e4100d002d1500043c40e00a0a0344040c04481c042e42e10100d00310296001c140d1502c51b80e0b124140c03d5000003200c00c000c0060741000b0499144100035561030716031345141c0c00d18001145989200540d45801040000e1030f24a500307810310584440f841114025000e1040243d059595002805407034103500045600300c20350000c0c040b18446500c55402481c10303d10544000340c0844a440c032604014000076143d52081840303d0001045e40c00804005056808000c0641070001c400caa000541d0040494071400c0d901a0500030301c1c9251010840f94114036010b0103000c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 957933669 1250 957932419 957932429
    0x705030a0503070f0f0602070f1a150103021c020316030b0612061003020d14061e06071b05060c0a05060c031e090102090604080a150c0909050703090b070507020a 71
    0xc403200040011800100c200c4482561000048044c51084d01c4c040005c1c400c001000740050344085105030a000203072003900045032040c81e00504c01803501d0441d0f08030030002d45d00b02c5c084d842e00d044198550350185c1d00401c600300344c5541140c02060855005400d03a0300840d000148509001911503030a0f030940605c000c6024100d80450074868800b00402c019000240103c1c031540a0444a41c4098081da040382e815031031020090101400d0058600c80f610025a041e80c0286400307420f81c80442180c20045000304e4009107030a10700211342d140c07440d40030107001420b00b0601038448005402d9840000901e0803007800c1014010301189418181e051080c0245100d08000c0700300b0130001c401000a500c10180c2d5800726104409807a0b41c820742d80207015600b040d580241c1c00190110342c01c00c1c001003040b0094425114039101800343c81c0e406d000d1380c82c0341c0181c40101d0040c42d414031445045030007a5074070940c00d00d000110041c094859000c526816115000800ea00059200550130b000c9941d40c00b0300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 957934919 1250 957933669 957933673
    0x6092a130b0405060304081e0d05060901150e0402070212030c0a060b0103150b0703030f0e100513020a030b04110a0303030f0507230906070b0702010222290d11090102070503 76
    0x2070f00d01404112a44001080109100c0c40040c2c4094584880800d012182c400885181d840741c1c1d54484400081c41d082d03880a1080060078000034121055036101d28000b03107960360300c084003100c030300c1804044d410080c0700300d03448000f245146100c104204081c2640303992044c018048803109091050441e8000881d11b4101410100089503d00300426014121610189003907030362081d6003412001009010806000e460030591915000315000880100200004000300882d86801940c6140500080d500a4110b81000001c1003c54254080c442c1d0107400b0301407000803044100002142d034003254108030b010981e07603184a401407185200b1107070302c51007a0400c0100440070009850302188203404206080f0300002e040300d01616080d042c2d0f110250b204885031200e00b031400c40070b13000c3c1d089150084c03410800003a620198104100a05080b07403400d9041d550034500c0c036140400102c10444404410716010410300142101c00c0c401c03600c2a00d554140242c1b100007110009040603071561105103c0d0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 957936169 1250 957934919 957934927
    0x130b07031116080d110405011b0f0b040c0e041217100b030606090409080409050f041101051b0a200307030305090907020717061e070806092a130b 64
    0x42511004403804200340384040000d800c09403034811210310800c01c20758091030401c214031742c815620a001d0300589800362900e030494810300076503055034581c4a1025001410092140300400c034590501a08a401008552482e6444502c603002c0050180d5040311014450040c100c00d180d8001c00442e01c2205118803441c40d81040c1c5500403940500e03010f03480c14010000041026940c41400721480d00030041c02c00e004903229814100030640107485000b064505140c0040c904009903800c007845241d100440b139201d80000b8004440540001d28480716031881d21030b07400c001980c00c0201a003100c0c41596482082c4006440308458201740702602030080c0c1c003030041400083c1c0c010f0700b070b10740007182075501070303450f43c0c48039400c0707161000c6684801c101c0141c031405020002c401049241c40b410303481064100401c004d5a2560680004031034800010340c59401043c1e29282c0b0010b007d400078080c1440030300f41048207402c1050800a0348411100c0007000841d90604100b0542580042c030702155441c0c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 957937419 1250 957936169 957936191
    0x151203350f1812070c06050705031b0a02040608010b040c0302031504090f0b0c0309120412111f090801051e071202122d0106051c14130b0703 62
    0x380340c00240611040e511001c0c00690080c200c20026207003029840115160356041c420942480d40c8001d000780c4403030300042c601090041c00303041203640b11603114000350716180561468100081610002601c2030217001125409692036000f0080504490000061181c1c0242c0c204401c0f02c51881120301454014002c100302d048030a541c4070643c04003039a011030030b02c0e00c914002c0140d8800300d03c005d1000080c6c10600c2030300c214031360203544a0b8803103400321030000c80c80d18114034442c021803203058440e405880d00680098948442040300540250010024400343c1070218041e128603040310000483c1c9000402c40c00109005894000c10580415101c003110702000070842c5c0b00080600c0d01b1300543c000c54450a81c410f50440d0500808210000d0081c00c0c180d064845042c0b808601010702e900b004070f0004801c0d00200518101c444a40f1020302d40300b40b44e80940c413000d0880380c4c45001c099692451000c403c1d03d200b40740748124500d5094034900d80551428220141000e00388504061034100e100300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 957938669 1250 957937419 957937517
    0xf100209130b01081315020f1b0309061e0d09240b0a150c0507090b0f0103020309103911060907031539020f060109151203 54
    0x82c00c000790101e01040e0722400d043c103241701e0701501151b04c3c1e21840003800c00e4405078003002504100400200700d001c2c00c2180ca86540e40c0340a448140c0e54482003c00041a0852003d00f140c842a560303404420300300700704030034040c0c00c842d607445041e600000d0b40b121068244882c48410a6070703042007081000165420400f00d4207020f5140603001050001010790306000b8000c000310140c2c40d520030100c9801c0b07130315211410058040352107404d00031400007800400f00d40c080d0003035a04c903110110044c01c51150400c0454060403214000b860014110b140ca030303202d2086c10603010140d040500c04400000c0300c40d80d005192a843c004e4140311a00100d041c410003a0001c50a0303021070717400120004d210003201000c940182a82c2189101d03045540d00b003500780e07650000307980d0200c6101b00380100b48800000e0080c1d0315420700c1140200306420400c01807201d400142d2084074403105420001710f003241c9400c03292403000c04150301036000c11040c0762814007058460a012801074000c0c9a80c0201c1002809491 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 957939919 1250 957938669 957938671
    0x2072d050f011e020a050f07050706021005090a020906060409090305090a090b030d030b0414072721230313120c0909050a120309110406080706050c0f100209130b0108 73
    0x380ca03ca40000d0028490341c401c07420b0b0b0710002415010603948403035600c5c00303e0769401113100755005406605a455100c0703001d84a4203101e10060b40c003a041852080e4204540c8540041c800e540c801c806203c0440c80540d02c3c800c0030200392103500c0d2656100140010004002e202d54004480f41e41854055005520040f6000301285d0080c14085407004007900002c015040400503801040c02c0003003085003072a0f010708910000d4480b40300400d42001041101481c0700301701d0040b0f050b80424418000e00840042c083d2a2080303024080b01002040000c007201c07900544419110100d600c0810100040800e13200c0c000018461407200300d03450440f0380e40c4c40d00d500300c4a01c610725490b55988006001c2c44000d2050400a40d131080c01c040040c0d4200300c0180040c0a1144140c400f80d446050306600c1c0e00b880c1c80740700305403043c0c0401454000d01d00442101d0b254000380c010200740c040c90240c0c8003d24801c2000d114445111003016071101030072814045a001040445268a820041c844407a640c000c242c0d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 957941169 1250 957939919 957939971
    0xe012f040b0d0605040f02311a391f0b040236060c061b0705073c18141503070e150402072d050f01 44
    0x41602d444990340440700a1105900054000e41003c88802548685500030011340c1d01d800009070300c45440c00324245c482c5039104a000c00550700304606108100d1401c0d510700c07400f465041708034508441d0510b6110b0740045404040c6a5030036004c45d007440401d00c1c207401c1c510600642c1c001c141203026502d00d8030032507194020300b03d421542c0340d41120054481ea0111606802000800000c0400e07107148035003400198603044181400b0b8021a520601d491401c0300c0408000d100104110703203540040140000180e041c041c410341e81048090001007042c00460001d214000440131010a0b00346e01c000480340c4d54080c4031000e41007942c0703a01003000d400540400c0d07903002444044030300d03104c4900e10002e003c0a15a010141c00b079804100b50040510a092100e04040d400c0e035460a80d2031010707407220fa0050310308066100d244103400c1e4080c102940540142805140d43c502d69a411714101c1c48840c0003900f0307007980407031944501403e10404000700f00000401c3d4000300039811401c1741c6038202030b102e1186 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 957942419 1250 957941169 957941189
    0x3040e070908010e07090506010f081b04052106060a060c50060610030b040b0d0b04060614010c08180301060f18020702010504050d060f0e012f04 64
    0x300c0d20691103110450090281c14000300a81440000d82503a0b49085104030842541800300042c0030354400c10789000180b000b52070350182c2c0d840c1c6801002829550320307512b00300c1c02d009100009040da00c003c1c650081c01e007501410140c0f0381000b0511403e101d802003007140a400b00718820003900d6445600c4640c00f0340c202255005c4001c40f031041c01c80340508443d20081c0391400c145800c0c08940180070606200c101c15141c60203559416107640c1c2c8603031040361403940c40001c241d003440520b402a017000d100003900800004084241000148005070403280c10707510314020508120400030248940006000b2107921800c1801805000800081c5070b440300821150011420a25480501c103041e030990320020000d10982d61a004000e1440d80c0c07074030a01c00445615084c114012016100300c070441c98043e034526250504001c00d12400400012007114065590718904103240c650784100c0d04009801000803800300c4c8900038590740b00740c0d160390300029414003007140100002c240b4202c1b0102c6901c424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 957943669 1250 957942419 957942421
    0xa08060103110406090e01080d0f050f0f07060f050912090609010e0a0e1605030601050a1d030105010603020301090606050405130e0f0604051f0b010c02060306030106031a040309050303030903040e 86
    0x40340984520401d5002d4100d0215000c10400e40000001054410365140c00021b40ea0f9144082c1e616001c403088100443c40710b1006600851181c402041c880752590b1019103800802c500d40f082c9503201b0442030f5101b540da4042440a89203030b02841d9084030b4004003d040010078050303a40748074454204590300c240d100007000311142e401055100502d80c0300522400c0d0451f503460600c4010a0b0849203800c0a41c5144030503000c80d4054400e4034082c0c5010385d540d6040211854056030034650f103c001c008070380c0505035084030b16502401841c0c0a0100c41c0d4000d610b035490040d10030160f1388650445014401c040c0030500c1551142c0500c0360807180081000b04010b540059064200a00c40107203a801d80501e5080005025000900f21545407151700a40c620b05070f01d00a0100705c070082800540001d8240741890094a000009180c20400003000011a00da50b40e0b0344660300300180400c103a480c1044c03401c1000380f40e008030001c80209400d4010350301c1d40c83d080707030810344070310440c0205550305c0b582d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 957944919 1250 957943669 957943681
    0x5060f0f160e061e040311030609161404020705010c031b020705060d09380105041109040e0f0703050c12120f0a0c0803070c111c060506030a061112011a0a08 69
    0x404c1c6a00c80502801382d650340e02c0e2642824440380101900c03660080c840c90b40440d80c400800a9400f1075120406080b02c80c0ca03080034030402e205844c0c1c03241d02c1d60094080c441040803500030312410f4234516003030318002031031083c00f02243c0b1181c044000440079034020010030050b64542d4030031107591250404c00042e5142107442c00f540c1844000d0400c16440c9401c00e00c031074115914043c03d42c0b85022600110000380c0c0d0700d104000c04d98140020380c281d060fa00384940b141c1d50030541c01c420101074100c820785070f003040032018482c40c02100d6402580d0b142d00101d02e055080c246101c80711140006000541b03009100d0300b07030502c40c2d0302c26109039901c01e0b100019040c06180c82000c0054007103500040e0a6030300e09040c10020f0070300b0b01904060b10504d04002c02203086260166840d404000e01d4421810340b500326480b544020500105902c0c2c2601440c03603010001009445100700608201a80d591140a4035030070107d605016004001c44034100803001e01c41d00010303015100030301c00314035045419a07100c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 957946169 1250 957944919 957944947
    0x3220f0c0e010f08010507050f1602040c092402030403150209061c0b030a031218050d0f020f0607050f0c0a06090c0510181203050705060f0f160e06 65
    0x10000380c598806144041541c00300c2990a0303040b0340d0000d02c00001d4075100c5468508a5a0644500c00421800c00456401da01c0410107000c2618041200009444440d00400c0548000f10496030002c0c0da031a1007031201070303884280d1110100c801d072501003d010503480080d540748101e00001c5c10f0303e011522405c0480040d50102e807150f11016003160346408116060080e280c901e011103040036800c0030f400e01418140007440c411303580d405035503410300d80c455000384030300511000010500010b1070000d1100400c50822512142908564814001c200781a400900301012990300090740d40000040c84009540b06083d50101d800102c01e02c5c0d80ca88443d480c0030b1410b030388000c004080304e0074500d0304001d22011031048412180107481c401800e2407151821640110081088000d40403104401c3c03004102020a10401c40c0c441d0801900e860300c0d5071101d51030204102c0310741c0c54980010040000000e005c40049400010398120a1088140c050014041981480c00c0c03501511010581000341e00c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 957947419 1250 957946169 957946193
    0x50103020a14220507110604021003020d0608120703030b101202030a020405030a0309080111252a060207153903020a1a06090c03041b1508010b0322 65
    0x8400704800f01d02101c41020b001078002107030840080b0310400d02d450501000401c58522a66000741002d158020100c815002500107503100210103039a81008502c4580030080e502c000121200a242c41b800140b9004095926025845005901e07504080300c0302608aa05030b00c0303180c10030501507140c1c2c1d60201d0000090040d07a02095251152440c01030030f168104034a00306a0320717011b0092120401c8080c2e43c010034400e0300500341c054201c501000d15841d071b40700903044400e4402e130001098603204100c48041c04503100144074411000700ba08018550301041940000d00300c11192100340ca44035440a0702c1104075494401201c0c100001c1c011000d49495000d80c424007484420b50069886418020350795845040700b22010043c0388003d074030b00303214812100c5c4104e1000b84000c016030390f050f810440e01d8002800489500c040b5008040c000040c01da00707040545040c0050200c003c000400042003514180d100000f60304040090040380340300e41014004008205407442e0304080d8600d401228481c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 957948669 1250 957947419 957947449
    0x30c030c020f2107091803210c081608061309030c080c010f0605040510120606030218060f04050f070e0112230a0e03070f060b180910050103020a14 65
    0x203030183c1240100034202002940841d4007000b2514001d4440114404542c407503000082d550303041e1004040003a10440301c1407251004000001d1158100300400300c2941d030074010510103c0c0003070301001101400760b00b80400a80c06807a1082540c00c11002240c1162035009030301d00001d4613207080c501414002c003002020b142e8842c402d56a104041071449000f41110300d140e40101d0308050300094603181602944c0d000b090b803920a911114a132641c0c1e120f220049040c200c513075a413500000070140e0342d00c00100f43c0340c0704000303a00c030a00e1408600704418a004a000e01c2e11440c0790030144440001c201c009194081c010b4141042c0012182c0d00503141138201c0c0c4a05440e00e414080308442400301c2c40d004803151120361503800c0c1030740c540c141c03000140c680010503603903035034414480400071480d40bc2a40d00e400780079800c002034000300f10307010982d4082c0700c40640807505908824054100402c0066070381000d00700004000b50b505590000341c4480e91885030310910640c43e18104096610141c070f44806034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 957949919 1250 957948669 957948679
    0x1c020a230d03050a12050f01090905070b040902090109081605091018060611062a1b06060123030a110c0d030b0108010e010e13031e08100909030c030c020f 68
    0x140500e070050a55101c1d4074940700080b170802d400c4402c5030481c0582805400400395100241c0e085c01a104000c0180900640b1580301340040000c00b02680320040c00070b89040c0c0000b5954102c0040050312041c01d0307900c1030002c0e82c01942100141d0340035803030140658004681000f0140c940c8240726105c281c46400c401102c0f00c60030380112074081c1d198016022500e0907116100e104420b05000c5895401c12180316420008100c1c04481c0010707000c2c4141c0000140700f4110341081c0c901280b041d144d200d5030b0500303d900d03032012050111030743c0c110088100c14134010410781d03440c02042d001101107000150494690940703440304003450b980d20406407882250030108507044410024401005441c8c4440c4181c04070301e0010000c0780e504680840352b8165030040d6034046c40b0340c030340c0800003000a400e54025401c00514100024200d03c03110074104541c0059541d0700c1081c1002718076800319480c0340e07001000840c035010b08100001d40100091420035014240010407900500109444080e800761040c1e04c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 957951169 1250 957949919 957949939
    0x50f010e1b041a18090402030d1107170607031a0303070b040501061205100f020f04030b060315010f05120d090302091909030906030c020d14090a0e0c07021c020a23 72
    0x2203e200300500b400c4003d14001c0c2c1c204206103418840c14050a940180d0981c1200303030001030450186201a040701c110f2011039032120b81c1c805401080408800b000c0e00c003500075005000100341c2c940611014642c0d020750696035158601d00282d035910800070300a03d4103e03000c0005e0f051120079031041c0018407d003a510301d0001220b18140e07844245031580140d000f803910192003d4440c261007030310300c84446840c00520301801c51719004030f40d01d8001d06044e03051040d044050117149180c01064020a00b440e0f40000540c1014208054400c50074a003032000e501c4071303069010b41540300950008580d01901c0030415034640c030402a5005450701440e185003410200307004101a441f0646004940d513540d42081110b070800001c903110221103101800052070000d1903105103a07400010042c044000b440300210171340c2e80c2c2c01000c00c0c40d0201c5440301582c0d40410705406600f094101d204000020000c00034180c8010360004140002c113009402211440075558400d090401c003158034041d200500032548 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 957952419 1250 957951169 957951209
    0x418020d09050a120c08030f040f050f03030a060816030b0601111c08060f09150f04050414071d0f0a020405030303090a020f1c11270a050f010e1b04 65
    0xb40701e43c000422036a8104165001840520444102220301e6002401505e56103401c00584502d41c400760061b16070015044051000460030001016981c41c0300000d19120318184c00030b00112059580714440325001954100711600c031070352140d401c0d00d9100c000c1703242c03035100d0000403601c81d10740280c0315401d0f01c40c41460801444010340781d12245003066031090090380d00c4009101151540c86101504a101d08000c130710700030205a400c05e00284007420001558614a00040c140d175000d4605607500c011404141210b2001400940d010740901506181902000f004909400310000d040600c4209640d010404802c030940461340105001070403a81c0740c3c00c1018041e511354400d044120312640406020003c0ca05201041d007203011508116422614029118016406c9482101a501c0782c002420120070422900c0c101e441c0c0072031001c00ca11507203032141a00b42124009040c60b24419055001000201804240c42d5030140014610b0503404120128051607030059820041c59040740e0700c1a401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 957953669 1250 957952419 957952423
    0x80d1803021c0c03020a0f020f060f03010503060a051e13060e0d0810061227050a05010e060f04151401090b0307050d03090e091603060209090f0c0418020d0905 70
    0x103041c180c203107200da4042c9084095408a60200000300944c10510b455030114441c2e007078400f00640040c010384070585d550400100c155104214003c4185030101c014003280c1820020039900201c0039004000506201784994640552441584c00d440320080014541844056803c00e1030b59203e10140103201590003520345402055000c8800103ca03140044c8511842150840450740c2c6610f6840000802034002005403807030b21048860701c8140c030038058000306680410701c482c1d80104003510f01c0c100d1500d010b50956456546120b0f081d44101c003881040c801f42401300360041d41c002121002820700c02c0c1720601510500420080300c11040000240e2007a040d0000800c441c0300f241035503000ba440301c08001710002403003000740028021a03001e006d543c04200502c0c1c0c20a04950446e9188802c00c460f0240070f0708603030411940140c0100d040300d8a4141030380c919800c191010301c82c4024bc43c0101c42ca00d01800b8a209041800c00d034100400d403641c0380e5504540c606900d2440c24407030b0702002c1c1443d136 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 957954919 1250 957953669 957953683
    0x4060e0a0b011401142a0d02030406090b041d060102010f0507090524030f0c0f0a02030915160b151801030308010b0a0801092d0509120412080d180302 66
    0x90451145001e03903110303203905100200c0301580281004800e41c2d0598013403286c0840d0404041ca01002c224071101c1c10003428600000036402150b0312424408002d10061050740300c001451001c1c80140000708149105c60300585103035402e08115500c2e500100d024100c98848444800d10308014882100c1e40860b418082e1502035584440b103565940c02503c4551030102c00d1549220b00784082a00303041c4460409820101201d038880c1054001c200000791030748219000e2016a000081100c11030902840c903580902500800504011070b8215040040602c140000c1c801900c0700000b480300d01d50040c450388135040240400e400440521040700b4111400e020a5022502d2200000344500c0220b04071340c1003000300d0340c0c0c84030182d01e48580a40507200c6001424802c0c80d5441040c42c284804100f650b04000d076008011619090018046003009107150000403181c60801c4103024600308841c000304d5455100115542d070b901840400030082c010026040d02c0c5815046100080c10390010b050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 957956169 1250 957954919 957954929
    0xa02210a1403031542120f07020a0c0e070c02130204051e0102030a1817010b090a0504030f05091f08150a0815190606121a011b140102132c0f04060e0a0b01 68
    0x7c4d20705521a0702c0c0c140d94230324002e8001007003005100000c0c80b0f1510390301c1c03203190048868100483c110110354001441606404840e081003030f404901001189482050380703e04260741003401b100c0302a1040000d46a104014101040c016403841c3e10b050b040c03140200c080100029650252412511041680070700150080c0d1446400e5001c0881c000c0f08030342c400c00c3d0003142c2c5034441c4010203400040c2540c1c0c035000805074a0b44002c0310000d403400629100b161928080d4640c0c1c4092035890701c0c0c40c42c601020404490140106e01841003400029000a8082101000d000482ca1940d9461031500b80d44d19002904185160500c00d002428682181803486a003a8481040c0f29042c0b0340e806400c14012180180d80c0061581c44108200407800c0824028150040c22604800042c01c903450f1b00b0390307002e494071aa51401c00301c001c0080c00c0c07152251480c0d80f02680b4602104072640112031011060142248409170a408041420401c1075480700160040120555100060340e08100c44044801d2240c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 957957419 1250 957956169 957956191
    0xc1a13080d0e070e0114090c09031c20100902030c12010c1e08010b03070203070204060303050a02070617010b090d0b01090b040507020a02210a140303154212 69
    0x800315680c2840074409050300c4044064000140480b4200041c041f4043c2c00301041e614100000912914240206044002d00c0c2980314480d140300320300184103041d042d5015100400703001c0c003800401408a21f8044005182c1c002140740e40d15400000c2c100b415a142e42070b070100203c243c0d8040001c1c10340004880585648034250701c3c00704907402c0265140800c20310b0000640c4400103200301c4c82c049015640040507031045900380f40b084e0f408107046500c40e4200b03402041c0007040901e64645d04102080113411180b4000803101c404100c009a1100180124900c6440200c0d1090b00b03503c1d04003602c090260003038483c420030350303503171891000500c1488920360146080c000040c28540c00000d001959503406010b4031490310791980410100c1c6114504044a401904800e4002c5040b060b2101120b055282c0591f50f00d08040300e9002c81c55199204036400380c1c8094805905900446030b40c0705029500358044207080340448082211036140080241d0364200200b112008010301a081921440364091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 957958669 1250 957957419 957957433
    0x110405060a030f080a03020c0f0c091006020a121806111603030c170f071a060a0810050705040510020f0f010501051e0a05030f0a030f0c1a13080d0e 65
    0x300340300c600855404040c044820b48050140002c1c0c4100c01454181250b01d401800c2500c2107008600b8540c12802070441548021010310440c6446d140303040d005207140e03e100840178078004019465007004040680075506204400c0e400502900b07101200c3c0244001c040b00c0380761280c3e405054058680440002441007030f1b54402c240e12240e008006803901502c56080c210340c260b44000b13041e084824544290442806000c2c4600e17a905c1c0a044903500c603024480042030804588002c01500418182c03050f04044404c010704a03010441e000786410b9400c0c040789a503903070b5009980c180b0580d408103400c00e4407000e52025441c3d012030341c1c1d4011005c46050310301c1c002c0856446403d880003030041d46d0344285911046a0010f803001c0c84646811406413108550b10343e2000041d052100942c0200800d4008944290030107500095070318010302141000300340c1a840e41c07114a440b0070345a208a525500001c003250050040d1501084010b52081d00503544131100d0f12002d003d00080d2aa80d1000e1203100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 957959919 1250 957958669 957958681
    0x61b06060e091c1d01021e1509070f0302011416081911030f09010201090605010906080d0903081204020d0b0108010f27080702150309060106090e0618071b110405 71
    0x7040792100c0d204aa1340c51807031900d8003106035010358481188505510500c00e1084013594101006101c180c5510054280940c811306070f003a80103801002d08070660001102804041c80700307198002900d0302849c08079001c5c0444940c0d03d02d54810a0410b00c00e10f41051064020001d42c000244013921402131043e0744482064030503a1445030029a40c5000d41050204081505009000c2c1000301c0051001044e1480f068941c0c504581007a00402c4a6030340b109418032070084104981d1207070070064500754031a546140c035040c41c02d008000401e1421210040450290b58840700040c1c805908650140f0b0a965a84201e50091910317010250708182025162290a0301c801c20200e11600003a0040c0880b50203546e074510507512000e0120391208540c40c01c4d010901c0e00c040a1481400307410010811541801000b802000303041d80404100e0041c4020050030783c03503c28103080e055411030150700068490180179106040000c1c404000b07040000004414011003da0051001c01d0564041003230303444403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 957961169 1250 957959919 957959953
    0x30c02010c1e03140a232104060b060301030c090203100b121510020705062101030609030e060313061e090b1b0313140319080628061b06060e09 63
    0x122517940046814403d94001c1040c00d5040500000b00b909241c40c5080744800f2444d44c0d002907146140c2d0b03001c204c82c0802c801c01c00b8510800702d00c402c040329024110344c9159914031030f0702c0d0a07000e801d101d1038020001c1101440c8802c000320181c142003403c1782e01c558103212030001e03000c401c59026040100c03028a6009500740380c6440c001150311603003c0c091083c2000280400c80e071146050891040c1c01400010395000c82d210403034080d500c00c1102080024580c00c0041a0300002c0321154443e42d42002402405054101d014031581c2c0c1c0100c0c0404c40890341c895054010365003403d1209900d007003a95240030800da041580344a8420803258010a000f2512070003018042101e02720145801c610703851010496a8104251000d03071181140d2405042851302c04c0310700c070541d02c49000b054821081c420750307140119090b504005024011151031002c4542103400608500c00c1009004400c00b030009030600c08150b20354010741022050004039507070040e00701c144074111001e0400313024101d42c800b440918 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 957962419 1250 957961169 957961177
    0x81c02090604051e03070602030c0f0d0c1b03060f09061802060a051e12190b06340c03050f010b0f0405060f04051504060b090d030c02010c1e0314 64
    0x58005400c2ca41010180450030114a103000780464240400c01004d5504000000c0030b0001c039800f03181c42d10507000400f89000e500c1803800d0506c0e045005003071911940700720000110b40c0c0121000702000c41e280180b0455560680001d01680d0030700b5000d5010401c15042802c1c15846400b0801030055513401002c800710120074000c0d40040b0412004203607511600140042070046032508201c84802e403010003d0b07a01150000301440e80b80310403c0f50040c01080d07100110100d401c4140210071a01e000111780d4132800c44082c0712004014091058207140d1201c13030014824902c811034140b801400c00c907180e801c0074031045a040c031940b403503442500e4060042ca031303240102400031161800c40303504220107840002c02c240d412022401807840305903070318000c040c064158001085503182d18102800140d90b0a90441000f01c0e000b0040410b00351030b0803583c0d03001c0c1501450814088081c500c01201d01c0184104007a001b0040c0000144044100f0030322003a90780c3c480d131500d091104d5444045222806 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 957963669 1250 957962419 957962437
    0x1514060f0d1106091f020a020901080f0705061308010501080f0f0d080c03180102070b04050106061107090b0d0c08010510140907081506070b090c0a1a09040612081c02 73
    0x404940d11010904000b000f4165002004000a01c058030328009485030300490015180141c2c0311240c0e0700c055040813102540074040600142100330039146415540301850310880780034210010f14014400e4078900d00c9005864840024012541c0d5401304550356a6085040100f42c0a8481c0740d0002070400200c52000b00f203591119019541ca03c100d50406d904020805010061100d42c0c0b100c1e014400c3c03008000e424071903003420b2000d08050400500312115500400148051169018102c260019008044074030b1000049103212413080420100f00f0b85100050440b4480039002c100c03440b0640290384a00d8406901801241d40c0e072014424100d40402c100341c03c005e0f0340300482c42d0325216505140e4840100d1101e61007041002d0042446a4000c820640b28060080c091010140f801d00166100e00800ca481880f41d80c10540c0c000c1480d80f002c10a842913840012f01e80c5a0340d01c41d45c03c09001028100200341c171000983c00c2c4400507520541d94000c82141090482108240c03131b03c00e80f06014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 957964919 1250 957963669 957963683
    0x90c1205192105071419080f070b01240201020306061c061a12090307020f010c03170a0f05090d1e020a02100f0206090114070c03030902060d022107020c09041514060f0d 74
    0x60a87e1682c0b00c4c07503030090103000048041000680d011401c00c20300c01c1c1c02010342c080180920380100d0f07a45501896420503500c2164010030070710034503580318019a21410714015000c0800c880c00a40d803070007410316621104001c02412248401d41ca001e00c090008078203104410368903a1f484031052500c900c00c42c50003d602010821201c005541300b03159002000b84a800d1910304c2d2160010360400007070003120fa81200c80c2d2110540720b04000c440c050070f83c00c440450018600c08645180150085001d80d40c541a50702d0440900c00241e41308110340d208907500030303010710100985103c000b02211031603c0d00c41c02620800e0b0115114120510503640d84c07076030503040d900380d6481e045802c90705514000401e4007055250350201c0c0150399828028140a190f031200140c0d90140388200080d0b2414081003202c0d07502d1800d08000341150041402c501520045501800d141d41c0c41c44c00303c44d06181200780c00d11881c03400b0321854501c402201e0846c000c1d03404561541c070490078001040801d00d1a148001c040b8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 957966169 1250 957964919 957964963
    0x2030f0c27010b0d020903060a0b010f020c0a0b130e040503030402090f09120a050c0316020f06271807091a070804091505060d090c12051921050714 65
    0x1284201d0007820700420043c84c05480d040b06800020704e0000d00340d0301d440b8042c0c1d0b580a01c80e00d5603008801007491300210700160109150110024100700c496124084100d0b00000308180d40ca647d5180c160040d2000c2000c0780a18105401c2c1203603650000c94041703009101040208030100d460403a05403041c81d114005050302811246058210341160242009018003403040078034541d420f10150000b05118000c1407c0c0c0c0800740104800d541681c0001340c094002003000312240070210420070b140c401d89450b00c840384004d041c0032815105210502a00126100051143c82c580c4841c11100b1031300702c40b001202e603c1090612006507c070f1080300822100d4208410810242d1640114003490403070700305061b000341d450012903800c1d48007400e013a0f183e65441d1000010403060034540c038080e01401141528682441c2d50b60f43e42c45041f1509040102190443c41042005e100c0c5114000c94071030950000c048074003040900303190010441103804105401c540c5003095030014107101c2803102c102d2400d010b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 957967419 1250 957966169 957966179
    0x100e18090a030e0a051c050c1f030b1503041a01060e10030b03120307180f1406030a1b02101b080714120c0c0d030902060301051c02030f0c2701 63
    0x78441441c16090700301380003100c000f800361b42d401440001041180c6070705803031107000e141003810030352003440041c4581d0722a01c1c00b800004000106c40450b800b24200058018220b0740001e0755034072103003405540c41c0400000c000800240d00082d40c0000000c0041c100182d0300d61800b548d16503188403881360030242c541700001d41e80f44a9005014100c80c0070342a40d8440022040f01c000e80c2c2e01c00c881020115500c003000d619180f01044070b80000b070803c201d0f40c00d496811300002c4000c0f041c2c00401c641c4118800300c04220852220b9211010840586844070000e940b8640042e40720110f54201c104014581891a61880e180310105080785034555142011030b644e81909032001c2c5000d540002c080c03102030016481f2000d0740c582c59030007100d03004222900c7d1500450464900584025200d0825042020900040e2035400550303054440403079001c00c10395402e11900110124540000c3d5141c41800b500046102001c03807020040d000c02c0c0e0f0703498030007540034041d089031484940030303c00790900070401000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 957968669 1250 957967419 957967427
    0x11070201110106181104080d0c02030609060702030406031116061a06071e080c03070b060a1e0902030c12150a12050a0201120906140702010f060e061509100e18090a03 73
    0x382117000035102c40c201074482c2ca002d8505051103a40c10f0211b4441c1c480081945010000c055002884a00500407440e09200003520390285115100a140c2ca03005180030712021a010341d52929640401c449206e502424000c010f485021541004840d015450003039a0400301c0480b45440d4202481c1c210700300354000310210b0540300c584261030264040c071103000b078104180001d1035528040c41001d52982000344c204014860b03e9401450798400e1289a0504455665881d104480d1100720043e142e0341d9503020b980143c885d0860042244000d00300304200c5007031104d030107803654005036080d030741e02c584075040d6419003240c0c18009403680c1d20520b4000c00540c0300e05050b540c83c942081b40070a01e01c1141e902d106c01c0d0381a007003008410001440070030501c640e0911078151120386581091000c5460960036002d615000390990b0b0042803510041c0d054620144115103850001800075440003c55082c01028050806ca41c140302d9071808854000d90405000f4150088904401400060859a50681e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 957969919 1250 957968669 957968681
    0x90201021509071706040c120f0f03050f040b0309010c0513090c181503050924100e19361505090f06060301110412080c011107020111010618 62
    0x12040f440307129400308540292040c0c1040d000c8080c070081032141070030724014503400c0c0203411004014211080c02801700d12800940641c141e00701062507411080c5041c111010300c1108410192031400080005050120500441c0308001d040020418000742a001310b4040c4181484174070040011141441006481c0e070142e1405001401c02d0264003815201c400c5050456a10001031201c000651580c0c042d0180102540322408070068088100552041602080d019601c40465040c100000360108011801000038000c09200800c140c0b07400711040520700124008010207606044401c500880c2420000027031044025541100c0d0041c1401040b0103980c5200c1614150010081d80b0090150707481a01d0140c000a80034014100303070107901601e081005031038039000340c0c50108580300402d0039000f56004e0b64906d0b081d10144c90410b0030f04140758042c440d1022825460f00b0740c070304108145100107042261017a200c40c00f4200c05000b003a8200c41807031244404500180100d00c0c5a030030780364800303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 957971169 1250 957969919 957969931
    0xc03100b0d0b100305070e012a05030706090c060f090f0b03090a020d05060a0b0f030a0201050f04031202061017070b0c0f01151d090a020904020a050d06050117010902010215 76
    0x2951542e402c000942c0c2c521043d5005003c0b80d134920134410b0075684099400d12039002820001c072070400d1a045481c1401c00507200101000d600810603007040400c3c01200c00c400d800a10500621241e410f140c840c0903420702c40c4002146542d0002489680a55203210840721402d1262104514203180b2040c1980700408048a501607a5002001681c0c1d45c0b2851000d203000790010f281c20b10301804207004a4036500b4a9500c0707140c6403001640290790010380f4280141e4203192140c0c444d00440d98100450123a900001c10200b0420401890307103078005600381c81010b01d0074180c0c5079240d4401e020000c41001151107001a00310f04010312440100d00c0092018882000c12200440002024242180c0c040c2d81c40c09a10b405094040018003001080610300400d034666912480c100181d2103030351011940c0000307008500c000002805c0d9580c0d16211401044064070b01d0311080c070f41e458a240100310074051126031081c16074517120200414420f0040c02641a002014884104c04444410440007858 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 957972419 1250 957971169 957971171
    0x1b09040f06020d060f1d0a020a0306080f01020d0f0b0d03201501080f010e031b070302040c111006061b1b12052802060d090203010e0a06050c03100b0d 66
    0x3808000481d540b006015824000350001101810185d0f0b03d41e0060141d406020184510711415144440d030b0200aa04500800e03c01607650034091410f901a02441c2d120a1140c000e25260002030001074005001c031454a410411074601680340090440750400c0756241c01080d030329020070000340554521240f080c01ca00951440010b41d03003140d460030582401d41040504c000c801041100030412006041201101c024002c5410841c40c2c030340e1324065101e5813001c100c003098940500d00001d000d040040c64020300240101800c40b500504000b60b4417030010000e12a48450700f4000d84144110410b560340c07580e40141d80c442c80310b014581c0d0703542d811080d107101035014410318a9103040050380c00104503820349550655201e061090030032003c2a40c10322540c4c0404420b1048015035070145034195812501c040e168111086a40300910b16510020341540c07074010464034124001a0307503500240f1440c4240602d0307460589070f000b80c1c001a0384080b410560200c060040044000181c0003400f26084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 957973669 1250 957972419 957972443
    0x902040b030d0e010206011205060606130b03270a0209060d030314010e0402010f090e061c0c06110106060516120c1703040b162106030828021b0904 65
    0x90401a0b060340c5440802c030300c50480031031035805020041c01041206a01d00c036050b003a880300c549517031005101d03a20a00c4009086c2c1c1c5002d0040d01124041c0103121460358403480d0940d0100940360b88040b00b814051508008241e02000000e2041241d503409005880285c03030704003d0010348500729504400741616511204c2500380080d440f5402440340005881d00344c282400050403128407440321170200042a941800703038030b030000c881b15080b0304144c8403a41c916407200b0149003020124480242007032010940018040da20188100312508d440c00200250340c1d4408003030b20745101d00e4103400d071304030301c011200c001186410b150300e45082d02c00c0c149007014000e2a40c81c007007440000d50603e03904580110034031040c0400c2030445031f071110914100400744444040050501040f01d8113008480326920b82c001030910701504000010341c1d20910312a1039541110680c4c1c0241c20f0701848800c401c0c1d56008162009100141400381c00026811000001400b032007071000344100100f00381c8801820503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 957974919 1250 957973669 957973691
    0x12020315040f0b12150c1b0d0c06061e171c0c06150b16060b0d0c17010612080901020a0b0f040209010509070f03020c19081e040e060103090204 63
    0xc014510602c1c04018009441c030340c078208200300105404c5261110f81d010b01d440c01c0624800d41a03040e0050040558192902c88a500380d07420301c40e0044855070603003e03011410705c40540000704c1402e1a40b10b0081071280f0764441d02c042d100110681d00700865840303080d80802144043c200e54401c100a40c20a59051500d001c000c01c403e0242e80760110b00046008100805228283c8070712107080d0f13081c41c18407800c42d20f415000725031405100021075034419080c3c03402c010412a0390210001003030260403049440054104403c03070010394422100d104c21080c15104007182c06105200548060b40b07070310100185583c94404054000d811150306520a40c40f085010810301401d0f00c2c854050003120311020301d0148140040b080b07041e401a4094040030040c024041d40208400362844a9031500503110504000e41314a4101694002058400e2001c48002031220410040803010054441e108580d5825005400c1c18840c1c0c3c411501c9560a1101040b220342c0700e50001d2421600051011070035076060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 957976169 1250 957974919 957974921
    0x50f18030d0807090b040e0106030e1e16090509030304030c170d020712020f030307260a0905061b040306050c09040515040b0303072003070f060305010608010b0a1202031504 76
    0x824208030110b0b00e10000c10000c143c0c000700c3c44014020800360541010b1502e2201410301006019200526071940180300c159001040f840e04442501e0004210008003400099204e0010001d0030200c400b0402c3c0120740c001c0c0501607580103c0340c801c0250716640d40c549084400b8110401c00311a0808000309aa0400042102030030382040f0681c401603690140d4900405d0f11a201c02490027950454516030710f5a540200c1a21b9001c0241d080205201000c5118000000314503513411209070401c0003808500c4285a020300031580c490b8003101c8090b2a03044004110000b008448501c00d10108001d03c002042d58220540142c029400241032114640000d011303035a0407a05056180f0b0301c210410194039041c0184940203900b030380510b00e40156511000f9030b80c411380d001b0f0080040d400c80c0200c043e840c1001101e00508000d8050009180c031103c00801422081c170a0100184100300081800140c00c0203c4545070880c0e183d04059030034080841000e0341004003284103800070001d450710070b03441e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 957977419 1250 957976169 957976183
    0x1206060f061c0f0f18150b060904060801052a0901200f0c010801050d081207051b0604170910080a150803090910271515080108030a050f1803 62
    0x306190120701d05810604110172160101500d0341603501408070103010552810b8002220445c0400101c1d0003011500895002c0c4141c01407160007038501100040d58000651155000d0480d41c15803058403290240301021880000800b440081401c0201122660141041e149212000c1140c501442e81080c407036400c2c0418075282090320780080900075030644c1e110744203501410b803c40c2e1381d4030180712a40322014940034800780c41050366000c05c08280c08900031002d03107505642c14800d0829885c98441203e403500c800741d904507450428400e0303030018070741900199070322041d001c0c080c11481c0076103e0080790711a4001d00b0405500d039443c2c0001500c01c84002d41100500382410041d81c0d200780704014807500c00c80041c00040c02d2050ba19044c000d103203e000441042c80040c0f600e07618980d8544010070001d0100101207202c07a503000100080070184c0c2c1208480d1740f0034039202c0c80c440744c0c0d907424110b032031f845890301900c0020003c100c00e000028501e40a000700d890500000702d842003408002c6413800c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 957978669 1250 957977419 957977441
    0x1e0f0f210106170c0a2322090c170712020d020415090c020f0d0207121a0a060302030d020109030917030403120504080601120305041404180c051206060f061c 69
    0x841c0000c4045420300d120700ca0000c20718a08021b03460306d60403040d000303080c1500100c1403180700c43c80c114282d08008000c010f5007040d45041d08004600043c075050f80c034100ea91199407010502001307a4114407a01140b00c0c001c9442c103240103c1c2441040d803c10000001d0140200d91040e5115035a5280426040400b000b80a18010000d265100040c029203001c080120011060b4890040424210350209541044403a4010043c8541341d0624110004802081812003c1801203080222581c10754214500702c81c0281e0a60f107100019690407802d03109260800741c04140413020800c01c0383d44900d9004450100d8000366810161079075180000b014502502d20006a03020400384111041409802e0040041032059607802d1415a006171a80c002c500c54000050042e44090600d510b850b003041c017110380b01100d007102c00c005d149041020056980206809a070f20300c22451401040006c0b441d0140c903004121082d0303050300e01c00b0001e1a034442c5040001c550004001c44220240300c0c059004000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 957979919 1250 957978669 957978673
    0x90406020913141f031203090c090c02010903080a05040f14070306050906040203060606041a1303020409031d061e0a02030c030403120e010c1101120b1e0f0f21010617 73
    0x300700306003003840d03030551a0013805108000400420000d03041000d03070485507000c4d0802040300001414884112a103a500030017250381030500ca18400b95040d40111280c1e80b10751141ca80315281d1b00b030b44070200c40044070b00034091b1041074501008a0407010059440036800000c03035029903101c2d81c40c0026100152080700056001000380021841c05206265101006588203030500c0e160042805940071001e01c0c4403030340c0a0000d400441c10048480b02c40146401510500c2040854500140521100c1c0c88411103c0b0381c40450103058540001110720714400008103502c404050ba02219595121301c15000661004100c01e804031081032024000440c003a45441d41189840840980540842d442041c10400340c3c019103000526042480100326000b0302c0c02c04401d0401d018000002c051728148280d1010300c4111201e810f070040008506511000d807458511120400f0a0101281e14401015400091620b492140041d0034071512801480c1c04004940300b9a101174072060098003c0801c2c41c65 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 957981169 1250 957979919 957979921
    0x3150b0d090506062409190303051914120603210a0906030506010512060a09020f0a1d030c1e0402040e0103031707020601150c080408060610030b09040602091314 71
    0x401014819103034016401d1750200e488080c44c86926621540c50407000080041c049941c41d026150140641e030918220283c004450303413281805030441d0450050b014001e0421031003203134510300c200c02241c801c081000701181008041404c240c000f1030001c086580620494038040a40440c01940be00c0500211040341e9032002100307401000c2c0555900003205050400040c4101c1d43d92100071991034440625521016403685030010321a00540da2215103411700204091451518280c020407010800c3d0301c42d20600281504404200e0300c0d19005075505810a40d0014802c0c03c0034031500074492005140442444801300006049030807176081002e580e0203400c014810550000f00004448c0040c0900b05030510342458006d40d600014010407521540c0c94081009882c02010310380d920340d07844038800d52155120100c42e5690301d000c64045114103070005c075124074540644103022503108090107100060399982ca403a4042d5204000258002080c4000d901644009109003c0c09104050303128810f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 957982419 1250 957981169 957981173
    0x912111c0513090203040c0e04020f04090b0108010605011e110a0609031d060306090121020a0806060a0f0b032d190b0f0607060b0a05220c03020a08040303150b0d09 72
    0x10015500100c00f168410800d00001c22014105202200c3c200e041000407640d562022031000f00b401c2c420180c220f030400d00400b08101d00c50101c14103075001c05000b0070140780c0d103400440d692031b090421060319844120700144c5280c424190200380c3e040c3c540c120303044020166136a800310b0b60b5417542a8001582000f50b00c0c03920902c40c070080e0f2480c0048809500f90f003080390002d5403140040c801d040000d000c03005040c2c00100c2d6507020f4240b1540091800010a5980c04041e4490070200d0790f13148500d0701d00c140442c4102c408541034044e0b600c00c0c4200c5056550b6180318442d09400341e1040e40c6031000144840c0c0004880d880c4079442103a011031200040c00340303000300005039592000c3c158420040d840c844400da8540d801980c0e46682c211344040fa0340705501c404032b0040d400700c0e0001500301905200c2007038491580c076140801c1c6030300000c00300003d0a4000c1e00701c0403802084080c0002401034000b15022900c00c2d0400f029180c8a44121051541e81d003a40d491035520801860203030a440c2c85820b01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 957983669 1250 957982419 957982447
    0x1230a050609091c210f180c0603150509090d02100209030a15110a02030403050d09150c0501060905012310050f1b0d11010b040912111c05 61
    0x107002001a41c1454103030411030303649612244030108052100302d40c841c00c0740e0600e1040b8101e000c1070f14544a218004010900307520082e20b5840703a0a0b051500b4180042c3c02190000d44200700d19402111640c0e070130782402000c41c064180d2400c010b0f101c41170310002040958844103c0382c0210301d0140180841100c6000181c140648030104841562060000300c0d2a42c03004202101d2581e4031250705100f6400e540c10b2000100944048640c1341d40e000304040c940250000002c2c000c1d640941d04035141c0b28040202101c02c1c1102d400b401d03c41e0741038003040355510380c017039032028000b144103000204016407201100c03002c6480907030101c1e101c084001da21400740e11180c0c4080210b60300076545d80f0a010b08014028040b03200d43c51868114120009400c04000b00c144a036543c1d0202c40d030241c070180118104002c0c10044104011440ea506e81003023800c992401d44610080980e0040075400703510720744207081d20a02c50b0681403101034094155040507031000300310703120000d40d104e07201c041e00c640c50a54030311 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 957984919 1250 957983669 957983671
    0x152b0204051306200d110f04030b040201183506090714150405011b080408060f0108060402150307031d0d03150f050f0d02130504140c01080c0c01230a05 67
    0x300c0780014120384015074440440031107802d030260781004207440103030340c0d400031141c803c00249120b90b0f1f50100b008070400c0304007501c1c03a010701c0c002d03643c019085803d54a405191580c901c142c0541050906025580c0e07821a007001d1498001c0108002a0460150846080001c00c60341030704a5004640107003d4281010ba000c1c00303071442500c161403000203020819031544280d000f00790510030410300e840034040102a6080f00300380d0180000307803140d03511a082030341c642040c1d036800c0110000b100042411030300052490b1003160001c01c01d080d44180c00656110030360025201c0400c264680c16002c10300c000510004c2541d5441c1d10040a8001781c4081c001c0440e5503012307814055051101041040d18900314101c0160344040700c60640c8850248001801c10580d01d0f03000703420080000c400c884002e040c0e40100d116601402480c1000f410b4504069258030741c2d842402d002c07401820115864003020809005440c0c014000042c00c079402c400d0001c070b001d02c2038242c01c3e50540c02100308030310080399004032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 957986169 1250 957984919 957984941
    0x1e0501090617061f051e1003020a1b0206040801110c010e0607080114061201140a0519030b0a02040815190c080402010f2304030b152b0204051306 64
    0x2002994140b524540d155a00a460998100c1e40300e07006503803020300815103a0040c42c00400c00c05c1074880d8458040008002c1c5c0d0a1148260307110340b000001d0f140030340200c2d0310103512a0b440c8980d40d40301000c2420540d540c507805981000c2d0511020420400900c2560012426013030142c5e00e50202e0210a82074411180740e10721240c00c0402400b100d1a0003080090540d54407450f01c80c119010600890f040d80944101c42140000750340001072091000034405003001015244400c0d01521001840220030f114112503d4484100400b0030200781c20f241f2054200003100005880c2542c0c41c103c26140400001400d0030340000101488101008520700c060500905074051103200c40260014041001c024400313070511081c21003001c00c1500c682c003510746a81c1c01c6e41184005548904050681c1c0e00903010841d0030488050101d255282550507120f03400d100181420101c045250240740c010846440195990820300d4040c40180d4540c0a080d110f0400120070003c400d8050512505030303001881c103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 957987419 1250 957986169 957986189
    0x231212130602161b0b1207030b0415060f02010507021015030c030b0106090806010605040306090302160e190204230d0501020a0806041d0a03030b12030f070c150203070609061e05010906 81
    0x8100103180c15a0b0903660458889a000d06c0c1c0b80c0e80e8103c0c00e5020f051600c035843d52180c80c004a216410400e07c0d5070b8401d461032503075601c15400301c442099080360701c1039541401507841300e000701c424441d140d04142085551013004001c0d040c0e4940e81c0195820b55074108940300c0714044014001e00d50b10606030001001c82c40005c0c8040d500d0824003600da4402c80c0000781505807601c0a0300c00b40760080140349607800d06003d0410403660347e04011a202072050740d001500044000f51446030504500903542910b5208404440d002c0100c0305007030318112142e52040d0845040c0c00b0345004a842840941007040c2c4c01e03240c84c580da00e003100c100021141c03000c6200301041e03024015001501c90001c0c0b001d0140e5807505001504400d00c0e8006181d400b0382d10000001b5108c009000103c1225100151255920135503014803071549132140c803549810798003017a50050b4014064000403d8040e00a860118007880001032103189849248420344000c4649407111622a4010000441c01d071003918002c100d1841 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 957988669 1250 957987419 957987473
    0xd061d07030c031b150e01030e0a05070510110d030504030906080c0a1101320a110a050d020912010e060702071a2523121213060216 58
    0x82c542d00342c007080740009000c2d01a45400000c02250214004010300300c031040d54290040035160007866020755060850000341440c240c0054540b000880c02c103201e6001c006880a24100024080030091100000d4100b01484a89080c0000c1c10300c180042d0b80c42c159000304907803a0070704018000c1a0240e0010040009840400400c000f03140281c9801d0b50a030710706000c60380307202d840040c05880040400c80e118040810511009048042c101d0845030419051102c07030741c0e800303d011040795086403000e009000d0422114004c070f44140d0050404c04c07259500141082005400300350a56964020b0b40342c1a95540c0c8020700200c01041465401501880208002c80c01c101480e82c1015418000d00300c07210b008034030bc4032044058000c82240b080003110b003255550a0741802102407003001c00605000b04002e01d008c1c2040c2c0082510000b14140c2041180b030400c02e0f11008030800070080c1071460507840710407250001051070000303003c1d01c8402544001100b1082c10022300651020318941422002c0300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 957989919 1250 957988669 957988673
    0x6110f030f040e090a050f010c030501080d09060513120f1a101509090c0305160504050904020f0d020a080f0f01060f05040b03071d0403030b0d1115090d061d0703 71
    0x3408030b4080d922a20040380c29521071951241c43d049103102d004240e07010b81c0c6041d50301c200055201400005941c1d13014006a66180c07000d503100d040790b0020000048880c50203200240c058802000c8503194401e0848916555400700c2c018058500011103054005c110108140801081c07031011902d2905103840d05401e003010021f070702c001c240c4a0080f9413204081e54070002070007940958001d0036284070a21441340403500c010010302003201c1da0b0042030b01d0b90624582880c4240146d4095034006410220b1944560b0208005040b811520651100394110300c1c03c0140c65080e000c00060100d90b0062011f0788400b22040d06003d004048001960300d848d00801c440682061410111a000e42d8000340740034040010a0511350983c0140780303a09040c0424502544220b929244214000d03032b410052241103008115804c503c0d172074003910b046540860160303070b49000c2900100d4417140d8038111b45881c40301300100e0303042c00740b44800713880083d0759010485030f41000e5004090307c3c0c19000d010f004041d00b55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 957991169 1250 957989919 957989947
    0x50604150302130f2f0a05121b0c0610140108060d140318100e1f030e1e0105010608010503100f0f020c030c012403030509041506110f03 60
    0x5440060310034a440c03000600c104103681c1c4900420740540d1805d100b043c14822040c4020700d80750203030f800b04d003a407482d0300350394100110290744000545650b8940b6020003210340c09840e9902403c040481460702c41c0700711001031000f00800110174008090b00d11480d1a030740c40c4d81000d50503444601e00141c48014000c0d0303683d1180c2440e40c818400c550301d0050102c0f50902a0020303005110b03141c0c8504c070020742d20350502c2110401c2080c0680031149020340401c000740440d801d403017103040d15800c000c840d4004a814941c1000300200c110552500054840b500381044c1d00d0241075603010341c2004140c805d9065076060a00505015102d181040400c9516040229603106000300581203200e41d6045088123680d4a41c2024008002c1d203c019501c0340c0032031700515144d51004ea00307041c0c103628151482d65000b2000c180100300c00901c1700c42000151a50302e05076615404941e01641c03203955000800003010320080650007500e10b030ba4510f4216880103c1c201d162003405482c140550f802408494862480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 957992419 1250 957991169 957991211
    0x901080a0b0405031b060a0f02040f06031820090901020712120608070b0a020f0c030c0105090103090c03080915030412140706330302060421061e050604 67
    0x1225080c0c8480b40e869061441c04c2d07005005540719800748080c802ca580d240300080c0c4501074805240e04204000e81c10000f0400c80c0b0552207800f5425410380c030200006802a881548260911070038802000c007250b443e00c0c40000300000021002100c11000b00560501410207607100300c01d113000310315000380d9449090424100f0302a080c01c224880302007009004298110100400e10f6000306c1d44007944070f108400703c0703400c0002c4000041c0300755030100051900006500b01c001d14094064000681c0f03550046800b9030004d002c490515486003110400180248000001140200c0c0a01e4591006400300180100101b044040031142401800b01107140407001c510381c441c02d0b040c48449403403078102d40300aa001d18240034010602e0000300007a03801000d4400d1403541c0c000102c02018010011003504d0111080c000a034003ca0203003c14008420041d06c80761150499400341d4045282c00d94132202941e60081280304081c641209800c00070085004041d00034074200c50600c810809022031901440f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 957993669 1250 957992419 957992423
    0x2030f04081c0501081005420a0f06020d020604030824041d0f0a17090619020f060601170a05040213060306050105030f0a080a031a0406140a050901080a 67
    0x2000a0003400541e000301106800081e200d0382030001c3d603511513170107498008013008003201c41e08200020364520810001c110008a6a6140105c10002405113005150840745580e01c20309095203449034a558602c0340c18000c05035002036600c0a805c0c40b1000b420002c001e0b00401c2036601c8417040c0700c006a000071503184d0104a641c2d04240e20145403c204d070484005486054100e4507010010056122030f65a000001c0508030456124848814800e542d440c2d5041c8043c00e404600b0184000421076000107003900d00004000e10b050003c0010780980c1d20803050464405a448000610460002800709036404502401e20401801d200c07585015010b200a00c0947da8079078901c002000c41d6191809035245030700800d01080620b440303180a800412080c00341511070300c10645401d5403c040080e40d20001a800f004407810300d180e90600b9409010750a40c4d0040c2a80030b0781101440c0c0e2264410000208140d82c0000c400c0446081403202e9006c4507085039000e072403074074014022903500081d201603460f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 957994919 1250 957993669 957993683
    0x10821030115120908091206090a0b04020f09090303010f0b04030c090207051509100e030f0712090803120609150102070501050a05040e07210912081905090d0e0402030f04 75
    0x8070302c0c2d41d41140c050b00c1e0480101602c902d800000030501c0741a0001c0c1115480c02d948060294a00202c071550700c20f411100c8800ca5231010090ac000561061140394000d4809071075003040c4050180007895154044400d01c409500c0413004002c115094240b12000f85400d545040c5400d0850300c41c0364888066014002c2d54a13000100b19080103000c00c480260034922407002c0200342030400200d03451710584c018007200c40f418030000c407412607408011200c80b84500b111091030803a0130750f00c0c9c0c12a018548840010b00c000d0740070019855801784020020a0081904400345162180404c4400900501400d020315100003006003281d8000131074501703503102400c0c00da8851060703a0045a003880303242c0011010000382010710440c00c3e00100380181c1081c0185d50304100102d0b11a4800440d8071440c0d01a0602c501004102901030140076840d8000c40d818211012113080c0340e4070401a0395050764145040c1d40070180f0b1950160348010940003c0f5401c85041d40345007080000d402d03040700e001d00064200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 957996169 1250 957994919 957994949
    0x5010302010c142a0102010b01080112060905071e0509090a02100305091204030503070b01121a0720060114190b0a03090b0403230a05120403050d140108210301 70
    0x903401c2000350300104c185600103e48102c003442404a2034094000d007403400341d800e08841010541c083e00b1850b042e15240003d00c01c03e916552038103c080c240c103030402e5139035002c0c1c0c0c02c002c142c0d000042090215440442030001c20f003442c110501007a1b540080c050b000070b03003000301280d00681d609079054040e49614600480c1c01c0c0c4030075180310b042441c4c07010402c0d05004005000410060048003901440c1c0c040d201801c0300d40e9032600601403a004114000f44826414440001b4000b5a1074503590032208a01e070105494030610044200c3d443e051101d0756035540044010040340e1031003034000341280415910904000c1e115401801741e5001800307600008807010400e1280107100b50b00030031101c2c0c2c01c2060228a4203203070030050180004500300d403d600039510761904210100004a903202019603403400e2801c61041890703454107078040c00490800034108810030359020940680c0155240300c2e00700d03c5041d49885003061401488034420003050021001c0f04c5807483c407242c15070381121603000c814010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 957997419 1250 957996169 957996203
    0x60417190f200315090105010e06030709050a0b090a02070606060f050a2a03170109110702040506010306080d030608150610050c030c011a01032921060c0702011205010302010c 77
    0x103000a40b0096a018480d8164904480703907491042806000700d10000c01a50740c1b10707505164004000c07241030350141d10a14041103c403003503900c05a44584c01010015803290344600103040c0003010f80e500700b011600810303400c05200345845844010800c074104109000d9210074080c0c03a03409012544420310403114a088134490780c09420000306032545d85120341d82c3c03600303180181410030b01e8200d1009810014001064461040c854105080302c0c10107241d080249503400c0202411005003054105622140001380244081140805000c41502c000c1411030030203000034580800c4504800e6154980c40030b008007600c030032035220038402c02803401035079800070652241c0c5140b02c4c0350040d4103650f1814407204140454080364040c41c80c0700340d905101e04010302c00c172181000444010406582e2014028402c01d16064054620b070045070030103a40c0c03511741d03c100c00741805e00c11240f0406030070000403050f003190f034007001d003201b00541007200300500d50658000900685102d54010400450f100c01080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 957998669 1250 957997419 957997463
    0x605041b090b0702040b060c0102041539050d0e01031116060b060c161409040c05040f0f05010b03010603051b0a0c030e030109050a2f040c0e060417190f 67
    0x404146c0c00707080e059480890140090003940300313101700300303165214403800c840687c40b400d041d4007405403000510424100081700d20591030780ca11080c9050429041003600001c20504c50714120468a4a5096131f520389000058141d800380b8003540b0381e9410403c000f604100b54401c0740e40c4140e0700710800103061854040403403154406c10140a4891241030400d45032403d800d000e403801c0d981c6610921102c0c0c42c40c101440724050042d1401031199102d60421312881c01c1c0340e803254440c0345007040e01040800210015070308403002a0880080c0364000001804401d415001f210b401c00d010307000d48170b10802c2113a0880c00034010940c1c80c6080014903903050741030500ca8000b0b1843c40e04000c008000d9070b0182d10700f031642e078948108120382c40800b040054100e000c203803125401882122414013445c884a0041000070a003000d14030061010b001d900856940300c407405030003e009030070450307414036110240d03003440c140200d9050044850120030400004801c403147c400300c990700502d04014900b004603590 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 957999919 1250 957998669 957998681
    0x20100f1103090601080c09040206030406090203210c010506060f1603050d0c05091206100303081e13050c190509091513031e050f030c0408060a0605041b090b070204 72
    0x2040c000020090110038880401d1441c1215444011070b2016a2104c091001c02e040480d4040d42c000020710018000c1460703904180803440c4002c7c180d84580381001612321390000404940483d883c0003259180c0f4180e401d20856401c030108503066801e10000d460382280b24811859280d8441803244190f2007018054801d54803687c2c0142c00900400e80410401025900f080c100540b04000d00d115001d0004000b01d0b80d14010081c500d84503071541e056032415103c000000c0c1c034281c00074540703661415a5240d40c0390351501680f0140c480140a04003400c2ca02d1900652414140c07060220b10071141501c841e41c400351080b43e0060740c1d034000c2540c500365014144441d9100040b0207181c40300401ca11100c04a1602103510b11a40314a6a00340000007403030031004038500748202040c801c010301030501c95550041c65000c00c3c904452031500d51242029410142c080d00c603011007039203885003400103103454040c90000d003081d82c0c41241400c005040081502e141f6224021409100060f40c100b135440b26000f030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 958001169 1250 957999919 957999941
    0x1e0f120a030b0a0e07032a2d020c031015060e19060306062601030f0503190906030f0506030a140c030105100306050115050a0f031410030320100f 64
    0x4a10001e5440303413030f008044003c03168800024503060740c40052031b04100b1003c41c407050a1203002e91415500b201614040040c0303120a0000004a840300c03625041c2110801d048000740e0f01070120381c01c0b094141840d00b0a2007180340802400d12080c0c0c030365101c1c00c00a1300d00300c0e0250b26000034600b03411004520161218400d84007152000c00d07021403140e40540280702100c01e143e8a003c2040300d00300d240b050350000207a2500d4803400c104010408038035a10340d102030762402107060fa464480e030900d80c004800c0a403102d40c0c02203061000b0400642d038141c85415641415500c05201a140180019403190b0000100038940c601101608100d45001c02450b00f040801900800c00381c100b0450f039500c10300705484100c40180c1070000116105d0003006000c0a25404c2c1d40750f142c144042070b0b07000e642c10586c0064190805542c0c41b51a08081203401ca0310b80a0800301d01c60480e0380e0b055040c02021504894140700d1400608000071507511000104010301c480c042e0000694230744041d1049000e030040794a2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 958002419 1250 958001169 958001179
    0x120b0f07120c080105030c060f0409090c0b120108011406091303032d0b0f0a030b060609130b18011a0705010209030115060f080708280e1e0f120a030b 66
    0x5401610f03410070b01181c140c41c8111704403140d0a109004000581c843d031031340008922014801040701c28003542201850911550f28407150340c0d01c81c00c484415403c94801090400d410340c004011120b001c3c40381227030070000d000d450304107860304401042041501400800d8200227402c0036a00349071003070740450820004044803c046925060b00041c4104820407546110b0380343c85c07280105440e0407007280300d003a240a02070a050910750340720101880c900401c681c4d0401001c0102121584d5078607005001140b10301d60015050280c00c05120a21100308d0020001c45a6000144400081c03072007810594800501910395985040c6040c1d4064080c10716065055801e18407920b13001c603015407081d13041e1540f07540c8500115441e000115203003002a509400802c15003004265030440012810034900e603180a1040c203030300c0c1282d105046500310752080b00c140c1c025905000c0040e12091a03129140030f034100500003407501c580000c0c4c651501e03204994203000c0c001200e00141e07001f900285075540c1c00410b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 958003669 1250 958002419 958002431
    0x1b110d02010212160308061008070807270e0a060302010e060a0c062307021203070f0507020a0b041703030613091b090911060a0f05130b0d0603050601120b0f0712 71
    0x5010f401d01303403801e54110003080341000052010b0a20f900020b0f2010f00e0340c0c0e40c1c04203d4076664015220020b0203807508040081d445806400711303142c10500100d0300c0120001c609143d20340320781c0c2d90010301d01601001340e60b03003801000c10150f0b9110040861248088644a6841403902400e581d0801c2d56040201041c0c10280003ca08070030348682d00951150f4041401100da0303507180c1c12a11070030840310802c800042030003ca4000c40c820482e004050900f4180170745008a141c0000c4c100840030f070702c00010380000040138808220340f2402e0303030115031140c0001c5095081043c00142c20040007500340030305030b0b610800701c0709024100345400070210480490405480d1203441c920040e000d85001680c800b840007500320036508004084407a04880c40c0d440e070907903100381d04007200c69500c44410340181c0c1e8000c181c00b003501c0448800400e80c2c0a05c082000404901d9481c2040c01d152059100b16070a400b8230a0001c04520f034400100d0780b00c004103803191082d58490780c0c141c03001c15440d07016003000d80c5000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 958004919 1250 958003669 958003687
    0x7080a0b0d0b040b0903040326121015140403060b060405060708090a050a080a0201080c0d020a050429160515040317091603150f020a0804031b110d02010212 69
    0x1011407400383d805980c18030300d1640c0d00c0543e6aa244a548002020040300140042007040d46201c502074000e81c050300d0900e054052810b807070300d04001b5070344416000401c62003045003581c2c1b1614114080002d0034080208081000801024011440041c2c5610b88070f914095680e034900003140d0160030010000c50311001399043c40d0b80c49401c100b100c24007030401d402c0c1c00b259900e0010700d920200c0340d182c0c00800c0480c80307650044074882c101600031010003406008401c1811001e00150030103c00956032aa10b4900d40081203002e0003176642844c02240f00074980282190f010000c1b13480943d1800b1684591020304d180c685c1c5440e0b403840015161b00500402d100c10903501c00d65100c00650b41e038028807003a88134080d0854650b090b100740880920000384081000a615041c4413640d40034031200020252400c2d0041e4080ea440318840400181c3c130141004205a007041806162101800b4075011440895541d1070920181c01c800d5071050140b41c0600007168407c01c1a82e130f1420402c0340c900e0311440c5c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 958006169 1250 958004919 958004933
    0x100b042702040e1009090b1f0918230706050a0203040b040b0c06090706050a0c0204060f030501140708150904110a0b0a030e0f07120302031611130b030607080a0b0d 72
    0x130354001d18138401d18040000c0350705140c080c5c2141c16820040035441a1500102050500046140d5070304540510034000f0b0401c0d010f10a044415801907140300e055003a034980303405201004d12001004103011450300c10f4034000081c0802c10790b40a0300300660b5594001c00241d1460003160b0040400690000d008181d00b05034801801445032250210303042503c58040b03036901c0e5145401003100152042c459410503500c549014000b260000d04001a41078441164100f1000f1541007911540e445a508024200121044a52040d030a10f0700a00c00d0030102c0381e044030440d2213888036125054a030081000d111015847e441100c500424100308244d45104044003600036a0324000400d18020005055207004943c6580032025180940380350340c2030a40181744040c0004042d0304522051105a0f800d04600b421280594003a547c1c03180c50f00701000405c2100c0d15900041c100c0e1a0814640f0700c0b09480015200d60001070604081286540e1000303598010851040c0c501c0d4014081a400d009116603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 958007419 1250 958006169 958006171
    0x251403010605071203020306150f0412050607020c030a03022e05040609060608030405090a020c031908090c150d0e210c160513020304020619080f100b042702040e 71
    0x410380c0d00c0c0b13150b008020415812070000329101e58102d11025803d584901850001f4940311300d2102155040c0340c0c031115001105c0c0b00924080314aa440b14003480702268040121034030351171080f00144108003a83e03030025140c1c51182d4101150b0030301102c42c1140b40e4000d103590300d04403c1c422020019403400b81007410142000703900642d03100d860300c2c00c08a0030b542c0200c01c55049e10805042a22991281e0072000d00035409000b17039822900046c0301070703498818044683c011165035036071001003034180031040310304191074901c40c24412000c00e580d0200303846018068544040c6000000078001000301c6034181010103149004410000039601300e01c400325050068100f0f41d105100b19418031038200f500108078580c07030103101d901c400e40303003201040a42103800a5074030030b1001d0001c0e410315940b40c09100862140d020300d14081035580c1c04001c0c515648082d91350b8008001242840013918020340ca541c1d034070450003541070103160100500349415030a40742d40b000bd0003200c421075956556003214025214 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 958008669 1250 958007419 958007423
    0xc050f130909050a030f08090d0e0f0a03150606050304020919110409061a040501051b01090f0f050f060c0d0905210c07091b0e1810150201020325140301060507 70
    0x2445480380401031180c03a610b40701da2082401270860300c542070800d6900c6074a202c00c1e20341c402ca0030081d142031502c0350300c0800025407050b4026004409400700180a4880640054081213000c0c400c00000d695040522604010031402000c0300e0005100c0405c0980300f045401c4c003e00ca0006400990300355254000300840364442c1014080301081c1c200c0301c4143c4640d1090360700090741841079218442e40d252400d070801c1641c07000061a500140c1d1000e5040e150500d041d036120500e034402c0d03000d115041c0031000301030b0f540001034940d514004030400400d0168482c0d28588c503549900000401c04104600410b030711081c428464019102c440448003948006005070450081074000585031044d4050182807200d1100000764001403950220385001d4800c42c000d51040e2030b207290851944101601d60f005002020a0818043c10140a112940c040100c0c96046a1040040004100c3c8401007488100d912207040c1e0003101c801c044c1180c1109400344660101000007000107000d07504a40100baa0078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 958009919 1250 958008669 958008677
    0xa06120b180a0606020f070618090c09051e0d061104120605010f060516060203150d050c10090803070209040203010905030c010902130204080c040903050d09030513090c050f130909050a03 82
    0x182e03c0c1c0c0412038a409031806d804c0d0741517214000610241c1d01854076800710410302002c92503103542e60080302050764649424000425401c031028402400d1501881000c3c600c4400104820008103000c1510354000c48005441680d86501815209000d202214020009042e500c848031007075062040040c0002c1c4100342c84481d12020010381ea501450a4130001c511114a0701800c160a13107070300d400b0794001041a039501110f051860182c1e03584d5140540da80380118010008030441c0030610a0305150850000280030044030104900034000003144c40040c0c0c15900d40c0c0d8a80c80b40e2002c05d01401000760010058003021450b242213040540c000c0540d02e00840e4100c0000505500c064124411030143c2c1500e5000150232100070304150b004099014480d00c1c144d4074182500354000c003214403001c0d0880009600040b003002007404c41c00000003409444400300540c491485001c2c103c3d115100603148500b00110740040c20b0b01d0244c01c0e900007001011003d0104000b9480c1c41904c403844100704030042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 958011169 1250 958009919 958009931
    0x60e010c1511042c1306020a030902180a050c03060d1104020d060e07020c010e100c02030c0619261b0f181c030212070219080303071d0a06120b180a 65
    0x55504d4106550003202000da641002e4800e42d240c03000a58030081407581410344550480005881d0704198204440340da031640b4086050010750081a18009410004111004c1c803c4c0b004541e14487c0d408845540000032003401c1c080840410068042c400c80c0368015482e1240c001602814211071505c03540303850b400d40f1000300ca10001942c1031180b2695850300050070789010108d00b802410704400c1580000d0840b480d40000e000003d2807507010703010002c482d0035500e0306484841d0300b0000b5400030170040f8080449010b1b40c20030b13044003a880140840d00e00403240784100045801c580884180c4010040b00507550401d80c41040030843c01c054101c1c0c01802c082c0001c500580881903030b045c450750b00d94040e105103180706207143d503550011030050ba4094404202000c0c2c0d04c1c50028160003d141c840c1c0599160300c5e00300c4000d0300c410290480b4544420840808483d590345207005102a00d0352400d0124003010300c0c510203001014494a42900b02c0300c4c1e0306c10340a8084501882501c50b2407030320418404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 958012419 1250 958011169 958011239
    0x50708121626090a05060403050d03270b040b180c10030b06031e07020a0b0708040305070b09010f05011e12020f2107060e010c151104 59
    0x184001030409896812000e20189641110403121a030740035000d005140c00380216200d88840c040088022a41c40d0100092144858144951108000c0008a0340300d82132a28503101d098840c079200e8181000c0583c0c61007001810380c034105031a130180c044d403004508034805c149400034252005031001d955080350303000000c000e00381c903282104031034103044090070501c29142c00b2301c410b500a0500c45010b05854940c00440740c0c440c030001d90b20820008008000d940c42900c064500000d01500040454001e00001c4000c502c036204400e400001c98a800903555032641012034a0f4001c0c084002c001120b48400e00c490142c0540011005d40b4403118204a5640e0312960310010b044d103d8070041d1b140c11110410000e51100c00c5481c5409400a000400a078246000040070580e4285603010701c0702084d040c0581600303080150034013401c200c0c00c184410400d80400a8076100c00b425009040310b6800e2440344030200c8540110745051482e015031610749489448800005c81d41d10303e4422001688a40303150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 958013669 1250 958012419 958012423
    0x4050402030d14090d0804090c0c020315060105070f11030610050307092003180606240705011407050a02160b0307110a0203030d0b010e030a030503010902130909050109050708 77
    0x100895008008001c401c0800c2c60580d0801d4005a101480d100d051105044948800000382c0103107100344685952103040c03840e610b0032102d180c0e405100308481c0100800041c0c0b00041d007142003101d42400f51390349586000049501c0c0c415540d0060400a500030441c0822010030b452140322201101074580a41c1c440c02c4180c440c224902c191540740e0b00020003002100c1c4554004030006121510000e898108151000340a900a40c1c0054a000702c0040014020b9428820283c20440407110f62108041182e100c0c284d40da00454403c940c1c00b800102d400c1004030941c480340039031aa003100082149400400500f154104d02008405400796030444207200048080520035101c110100900b103458103c821940c11a0714405503c2e988a4040e100000d69802c1001d06410306c2d07803441c08122010004001001e0407800c80349103000c3e500104140340041d4001d015a81540c0c6003000050f112204580c5208010b242e952101c804070f0300c1c01c0310032000d1050640207241010b020700200d03240c0325610450710f6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 958014919 1250 958013669 958013671
    0xb06011701061805030712022701050f130f1b030501081b060412121e09090218120708012a0c0804091e0507020d08150d0c060306080c0405 61
    0xc035444030005001c1c2c10f0042c2220480422285403498003181c0354404a4648045900309420204d0100256030440c50500300112900d0490040d102c100c4041c0a00c51a54203810700072180700d006003840043c003544445d58401e50710b810300a014051031690414000040980b41d80b08038030300a030800c10b401054024085c0300d0486134000000c0c00c20882d0303107880e003001c2441640c4a07a800f0034100000120000140d030421403941c01502080d51850040380090104511200035519841030304407040207080e0042041421200d445101580e5805409100761072180e0038803400d81d01003841da807481d104c02c1001406d40240c03402c0b0f000802c9111441400010394142e08601048079028a11800340c13468450050301c1d00461240d00c40302d0605031580c1030036059030070600b000c051400070110030642c060124029141c0142060000c1d011258546070f00405e09040140310180ca2450705891941e02e46600901441c0550440c0500708080d03160b000040290400f442000c0107449a200d020f911071810b4403c20b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 958016169 1250 958014919 958014947
    0x33c030b010c02040c0c050d020f01060609150311040503010e060f0609010302030a1403071406040c090c020d14090306240121050a0b0616140c061608040801020d090b0601 75
    0x402c9020b0415802c00028000c40817590081000c41501500010000c1118078245200d035000f4000100c1d11700c1c025402c45d078807035202c81c0410450520811070105882c0c20111443d92915001c5a1940807d0032100e0500c48c03680840c6d0150302c1d04121041000d0701140c20b42c080d000c040c45192490301c41c0c00401081d80420302000e0340c1500200040d4000901800404a00f41c4401003503a0400e0710903140c0304d1900111042240041c0c000d04100000c020a5009102c050301d810041000404002e402c02552450209180020300400804503407107081000141c85500100a04507102442d14000884070300c4800900c0d47c1112a0143d0403d501e5800342101c100e9040d1510300740c40100b1080d5040c0c03405800c019100c5510f00c1e0388e6048500c0107803a50380080159a03c030608400381107209240903081c002500302601421340110f0340c040d00d580c5d07404080700c8850700c400001003103034181410150b00900c9a03034884202503100240000038048107802004c82d00380101e00140d09540c51600540c0c0d0481c13030580c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 958017419 1250 958016169 958016177
    0x50405180411092805061003200702400209180726070f03050c0315012a0c090c0806091e0a060f0f14010804033c030b01 53
    0x4404a50803c4010720380d02c2001100c080010804040075146014015590400342ea030302d800400065003080101c02c0e00907491031404014420030180564411680035000b02c03039a44000034213409568405880403220a601844001458a0103c040e0814034602e1a0440c0403859561070001540c954401e40b03450381c01c040c0c01d100e90641d882c070301045910401021030007400300e041c200c08000e0400c0541740c02a04110f1030317158a00e04000300007602d0914030510040030542880b007044040f4181c2001d5031b0700306e0050b024030158100c00c080107a419650308282c3e0364006d103100c82480c41503022005010040760044c50380c04070503929200881c0507240c0c0e424600011a1590340482d42a041c0940004d60204292144451151a2002010070303520700b601d44120040c2c4405040c001041000c80e101c1c0107001c0381c20440c0a09150681c10703940c81088041e09814014001c0000d01894010714459031414011b4400d542d2140418014482c600030b0444810035040702076400c150864000e00c20307a20f540405841e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 958018669 1250 958017419 958017443
    0x7141603080a0f05090106060e0406061d010302071a070f1403190209030d20010516030c0e0406030305070c080d0c060209150c0a0506060f01270f060504051804 70
    0x1029079810501030318070310006641d8071500469545a104907401407166500203e070881c94007000426803003414101920443c41c00c90100412030f00500c0b4041590b48400030705200005d03520042c1c0090241240151117500031a0707101503110b41c1c21890601c0381240e9100ca52800d02d21010850301110410032907801da00c010400300d0080b9004615007030300090040c2016107000103040c00710f2f0500c0502e501405c00b15500c03e040042c061009038180405440f80d8000308010f25005442c085682090b862183c281607607070b6145404103200d806554000c11003c0c2082c4260740c0d482c600140140e01104c815140e038805150f01080c04940030480c5404114140e64040c00404551940e00080d440b6050403640700b0691000c070410810600d001e02036450300207015006c0c44034581049801c081004001606c9020700001c18555a80c01660400050085521011004550007540d0400254070b0300401c41d03903001c1440000d00c142d400340050040e0380c03003a80c9240509200480d01c410413101030b20024413400c0171078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 958019919 1250 958018669 958018673
    0x16060c1205031008190b0603010b060f07031b11010215010b090613032012060105130b01033c0b060714150901020a030b0913060b03100e010203071416 66
    0x4041c42c3c1005481c0800402c00d540d410307a031490220024111402c82c6140c05c46031050161071910980d0150f41600280243d016601c0007901c05d1152102201040e44082a00e030181031190703019141b5021805042c4034482081e0902c102055903003071030203005225694000c036095680015541c1242d140b07000305414001c3c018104180c43e0400c140ad640b20104a041c00800708003004c45808441d4400da41d00359899170b1510501c210b031000400d000b045507010030300402071030300e801102c102402600c0b01d00168002c20440100c000e4410581040458410348080c0b0404140344500c58030000300d50385080c0481c0580383c0501d001d44084103091b544c420400e10840c004540c1080300d80040d10502425900c0c0d03e614030703002c0341040300c00380c80b1070000341e40c00b140700c10382540c042c81031440c240c204888000091429050302da0721500c80700c000410341512920b100070207841c1008a02d103203180044c03090159a45040c1040e00035001212004c0008030304554100c0c501c900c0c1411994081d410b207203112220030b416 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 958021169 1250 958019919 958019927
    0x1050703062301080105090c071e1704030c0608040f0b191b1407051501080106050109350304080111130f050105040e1b04060507060b15071e0506040516060c12 70
    0x7040c948d09502e08211510000d00203d40d8602007074031400c100d82c44404a814009080d9100c3c201314814000308000500c0412042001030040783c105250001080e07a6610303100201c00389065004060b800e00c803090148c0741000b01c1000d0010400c0c000104600603030545040740d4140044026408101014030700046450b00c840144603081c040c004070745042a94412016207180242c1c4a1422655144410f008541e4007001460041c402000751000801400c200000d011086a0959003201104164030324154018020354000b003500d04001c120004444014400b81d0b070121001c1c031070002c1010004200420030071103070305c103a80046c0d440f10b00703040c1440c125a14681c005401001f210b0f030307141081030358110400010301c0500440d607110354851541d8038000c3d0555013900300140c403030310318a9442c01a201c280801e4a07005500800058242c04070380e40700504006100c3c07000703130213030081c1c0c4204000d01000050b42c6240c003240e031418014050b61058200c440011aa40081860040c110a807400c0c03445 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 958022419 1250 958021169 958021171
    0x80a050f011508040c0e100f0b1215011107060518030114070c060605030d0c03020118200f15040e0109050705270d060c020705060711040c0c050105070306230108010509 74
    0x41105c032000025114012241410001c480c001d0a03d10000ba040c4015045800f10a00070015070300c400c0c0c144281e50316030b104d901500405509030210351081c161510380c890b07410220f02c0d010320b07415a8529900c03090010866400894000c007402e450f82011041820305100f80a00000342402c1c0300519212242c0c215400e40b07025800361405604c901d0080390580d000e020228a10480d500c5041d1001000e29001c1d00352030240024490940c0d81001c1d40c404643c4090a038041490040701c00880810f107440081c07200c2c40c00ca00815085021040c000e20050003540c000c1c0140e42d2002c0b4081c407641e036111040d006030348080302c002001031024041e8403004c00700301c1109045400f0310040e070f000580c0c0040114000d04440300301950701940f1048071444e02a018048000034000550f00180b4141d0a500c0b10a4490034000035070313000329130f586c1050860390700c100080c803a040d1b40708000380a1402c01d181c004024140c54000c005803e5071400c8480480d141d0062480d90011040c3c40b4041c441c1e18101c10040500c0d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 958023669 1250 958022419 958022423
    0x106120f142e0501060305070c080d11030405010e1507050403110111010c020c0f031615030608030703020a0c17060a0f020c0328020127060b10080a050f01150804 71
    0x41030761200b503030380340001041e0b08a000710848010300440c1c044a056040e1030060b070103030342498a46018003a541d41c0c8401840c0d071090308246042d9980ca01c7c200d800000b020b080505460859020051104012040d0000c40c6040d42c14001c44030700e1452030b2120846030358190f40110101c0c0c4200410000a2401d41000400d244141401c0403481d40c4082d2a500b51000112144010303049401808043e240622850910f040141c0003090281304c08402c641204000340560703110350b10180565a200c42c8607401071006030103502c083d00d8440703825103806907540742c1051088618060340380000c50400c0328844a80802c0e18101700600050700d400917140d0040840d0400d0781c511a408100440d4182010401800c0341c04510102c0c0c492601c2c00c0c03a45020502c2c500016008590502d480703008031107004462250141003d524842c40305410345030090050603401c08a07904032502001d090341d0705800c01c402d030740300f03082c601d40522950307031054058884d5240c24003c81003030480c07000c84130518071b12420a0940c814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 958024919 1250 958023669 958023673
    0x1a011e02012306030f06010b12091603030c0302060f0c04030209040c0e0c040905060f09061210050712200307200a050d0f260c13080705030106120f14 66
    0x80e009a40c2e0010316012911403490556407405210041c2030401501c1d0f25030030050080c143c0c81d41864a808800d01c80c0010160007110100042840000244811410007148101c6642d0960366454041c01c24a0781010950150040500103030410200e40380320351150241e801d402e8906400d41d42044084d900282c400d6841010030400840c0d20007158503035900403002840c50981fa14a821031910a540340282070314010120030600c6801501d541e0f8525803c07240440d441104468024801032074400b6131101280315504200910a01a030050f80d4001c0180143d41c05202c001c40d1300e8029032483d015030411451030b00d410030014068611a81c03c15884800b9110704042c1c14451000c10b6150841c400300a440507000300082480e000d402c090311043d087c034070341044c06803440c0d5202e5151072070316400e40d421911100000050050351540e02101c00e102c030100c1e0803409040d29a20007a566024901500b07019600e040c030b0110f030442c030442d440000d0b15801000623206480d40c0c6c0d1540d0034520b00c454054803074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 958026169 1250 958024919 958024931
    0x6040915060602070801271202280209010b0c060103080a021647070201110610050312130b090a05060d0f0f020a050a0e060405180a1a011e0201 63
    0x220300c03a018640051000c0c2e070007850034908012502d42110b090000c40c0804160007040300080f020055071210303d40303411038943d81444100382e4080c1c0c00d10500341c2038844800c40f003141000307803c0000c1111064150095400000c239a0b201d8448a51034414038840404a90003500100001180a801031030796101c103105a6802400c02d600c010b002ca04140c112092154041400005040030b00c08a241c0303007007400a04040d140300800c0d041c5540001c0605094241d0320000303c210643e4050981c0d41c81c800807803011260b00380b030103401c0302ca1004114001c0038424042d41d090404400d48503002e9824001c41003035911a01442c1084012084d4005102c0d241c01650700600000c142e9600e202030b0000792111034003c5900c104202c00441141c0c0d287c21440803891051200307004060340302e02505e030114180d0802800c88060100098401e00035540700646c05440e880e606512107074070b02c031214003910f5422402e1002821210207901907402c440fa00c05d0000701041c1402d04d0324507480740c41e0000001e00c6d00001031030f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 958027419 1250 958026169 958026203
    0xf150102010e0a0f1a040c090c020a141c0212160c0305030f0a020601120f24150501020f0105090607050a110313051003090b1512012a09050306060409 66
    0x51a0300f01500b50780101070401403070309024850700107512211464000d10039900e01595907821440e1280103032440c19a407040040e403903134000c116103560250004140140d03d25040d0807a0795484d448a0041002001103402c10a12070000600c0c01c15142c1031040941040700d14100d0194203002c2940507a030140c030a610000c08200207200402400d208911070f25552040703e04064601807043c1c2c404002c044403c25450007240300c210032243c00741c0d406000509400616140c5195041c0300402c160040c03882c01c80d19024440400b5800310840c0e83c02e80a0303e4410495040541c222501121800403940100e0000340c1e40d580310b20000c0003820001e081908001c603001c0603003441c40d0001e510440c40e80d00300480a200510341a00303565108402491b0a1002100a0381c402c0e41d00100500408400c400c0d1814440380d960f01c40074840003c8407500b0080142d00000740da151600380344a0703a00009a299100789030310340b0b40310346084400e840c0003800420243d143d240070b010040400034010390751f0700c20826003008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 958028669 1250 958027419 958027423
    0x90207170a02010606080903070203121c0e0c01260406181203060f120302100515180109110403050c09040204230709140f15130902120f0f150102010e 66
    0x14541d40c640c0002805800e141d4054003060b8058036581c1268824000c00380160740000311030b011003180c600d1503a11804407400d008130713030b00c1500d880c5184907042c82c1079100b0b030b5600041d000030341180c2643e8071041201803402c0500300b40c5e030720000001c0c003949510008020170a01c0e04400722644540070800210300640c2c9808003021070f0381d4101c10001c0d880e89010800b00d1007521f031201c054641d03c00c49205030440c5942c060b40d10b5100c1c420b0b03d900c01d601c42000031000d0580c0009a035203004090840c656074403a50440004d204001d000c2c080000b85054110f039140d0300e002c01038805480d03015008060001107081041882c81b0020f0049a0142d140c04441f010b424802101820f1411400001815414102405050f10502e500142d0803034400040111042e0f84294030554840c0c82a6243c0401d1044403940c44030900c0340c10704219003031100050001d00345841c2c0e4010806c0101a540b102c2c003907280c5940807001840c003074034000c0b03c03c020900400c950820811450002c42014000003910448040e00d0b18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 958029919 1250 958028669 958028677
    0x21302030705041806061409030a060e120d14150a12170a0e030c06031003030c080f130303030c0201110a0509040605030708010e0613020102210408060a1a0d080409020717 75
    0x2916440e05c4203000c000130ba8010610546c600328064129082c1881d401c0404d5440d044010041c120035150081e03a140c45c3d501307220090384019451213407940c2c2c111600c100c802070944044043c074000519000241c00c103081440c910b050080041203082d925103081148003480712070010507100a42c0380c0300500610071260703004060260454480c044941ca1410406003464042c01d25103002d10020001c02c41d49101e0070040038141c80d8141404440242503041c451383e1030107442d161564a100c00561015414903244c106001c0724829502400040103900080b405e94120140607203840d4003e000311685113004002174005c1d184060000114150350381e0010b45045442d905c07031100c696481703802d209060000d020003503101c6422421307240300b1646640000d41c0e030070502080d00d241c02075004680d156103540704100c5004054400483e007140c10240c42d0f085c004e00c902c203000c503207402208500306a0f5007425819012405d0b0017894041c1410f251010800c003960003618205d815620000a0303139101c2486da80a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 958031169 1250 958029919 958029959
    0x30c040f06030e0607080903300a0608190b130204090605011412030c0703032a05030a1d030727090809210c0402160f030221040302130203070504 64
    0xb03d9075800d881811070602c40003070041400c108442c81045861000041281c1035080c944481140c112000701e800303000003181c0c41d940003820701c8140034400c960703c441d0130140513941008145d44c044240c948042101c0e0001420092a5141080c000703004040d00200f80c00302a400540003103103010f45581c6034008c407042600182140141040d1060060032b08419034420405044011450007100c0c0e810030b59202c10510000f810041015848500000398518a1004034400014400003601c1c0703240140d00c0b40c12100590000404000804000d01800240041c402074041e026000300307424408503400381803511404004d50a600c2c0403840724001d80e840381c2d0028500809035183c86010440801103000c0c09058020002d400c0c094010031990808101e1075504001110b0040e51103460036225507142c400c200c0e002c1c0201c4020703000c5005042e00800c3c1045424881c808103a4012048183d0160300c2c015400007030f40110808200d9000d0950070382c01182c00c6140da0500f075040994540b03444503400c882d4216 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 958032419 1250 958031169 958031171
    0x3020d020a0e071e0906020c210d09091b0e10140a080a11090a0b031504060801020a020105250819181208040809060d091202011d03070512030c040f0603 67
    0x1141e480c130204140705400310009031030009162840c2000003980c0e031258001162085440001c548440a03100d0182007801c40004240e0f103801c031340740d4030181030504d04e48100e075000c6041c07003038500203946501d5042c2100101074071070f00b0361005941c00380800012014503040522540c01c8010340655044405842440d0b0260b6504606240c01601001a20040c0c81804405601486521043d941d84500b0f101a1058951459200da6500302d440c1d02d020806803019400500e0000080b6070704c14103400604490784036030020310994a0303031603400c8602c0c21421040d4000c0c8082c03900c65506107200e00d5602c0d400001400c000f5200d01d440b0400c0350100c41110b941403030310880c1101c400c0204140c0030300041502d5002e05007400c1038034203a181d040182c42200900d41c810440001c0e0800c2c0c14800d230b4402d2044c1e6401c8004114820075580002c0d008200280b0700410040050b81c0704c0c844104000106c07100d4582c400c010f0310503001c00031027040403604040c1000d41c00b454140404518491088000801011503540c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 958033669 1250 958032419 958032437
    0x19031a0406140a08070312141204060c0305090604030e010c02010e03010c090f080c0f010f02210421021c02120f030703030f0b150a020c0604090c0e1002060103020d020a0e07 76
    0x2c00c120028180c0e500007840c4d6048540308001043d203040d5540f000580c00d0900b60301a072a80c0c5000c00040c8180390010948150f0325090000780700720f035400605071600580303041200361904030119540c3d001c125002070002d45032901e1105079511408070160041d10605141c414640e80c0c0c0c0001c4c0c00c3d20380c50704402c80012a5040c041008101100725003006020306d03005048048511000309042d40082ca80481c1802508452252568800c200e80c1c062140c00b9070b4045001c140a880d000390a510070312501040422000c0e00700e00c603501c01400da040543d030042c8420022010101da50744c0c448094582030b40c1c04030488020840102081c04100e01400340d41001d0355540d91180790150440f4010984603c60a142814842503515040059425909074803042521403c4003a422480d0009601800d43c1112000c20700041c85945904a4084060b86445282040e60007509100a500307103c20180d0050744950010005070a03d0580300d88500d0000d0301c154504c40e11540d80043ca20401c0e01e040e000104048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 958034919 1250 958033669 958033709
    0x30b041208070c03020c2103031311030d08010e040f0203030d090b013618030e040e0a020d080304020301062301021b13050a060312050a1419031a0406 66
    0x604001e91242d89418014600d08481c3c03002035a40c1420341d103d500a08144000e6005000c9001d011a08240c44104036a903d03d0600250b610101d4400e1044a481608560b042c4007440c0c04a0840c18402040d5a981c12507840d0102d07801e2030090180099400301080c400040158800340f006042c0c07441d01503c0400e54015a28000894100c142d206644a01001a0030f0301d002c24035064140418032100c510303512040700506004000c01143e040c0c0000c2e02501100802003581140f04082080002c440410180d50f50b20081c43d1200310f40700d8025848002d2056400006000401031030b0001e001400000b40b513030701c46844485a5140d40d01c521510000c181d2004001c0da810000c00004500745400410814540c1001c00d644a4030400e0b6a103140e0703154000074140481c030f81e00620040d5081000ba01c5114111100545142d1040308100c001034071004070246061140780c12101840351038400308031201b40c41241240180a00803510102c425607800c0711099035181d014401c05414160a008410702d004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 958036169 1250 958034919 958034927
    0x1a0709090207020f010309032c1306080703030c0503041508010306180b0a020901031812110d1407060b0a08060105030c090c0901030b030307050a030e120109121404030b0412 76
    0x1a600c540c040500421080c40181c4550307507440d092000a09010620b98124501913441e03046141c0d0785001100c50700d0004030300e048903d01261454000f0382d114400b50340000991800d450190213010b0060380500c00c02c00009104518200c6810b0040f003c0c1c038207244d11f41286c0d0070303e0000320680b240020b44000050051015901c2000300140000e0407107820040c89231341e40000c03903070f0080101c000e0a50100d424400d5900a400c1101c0d0110b040c80403000042c0a0300d08503104a200409003c001101040951040d610014140c0e90386905502d0320001d00703804202000059011010860f6400d031929a42c41407512480f054801900c0404041e2005604020078149060400340c1000e20400760b000c241310360a8120340440e108600c0a00e00442c8a100c080f012902d0352092100040c114401c00302040181940100086103112045801000c40317080d000704070b8242e035424080074245a000b600045038840c026208210031200340b4041c03605080d620788400792072000895040d1039442078580340325122a84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 958037419 1250 958036169 958036187
    0x5070503060a080c1005030c16080d0612051009030302090415090b0301060f1505190f170106050a110c040213050a060503040c0b0c030f0c01090203102904091a07 71
    0xc4080100a1001351800203100322180503140300034444008049051102c40204890791040d041c86032520031a036a25100f0310540c40110485055460007a0110741c102115005540e0550032200800c050815068400300030714100c0412414954200140e00340341e251406208051540004000c081a207480311010a8946a2031942d2080c1d2500009100555610f810242660b1010b1010304255520780001c2d40d05208d409400300805168109034041c131075000c0c03002004080d81e5030302e8141d0300340710024105840e83c007805400082138040c000801c45511403011341078529804c03412500030085c0080801c0c12031340948003041d02c20021413000c0c01642400040c01000380301e149401d92443c54140c640144021440c010070484140001c3c610031250010020b80311100280c1800559030b080b984101d034020062124224000c1c010380c0060940c480062040744030f0600c400c2c1340d00b40c100e1407501d00d00e41d40500368482544d005650b0035000d0041206803000c48018848403407400d80d40c2c1040a07002d4000f402d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 958038669 1250 958037419 958037429
    0xc0c0b030717090d05090a030209100f05010e0d0b2a130509040c0b03090a02040f0b1e030d0c03051611011103070203070b030612060a2711060901050d05070503060a 72
    0x10b8100911640070800902c003211100b40c2d1070455152940c85000901c01005640301941c407035030000c103200d003103030403240c0000442d11102c0525650700d40c2d600064800c5001010050350006c20719245101042c1c64440c95130307011030b134818543c601700d07000240480794101c1d021700a1910400405d11403852020b0403a102e019040850340c1400b0791400d5a82e80083e4600e034000c0c6228010084080340f1601c20401414190070b0340100284480c1e12601a0b400041c544040c00900c1012032005120249a0407144451000e41c01340c0a031128984c003000954205001003021020440100a6a500c01420b0000ca101032441100c2c40314a44e601e10300014881212004144c103550001c00c40100187d40c00a486030884088105040c0c0303aa0300c920001d04194201c203010003141c0201d004001c80c00640f07a1180c4402c0b44c582d565003942d81d14811626404450b1901c00408507004000e60455614000000e44105071052608510b4019248542400d88038191000c80c00700b000401400300e00c0c640300d0081d001030a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 958039919 1250 958038669 958038707
    0x30d060503011427030d090b07081312051e0d0e300c01152324070f1202060f04150506010207120b1008120a0f0c0c0b0307 54
    0x2411201c421000d07810090000080e1004500aa07001d04d9911011070741c2c5603058805403078070b4002d04a840c501401d2162002c468254a00c0001030031240240e00b1b40f8010030110186018401580e520001d0058507046210300b440f00034480e01c90440d100f640e0520032070305035411280c0c64030001c5024070180c48035814001100d400a805451030130f51107845005080c0000c0e409282035101001110f0f44d580724420440900307500300540b0348001c0d6826408002281c881380f07441140491099000031640c44400019544104089158401d92071008481048203101e4030605240020b1544ca1317280c14244000e084452a07036049018001c0c0f80c0501134140e00c061026502151890542d45401d407010484481e40d45481c2c1d9070f804601e1300c1e4407c1103074030b02901d0080250a071441060510000e507040403220b60b4000103240e8008610b40c00b020400b9110900c0f00c034411814203034003d100360342d18210006013808102d509990704012034500c1080b40c0080c0302c1181c086689080c0b62000520810301070804003255 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 958041169 1250 958039919 958039931
    0x110102300702060a0f060b040806070f030e0d050c15011e060c08190908160527040807080738090c0f0102010219020c01120b24090a08030d06050301 65
    0x450b40105915901c00d00d2407400003528440b000d82100100034039040400020300104005c194041c0c0001c40d036000d00364544402c50740c07042d02d007400c034182e07a10301203031080d60f4004136208140d03140928080c0405000000580d60b540c8103841100308403130030990203485100c0d403201407401c0c6281018496005040c0603c0e104003038095a4035241080d119100400c41d00c3e103580010241c40c03900c14040030010b40080400d0381e00c04a18132804d07080c1c0c0800e500031180f00d0031400c0004825a01c1c5040241d00190040304140700075980d50300d40c0001c50308400000c0e928400204010030000d46894140348183d0b81c04121a86015404001000c0f004800502010071480031001c0c440d403d2800508585515811102800c0c0c9565800040340603010b80203a40703803402d011440010b80c207500860b04542c41c40e42a682c23000c2403202c5101c400262000010300713941024181c003c50414400e40e1031030807500c041041803076103840ca1560104010075250360010610f90808120a41201c40a000700c1c80241000c80082c010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 958042419 1250 958041169 958041181
    0x2010f18030803190c050a020c0d0b010e280203072010020309190b150d0b01090b0a0e040f110f0307090902030c1906031b050702010e0111010230 64
    0x54240a01024100d00703408400180d0104034038031381504003108040144044181c2c480003401c01e0300001080005806040d180c40e00074140b0b0a45200c0441d000030b0000c804c0d92030450034407500ca1002d0000010b40c00f481c0c604400a603100081504541003d40d001031352403a044c44002d02c408640b8030b00e040d400c101c040709403038000780004100c000580103007001039076038407002c00551402a80c60760610200da034903001441400f2100045612a401e1501089510007a547c10007480e1442c0060090500d0715860050008030304c10392151400d020003a0203148607039100d090568810f10101c03003c8076101620011203040182003044105803074801d4807241f8810b00d40100084d103460180c081c00080710b5986241109641d003c005601101a0282ca02d091600301110000c1c01000d07107005480c042424980d194115220314480490030b04440d81c0c07031500b0520340398011a4000d4140e010203040000084ca240c004a10030b100a0441c00d0b48400e4481c1d84410310b4154008503000000401c1442c0048410044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 958043669 1250 958042419 958042457
    0xb010f030f02090c2a1e030717070206030f16230d0212070c1a010f050105210901060306060b070f080715050726060a09020a120e070302010f 62
    0x15034950403141540d03640d944a004c403689010b00c5043e480300d002c01180302c0400302c40011002c44800d40c05400e540c050310440c1200c41c410400c00e40c101005034810403803000451242c80f43d60a2154101501038604542c41c0c000800f9900140c07194000014010217000c00000700f0080032201c52158200b981260454280304451549103800111014600050501c0d0300c05141d030440e81954950041c5207071034181500c005100c0e85840c0c608441d00f0a400954078400115415031504030303010080c07070200d5a810300c001110305812149101d64411640703441c051b40d6650841d201880b44044000000f4030610b0340c20544141c0d0b40e9684140380c80380040007114042446481d00c10f01d49904850000c2d90b404d01c51500303c0c0c2040d080500c21500a1410040c1f004c4540d109445881c42c0d904840405071a004c1d000b124030802809a44060b072101c40c2080c1040340c00e616401038140503129040000c0221651544c180c15944162540c00b5250840c0754140b0440d0b80150000d552204285084200400f0a81d4801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 958044919 1250 958043669 958043693
    0xc0e03061611070801091b0b0304060209040e010507110d080103050622050303040309030b011512110d061412030309060606072a090c050c0309040b03010603120c0b010f03 75
    0x122240740100e008096550040c2050b04922420104850042d03a5071662640200940b130b40c21a510b01e9800c5504030420050070b4a003040d90b04000380c041c61070300c4a6a86000a52040480341d0b000b940307402000700d014a00780300e0b491240c0703440e0301c4000316522503084841c2404280c0b1024000d02200400601c08510006000c51340300d400f0308500c02da0094030b10182c26282e400c1e0000208148400000c1004041e80305034620300301c030711540308071015988807041804070200380128040040c0d0740b440c101c040d412103034005c0e43c1d1541c100c41c4001c0c03805d0005a25501558200d402180801680094981c071904200d100d03110195003505c003443c00d5042c040210390f01c9020141c4824464100480e040e0140010002e52a03c49401c2400704410000291000302d000006032180b40c130220b291840c00d05003540100c00322285c844e13094010b14502841c4000300b2000b085913840654140d942c4200210000f81c0b401c5009080d5200b40d101c00032001c000b41341c4a00074041c16085100e0041003090b00704006500e0010340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 958046169 1250 958044919 958044931
    0x14030f191404510e060402040b0a0504111206060903060f0405161415040b09120312070503091018030f0e06041715010b19020708120a02010c0e0306 65
    0x50880341600490b0070441c101d40200301c12024811030020454444000d00e00042103c0020b071803000500d184107220708590100032055141e402980000f0018985a4800000217000800b00000c85485002040489400107070545405100041e80794211441c00c502d9035000108540441c54145100b0203e501c400001e0003032040f1800d10b9020408001702032001c801e02c2d500c050440d0030310329522000e030203481251103030060049100ba0040313404048400101e800782d0301c0c11498140703050105030621200821701185d9240d280001e104041508003030311501030041d2042d60781c20b502ea003009401e06003000c40b00b041101c8194034201d040070901e40e2000700e800649030141021540c070203c1c01415a4a800d01903049503100b88000340c041145245904424861121203007200c441c0b004003a022002070b0001e009030310407107106001c0307102d034040118029203540d43c044c41a079180c941d40310740305440c096000c40555200380e808910351404650910035420030085a00e03241d55103003201740110f9281c0d0340c00391003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 958047419 1250 958046169 958046183
    0xe011d19031116031b03170c0c190314010c0f031d0706082a0d090305040801061412030a0f120b030609010603120504031205090114030f191404 63
    0x480060502840c00030030115814403d4a81d100c003405508521600d450000321010030001005c0309600781030f980c00c1820350383e000543da40e218540000e20b00d00358100c0b1200c0c0707110380314041851542c0d403501003081c12032204104019201605500d0020200e011800c006526689084110041c943d4044503d40d011002c03400e0004904448041e0034070300b1403100781c80c0220f51188030000100242d0104619225088540702a040300c8500c0010a04c0503a05410f141d8000f02c042c014480040120f60154090a2003820176a1a00d541d8114860940b5176980c40300040041c1c000e80c00e41542880149680451003a0b0061450000034002c0a40030000135040b050412101c40504008244640d12030b1015400c01002c80d0b00341d10300121018080c1145e400112460341001c240e06154034060f80544059a40c0042c0d014075410380100200c1c0c0d2074014942980c1002140b1610350031a4151400a5000e034007140e01401d03591501c2104800002d2941242d614264030b4950080e881844005200d80c0069101d00c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 958048669 1250 958047419 958047463
    0x51b180c0f0904050403090806070302070203060613090b0112030906030b01231308010504060b04050603060a0509030f0f22180902030304080613061406060d1e0e010e011d 75
    0x14480c0a40610300d515a0484c2c50f003410b010a0607017200e09501100c444c1003c8900319a10080c0440036030068101c0250194031200108109142003885200001e11505c000115500c507500c0d189030056081e40072070310600b1072070007040501d5441a048806002c0c24101400700c2c200d203100003003c45145549044207611070500109a942c0b4240448880680d104400203082e40c44081150080000b920200c40e03080c9051100c96460078507004091044900401030549a0b07280c1e011000a0000142504802e0208000e5890305100050207031440600c00c540154803090300c04030040da01c1d0041241a458080075000800400c400414040d903426500c00c00466a015503101103865806a80c10040d00d41c094070007042801e0140c5030309404610f001e05c009000011000c0145010b401098404c0c5800001c100100c036510341e000e1f00f00a15405c0e803d00600e10600c001c0c407142e8212100c0c5042d4100036511094100202c1c0070900410703080042c1000d40c0310020400c000f40640e242500c0947c0040d07816001c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 958049919 1250 958048669 958048687
    0x50a150f0806160914180c090a080105072a12110f070b0a0f0e0a06170c120406022802070906091107020405130f050c0a091505010813020409051b180c 66
    0x29100940c64444040d814106e070030604400b10440d004610064003070074142d1000100038405004481c0a000070351107929140c42600925000c803401003908880301081d401748240011508094040b0f4540681e075400c1d4500b03090418242032881c144480769070750f842280140084a04401220a94460382c1089507800150510980345507181e096516805044101d000881540080640310b0b441e0368983e9030512030380c607901c180c80507000c1c03031500100c071455007030000c3c0001d00d1540c014411038010658181e060003040c03c0f0461106140e90b44440181c0101c1e408004030380702030080c0c20180180d9a014880d41d85035104941c0d42d0f0044a90281c071480e03c84c0040f80c807074103004090025203608000148590802030418030380c0d41404485d150302a40c8000300026410303000b4850034500c0031032009000309051820004407141038001d4200001400c3d28100c02c070040e41c807445245040b0740300700301800003e03905a180c428828859038000c0e00810101a6a0004164050340a580020035101c515150a040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 958051169 1250 958049919 958049929
    0x5010509040e0f010606180806040f060f090f030305010f0302060702060a03140406021314090f04060b0316050f0607030903080c0106270b0105090303070204050a150f0806160914 78
    0x2104a4599405501860480345506400190a840140d2580124090442e03001d400001f118810068560044004036000645454042ca00b66025200209846c2c641c4000741045826854040711034581c001042010075826019480c014500c60380900008d80ca9900403550610408800034404c50002882000060007580f0807039503c1260882400a803400d441d1200080d40920110303d02441c06040004880c10b4a021198403550050042451501c94803020801318201900446800d80c0380d100d994660b4030104100c0c00c5003080ac0e00c4144100385450184004c005090a1140c02003600b0420580801d410030040001c60340e0002945c5c1d900d10303084001030b004002a8001614052151040400045d0816081c807000c0131104020021040040c00554051165540f183d401d60005c0c4940e0015241950119034401c141681c040380900304a1401d941c90340c4250002200000c20f00010700c01c40d6800c10145500500c0b030001c0e900301d002e200d040508035102d584070f56102e00c0d00c02c0e40030b451140c4071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 958052419 1250 958051169 958051181
    0x20a1a061302160f0c0810052215111c02040303050307050d11040608090607080103050c10090509010b03071d01050904230705090111190201081f08031903150501050904 74
    0x20b080304c5100c1c074007458100920900c0344201022403140c0c0c0800d100440c010b105140c090f562245400c41c206020354200030032000b00000c2aa0b81e80c0030101052100401402040c40744460b180b11165143c207900120092081e04d2642240c105106000500c0003c2e0410f00300c0e5004040c504180c0d8807001185140c00c0540226040507020b088040340c0003541c25000300241c0c2c003600f40801590350580d1400030450b0900303000d10024105900071031796203695042c054810030685040340b0b0142e850603200c40128408801c20b81c0b2a20301443d001041140301c5038465582c06800c40150b08010a0f6084480000c01a0141e0300c4420710030b50b500d2904e2480300884540c40c411904a4a80b500031610709030381c020704150810395086001c20050400030754038150200e508130280194407490540c016040c0c00454281c14010001d03030341d0301c01c1c81d050210104030f102d200e40001c04801004507581c0d0310002d5210f140380d1864000d81c0604d8140010b5050590681010b501030303d0382841d00c01e4035807044000141c09052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 958053669 1250 958052419 958052423
    0xc2a021309080d241a161506050d0305180d02030f07031e0803010b0c0712050601080d1e08061f2a0b070302160c06020a1a06130216 58
    0x49841e5126082000303a201803c4a08001c02040044a40d12245407984e48a680e10030b81000c1284d060a03c4171601120784900710700a40da60407828a5242c60b031000014500d004103035141071b0900f030b000e000c08009000e071001801d07090b190714200c0011598068401d00541c12410381c0300802404956050310b03410343da10415900141281c480e14011410940c9441d03143c00143d40c000c2d0b0142d0390311030455050301d00c429013507800314020345903231b02c1d004000c20075400804d420b1940340158000040e00c07140300c0702c02d4040c9034040e40c0642115403600c0101c1d807402c0061300c2c00c20140b203409207d2550010814400742c089001d01c0c10220348690360b11001950843d0311030205100540590303041d0303c845a102103040d18400416030f03611100400f41d201901030017030b92072008001c110908005404903100750050300e00d81000003080900b60820741e0b00c0c010605483c3e04020016030110314414144440483ca4501c007203103580f1640741ca828103102203822000d0f002914845d00d034000520040c00b01c141881003c14075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 958054919 1250 958053669 958053671
    0x11010908040b031503210d0b060406050301090605040501181e0f090209060d020a05010f05070b15030d0f021911060703170703020c0c0f040905100f0c2a0213 69
    0x141c88101c050025001078404d01c00369004c65544218604000a1034100700030354006c3c501e6482d07001c0191448591140011042481e10f824841090f921400d01a0002c7d0041c0d859803030712981041c1120381252440e41c4001e10690610f0010042081101c008080f580c00a03400400c28402213070503600c1da50b0030390039807140340351400c1f41e142c00e4404158842d02241e44200c0700d04640751254030401c40c0b81c40419002035805206d0410800980d80150307001c10046000341083c03414025240c541114403d411142d501e00c5140020b1102094074040c0071514035051a403c000d40d10284d0410000e54446400c0110500d28403048010703818000d0384007098031415002090703070f0303941c529514004101d80510054040a080b10340c0100c5c24440c0680250303401c0300c2d125030046c5408801101001001c7e44081c050f150001d5440b013400c03010070001d000344040c0250412003c158540103203a0701c0121603e203003c2d1000c2110795884215541c100c05110586e0381d0b00380c03030441c7c0c9140c8903000080303a10014410b952801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 958056169 1250 958054919 958054927
    0x7021c020c0a0e01031110210203010504060e13200a0b040608010e04050303070507060906020a0206060f010908070b09040209030a240b03030d1a040c080f0a020906030711010908 78
    0x10a40c005112100a0401d41d03410114a554150f4a96002000c2c04010f0440c000402d0303201340d030f0800b00280c011002c2c02d440c141803c10040c03000c141c03600c40a02c000810041c2c00000600890a1900a144c0200751114002400b45842100c1803102500108024598429806907100346001031074112507540c0300078581921942d80b117007440c0103a0b02c03e00c039040101d80e110000054001c4c60b8101c8030311440e00070300658655a903200d0215255445204103e460569504131074006c15110720240044507540e4004041c6810b000f0700300b2101c07007081c0440ca030402000c00002d000c0301401182c080c0484050803206504c0d60101070001d40a0300940407055013600c50030b0000d20601004802c9600307014440b0032803800301607035030001c1700649040a2040d41c05074000c00072920b28400540c4072640803107811013000252843c1c140010700741c1e00a011a80300280c031460031700c006c4914401599030880b000c00c00031072912a040d404248280070040030203091080e005000241d244080d003040d00e2040d03001c58082d0381c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 958057419 1250 958056169 958056223
    0x4020d060618090b0117070303031e0204081e16170309150d05060d080f03040f050f010e19260d290301270503040504020f070b1b0405090702 62
    0x42418601c2034a02c13001800c00025414602d85078074024282020103061501d0840e1819400b43c0f01d115201d03051040341042c000300801a9102800141c81044060508648520a84041c0901001495819070070004c0000481942502d114080700d010102983c04d807256000c513613042d4045c01000039002581d1405142c42001148020328440914800c20021501c9030f0051200b01c0c254501d005044910820082904120b51405180d01a201d0851508041c0095032103d09201c07280380c0020350703a0b46801103840d2031141480741005082e00c4c00360880a000c55a150f500e8400b140ca1020800300ca091152107134043d0b0001c01301c4d1002403d030f01062100e0301881304044440040800320381c440c103208141d440405c0c41c060165144183e0301c4003e003602112a14001c0c04410320b8071070226880d00c0200800601c2da10756002401c60b8606000d0321944406080c1418001480014030100c03240e00c10300184d40d04400c030a4140c13419600c0039244102c513941d03001003e0b40b0b40000c21880b44100d650655a8003a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 958058669 1250 958057419 958057421
    0x203040809030f190b1317091305090a11030a0812010f061d1903020d05031b06040b04170c06041209061422052106060f010804020d060618 61
    0x60101d500350211255025030050441e214400000c4511180d04100407044c003060a00039056040b02e900441d5018036030280d134800c1c1c2d201281441588100f840420103446520b441c0d0000b401d1382c8190502031140d0325000d03076095100d584202d0000e100400c405104112502c0070021500025807000140f69200500600d5400d8854244611021020b52900110740c41d8071450341c0c00340e010f00602050f85c0c0ca0101008000c00c0450744004c07e11407070302644c000030245e512901c405201c6401600603580e40e03504100500e018884100c05041c00f45d2012080c440054443e42c0e4096003e0340103409840101c0440d0b44040007440342e0030000941c0e110b200148018030400c0911040f048044d80c90b2045034585d0381b10301fa1101d80340e01750050003083d0140907041541400012440340c4603404174145482584842c0001c0020880741c5251803101d5401200c1211442c0400c19142c111104803540c20380e01d0060b400003820740c00b00030300c024054050b02e00040100900d03900010042c0c800314006452000103071860750 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 958059919 1250 958058669 958058677
    0x9060310170a020406050f0618130221090c030d120605041103160816080c0403051501090e16271b02010f050408030f190903050a0e0f010e040c0504080102030408 71
    0x1070321031172424030700181500d81b649508240290152106091848150591400e155502c130030603005442c1c0e2000321040b0110340b00420341034580d07026003031401c40403190f000c4004c0802045840c19511a40d400710b6540d60014031012000d04e240b410841601038056003078003030107007a4401600306013402c0c6401d51900d50103001c2e501c54000c0040385802c002c40e6080846480d0f00c10303521041201143d40e00303030b560203100c0c0c91069481880b00c10118a0107542e90703101450000c2152031a00043c1035140140020300c040e00a801c3c621884070018880d400521500c2c5801c04031500c246003c811010728941070300b42a01d2402c48156a030380c001000308041d00981111020341201e500c0d00194a4241502e00600c020311030280601c0e042810703142503545009009000001c0940b11144e48080707901d200c0d40c411864058200f030310740f00e0b9071929150910858090404004004514330441c1000389021982e640400b80b0703124464100c1e0003003040d07240c954040e15984540d03041001c230b41d40004104410700030400028 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 958061169 1250 958059919 958059923
    0x15040201030513020a06120212150111070f0501050703020c0301050109020901032d020306060c0106120309080312060114040504020f070b01050d0b0a1d0a031d0301020c0309060310170a 81
    0x2d22080e51400c807901d000142030500254020100c6800780105485250f07402e08013201c0790740042c43e00e20412140c3e658680304070740000a400340c451001040f0350740100500c1b40003e01c0c9009041103410403840e041f000c5104c2c001c0714100140402d81c0f20a05108014401418002034001c004950712400c1d918042d5100c0d440c16800300f41005441c41200c0e54100100c1d0300f007860703100b1001c180303500284044069032020349040c0d80f202e814481e0880020080c03091038001e21a01400004c800c840746000303012200558041c117025002401160020300903c002c00c1d91000b000d103000c0b41100360300c1700c40030700900a0750084d41e0800d1000c1262003009801c4030050040750300590300181d4982e611002c0028019001200402490410b008142441d403241c1240c03245030007903210169032041d206049450711410180540004584501c900c1d180901c840031b401c0b40460035802940f5101c0340a500d03565038451000124012100000010001ca415061500240555803403440c1c1c164000c03000c0d0740c0d40381114042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 958062419 1250 958061169 958061171
    0x12006090d1107090207060e120a030c03020301080c0f01031d011a0406030c030f060902060a0503075a02030a090504270314030c04030c080c090c0a030e1504020103 72
    0x79401d14980124042d101e442045002025042d05109101003e50401d04088410546500310350070740000610039004c0c080e40c201c20442c0c54185075a001002e0751801c601002c245071040006204001c00444c03100107502090320705403d00e00100c80101c0081800c0107250000c0903c100a400365544190401c1e00b6440c94003600c1010201100c082004807422031000801c1c613071f201041000004e824000d00844a406007100180c061065004692030350701c990000380001d4030000800483c40e8111405070840300031411024005541912904040e10400400304032003c0080380030b5915100d1a400360016103034190b12507414080001001c0d5480d005680c148011602100740441c443c142841484000404d00d001110320006100c1288411030180c0c605508010f504c440040719201018000c1d40035240311403134150b985185080211042102d90007a840b02e07000b04001c01e80e290b940406c4545c2081481d204650b88800c0d282050b0000d244900d02c410942c043c80c0d5040e80341140d99100548140e000ba20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 958063669 1250 958062419 958062433
    0xd0606060917240c040506040909140a030e0111031e19020c06181c030905040b0612060103230405070614090a0308030601120203010305031b0303090c040b01200609 72
    0xd4080e1106440d988403c8a624041000340c00c1d0001c0412064010400e80344691421342c845022505c0b61f402a0071522100d52201d040c00d041040d07840e00c07000c1101d00500580342c400c819070350041c104008800c80504000140c008912001c03c1482140d80403a40000f12000382c643c0c101c032007842c940082c5000c0e0720003483c0d1100c4460060001c24101d07580381c001440989802e5440d18040588008495500d404c259110b02c02c0b0051480289000c0e20300d07000740c8600807031519207400c0000303855034450141c0c0910302c01d110281018020066480d0450000d00340411080b50070418038800e03940120f160040901070708144030610001154040a8842c69074448244000b00f41c080c074000d00c03d0303e540c0e0380c00002c0301500300080342c0143e001d1504068140b40403110781032864809001c1e03801c00c1c1c10036070355500000b640100c00a9091141036080b400038001d0740c00d40c0380000c205501c0e8007018644c40e000d81e4840c1b00f17030901e5a210354003006a42c48031400350380312108a682c41507614401160364075a50720940b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 958064919 1250 958063669 958063709
    0x60109150e0a1a190b1b0d020606150703090302060d0e0a0b0403020705100c02151306030614190e090a0819080624130803040e191a0f0d06060609 64
    0x44041350f10307803c203c49806858902d8400b207a41c44405101e1104074030307050041c5500c80c1030000011407817896004240f03030b0031314608210088000ba0381d6880504010411000080c3d0403d110600b04c1e50100c070803d4864001444c0f120107081e000c0c0180c00c40380035100340c68040014182042d070040b0b0080d401c40c4d02d030a40b03610901c5020f02c0980c0641e00448c0486218000510706200354003031303865554104504004040e40400103100c1c1e140c2090b008207850b02c0c000d00140382e902c00341c240480360071aa60040c03c00d1300c8c2e0804040f02d41a00a03807001e916044002072a9510412401d40d00a600102c1c1d0342c0d44040110351040c0b0018038070850400600703000040390081c40c1010f102e030b00380980100c07400040300c034a0702c061400d64003003210f1581c10b54800c200011140d0003840600000c106082030740495103844840b03280c80f5525540c001c0455450400c41031040c080803824081c001c0320503142c901d141801c0c14001038a184034004014446400c0450226900741c0c485600c8040f201c24098081003040300c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 958066169 1250 958064919 958064929
    0xa021e07171207030510061403060a1502030405030f0105060f012006040c090c0c02032d15071803030507120225090b1c030813060903020607080108010905060109150e0a1a 75
    0x25216802c005048c102c40402a003038131400a40d0054030003044203d208c6d0f40d0302d036403080d00084d0b4101d00c0c016800c041010010341c24240011a148525039000304545d1034404001001d201c5510b20b200c1c104421556215504510814581d03c0011060201c1d919403a180c0b4000d07800459600410040500300052442c50a00401060241076030090180000c10500d41c18070b48503005104c2c058000c405040d0000450400074444800390310440c082003011440c0100000c0d1150255480d0120004c0006030100040395000d17003503c01c1070398408503044104032040f9080386415111220f00c254683c0700c070075044008e240d40113200101c0f0603410b02402000165010850104001b0b80503981811654600c1c01c006031090344440e0f481318400d0a90140320040b0340b20a82120390007141100564400e03010b010325650804001801410b800c002030000d04d131659142d0751203c406202d03400e1304648580003100d00220122001c4064007103100800361919210030400090020580004030340d03400a600f0501906203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 958067419 1250 958066169 958066201
    0x1051b011d030a0206010302120705131a0909030a2d030c02010510030f0b0a06031209030b0f01081e0c03010c031a0a050a03030e01120218090a021e071712070305 71
    0x245802a0605c0d07884c540a005841c0415001420140a9104041501d80d036081d10246403c0c0e0000380094056a42003910703003070384650300619128540c082d0800900000010448564013960b240c855441010481c100c804a5194081004d08543e0b03901c260341d04680c1544421090940c0380c1c02800b0030f032031311068600c4501c454000036021042c00c801c0c01010941040c0c0c825084402c05000081940e580c0d151680481c0f00d03040807100094600d0002c0042c0007820111139001011410008400d524110b02c0340c0d55400039207150050344182c0780d0600d02d80c2c541402004200500a002448150800310f401401065a0f03e48a08021048000d90603603081c4112a2001c1d190050107a100450650b1010b440750046440c10604000510502d1250041c49001414101c20141e01d12154480b40d841084a035110007402c00c4c03075007481031021849044485c081c4090404100e401c1aa03281d550b800e0100c8160102e001141096000081d0207601003d52682e00e4070480301580c040040e6101c0001030011844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 958068669 1250 958067419 958067437
    0xf0b13151a040b030705032416050d0b03011b120509011104030b1909061d1c03150503151008030408070e0a1508030405010e03060615070201051b011d03 67
    0x41c180415085908069110703211600b030007000c0b80c142c2c6540e48000780c0b40c41194040e0b01c4034040f00780e05040e245030240800c1c0360402022000b001210908282c028607a000d0445c0f030b198030503180c00300c0b211540c400394402032035807410450144040c5113000010b46405440880c1300680c0d0f01d86000280021010300c58620386850356002e442c5860f02d1900c4640c5c46103000f40c1248444010031030540184a400e1051b80140d41c840c000c0401c000c3c5004812110601c0c5000f4408401c1d004102040b001741b0b03113501141014601420000f0f640e0b0508442034005400e140c000c140c2620910b90304002039840b04a5191043c0c110082e00e000c202d03200d0007021307183d01881c4186407280c0c0c04200188283c80c2c4880500f81e10590001c4006900b0120385100d0030384020382c0e8080c0c0c08603013000a041c4400e5a01c1500428507070401c3d401461941041d002050500188081c9640901404540c80003103a1043d8101d4900c1160035401140d4000101e003d81d0007800c49d148501e84034000a4981e1000702400710650700d40b04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 958069919 1250 958068669 958068701
    0xa030809030d02010b03060f041b12120201050712021c05040804090e0d052a24070c02060d1d1501050a06140a030e10020c01050a1a03060109090f0b1315 67
    0x144410340d0703642c00230501070012501c0c1c03203020b080807081d601420700c00c0c001000018054440381100e03003070940c1c884524810280031641400c4c00c1060355500300785010303a0310401040041e5034041d0a01a40840024100f0800640307003800140400c1c0940900076100b036444000003002341c400f8000907155540c4c030014403200455400d0103085501400c3d4505081c0c40d4000c40318241d1107000c0001041d0804c21441c0e070050054a006600d0b04051300d41042c6954005035505105031030400503000180700c0e02501c408018500d0300c42403034011448041d02c1e408182804102141c4110714840c1c000742501074240105400b070095018000307601849914080d402c001c0b80d80d0080c2c548180c0c0701c0200c000e041c58840021035480380703a00d49022020144010101100c035680005101e0801100c0902561a40002c0340990318040e80c1c01c104550f008568941190a030100002d2070001d40d141c11595607205820241022805c05c0800c217120b9100102c50146c5481070301c0482000f01c0b07100f08001241c1c2000b1b42000c007c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 958071169 1250 958069919 958069921
    0x70801050103120e03070314100b0405150f030c04060305030a110303040c0e04020a03140f0c040606080601120e0610060e040c021f110f0403152313020a030809030d02010b0306 77
    0x4140990100413031040c0c0542590300080d12030300c079550309090074840c00143d540068160304004056204501045004460a100d14140401080084407983c00007d108501079881041556001c2001c45144c031000740c0705000150756401d006440750089049000800d4028101924920000c030031a0300c00c50340213650f1194581405030154087c14002d00c12600117030071000c040003090038034054442040f41d0301e00030400702c02c2c40401c15040510401d0054041e6007405400d0001c2504034900079400242031034041c00790f8540b003c5c0350f405030404040c2c0000c0c40c00b45006020f02d41e15982c0c0e007041070320b0064581d205038031801030174407003140d458000540058014804640900d000c424402c40031502445010402c90f203ca14809942da0104141c0d0b40e00d100c00003410000c103d4100d0410740c50340c4512404000c44840d1000c00c04c000c04240c1c1701c00301e0340c000020026941078506001c806102d43c01a1060014948925140070075500243c0c1c1c107880b900c111081c0f80d4900d071050003490710803a0058003074a41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 958072419 1250 958071169 958071203
    0x5010501081b0c060a0b010207051c060b0316180606111c03020c060a0603050c01110d0f050c01050717090a0f06020322031e0504140d021f03050405070801050103 71
    0x1070b61510300501c81080c40401c0454802c000800c45140a03074401c1304002220103405001904d8200a0741c005030060091a94282103624804d42c81440507400003004120307840c110001038101881e405d003100340f070014150003081c00300200944200c0b4840a000400180c1d4a0f070006a60941c00d0410715923240d4403042141000701c11078683c00303034150301a04001d030400f00c80d84001410032004850a07601107569900030810721008010b0304041c80ca081c02c0c10540c0030740c000b449c142c9400c1d01d080d904050060440340c500324644a10100c075181c05502e0001c1201c1d040034031000700301910f1746400b00010900c03c0d000c608244000300c0d030322032042e034020002400726003940d0b1688082e4000503c5074030013040300c220001481e940d510001e4140c42c42990f0314900c000c5034807040c8010521aa0300d01c020400103207c01d000301c0211042600969004665804c03080085200007501d11200400503800c0903203000c0e00410441c0c25801c65400385d8480c9060303a6545403201009400c0f50f100f44009030150601540d00d640b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 958073669 1250 958072419 958072441
    0x60708011a25110d0602133c1d07020f03160b0a09060507090614090a05090406060306021617070201080613061a0702010e0102010902150a030f0606031508010501050108 74
    0x801e0b24890780b081d00f90300c0c00e0440041d640e02c0d00510240d60664000411403c1d041c00400c00070003401d481003030034500202000107400361641006521410042a480f41d109180c00364840100a00c816031024060595100e0700446004066560801505c905078144c84601400700580b03003180c160840222940305152100e048085000e462420416943e24441001c5119409510b220368000e4513140c0042c0c0c54510300800900b814842c1820004040c00010820781c1c03815140012120106c4100d059501c031820014002d20031a80000c20040c03001940403140070440580050280c012481c4640fa601c043d1109060703403044c1d03603000703001603074410004440d13141402e44900002d4145000251498035102c00d0100c84841860208520802237000360856a024010705606902031000f48050181903010401940410b80321100b0070320003054404410344664001210612a80c00074071007541e858801600030b052030f11030f81030150011040420340d00340c14010f44c2c3c12114180c0d125541c1d13603901603401c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 958074919 1250 958073669 958073737
    0x20d1e030f0b060d0203042f090c0d0c26010f09020c2125020310051f0e0403020d1d0f0a260f071d09070503060708011a 53
    0x1c9030325540c0800940a44810010304800340c45a10010f03a28245130510600003004c030b00a12000c02940345492400c0030b005a100030501030286c681d110103461307030340f0305100c1c1c3e004101d9580c00c00b42c03070448410b901c1a4482c0e060f03000035040b40040d0001c3c0c0382d00c5001c46000c1d1001d0003400e0b80406034050030400b8140c1c550040001802c0c000548412700409140383e250307220140109070242001050344420100224140c50300c1a00030310031030b00e03100314079408640ca4074411175518480c01d40d5030340002c1114010400e0352120044205100e901162501c840d1074400e00f068400390b0051017804419508240034004c0d40702d00407044070031000550310b1403013000009503d40e2480f40c0c0180c44131100140c800200c0094101c1d049000000c034414242d131400c2c45150078a03054014905910103842041100318005c1500d0a070301008101c2040c59840700c410910306070040d0300541e011300c1040c6c200002d16038802c0c05541a181e003810000440d94600200260038007510394083e040c0d0242d4650b49140a2200c40e0207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 958076169 1250 958074919 958074941
    0x618060c030a09061d030c13020408030703031d072306120a020c0d030b010c080903070e130309300312020d02070605100609031b15090501020d1e03 65
    0x600d15040000e084203065801041c00740020504411051002a0f01702d00e5075144846005440d01c04a0321304000655191208a0268002d9426047c6200c0c0c082294044401920022046079503407201781c6001801050030100d080f00d031101c003029184032604045011030458030500036460240304211100d004490700b0001280c0e011800b04011218212210b440d144100255400180c48099070207041d4100180c0c001560109481c203203001240360b0b002541002c01c0d07500302d69580c0e2240c040d6004130703107008041d412601207030140320100000c031003410381140403451280d61140c882a6484680d201c54024400d01594407444d0b20314182959686084440615400303482c0c03072101c400320030b01418100da1160b400184415000980700c0e040c48010b0044503000303800d40d41251042d0b494110010018032070750000614480c041c18004040b0f03099a8020b80103061181401c0c00d17920558540540b403070610384219030240c001c02e0803061066014180d4000b2843c007100d00031043e00c12100049004000c20000c4d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 958077419 1250 958076169 958076179
    0x912050d020c1605100c0c0b07020a032117040305091216140301060b040f0902160506011e14091609081e120403030c031202070f051011090618 63
    0x62100d524420084100f022110030000e6260904180c21300090104907030f1200d061000d8281e801002502900e07111f4205d850b880303030b0580c65952503c009030000400742c3c400303040501c0342000020183c00180c524802488280c84071910070301c076624540c1c0000402c86026021681c14082c01e81d041c104141000c0d0007a01180c29240d42070154540c0305c1d19040c1c00c0d040981c1e07980102c403140281742001d100e0301c070180c000440310a0900d49020b01101150300140500150300d034010406440d10524550f9550030554001d00f0360703401b50313128050706d2140400001800b0416070780c4c2000107007078040078045d00308184000e00180700c00d54030280714201d4084600800c8041103000d03040001d13403100c1480249480c6050001401800102c06992031a103040d064071101840d0082008000003074004180880d807580c54208050615030349210003000303004401c2c01410924080340320b6400c1001c08903113900b803a14420300801595984503c0d03280306002e52424641c0012003005981140700381c081002105180040c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 958078669 1250 958077419 958077427
    0xc0a12110a05030604060501031101050c0c120a120807021002030105060d0b032806050a18170d0e0312090d14030406060b1201090c1407060c02070b0a090501080a0912050d02 76
    0xf1a25000c1d04440a8924903591401030081081020401c01c0c442c1007464030500300303d02c00842d0703034803000b4a855140c4242011070f662603010106002c0c0b41c0c04a5000240b840c0c2011411a01030203903041120300c03070014012804008521400c03031080d241a41d1003d001603003402201d4800c000141390700071106503d84070fa1810709803020380400c81e04030260003100304043c61800500d0940151003001d045072200030304010780790811021b0984d0a0321595000482140d01641c0c801800c20607204460343c01c18400c2c104419201c0040c0000b0007401c0c02c01000080501c556100d0801d5070725544034888120005000700200d2150f06801d401031034001e8003d40700040c600c1d58414a00005a10260711813a070131000c1d05c010881005184a10b044040e00350034540416503a69103100d40c01e1141000003845166202080740301c0314400c00949002d820503a581d90760321030071038101500d8400e25101d442e001a001000040e54100c46006907540d0710b9000201c00301c01c038490201507503581c00035031840b074007968244 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 958079919 1250 958078669 958078679
    0x70303060b04290f0a0f030b0414070f020105090316052a0a0905010b120403030914030d06060513090e030708030109090b0f061305100803070b090c0a12110a 69
    0x500060004a0f290308008040c894001c04941d248079030072002c22410301c003d210601545003201c04820841c0b030000e1581c07090312402e81c0140300807040d40d0b0708207161401a404074800c0301c0c44280a8155a112880454200e0360100d00740e031000c9483c030b64590414130050400d01c1091030b920004500c140c043d1142205902e40c41e81c0c4101000788004c000b40c007528041042410464807110141640c05000e105540c10b12049c01c04e58410700031007104da43c00e040f00040c245441307a80b0100b02e0326402454005800c40001b81d496503600002d503000200303071400800242150140c400c940b888207480d00d6044009280403180710040c07103610480f42660100708568000a142180158003038501e04e4000a0100f0160408000186004102c4101d010401c801d1108903034999031881a06d01c40e102d408151075842800c2400300c0380840d403000c04244008160f0104107c1c1000b6441e00c00d04101007261644039942c010420220039070700c0f40d0255025800d580101065901c681c21482c50005070090086655031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 958081169 1250 958079919 958079939
    0x3070317100320100801300b150307120309090908040f09020a08070509090402240f220b120606041a0703090f080705090a09050109030c030806030303160507030306 72
    0x2035210f00c4807040c1003e8009031641381a503d4140300f1612440d1202c1950b0401d000d00c1840c0110b44a4901c844008a03080e18400c4060407100d50300c2544070400c680c8908185a02102580c84401c00c640f1902503040301040e00f0120900c2c200b5138580543e10540070610b010b11403401841c602c44155004a42000040307942d20780391070400300424a01c4001603440c0d040301c0004040c1c150207080f50081100c10401c0303014541d2521030642d0002d80484100c402c20940407034405001d9440194251850004540880000a070401402070300c459080b034040604814100b111000505010751001e41c1414002c0840d81d40715102e400c0e9005201034151441c1507291140c0e074080205485449903c03000008116017059402040381c00188a00000f02070b1003420301d91081d0300c2d901c081c0503150140380a18001aa04011900140d2403250800300030881c0051508006120380d80c0da41003070340420500004a2140e050020031070b4442c5404000f1481c40d519020f008480e2603110707000941c00c05031031320008181e411503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 958082419 1250 958081169 958081193
    0xe0a1b08041502130e10031a100905190c112401080c09181f06320d030302280813030207030605040201020f010518011a03300408030702040e030703171003 68
    0x3403000010f00301d1603e14000c209c1c0207265007007100c0b024282424842046ca1110010325100e0381c462001c01e03c6804001d0440300f00c5042000742503580b02e40340c1c18505041c1c8021030611505406500d00b282a038032880d15a90350b00b040d0300169041201a400196003413084506100c100b01507002303a45014111120030380c207140305c1d0314000c8442030307854800f04003045862500d41104c00322940b0300252425485107075103600036244205400780712010409410940320364100c41d00800d18840d4803058a0702101c10045144200c2d0001001c1000800807540442d00c103c40041340c00e0f810350080c6841411039031140c02a040142040307040d0f1041c0003a220004000b0300074544a2402d02c220080c1e0111803240d890300391a2400c007020907080c45841541c48907200401c030131102c6c00e542d0082d0380e20b000f01c0046000c442041c074940750240d02d1000ca008500e04101000400c2c505008541c00e100801c2008103260300c07489404002404103400128041076501280710b4294000518022011a02d940c0d03101c1581002e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 958083669 1250 958082419 958082453
    0x5210d0b01030506030607080a0213180e0304032619030905010507050c0715022805010c170402091b07141e070e0a1b08041502130e1003 60
    0x100108518540115030311900460900902c0e0038040390a04101003070700ca082c00b4207194104145a000140742d08016011a44440a00e40300304410569a061280740041c80e604081c90386820480f208460240000603038040d26040401154800e4103040700c0400c4600c1c181c07410300040c0083c81801410300c1100f094940e107030714603140404d0b44c00c402d00e0840d00b181c50051185040c40801d03c010300309208001100d03010f840111440080e4601c0740d101c240d107405c103107100c07080d07084805400100804003c03108410103541b08400a00001500d0081501c0311300482884000402c0c842c0c0000380545041c0ca19160000c0c0c3c0c44101d40c2c01c2c00000e041c081c0c4030b58465681036a5080c41400c1458100700d00300000400f298005409090704421515140c0c0c0383c403403600c954840b001601c0d0106030481210f130300001240c2d0551042901000c854000a403620720201c90070f0f80e0900c86038845a68160007802241c90610140c0240e20f041410700c07000f11480c4501a11803050142d5415021000400c0c020100000714 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 958084919 1250 958083669 958083733
    0x50d06210b06010306060f180807260105010302010f0f090b030c12010b03070512100e1006120c0206130f120309021c020f210d0818010e0601090905 65
    0x380450928248900024040e10b040501d49034003008070700d41c4507000c00302d40701040c038004040425900020035030122941004800f40036408000a400c440d80d140b030a81020500145c030005451410745508035030f024030010340800c10301e20340c0406042c41064107022100d09030030a00c00c803e80710182c06030260003ca406d450592800204e0000910252400c60b00616450300000e04c2c61400032002803040c082d0840d81089011032002050403207130041103a401501001d40c400e6194070701900d04901c2e1801a00c58140400d02c203201810444801d8003c60114650580007404aa00c90450481405800240c2954108214071241c00001c6c501401107c55089954020550401d680100300c484415203406505a4282585400042c0c03140098445007a6040340c20f40d5501c0f20303508814106000c0030300e4080c0e8a000e4038010b0b229203500210914040c500701303018803541d101d05003d080c1c202c40c120f40821013031b6413000004010b0070500790401440c02e4420380588a006254403540d4a240c60307140340030351890f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 958086169 1250 958084919 958084979
    0x91b060921020a09020a050c0a1a01170714040b13020301081213060f051902010e060105060f090d051c08011d040f0b0c130311030114070807050d06 65
    0x10075840785516914020764545020380341040e80040c42d403900c07070710400520603000724484840c00d0003070090721102904141982c1000c0100e140a00510341c200340807035400b20052001094115440000107818a0000c0c000c00503c3c2c140001070079410801d9402ca5401915440c1c11005500e44041c21400500c10441c0940c2729418003a0241c00c04450000946000c9418404030485989510400080329034604008031020410300c2c040301c462140244400b107048802214004a03981540115160300d105400e46010341d0b259001c01404c1d216480000d60200011300141d916031030440074010100d80306108582c0e0051101745034901384680f40c0f160101182c0e1071401008082401e2002c40071200105180ca88075107400d680328446980c44940180841c003901002824806804080700c060102c5080805107456032032030203015003400003003031074000c1d4248501e614240c080c0d40030303050042d0344075150400d0607900c07002c04440d0358006060100c015925943c0000c0c00903040c88410080e00385410300b05100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 958087419 1250 958086169 958086179
    0x303072a0305101407141608030f0a0614010f0e0307030501050103050601150c0305030c090d020604080d02010e070602061303140a0306031a0c0a0e03010f050717100f030303091b0609 80
    0x11106441001200311320480104207a10703600c405c5400d40d2418180c4d81c1e6449107064102e082e070411444500030704481d8000b061103030010031031030741c24841d5000500034044079813503c04411100c20070400c0c0d5800700b10341000d40c071001c074050315242c1d070541009001c440d841d940d01d40702c02d802e40d0b8003a80281e5035500000018400c0306091189109003003a5030070070500101c1c00e542c004000388002040c58030350520206426485079200401464210380041c14261074a490360155902c079541480d983c0300ad03600c2c0c0107449800031300204041c001c0381d4854000d8a06035460000d104025110380c4411410800e82c80320b040d0820022201400100d072081c0e500240d01811441d0044581c0e0960907800c0342441c402c0700700001c8840480c100c400c070003041d05d4107100603204000420301428140c0488111a0305201c10842e807154000c1001440c00d41584619200340c5800301180d000c6101806070000c039900c070503401d001180c060b030861105a0b200300600d048801e0301b440c034983c12000a030070203030005010b0041041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 958088669 1250 958087419 958087421
    0x708010603080403050d230c0f2d07050a090506030316060b1306050904080c0325020111150105040c110304031b120b0121020d2604081b030c13051e060303072a030510 73
    0x22b5902200b00040083c9420600001c0340d202c103034030824000588030000241c4c00e07101401600d01c5004542c2141c01001201c0c50200084d0059500c1c8a00481c0103012480d00d40b030050190404544e0050b09840c219152511003119a9000c901504001e100030040f0701020309168285001c04001350010324100510380c40010600040d40b8400c011030b0780300f008552007007030706602c0c3d550448204031400030b801c41c000d00c03090303030040d9403084002c981e8000404c001041c0a1f20b11110140403010802c04240c143d190020042d04244007000502200b071488014030000304200306984546143e160101ca0f40c03840c51340080c800300904602200c861341c10401c02d1790400c60b100e140000d07464500ca459401e0138204a009603513902100b04504144a000144e00020744040c49540b40d040006801c2c4d4803c0e203412003049015140c10f84d140001d00040c242c002c4418404104810300416004010f945082d0341511072a141030345260300d03109100d003840112914142200302c40401144100082c201528520031440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 958089919 1250 958088669 958088743
    0x8161e14060a0b091609050a1d0106050703120506180a020a020610052206082b02031623011d010501150f0f020708010603080403050d230c0f 62
    0x20050b07810400301280a603a1000c0d03207a88504071120481c03c84280090880b420f50f0168032081e00a40a500046941070380c08149a552040d6040b80342d0085c1d0381c1d108102c0e4140b041e00c1015001a424225007561000990040d9801150040500400010520400d140702e1400d462403100f585d40000d0344030310540c040c803c0b00d50007000403401000d1346203400013003041c400e4039075143c4005490722800c4000c01910780d403150014054100441e400e02201c2d901c44070410b509003521909508003207400071070562000003241c0741380c0801e403030039600b45040b5030b104840e0707001c803016001d400c0d44603030000c0900800900c50215804ea42c0d0045d15032194210322403c0c21a0010f07000903071b2010620b41480a101d420140d00c0c280080c076450516041082860b00b01d0400c507441d04810f245500b0403000004ac42140307805002903900400690f0381c0b0305144001503c00c00602c0d114501c0f00c05441d951510a0f104003400780c000300440e0420b490813030800e915241e06090704000034908001d00f003008048500d101c40b0041d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 958091169 1250 958089919 958089931
    0x12030f0412020c1027030222091e170a050f07060b040905030a090e130f020d2a090216061e02130e1806061903050327040908161e1406 59
    0x400174141141c010541000325150400c95041c0100300d02d22800c03495600c072643d01504245404041d404960129090428881041d10241c8040340344646540c030312000c51701515400c2c5c0f0303918a001c48000401485400000b0180c2d2407982c2c4540f002403e480300e020b42159284510040c5644401e800310161004000b0b8204441c554002c60030040a12400c8a50740246a08901040001c5203944002105040f1000c1d0041c442c020501a510a5410b0809002d40780074414510005175030700c0c2e900f52400c0b40281d0b0000c40b040f800c00c0c000c0c0701c0072584503400705140c190f500a0301402e0268401c919001e0340e11200d100001741050060030000f2400c132a143c41c2d0048121041d040c1014030240d500c641d40c0101034906072045040350500035000c247c400d070000c0119844015640c81e501d50307070342da0001d0100c0e58000c00016405c072412a036062402d031140301450b55001c00c8141c1441b82680003030308003080e400802c481610305100340c2650148406034146042d0702c1100000c0201c4e00403001141001400307801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 958092419 1250 958091169 958091237
    0x16060504080303040609021f02030901020118030804030e192306070c06050309030415030c0f090521030f0313050106061b1e0b071112030f0412020c10 66
    0x41c01107100110440ba0895003000c0c01240e43c035603038000510500c1030040c0d172640c1d110300c6051140c04030b60080080c01404400360020008001c0801c1120050344c1c40c503500500107036412000400080c01884400c030010800b130700c3e00020100c0382ca100b40580103142c0022000c2031404072402c00340030031200f5a514800d410756200b41440280d45c4e4864a110090003000300b4400040300084064000304160380007019aa000c10202000790720000d0700034030314000c0700700000b0010050b4100d02406442510100e4202034034200381c50803042001c01491100c4450700d00540001c200055004428001440c0102c0041c504071840550514116003120b08991000027404030191380c00d0803100e500c0e02d94602e126000205001a50f8000134010150301100c000284400d50030410b02c003513243d002002d2300e070740100c1500304c480301c0b00748011700e1550340022140b2401e00b920300e01c002800030743c072200380380c0c10f000240c0125030b000f019050014035103501110800d4001480040342440344402d14000e0010391000000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 958093525 1106 958092419 958092427
    0x3050904021602010e04270c170c01020624010c0303090204050109050a0c0201020c0309010c031403130b01120314030c09091302011707080a0c09090e160605 69
    0xb50036400580303c0440301907039007410b1040a0800070405084104103003e00349034a44204404002c441078140c1d01d40014091942a0580c0c40301a55200500745019510000a1404c6c0c4000d040380c410302d0f2030b0010b406d0344150b01c1900d032500940030310741204121103a050070303400f81165480003034101d8504400092000d080e80c1c0458042e031316801c018408a464080124242d004030384040803103420820007843ea541c000d008400846209040141040d59110070580b615007045842404210380803c1e640f0410030003200a45c050103462044c111000c0041d00c005040d01a001049412544008045010580c1880079a24024002000740c501d51600315610074040481050880c0410f0b04036529107a1050b264411034030600345945d41042c107546005814001d0003845050009101004034049500320680c000e000d440e5008000400441003182c03a541040c0da480e0340080308001c400c0c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 957913669 958093525 := by
  have h0 := BRFrame.cov_init 957913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 957913669 ≤ n) (h2 : n < 958093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
