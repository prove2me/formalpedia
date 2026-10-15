-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4277
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:05:55.420991+00:00
-- url     : https://prove2.me/submissions/77700c3b-8ff9-41fd-803a-a3db3d37b0db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 769064748 ≤ n < 769244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 769065998 1250 769064748 769064773
    0x9040f0204061e0302030906010509090a050a030f091d01050907021203010b070605010902160305031f080d0807020d120c03090803190f0606020a1506080d020a0512071203050a0b04020c 81
    0x41c030750940070343e19060440c110308200ea0b105a41d1401405010f0280c078004010941c41346080200310142d0740c0c444219243e42141d45401081719003c1075440000c02c0101001141c1e03024003030b582d0030440b41c07001000801c5a10309020002101c0d070141400c1e0079806640134400c01c604007a00194080c003946100555104a585056412288140d003c00325952050007514005100207081d8400d190301441d00540702e88843c400c8008000700b4515024440303d03440c000260400c0c0c0400c0002081c000340d00e41191036540c8107801d984a80104441c0700018001110302e03040000b0a511842041080f460f00042d41200c0c3e83e540161030f4402d44810f643d203082d00380c90801c0000140640500860200401d00c845481d207a0041e64480c080e000c0209410010910b000d041013260307012200403c0182e00b21507010b105500040e45840014200783e5460281c42e032019941c04030001141c0010340e01c00702146c0c4c40555610120010100500f461349496254001c5402c41d03507541c000382004011200c06081081d0096 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 769067248 1250 769065998 769066037
    0x50c070b0310120302030d0b061303060b04050702030c061306060e0a050402031e0c04050a02070204060e0711010902013e0c120a11060d0e060a02031503060f0c09040f020406 76
    0xf9440700c401c03825043c128000007035010068602e80107001e103000c01c8400d62140011414080e1600d0200000068500002803008940241c0000042503504205030b85078203804a03143d21030442d03898110790240001c500403429507011120440e009100014125031580e000900e0260107842c17603440c040d05ca81c20711081d46424020022120401c500003003200ea00066507d80b1032085180c640d02c501c1d91480000c4258000750100c030300141d4010700401c50740391600c41c04040c6100c207a03272500020b01e004460400401051062929aa805031100b20050900c800c100316107541508070000c582d9000b40e00041d600342001c880d8201d00d803011018101d9445100c05100200c488482e00c0016a448050080c001c03074040020030701c09106c2a07410076070ba0303940c60b50450003904544050701ca00d0b00c942d004001028520b980954010a411003085842c0c915800425070342e04030550b000803404030344402262003500c25a00510381e9601c00ba00c08038007070f86040c00c1d0740100c0c0c20541c00100440c200800104204801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 769068498 1250 769067248 769067281
    0x3030603030e0316060309030c0b0405060709140603180a05010e061f1505090a030c1d0f2e03080403050106140307030c030303050c071b05090a0e1c050c070b03 70
    0x1da0003090044441c00f00501c2c0c134102482800285541c40c840c500a08d40b040200304041500003400e4550b50425290482e55680c08a407a000080e07030403580811014840900c8460307100c401810141151500f0600e0745109001518103070151144030060710020b00207000d2040c00b25852400360040f4900012581240140c524102c1103c10350010305109140c2e0301d040c59540c2c40c10764030b0000e84034a4001d02041c80070f4078507000502000101c07000020141c1c10040c64117110a410150042181c4844801510008090b900350481d920000001c10007031103006000081101c2245007000d44555070789a0001755441078006403403d9441d5042441000c51070182c0c1d41246c102980180503951454684200e00a8280001000c05440310049280041d401060741c1c003007508000d115010b0b0b40e0503005202d07015058460a40112400000104013210620645501d6440c0c00c0240a1030301c910a40f54540c501944100c00a120043c44640700b0003a040000001400003030803107176070340d0501c40c0d08404c0a00b01d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 769069748 1250 769068498 769068527
    0x408120c3c0d03051302090c0a0c0803090a05010c17060f0a1502030d050601020609060f1504020412050606040c091404060b0309100605191e1e061701080c120f0303040303060303 78
    0x408400200181c5a071f01003241c2c08034007042d18540710380810303a00b280c405244007006455050017200744031050740c002c5801d41903c0d1244008110440b4001025210380071460350f03a200301c080500001d40d03103050403000e8128119000f80f06283e40d84d103034001c6240b42030082880d8030045c2e001280910030307540c03540b007260f4001ea02400180300d1440c040b07402c50b560f06d000410710310030f420303002010844410130148581070781d1400070020b540701c58407281d003000c080b00f5406096442d44105c10100300d039802c2ca0b12401a6800c2c441d55115422401c1c011403401c0264000034540d0029910400000d04030300b03400141d03010300300241c050711034100e003240e031a010340313107581c005030b11035001c045d4089103c2c84400c810004507004407040402c03c00300d8407a449042e0040768401a00341e003203440e000c16840c031888803c0b01070b41d01a03110745900c0c40790850b200315100424082d1040070341c001d1542450783d1800105803005041e01d0b208a902c501c0b44000d0741da08503002540c08502003030715240203100b0190404510240c040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 769070998 1250 769069748 769069771
    0x807030308061c080a180308072a090b030708010203040c1505090303030f070e121006060201091e0f140d11010203070905011803060603080408120c3c0d0305 69
    0x8003da01d0100c0480c0c40c1800080c194180050001e006038040e003084034400e09400f408828255580c03c1200c826401840201c404030b6508149600700300030000703065840c0b03150410804045003031071003c00044ca400c844080c0d143c407500c01e00140f1030390240011449244500950025503140c9051074407440d9040703813a141409010f00122646450010a89510117140036001d400740d25809015100780038000c550340d400c120030307941009003194001f80a0425444c004010070210740d9855049088170f5a48100400b1092104200750b02d440c1182503a0060a024421150a4011507980d0040241c0c0000960b02ca40d040050180f60715500280d6040349030300c2c44002580f4518001d80d0040500200d8001d003814861881a00d10301c02100c201d49602856010b60208586922410221450740040c4140e0156101d1031301c000d651040148150780506000f0130003003154010200303c0d410103014200074aa400822a620001081000440002c032600b000b4040c00341c5826503c4010b096440040164151a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 769072248 1250 769070998 769071019
    0x1090506030112150b0d120e0f010c0f0317090a03031107020d020409080408010c0203030105120304080607050c030d0606030e060c1309020f280e040c051801090906080703030806 78
    0x81d40144401c1c4116600003401d41c00c850500001390300a00c1410101600400081710020130850545040000c0c1002905d0713681c2080d588030b00f00034524602c115254009030029a8a5001800d030a0f80324003882d100e130800c0b4424403048006030281e10340031210781c042548641002070605816110303000201c00030a0f40d2610300500c5401003a00d00c84c48038002030103203503140b0036101408040d200f550b01411180000344941010400020740d650400c0c042c040c4030f40b01c281104c8040031030000131942100c2d0041e028140e6a984c40000360f425400c8441310312030380e0100300001803400041d0300c074207400742200e17481c0011000e501c000103514080000703002841d5410300700800820a810b9280c10401c031030072018007598900d2400740b41d6250340208020f50140780d0000c0d40000d4900080603c240ea58000c0359584018607011904000c00d551081a5820106008125412075040f100b810982d20400604143c10195900d10601c81110b0315a0721464050304180d200f4010550700140c410340002c800c48000c4801c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 769073498 1250 769072248 769072259
    0xc120607021f020c12033301050c0f06010b12060904210207030206030a020a08092a030109060212040b09030f09040b060903100e0d17010605210f0406290108090114100302010905060301 81
    0x12205247c030b0241408000b151518514804100c5402224468410f807141541e6404241c100380e000480340c2403100d002c400001c1c0d40d509202c032006200c3c5800026810403155460040c21028048070800d034118090204044003680711100254099040c441c80140d407010710607001440030310f02906c800415005407024003000015603014030803030f0b9040750140d61101c8142000031700400c043c2d10010300b042e00120303003600014007156140d40b05d10300070800020666501c103a425143c1c0f00c0d0341e091a10504003406280402d041076407124180c43c401030b01061510f520a40041c0c40d0103078400f40e0f10a82c940340e81301a003250409201004071003817036040c9914074501445220fa1030f0017050040a04000011408400606920b03d503105007161940c0c40d100c43c1c0c10000020110414201c909480440c203007500070700c1d802c206aa62030803000c0c00d07808901010300240d00444e4001c1c0042d101200a40d21842125211030040c903001e40160016029030206629500c00544a02e001e540041d20034502070004114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 769074748 1250 769073498 769073581
    0xc03090309030204020f0c06040f0203160b03010e131a10050604060518060910020312070804080307210f1508011e0906110c0c120607021f020c1203 65
    0x2d896045038090388403d01c00f400b00ca0b02d8041e2041c40352030361042606200c2405070f46480152558026004e459581d0421569240202a64421075030100001c0004201c40e01d401a090364103d00700c0c48000c10400181c0c0c4a0000d4280390a2914003845180c0007404150000c100d00040100803d4908506203441c002e80540365018040d40c80c0040c0c0d0000c02e00402556481d421101c248000500c159001749000d0f2000b9560380000c00100b0b00d8100072004034410600034502c3d07900c600d0b07100200d1441d43c0c3c1c8401044418540d2003560314010000c10103a43c1101c005405400c00350311a01a002804a40100c45032040444952101074564900030070400c0d00010305012000ca912611400318984032249800c1c8000c040d40d0010344403042002c213144000c0700b0045451550031030304980802c0c81078001c40030319480380c600360340308005644441c50860701c580d424108a0180004900014200b605110100d82008a00c1102e0382020400104010405c210942184000c0801400018010b80114200c81 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 769075998 1250 769074748 769074767
    0x60609012303130c0602210c010b040e01020909060d020904020d05030909043813150c1116141210060605040501030e060f041e0b010e0601030c030903 66
    0xd0400c9000c500c040000c030720410040c14501c50000110b95a0702d80000f06890180e040034003204c00d6000200300103055480000d50721191021a01107104540d0a601d100805505c0380e14001070554031030204020b40d5890303104240c9121036400025070345110210400c0314110004103290721a03070b852648507016858544000d5402070341510311235030f001e80341d050607403860003142c210542c008107041c1003000b080780664400c01d8840000890405004400d20164a0442034100384d4510006c1c40c400124442614621014003d0143c0c2148801d40440ba0b40b480030750302e5030700401e40400d80c54005100070b10420400c1030031040281c0c0e4a501280c0c1084141c508000309040e407580300c0c004e9000c55000342e103814040d2031044000e0343c004003c2e141d511600a40709800078440c66001c0b901c0d21801464164021071418402c01c0030809615060b07540e50381e0480c10302c1d0381e2040d108a0840308500c4100184c01520801d01800030300d480c820b040d10b01480010300b07480c03500c071f02141014105811000029007040380c18 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 769077248 1250 769075998 769076017
    0x1b050a18031721070203040312020f06041b030204090b0121200f03031b0d020706170403200604110a05101d040903120e0609070b16020d14060f0606 65
    0x3142d85010391100100905601d61112002d2481c0c4021300106540000040088a1051881c2100342c1c001c0e050680c0c03a0000032000426607040302c8000380001c0e002c601c0d08040d02d8000c2c0180000140c13250081000c44007138540480b041210080103000641c0d1082400d5103404107489480e032404416035410b4010340704c1d4044903c0318005501041c950b582c81070b0000300c0120014003100c0c1c80351542d0784005410035610410580c00d008220041154910101c0d0045c142c039001d13100c041c00b403c1080095021040000c000f902080b812440c1c68504001308031860f64101c4500e4020f100394205410465070f8091240305862181401400030899a25200820298019036040400c2d4409100c01c0351036103d9414420b090340545400030480070150004110300d00011001c600b0001c04032058281c0d0ba5840c416214004aa0b00145017002054000d4008014089a03a07800e40980c0c541a40032541d9038041203811245001480490031009000300701c802d910000300552200c1d00d00341580891082e1080807400e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 769078498 1250 769077248 769077293
    0x912040b030402180a02090103050106030216020909030d2d0605090601050304020a0b030a0e12031015030e060f0a0c02062206090503040e092e02030a1b050a1803 71
    0x20b015075032400c0503a00e84208012082c90369160808580d00258480c0110310301107490f050000c1001e070310902c2030301c4112003041201640c60142e034081200e40c64005190080f98030040100d00c5408104c3d020340e4106004107000419844e5140348090120840c40c4801d0031450701e0032104200075641c0d8001250004428207150303030749403568000308424030540e400c00d0501c5540001480010141640304c08180c21501d41a40c111900304074403220140300c00d1322594101000d200b0f007807180b01001c0c0580035489495040000d6000c1041d00d07030303a051210845100c4480d00b28081040314280c0c2c0740c0503070001b403070940c40948414980051030400c2e422a480d040340c18030441a03100701c10410142d1110343c030755400504994460ba43d8089942e00c01c02c0450b03840000380a80192861406509000d4942c003038209820021403030140c4c00f82d500290030040c4140350385500e540c030600d1241e601107452450004a07640361582d44071492030280c0302c281214901c00c0544c44400041000c50600a0001e11100030b040f00b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 769079748 1250 769078498 769078501
    0x8010905150a060206070f03020309060601030b18010f0e0105030a052e0203040b01170a170a3615050d2f22030f230a06020301030b0912040b03 63
    0x4800e010740e401c000041c1d002080d10b400800c1c82d80d000107485115903502d41e01c107030f01010b00840844c10b0340005c0d64242c003a42e20000102c0c904d503020342c00145010b14040d040c148070342015032201c140e002080e48226100c2ca0014010b0207454002d010440c05418142c0050190101e6541c0f06680c5010b04500a100100c82c1c014041c810703003001e10143e2000134881400c0d502c90070681403070004c0c407800303101c0d5500e24007254050705400c081c04101c81d01440d40115030321544120095205019520050707100040001c510400d10031815110300014114980f4842200e0112488881455461290300107a605c00344204e0f821b2401c6070b00c40115008140c03a41c0002c1000a40d681c034101c00c00c40004080c455040714201d1142c18804500094038542d0a11412100ca44040a1072035804038032900010b4008458051004080b0f4800d032800600b03100d5180c40c030140024501c54250412200c0030080382e601e030300080108240040755060356004944480030b465081d0f40700b440340b10180b0440c820780800010100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 769080998 1250 769079748 769079761
    0x702031204080c01020a08090c0f0631120501050609061c0206040803030f0a180201050d0207020f041d0c150a120b100e01030c1d0409020a0b070c0e09030a08010905 72
    0xb001c1d1541442194000c0d51200c02014010f0507000007195102c00342e1045020454003031501c8004407800d0000507121070701e014084a083c10301e00c580f501900c40401280441e0080c100034400c0340344014004c0d10703041010b19001b441c0203801c3d2200079140c240701e00100b1003400307050b64920180b495280f29407202074181c001c0610204801d030003a41e1107040316020220401145c80029840548107840b8000c04101d49500400200380c503504050010340083d8090000c002264242e5008040d030600060107801561140b0002509444001d0100c1c244141e0710007544c00f40100800000c07620341421900034100e2581c8046c04c90721400b421002004100c000141d10196200a0f4800419078401400102e01c85c40d900d000501404103401045000a1419480e04035146c440ca80e842402c016801160208144520401011f007803c00c4c402d0703a2004c500300000445640100050000510410040c26524030f0044d40144074035004041410301e400400c0001c86c900d500508950558041c000700007060348911 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 769082248 1250 769080998 769081013
    0xf08131a0405010f05162d0c020306070519082503020a091d061005070b0c070311011401091104050306010e01051c0b071d0910090e0703020f12150a0905070603050702031204 76
    0x2412040130442d100d41f9a41106940a00c0010465000350100c0d0764a8550000440301803055011041c0081d44600310b01289501c00c410807a00410400b4039881100c4c607800d00044951168010140400d03400640784461580100c0244007d250603040110301094008031090758010051240d4410217408070303c0c802640c010010f6540c529000303d41c1300460f00c2c0503080041964422031064005c04c80000c00e50b945803105004640100c07002c07010504490740b8000c1220050310500070000b00c80d01c0300b0710006c0340e140c40402c41c0d11700a10502200402c1c9514002c2813001200143c1c98070340900011002144c045034002e492590040b80304d15200082c051004100420b4003044603090740d20000d1072082c03061141500721401c0035210801c07010099501701c105030903500c030210311009410040e88030561000e803400d000050140c4003030000b45c3e0b001040076620f03099592401c4400050300b50f40d80f4442000d10404000c480060843e6080401c480e04110501a5480c0680500c2800398010000042c0030090742 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 769083498 1250 769082248 769082297
    0x18120b0a0905030d020909060f030a0b0603030c0d0c140d02070b09150a080405060a0c090e0406020d020403080a0908160504020a0e03031602030c0a05010f08131a0405010f0516 77
    0x100041c3d030b8980d030460394000c02a601511340c0904c141600e1010a0075494408c18401c0c01303080050003409060104d555030036000030002d008a5140c041803010000141c01400021424243c1799a0f861002c683d501e40341070b490400d0565010341d030740aa450007070810340002e8644140ca001c0b001032521280307042c0c0025181c0c0c0401c00c104088490110f081c500d003540004031280140c1c424002c0d0ba12a90b103101c0035030110790703460f0701c98030005840314001c100040700384403229041070060201510702243c05211006980c81030348222425040050f00d20080c1e41e0140c600c0015061110181c0f28924110600c542580c0080c05464031641d400268402250f004160780e503511030001e81a282c0790a00c601c1c100000b910540c4003a40a03000700d4107081414035240a009007070740c1050712030b050082c00c2d410007152000c000030450b92081281d01040d070049218540c154240c01110704185519140502c0c2150940710340d003107900e40e03044c201014000c88801d1281401d91010040c6495250801100c40b00b41d1100034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 769084748 1250 769083498 769083503
    0x909011109011b0c120201110c0a05210d111e1216020a060503010f060302030f04110307080f0a033b030a06140f0714070b1b0a090618120b0a09 63
    0xd03903440000d41103031040c1c0d170600e507500036245d042840308c1d55010710f07464081300c00b4815440600b0305410700241c64403a5241c9801c403100a001c50220321aa410246451010003182020441400400c95161410041c040c070013030707141e640c0e0055003000c8103240d650750a440b10440074281d0041a040e0200e602403060102e8650024450b0000ba0754551000d00070f1b03030080c064024104003015003c07849901030700032203002e2000070f070019445940702c3c0c46281005c1e11a41060381d15018180c0300081c030040c108106014410810064400703a100c501d40a0454810104201d00b010340300d9107210047c40700d44605801000c0d9500c550000888440d0000e410304181250050001d4580218003201400752600c2510502c0b460200c1d4004d03841303524003683d404080f100401c030000b504010303400000b5000c0d800e140d0400803402403580c000b0080c0e9012106608140400703c0011107501e0108030762540107401320201d268030003580d101d181c100141441c82203408400a803040b90810301040d824909580207510294 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 769085998 1250 769084748 769084763
    0x72c130213021303140106060804020409140f03220303050a03091121192a1502030702010206010e061e06090a030305070b0a18110f060a0306050909011109011b 70
    0xb25400c050f00b943c501c41e40002e8170f01c600c2c90303c090140044144114010744001e0346034401c0c0c40e51550b00700005403e00b1a42100c02d541e008184003d008003c1090303014040102c0701650719015814404908880c00404114010070300f4403081006c40d41010840b14460207918001c20782c119a400c151500790008907400d50080c3c1141814988400310f40f02120001d504c83d420380e401140b0701c035500314200c0b80480c000384c42c80140d010000c0d5000100384045035900c281d520120740d020341d20140c1c4042e007080c080079907016802c0040e94400315a41070110078050b120300000c0d00010708050003c50644c60703649120000c0c0303440c041c50450095403401c00f55440d11200501c21117040303403203280040c100d4100d00310403034007544682c02103a001651800b40b03c4280f03e01e012810350482141e1a4800c07008030b0003548542100c18110300d003660751600c4005110200440d01c02160091805080c00240c00004000a240e40d14050b012000c034007040e402c88082500901c3e1692004400400140c1c0b1560749080041111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 769087248 1250 769085998 769086007
    0x141305151009150e130311030409021b0105161d0d140d0806011e1b0803070e030c030709050c0d0c08070908211c050405072c13021302 59
    0x2111050142001c2c0c0b14140000d114034421440c003800d1030001800b90381c200f6244000050001004000c3c4110701e14081d180c0421003c00c455003041c00c540c40350f00905072031a000a024820458541e43c650300d6400524020030603480d00e0000c1c84100200301d950341d800c20003c180710300500d0402d00c512243c00c00004107401c070408042d1a2400d040200c1000d403d540b8041c680d00241c1d0701c0d00030b800f224451041070319004411381c3c06000c1c16001c4c0c1004060754040c0407501205642221440031804881031240004c40e0307036420086800780820b0145601c26100b0340c0800101040b40e10f0100321002164122a004146529401c40c407c41074045c0d83d0100066070b01e451030810b241c81d44620701c0c07800b400d00b540300c0c40c80b41500c0302216919801c04d8100003089481d151480c1c445003a071074000300710031040740c40c0000c9184580303100c52066840581d01525281d00094062018030188a061402030b00c425220102402c80c10a25581001c401400c016200d80c01d07041c92070541d124030070020300c12240001d086548 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 769088498 1250 769087248 769087261
    0x306031006170d0f05090d060f020a120e03040f0b16050303040303150e0103120f020f01060b03100504090b130204091a10050102010510120c080d05030f0a14130515 72
    0x345400350810003118480c0703c902a0655002e040610340135045944c5661410400905004ca41d001d0074800b15005955107864080d841040c0c40a000100381d035039240140794209018000a46400071030002032078100300020050000780d8606001206d020040b4103485414460803c40004080c2002800c0e5000000800081551651000c3c08080c072070401800c0d225191203069075045824080200340c0c8100c020320810040c040c02d1031200000a41c41100c200101d846840350a440c590341c404108a1400b00502404010615480c1c0c00b424007910204a840043c0c1c407400352041001c0c0103500c0d035008451020b019500d964101d00b071644d0308a00060088c40d07031946103001d4004200c540303e8141d58240408031300c0b588103008250050282004004000d41007003900d5150b0b41100c07404843c07001c42000001516031041c0012080e4014949506840f8900b100d20a80408002050052038902e0213186014070030b00300022640140a94496030303900503003440d2503031038400c1b41c00c1040c55005042081109 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 769089748 1250 769088498 769088519
    0x409032622020f04060f1a040614030a09120c050c0603041a0705040f0e2d070315030209100810091208071b0c080f0c150c03120901060302100e0d080306031006 70
    0xc0311969070000c02d807c3c4907403e030320810f4001c5024607170016107401c12100501d406071000d581c00040917400003891404941d542524006900a1031000c21446807080c41485024013207081d400c402600c2c0549180341954a4181d00340503448000561803032400070408243c400e8083e0380c0174001d03a03084500c03850340310030000c28050340445107170b158030460703013034281c82170b01c0c0d80705449440301000c140050740361141c0f0002c0d000382400580002140408150000c0984e491000da070b4000c000c0e001c0000d24407814120014206200d0658569005090800b5840012400303111554041d41030b143c021004e45910b141100d1b00d2004241c0e01c00e054007402504001d0003207582c0d125048550640803603595001600e002074540c4145103000b40d00c40482c55030040240714050007482c1d01002c100c00c0d42c1c9401460400c071407501c0030944540200760364a1409004501b8081e003203112034003a60401c490360741a41b100040580740c00ca1802070261030040081495078030204001500c001d50403900384042d9403120444503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 769090998 1250 769089748 769089779
    0x10050106020319020a030806100c08031905100e0f0703060b1306030605040e030d0203060402070c06080411090c030a1a0406090b1f0903060203060307050409032622020f0406 76
    0x3014000f400c0c4040542d0f000264255110f81d141c0c4480b2100e640e000308200d86180401a00700600c20b05650301d0740000c66000c0190b11440c0640f6185200c0344040368a00d00300d079070041c145d0340c000c0b2003540c090001e6000d40340b201d58130840d842c920071265651604120081c00c001c3e404480ca8080110300c01c101d54140f000c500c0e05658065404101060b40d0700100010b03250381c2526002c564104200080440110b60015580140060405844c014070b6658103440e0b01901e600c4580000e00c1801070101b003182d4a030320010b10b80000c0303034480a0390804e004c0307005451001401e420380c0740741d40d23590840064240c1040c01086040c000c0c000c110440e95100c3c1d0401410032244640d03c100c0c15190300030403200c0848807900c43c10300e81d07544105101d411903071303940c1c02540017a0200f58144600d500010741e681d8ac42c05641d800e98400d0f5560802101f901c400744400700240c01c11182d546d003982040000e02500101007240503074035100030102c0d400c0c3c1800801c1111010806980e00242400004034400705c003450840c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 769092248 1250 769090998 769091017
    0x1502030c0c04020310061101240608010605131202030f0d12111216050706021c0f05070f1b0506100609090c023316090801090c120302100501060203 65
    0x4030011501c14007004202c1c03000f220380200c00018540706000340d502c40e01c2c0300c1d01411400c034000180005250780a22440c440c0303680c0c0c070600c40c0703d2000c1401119032184400b401485237041081c00c00401459941c817090041c024900e0840418030040103640c0c3c20803050901252803002e030f40c064903525000410b4142c03040142c444090a00c410351442c4c0d1521030880d05090410340c0019401d84408049c5001d82c0801d44c045070400c8001e1203000c0200b00944018520030b5442c1c44042c0101004484a0003500c0c82000c078501c1c2a440d003010420010f4003d242c150481c2039500e060f0380040403440c040c29200051580180c07442c8180020804110700404400090754401d07200e01c0e412075610003904c07060b1541840d1200c0160080020402d109460398451508402d83e00000320312981036880c0e0f16920101102c0318103084008048841110380c105400340d010b081001c0003448140c80c01c0d2183c000c107d00d94030401001404001c0340205040c403e0000050031303070700c043c0244215695144000e5a940141110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 769093498 1250 769092248 769092253
    0x1206111606020a0306120c1a0c030c063301050a0507080d05040203060c0310300b0f06191403010b100207181407030b041b09150906271502030c 63
    0x1c284154940d0f90443e4055200e920b400080d818003071444891441c0480b1088c80303807024040500303018802d00c0a00301e4105508024040c83c6021409041a4038450503941440007070300c410b41d411079240807031400d11410300b030032712540d202c0c0a01c00860305072054443c082d00c00c8001094a542c01c00380d6811041c003a41c001ca088407140d40740e00000c0120b81c882601c40f40180081a94200900a202c801c000e0840c21000c100c2d4407a0b14041503554004081c04004072103602440301002802c0440b8969560400d03410b941a0005144085101aa84006005440360300b00101c00c464202c0d60b094100b00300000e0302816080b0390568000c4041e5465149020f44903004010b01d056070020f818138480c01c009509200e484405646840382d0550003000700e41d840d5a000750701c6215091611101c51001c10008109584850015142200c12000d83c914490640b0411061a02c01c00c01d241c0d010840c5000b1400c500c0001d500000503800301d0400c2503003a40449900381d0f54881000701650040003078509910003005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 769094748 1250 769093498 769093511
    0x150d090516080325110a1502060106090f1a07170c0c0603160c03020a120c020a05040e1e010603120c0303050717131a012601061206111606020a03 64
    0x128507489001d80000b19181c0c500b205500a1114250045051210b0081070303117003003400d02240850902c20047c2c1140c400004068080f9868a504010b0207004040515060b10a10b04060f1440d1200001c0d210300c2101d03066070001c0101c206481d100302e4020b940d01081e44420284144220b0255030000720904426006006c1d440c2007a04102c070440340301d60b00351842e41c003100300000300c1074a0102106505074218811000500c1c002007045008401e01601c0b034886d0480b40540303204100c400030b42a00054041c40c2012030851880b42d001440d05400d001324404c8900044884020310300400c183e501c0036103c2c1aa46103010b100c2604441c00590650003130b60207020701d5036210740079150802c0718071006042440c1900003030160315501c281c01c00c8140c071443d1200c10140400d05840f811403000e0704a512031340c180405e08800c0c0500d9198402c01c0070103400090000303601e070102070b031228081d0200140075152144511412203e00f81d04071030f40700301c0145030400100300d00d0401070002d42280c0132200121b4038008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 769095998 1250 769094748 769094759
    0x10509061008060c030414160807091446050108061302010e01030b15030f1e01030f14060a0902030f0f031b0c03032101060e0609150d090516 62
    0x30041d02c01c5440202026100c9800304109a80010010350f1103d120124200c0c0c0481d040c8141c100070380402c00314003401418074031000c0c240320706079101d0b051103480c0054441543e17106034034141e800068001400c401c24449415003211100607400034144007181c0c1200003a0481079104000700f444000b008009584e250b048096a4a0040c0e403044c90003100300740d440f00158072401041c2c0705c4c1c41040c9000b09088010801040501107400065021600e0200c1004504120868910b0307001290450888907000e0041c40406c03c0d140600006c2c1502d401d01e4942000e014008084084030b0070140700b11522441e01300200d20081c50010401c0b4801d01035442417204084000603d0200c0e200010095440d02419003a605595001c0300c501d10203a0045a40400880d68288050500060580810340703040540000c44c0f2a0a04140c001d003042c040642d65041103610b480d819100d4800c070948504800207080e50041580c0c0c0650005008591f05141303404041007804148100e40c0c00044400d8103c1640f510f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 769097248 1250 769095998 769096021
    0x5041a04061211070b0c130807081203040c0b0702030a1e05210a0e0a09020403142107080a09050301060603090303140402060304020915040c0e120c03120c0118030201050906 76
    0x6090803050300910000b404100c1d117500140c0c010019001c030902d04240914040700014060780100d074290840c4808201a01040c800080300c2001011101d1561400350b840e203031400482c0c010b4284803a0f01240781411510100440c18075603800c1a040007403038201c180d42821440600004035401c0c0200c0300c03002c0d0300321010780c40b05280480c1101c02c40d062116002c000c0310314031622144d25034000754480001440103010f1000700065070141658007e030200c40c558803441d050240c6243e480e503030410041992941400001d99192030f40c00b45100d60360340c40d0840b0807903400300745401440e0300d5480c141000440c1909944802d80306842502d00340401003041207071445495007254043c0d000030341080090014034088040c15070003108043da017010b5102c84004102210a10b843d0900854980d90030a1142e02e400c440241045418400601e03c0b10100004603840da01110038180020102107002c24074500d00b9048055291600103441d89442054240280030344401e907018007c03401000049400040c12 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 769098498 1250 769097248 769097261
    0x140103122d030e0703060e0d0801150903110d050105010609060914030a06110708070f020a0509060f04180803040807060b01090605120a06030b0f1501030902030c090705041a040612 79
    0xc0c0310420000d5101c8015005090941e02c415040d000c0d00b800480000c00b948222103100154000803c0001c1a0500c00b40005406801c00d080480424203510300e40c3c1d5019404c2c5003540c6e48896a0803030290b10701c1c081002d101c084031008100e5420140081a400e034040030031411180304d0358031702a0855646101c1c01d0080c040c8042d00d909900506c50400c0424420707000316000d80d01a85e0794170316001b0191075802c3d4030703000f00c08115044c582a409103003c1d850301c0019a00a007001700e4021915080c14000142c9609101203400d000e651609000c3d11030804016002d00b000f60807900c0c071036a0789000e1501d4412544008800c462142c40d00c811100c055101e034001106940d05a21070303130300c1c1400c06a500d105104d001013940d1400344c3c8890001c000201a12600c41c000c040d080c41a190b181000e072503003c554000c034110141018600030304140036950004030941400c1094680c03402640318a14215068070440d0808004030300402481c0040f03041d100000c1041b101260b07122091950f07170a01c80c0040d07404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 769099748 1250 769098498 769098557
    0x30c030e060c0a021f020306100e031b1302040308220501080117030f07030e0102060c03330607050f070e070503010915231c02030d110114010312 64
    0x80758001460b018001070042c625018280102d507664241000a90300002000010203a415008018881d003400c052801d0b01d4001140d00784003821190050101c0e503103c28200441c42e040c003501d12840703202d4960fa66014400c4090b8176042d507446450f0304050280d5404810704242c1c80d00010b14001c5500440101101640c505a540d124540d01e0100455581c0e890f440342a0b01c2c40c0005c0007802004202d0f03000030510030740300391101d00c21440900006410507000902e20880340c003080040140c60590217000c411100f003200b160800307030f40c000c51780e03d2000c0e0140709481d5085000010008140603001604880c5142d2060440302d0154a906003211140700603904500411420b000501c0261b4158004207181c1d000c00f046001500e5a4054010040d1500421400712090140340c86455040011442400c1d10345050104038505256002c40d80e22050050f40740f040040c00b4260040040003234012018082c81107280b95002d58407810401c02003180320780c01801040300d140f42c038001d4104510402c059881c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 769100998 1250 769099748 769099753
    0x6040302071203110105100315050106020c130609181e0201020c01260c0a03060806010b0d020c03040b0f04050a150905100e09041416032018070f030c030e 68
    0x518060882d52448010b1008505100301201c4010114009108039403142050100451aa0385103007000d0040000ca050a011103d003004018040b45d0303000142c9040c141c03c141c40c21910000d1381d075030300b6000f090746401c0800014109054a0124100100c82d00d010718080d4a9200b507021001c04400101260490004d02680104882c0345d40e030360040d51405241e4008510b412201130541582904030030049074200c0e5001c10110f5240c2c14254188900b0024142080092400754107103181c0c84a680241e5000c1c8405035000a020f8103010030901c2518002e00c65881e0312a184c40354401c5d2824241c100c0d00441d8080d108500c40052034840c895034900702c8050310b0312102405800d004c00d00005160390f424900911095055080c150b49911040c94801c41c001c00074804e2200321086000e0605640340102d8240341c03110403085c000310700700a00010320510300c000c448001c600c00d800813411070a20545105600c60036a0200510150404001e10f86c20400356130130080c0a92000050b030440c0c404503506580356 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 769102248 1250 769100998 769101013
    0x8100c08040c0504020d020706090b1602070b070b04051f1b030203060913020103021b160b13090f090f08030a0b09090d030b040b06031608010812031306090b0a060f0806040302 77
    0x80c01c1940c006c1203401d46d00e501c050726020280e201c03d0305984109008807110b82d4030070b013003020311311000f030140700454a00d1000d00703080703480c00020501c24051000c0141c0901c011034041810407104010400a016010408190403042102018014040c070202d00d40009105845030b114503200e0b108691240100408000c0c031502c82c0c5004102c0c0020701f171400c0341455400c01160343d07901072011901010f1240e140041082011807261040340103016481400185010302c042c11481902c03e85c02400d03100010400200d405242d98400050002400013030400d1180d40e4a9000740441781d00250301c41c0d8030003a8144980311f201000c2c03003113649003104c6500540d000090301d204024442d4003c5060840000c00c0804c180200c00001011940b0a6550380e00301c80c0310403035910400760880d40d03040c01413102c4405411058503500d2028240e01c0001d182041000f078620340f400c10407480e5440300c098260403610406051070f02c41c000c00002c140c10b0203192040744024200003071140000451600c01d80d4035a01400c040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 769103498 1250 769102248 769102259
    0x5330d330b100c0204110315040e0f03300106050a080907050a0504020a050f0c0102120a0203040203030405090c0d0606030b03070f05280b12160302070b01180608010608100c08040c 79
    0x843c1001c00301303d074466110364800a184404901070750151a204030101550202c89040204590510f03062000b190814040742e000c00b400801130f10b50840c1034403044a2110f40510291b00d000c00f15542c0b012569054070700101e5440e0b0b204000d0480600e850720340d0300e400d4860b5030031251b403a10640b240c02c5d805009080c05102506241d0080c00e030941d01030070254109005001002500c0e0400005036065a601250b03001c00c1001d0000c0054002e100001d045185080c1900440d0300c2c2d1145000d594010b80040c0045056050700f081282c440141c056010003c3d280c45842c000c002e02070400203d403107413064441c0400e0f003e40c3e612100c400c03200020066403c1400743c1390401c040d1140301121348c5048031a000c0024400d07031808001c288160190500403100d15003458403020038000218000109031043c010103000651007030286041d50726480c0c01c1e4038881c0d5003004200142503581c101c1100380d42840d10000f0142d100084400051416010521008400c0c2804491004044a010340f0191818604010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 769104748 1250 769103498 769103507
    0x305010219030e2d1c03050f0c12060a030206031f0b0c2508030f03060114030105100309060f020a091404270206130803030a05330d330b10 61
    0x2c5064144d248000301041c1000c4142040054480c4030500c0141c0c2840c00d4034994944156607000c1400807019185060444006959001311900a100581c3e40c101086003642c0d501c540900855006152aa50307103010000c0100c04102d80a085840401522001c20700454180075105070000e100010b014052207441ca800c00070300c034062100000003039408041810b0b0700c207200608090203403d0000f0341d80e040c41c0c80010480802a10384400f1300005200600487d5103e4604540382a001e107000700e083c0f489424448018184081a5103015100003410342240c4e8010490317000f16a044c4044500c04c011100c140010b445c10001c1c9003c7d18501011540075401107000000103250000e0aa00e0500a44070841c02640440c0d41080705076038404800c00450000b0703401202d42c401c00103581c0c0d2803108600c0440d1650b5818881302480490a9148054143c3d03c0d040030b800d0845420580f5110210b00c50281220000480d020200d1201d40d031055245581c1c00078019441407440180401c0482c0743e64110071103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 769105998 1250 769104748 769104793
    0x609031002090f03030703020a1a060a0905042f0906100203071209030503120105040e010e0c04020a0507050102121801060501020c0909150702060601021009050303040b1e010305010219030e 83
    0x96103c0c1ca05603807894503440030005424080d1084e0002c06540b441e9040030705000d4100c0c0141c0e140350075041c0412a058607440950800c840d800c510101e9907886618041c1c1c11130003103012b4020009201e5029002e08414065103003822281600d6035082c54645606005a071007080c01000090f0b4402c010480025140303c0140c1040d0f41a032410800306516aa01c603810750303204590030100c9022540041c04185054400c0c3c11501c45008004c0002c6c181b18449240c03110200001148540e601141c5c1105040c01001203a5506910800856940700342c110103004e00c04050b100400e1600ca14200690000310500c0b41c602500c10580042060401c3c400421006080c024004800d41c0114449003441d40340c062456406500c1301d402800b40c0386403810009240080481320342c1c8049082004d41004150007208a03a0404c0d00b0107020701c0140e941100000e200c00c106100801c031103c140000100380b05042d40500b040c50314030806500d400c0d44c0d50707904400b82da034400e84c1009035421880c20641002c00000c0d128 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 769107248 1250 769105998 769106017
    0x120605030703202d011709061b0409021b0c01180b09011b12020d03090305041502070308040806010e011706070309230f0d05030124020c040f15050609031002 69
    0x10b0000450340100d40e1490301070603000d85100701390203503150015a0020642e0000c252104030051603032418011560f41ca6101400c0342e10803080e04400800d103603001d81e00302c0340070b01007012042d591030703540c0325400842c4801200080018002d007032101c00d0a40c400d400c445460100301313040809140c1080390400095128444060521640c0d07a05080490905141c58406501860b00800303510b41d14500a4104140382c0804000c042ca092503032400283c221040d982501e120300d1030500c45800c030001c280c0c40e0124540003e020310720049070001d000b003000141c0314141c401c4165040f0190340e03200202105408511008003e54110b1030001d8010b511a40c401000580540180f030380d4082000841008118240311101294011001582c28010208031120010416140a600d150326058503200040c4049a010505c181c03801d0503242803034402c101004a94000030010092082212489401017a81c00900c0980021444c030006462800030140c038822200030740944080444a00124025880705c08a0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 769108498 1250 769107248 769107259
    0xa0803090c2205011401121a12060a060605160f060f0c1214060a0501140d0c110115031e2103020c1911151912060503070320 55
    0x2104071a9807010500b2a1040d0322545079080e01188840381c0007a542c0581001141503583c9400360300b940da00a0b005640c641c2c1400c000520303406201184100c0ea02072a986543c0030300101240340c102040070840501035103040204001040d03490805840900400003640e07074080000c06840040350084038041941c5101e110006810b071846c2e8042c80c110303191030610b5000251807600c442d01c0c0c64464810340b04c2c0306001d174030303094480c3c50405c0025211410501680d410445050b01884400d030614042e10030801440c50144100130484000030000004c2080c02d180035030800002c0c03900030070f119604106407600310303d8801000101044228134075458000496111003405003c4002c0c1202e03490b001a150299a00035030b403001002c81c1c030351a008401203010500462000468000345004501d03c0100c0d00540f00201a0500711420003134502410603a1020441d401e950314104580c04006500001003d02040000c1a102d0050691710303421800001c04000c0301255021a80c0800c024004819600820 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 769109748 1250 769108498 769108513
    0x8060f040b1513230402060915130303020a0c0506070c0504050c0d152405070204090623010312090807050d0203030c0d0306090b0f1f02010e0a150b06030402030a080309 74
    0x8940b43c4880c43d2669424666140c0c0c0080c01c0c52401d640c030004815005581a9160034a500092510f20600100c0e0b4420900710003101c00c501d0003e01901c0045c42450f4089076420382c6c07400c1c040c1d20350545070401c179100340c0a6400810720303140c00782c19a0007003a084000741b0101c4e801e100074403004103c0070709607045611b001d00c14130b8040304407800761100f0264840d0a010809103015250841c0012401c1c0c0788100f0b90000890000c0c05500409076164203030112404900c0b11001e08140707008145c4144800c440d88000c2c0c0c403081440c046109081c0c102ea101c0c1ca02c4051090184504460303c00090180040b6138100702d03010403183c40c00804084031035000405591a0226070000e452401c9440d0f080c0d1404a611000100400c8500340700c0e1482c0501c0030b6440e10100680c517000036982010040040d0041402072221055441c400d41c0038505801b1039804481d1a518282044104d034100350792544070aa04203014a030f800d0600b081034034081e41d0302400820350b020055440401c2c9070002040a04288a40c0e41c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 769110998 1250 769109748 769109791
    0x1506161e0f03180f0b090406080307080f070f060507032004080712060f0513060e0a0308220b070c021e0904030c051015030b0a05040305040506090d0203030309150108060f040b 77
    0x50001003152880b100e03070320b944590031f05c410307989154420031039a001030020b5008070b003888040350b19044040038056901c01c49440c0014483c001d0510251003603143c8020080c003150550711024010034589071540c49085280c4020703c0034407403401006010b0b04088400c001d83c1e11520030000300380d48507103408200c1401da11085021103908441007c0c80c641d00c01191414000035202d8140b000100c50090000300e24280c070b001c0c5c0f83c034001421000039401c00c51180032000b0111090004c0d05a44501c0000c6d0350300748500000d00718502c00805900c100d200c00c01c00401e0020345440307040c10f014050901d0115036115107007503848030b407062002d980f180501083c1a8000b00b5038403a14400c40c1c0d001c1d00710070716903055003800000c0d940000c28592480e4589400d01c008070b03410500b66001c446045030180e2b941d449003408940c42011a0500a400d48000300a020709a031000c1000d8010010610403000982c1e640d13100550f5840b000c0d43c20881114980c070110700410507840507a58454240d000f14080c004808 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 769112248 1250 769110998 769111019
    0xb09010e0303090405040308060a090213061b050d0905010e091003110d0f0308041403031302060f0c100204091b0c0602030a1e0507031a0a0e1506161e0f0318 69
    0x1224100d0001e003141c41040303c2c1d072030010ac100300070704034617802142411501011140b400c284c074018a028880c6540012002c1c40640004c0120980e003d41503038500d280268001d04500528050240070030501802034040e410101a048d01c98811800241c02c0c0a182d078407002e1b0107640d001c011300d8003c610000a036003c134110010b0b000342c1c244242d0744c141040c986414002074200c0009c4148140b40c10400c203110790880290090742c6607540481e00c013590344088030081f8140c1d102d08003446105008040c0000608495680544111a0088000c0c04450311002035850703505450b44140d000304400c0b91101011441030b0780a5548044400e03400185011005034103071301910202c5207407003119102c87c204070340c4070380c540190701c1440c90002c01c815040c1041000a5401c0400d402242900080d400c00114400c0404450325019540600380c155142c4a0540640502042e40000c0c0c40c16070200740d9581d4140202400020126001841c3c4000e0f143c40d03650460f240d848019607000c0c1c5101020000c81c00c062178 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 769113498 1250 769112248 769112251
    0x50a1418120c090a0e06190e101a0103050105010507060b0d06090f02191505030405070e07020a050d02060408190c06181b05060304030f09080715030b0a0b09010e0303090405 76
    0xc0703400820900d4800400c0002e1108000d003040005030604020380717550040050f42c00d070012210403e1110b07580403150b03280300429240c081e404e0035108020700020f011a2a90003101100005038580707840c0c0d40100019019140700788203550001d0070820000020030030950210281c038000400000c054105610f40c02d003500c101400580b2405032a003115411482d04205004e004942040623042d1340b407421a01e605000d001c01310720024843d000000400b0440b0500c400000381070001c903410311318200030f01c00030342d50300d00e240c408c83e0a031103444101c04030300e400000c43c03910407944840c0143c54420441602c003840281c01b11031500344171103190000005401070080c0d0704c0706d510410014030710801608143d040416280c10051051200708000c0c031480e1200b03001c40e076220360581030202c402c0c078409400329a8004254045030303e6021b0344501150800c040b00b81038241c65440e039000d12100e1400020081c683d0301521038151041020051081c09500440d03448010341c00040070349051859032001b19055030700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 769114748 1250 769113498 769113529
    0x30c190801170703020f040f0f060b09101106070507030e0405070503090d0903393c03060b031e0307030206090a0506070e060903011e0b01050a1418 65
    0x4940e40103120040c60124000c44031001c04009180062854000c10780713420000040368025070312902c582038880d40070b0300400240d20607940e0422840b5512180001d181d00f0112107a03101e41152600c12030030324072514214441455400260000d500c603864151641d500101c811410710800d2800a4000d81c2c851181d1403252200713807102940da10b441800f20703040c1a440ea036801e003401554501400030594802050740d070b850000800913224040d168004410f4440d0668416440c0010f51000c01e07142280e140204807180b8002c1c08041c5244c020b14002c0c8070b10514060103191052a8400b0070104149810440f41032801034152102d0004d407400710ad91b4140b68402c544440c0c0d00020340c0c603040550400c4510303400105000035281345c1d10b550b40c4a9844d584064200400c004170b0008400700b540e2544100d40f0200c00060080020b00c6d503200082007181c03070048050305110302d0920114803e500600803124045c1199480504201c042c00d801c0f05c0941041c83c42890412041015903000d40724030004a05005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 769115998 1250 769114748 769114757
    0x21030304032c0d0f14011e02180f060c19110108040f3e090601030501051e0418121e0507081e0f040e0c090607030507021909150806040302060c030c19 66
    0x120f070124142011000540154107c6104202c2d07100b010812001103031807040b0846d00344640c8000c10000590a02502d00b8000260203001c20021402a13555060b00780c43c1c2c40b80c0c00c040c0c05404c20300d0055034040c0d01142d018100c1c005441030907001410200b8001c0c4d0f07040010518030410f401d070307481c03081e6034001d000180180c7c030b11b85000e00d81491400d103800b2075103d6024601030180d581001c0c040351000703004480503c4038442c100c00c9031450fa03445400c00f4040d07032202d240e0b80740303104c00e58204455251034400803000412141c5040039803294070303042400505075040d1600f902c0c12a107a5a50100e80d841703140d000c2d15046656015a19001c0701100030b042c214134104009441d40d00701804904900070180080880c1d2000b0066039503203858001c2a00c0040f901414410f071590800c0c00071034003030400c100792125013100f4414046020070382e96000109506821031803400d0b4949440815a86050956000d80541e000070005a0300341c032950019503019a01555070f509040c11810300c441e074842814010303c0802d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 769117248 1250 769115998 769116011
    0x60519110705070e011a070f29100312120603170c06090304050f0f0f120601091808091c05060f0a05060d02091521030304032c0d0f1401 60
    0x80003c000f00301c0501003803090004654076140a9140105400f69006007000000c1500010301a403101105000c9820080c00c0c10001110711031080c2c050300c0d040c1000580c0640b640410000507070010403400b603e034071002028007607001d4002aa084a140d8050098030780e00c402c00031002800c80da00d84820f4102e946c403450340b50041200d04038240b0034002c00440f240e60042c0010440d5554005404015000c03d0750101000c1009602103910f0440045804d90009582d0742c10300b10b00c0e480091341030304031460003000304510106e000d0010417900071214080c20a28042c4407107149840d0030000769510700b0040b84041c0e441c0b009a610a0b05001c2c08507200b2480f0391650b400c000c09404940206c6a011400b1a403031059111a0740c001240b014001e030000c601c24421714010070107600c5407491126201c02c1382030b210624401980c0704a0341c9910840f021070010352809918007000061201ca0340c84e01c020080100481d0140d1410300140303c860503c10303280720991000c06c0010030410b803503100c1420318903800801c11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 769118498 1250 769117248 769117253
    0x50d0605070e030a030f12020c0f0c0f0303040f05090601110d030501080c0a06051e0903070b090f04050c0301030b060d08070b040201110d0509040216080406050414030a0206070605191107 82
    0x10010b140850502980040c2030400c0000d80c02040c08102c5202d03810260760480b03c0c603513030200078016030008078582e100e48007803402d02043c0003a0007417921104985080f40c2d0400641450348074001ca118032410350b1203640090201d03142501c2083c0d40500189030900f20800e400541500e800c0750b20f00d03190702007640c6030010704c4280c00030f021300c29a0074070554a42c0c080500e0044000c00300c0c8248285082c007020300300c62038148081e60008132024014018101d4807080c0e100d404550595002101652250241544245103803d00b03004a602c910064403505042d6881e6485106621030f000740081d6005044000c0d040000e0380c544040c16402d4001c140d944041d140510015044802107003006140754000104c00400390303070000481d080654183c07009a04e590b41d405006999225841c4010072040c4086004214581c1c860b001d4022074003181c0000507610310900a1581b1000c1c04a00603401c240e00f0403a101c04a119a04015000140e8580504200498600e0101160700f01e0212035440b540020303c0c1d03001e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 769119748 1250 769118498 769118507
    0xa050a0f11060306010e0607030e2805040501060f0c0c030605100603140c03070e0102030c0a1b091404031d030627030903070501080c0d0c0f09090203090703060213050d060507 77
    0x45035803042c1c48083c40c504250001a24a102880c2035074443c0b0b40001c0d01c03908051040e0104440c8100203417004100c0072a40151915001109031020546003246400064a04c0d080c000e20341211000d8070741c01c5440014107404c40f00111512026110250840d1001000807660300c1203900c1025241200c18146080090040c240e4820103000c000200c6800c05008902040c0c82c110780d0442154100588041c03d1100140e081d070142120001060180300084014406201002c410640014611001d45c40d2607110034421201c1035500c0c4041c460b6840000780c006405040e041018100700c0303058001c907401c0c500000c0d28020f021503003481001804500001201d1041114805443c121800785003401c40c2e0f039004c00d5076145948101c0b4104406003010480e0f0404039000c84050442c18202072003860716112000c4c100b000f581c09418001440d500c3e0014032176402c1d10a0328003130b070401806060003918640740d44002e034000e091041d090790382c2d021001074142e8030002c03444000c502c0703100c1c040707501e1804850140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 769120998 1250 769119748 769119773
    0x103030518180f0601020703080d141008100203060f0619201c110d1707110c090601140a080a0b0f03030d2f09100e01050d0207050a050a0f 61
    0x5020b411184521002c10050b0204240c1c0540c02011400300d40c1c0d83c200c0100d1402c2410382c40540f150000191559103848590410903244010900c1c0c1c1d0500d458118000162821520800c0110341246030b041c07802c800981c00039034100700d009129044104034100040c49070741c0070400c1f5003503a64091843c0e01ca502d810082d092021a1059040c0d9506980c8100640d240c0b400113000b0340440700e44030154040310303000d514000203500c8000100c981407500081b010f4030042c2007042071984030303c11a000401d05445031910607e00b031512009006182040024800710740000382c8401d05001c0c4610703155035020249805052000410b0b0340d18800703401e100d14001d04131071221081d070740140d19010407241d00c1d84000044404003100010002200d840c601d0f0303810210031600b62410b00901e03030300d1005080c60b00d00d00003400503d8411140b030040c0c0c103000102901c0c3c410300401c3c1940440c1090058a450300642d90150a445008070300341c5490407031039034031135081c0050240c0c212058025840100d042c840364103c1c1c0d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 769122248 1250 769120998 769121047
    0xe0f090c040c051206040f0905030406110604030f1b02041a0910030f1e1506050108090109030e0d030519020715030203010e0a020c0c130507230906130e01030305 71
    0x2004400a2900d000f4180c0c4100c2054100b0500c6290200362961201e81c04501443c5214071b0400c042d01c05445d055459074424815100020060540d900c0c22401c00305219008550680b515114005443c0007a2650408468000f80090000c501503000d41c0312401401001c90200c03002021801c40712042010060001d006d410840d00c0001051000584a010b001ea4007500b0001d000e54030607050980215030408500010100c00da00352101c0020705007500301405403403090321136007080da41d09007000c0d080300c64032100580000d0b5801200b54040c200702180c51000342c001d2609a10340b180c244481580c00c00d4229101c001070f80a40e9042091a0204027004107000644c074081d440c552514a0002000030040c0210000a60010b000513005408000c0489510300103840d004003040c1c184103e01c01400122800300201e41843c0c40380c1e00c05072142c080302d0504d0030000c050900304201d0400b840301036004070703050300c003003640031070000c9030021210303500c54029882a82d6950792862074450341c0c0307507541105285 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 769123498 1250 769122248 769122251
    0x19020723122d0c01090c14090f04030e0f0303190816050901032a02010b0420030114040207020904080c121c15050a0e060f27100e0f090c04 61
    0x460b48800c0a04100711615900c01d04440c40c010050b5441100c0c0384100030780018a5860702070741c0002c100e200d0007200111900d40754400641908203082c0016101e0440380031403c034400100140001740100460507004501031f120700c4c0858540300229103164049202c4071f00f2100048041646035600011302603004104101401c000f40e2000c1014004d0301401c21036070b05254403002144203800940c11248000f0200e0303a800c00401c0e0380c08102034000c0c00c1d59080360b4052810040b5a070030415814154440701c1c41104034007482c603840c107410001072040101140ea8042d408100401c05030b40e6041210b406036004000850360f071518070403035624001d6203420300d0640031424060800c0220409410079519804401c000c60100e03507100c401240350801c0c0d0802d03580000d020710080f40a10302812114400d601c1604e8070f1325030b101440100701a2180d1542c4440092000c0800c2c500da80b4103040c005900060920386401d06940c0301d11101540c030404840b4003100b94019000c024044c00b00701311824048205850 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 769124748 1250 769123498 769123507
    0xf0c1e011803140d02030403030c0206100b0a030906020f03010b03220b0402010809150a06050a0b2a0715050703020c01181e0e0405160b03010b031902072312 69
    0x41680c1c030078400c0c940038003030041500300e9180c40050342084580014403114210355900d064640030f4000c029507410400113200350000150300b00f44241c5030740f007070380c150300e1140f41000000b40044001e8200b23054100d0ba003039003c1c06098410001000998064442403582644910b8406101c24038412107102550b00f01e20600240404252010785064010341c0a10300f801040e0b1303610b0000b600c0c140d0034062452010002d00e040010710300041e0301c14801d0302d1003180c5240d140c50b81c0329031710a03446c0101c07002c0712664501c0417800341c0c05c0d03038011000308400c0302c030f510544407065502e40c40048002c0818035240041440010203408066042c008199000740900700310180004c4010800c010902d80d001e8a0080c107a035038030350510f41510382c3e015001030a03900c4190380c5070310301071074190344a503d481200c108146c800a070100e115980201605d05a4003149842402c4d41e031000e071250301c41c8510030303500c82030107a0070014240800c8030480092290009401d16022904519070311614000700205980100d120902 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 769125998 1250 769124748 769124771
    0xf020319150b0d1b080d05030405030d0b130e03040905090d090605030a0b0306011e0b040b0d0c0509131d0f0307061a120109030311031314030f0c1e01 66
    0x201006194002641c000800000ca10085200c21540240c09001c44440c4001004c0c01ca00440480060303400800a4852001540300e09403500e00064500401e16001842203019502d080c1c4d02c54001814000c0c641000f0001590900e021154882d00c048410380000a007440341c0304141c0200c1e500610104001d10421503840001004501c0300d001e21b0301000b8000000c140b250840e50000c00d01000000e003035606c82e50355002e5542d009040f0680300030400780c4004000a203d60362000391800c44150003091840c215201701c042d030081c5035421042d002e0104c1880030600345d8482c08444407007090340203000280340310360070148090072214104101c101d0b400600521800c007004400d8904455105801148401c2c48041010050b0122426240c1112000055140c41c0505412424543c0c3c0203440410103e500c0d580d9030380607031100700c0b85810000801400c2e98002140c800c1c007070781d1090494080d43d040c9a0101661401a40411003030b1900f58030038508509070048414604540e00b072030400800403080d800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 769127248 1250 769125998 769126013
    0x41e05031903091505031509070f0c05010f060e0a11090d02041e11030a2a0804050708120702132a030e120a02061612020c0307020d0f020319 62
    0x1896800401c4814210030420540225400406031030f00f40c40c080001010143c0091050b00b045800b0319030314180c2003002c4650f0500400c164000c80040d40ea1019218000074203603210500c0180483d001d640e1500b9810388041140300b0100a082147d45100c01070805e10a548241d8001c0454440c10030020000250680d64503c0c2015011f68140c50104004034024840d86011030401282c45100d800e2071240d121902c5d417180191f200d030b1080c5108001c50f052503c1d03105600021042044c40b020602e42544e580540a01d0380c071988248904100c030421921280034600389085203240d140040700205040046240c454480c008d034030001e079810440c440c0d030000764403891401c54102c000e00c4000540d0070245a4800c0c8c001041c408107000440b046583c031741c2c40120361a13102c82e0442c0014041e4a0124568240c0d2100004290400350744441c080811030b560b40c0700039400b0440942e4288420800c1cbc90042e252011040c10450040038010403003d4540181418003003000c0e81c890211406190400009001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 769128498 1250 769127248 769127263
    0x4020f1e010c0501020d020708270108060616060e1e0118081e130504060905090d030b120a0b0a1d190c090e0f0d0302091f140f041e0503 60
    0x340790082c000441d070704002d070083c422a4240200c4900005a80050000010050030103c0348194149508440c240b5044880e00c0802da4490000e003901010852030310f001e40151006820b12000c84000041c5940d40b2011542809115141c64000c0e00a1140b00001c070142607445010f8a0000c0c40f0b0310300d581c03141801181003c500140250300109070801001d4040e0320610081c3c5089119542d250b4800c0b41070f48240c5911311400c0c1c03140741403442c0801c49007864005c4501524440004040f805958101640604186940d07a500301e40040118181c4520410440074500c1c05845104d0080c104030f2000c500380d910510200300400c038140c0c0250354190f030001e01c01240c003034105606c0d01081524a080c401d550f07240c0d8441807030581490288030650b071001c5030328456015401e0072aa4100441002502a8059401c00300d52020070304000303081440d00304000158038035040c500b08241250016240a5980000503000440c0354045401d104095080e00c1207030002d40181c44400202c0d14000006c3d43d603004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 769129748 1250 769128498 769128559
    0xc1b030f0d0813030c1e020418230f030a030b0a0f12030f020c060415080702061e06130c020709060812040b0a0908011d060604020310150c020a0e04020f 67
    0x46141c075081410710171081086119400000d0341503003420b91700d40c111640c0ba0031100742c0c0304520300400d07840d21003007010750760200300d078012600700000d0700140009800c1544010388604901075403140c08004c41080c40106150200790f100000e80740702c0c44040c4058003c1035040b41100d920b1402051244400c29040c0666480d810303d480d00c50b0140490b022070404000e0405280c01c080c0114021800a580b0442c01d01141d42540d5028040d90342d113079040f0f0b914141601c1d8458030402d07a0354080f19051040205542c4418054110481c180952004100f11009a0150001a0030010f01409214014040c800c01401d2900040100003403024400c1054416486101030760080050015051401041600007c0c603801000308030000310303103100f40c04c14041c101c1940001e0095500081c15440c091090780d02500b01c401100b03442c20304010700350184c00701d22400c1c1418031421251079401039442e5160100544130301c00740900d4506203441402102128828928450042042150f9075110040e0f410602502c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 769130998 1250 769129748 769129771
    0x91e0302070515120c04080d0311040b13081902090702010b0603130203160b0d0c140d1509050c0a030e15040201031808030a0b19030f0809060c1b030f0d08 68
    0x2e0f9922181d01441c41020030000c9025603400802c80c1d030040103000f030811610740006031803402e618a28100d0896403030b252883e008801c00e01061216800c02c0300541200c440080c9420319084d15001c0d220300e8048a04024000c0c0e0200607503681c11030130200d041f1500f15105000074891340200d00e00043d00f40c0001401601e094000c10911403c2d580e04000c110303141c0c0c0080007001c1c01240c4808c610b01071913005008030603013a400d10030001c0b6100c2c4210b00c2c071800440141030702c0381402480e600060141c400101c0d2808140c070309820215015020b84038243c060b2074002202d6a682988150250548480070821441a0070542da030f8048100024002a0b109509180000d141144840310340c40b42c1020307a40140c8505000300c204140c07940741d90f01013000700c0300443e049d8078202e9402c0f442c0c420020316804002c2c00301200008840010f00b84401070204030700002c00315400c045800a16a00d4500c1c400c5002002001c0f401c250122400c0c244007100e182c0410f5000740c0010070b405c0300c2c0a000c405000c0c20408245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 769132248 1250 769130998 769131019
    0x50c01020604121d040e100e12070f060b1009031b030201080415200c0705030706021e0705041a090109020313030e03010b0303031008070b04031205090f0a0801091e03020705 76
    0x4d034680040803102c0c2c0c40c020300c00c2001010782290307581e0350030418607810260b600d42071616001800c006181641c94a50754502454408641c4d00c01d804210140000c4401a49400c9a18841e0f507800f4030b03003010303131065684e44c0040074914100920300c0140c1c0802d0300c41c500c00c1c0004c14005070341e200490305d50140e00100b00400302004510b000d13004100026808560040400c80409000c00410003072070f12007854003c4910756a111010141c41c0d051a02c16a4096401062000d202107500c03042e411098420900342c1c0e00050750782c0041016520074514141401120440c42d5844e0301e0010044c0f0b001d851003c4046065281251001e68031a42e03421020701405080240c07030f5440d903001d4000d1400d400000d4281d988070304059403041c0310100e581c001e0000a002d40d000129252900b04103540450750000708241c1031a440d200281d400c0d5101c0c036045070300085d9a103c60040798950900d01401428030b480001500c4605040c030f0841c0c203848030305090031044000c8900e00400d600280b0b0300285d601c2110100d42e01e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 769133498 1250 769132248 769132277
    0x906050306090a15050a0b04080106080f060711011b0309051902030c0112060f0b0316021603030c11030f0f010c05072012010c0c0b0a0c080c0d091e050c0102060412 72
    0x11844613078060386c0e00c010541e902003510a040303400303042141c16000081c40bc064071410540e840d0524004614111b42c820000203062038460080800301d207407000c00002c0c98650340c10034040c10703000c1107420a0100b600d1fa0203030010400100700326959903041d41c3c16440f40c072401d030f40041d8075002c0000346581048400510368600341d140d9031186001f0318060101c01001a85c580742c00c012030700300700d940000c0c0c04d00c01041c9840060000c2400c04600c04490003401c2c003603003075036400e0318918813000c001d4909024144850540ba2020000844201030103001491925020000c42d03095541c0e1180c000300f000301c144235100019800844018695104516200132001d1600c0420f03400c0800f056001069805d010a111403035400c015034011060041003140c0e11a610910a90291680186a030f170005402030001b0380c0310081040544168134104102180c00100e9442c1c19072540382c8005425010a1322211610401100300002e4200c45402c1c005044645025281d0740c21404114644c80d0600a01003030880c031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 769134748 1250 769133498 769133531
    0x9041506090203180106060c1115071a061512160c170c060109020f090108060103020d020c06150102070315021303020a08150c0310180f090b04030906050306090a 71
    0x241c41021811916858035424010000c5421002404503510744040400c15510909108034200d410000c2180341d8003141041c054405031004804101902c180002c0d000a00c11092603202000304941c0420541405410442d01140d84a03895641240030020403143c0c1209208040d0301010135003d640c000540b14070141d41c40310b40d10000034180901d16482d0101d000e40f01c8054411403a00703608844240c0c2c1c0300c1407810200d00c21801603621040090002c0c120942c40f0b002c216a01c0300041c90301500304241c2d20144410798000d29800c58858014070200300010b040001d8903541d13201d0900c02040614071390788030f416150155a18070074043d600082c52002c100390300e2000d8001550b014006c1ca02450362600ca80e900d50900c00b04c1100e080e40c000e80880d0204035070038103480c0290f03511000302d1035151a1288246007219460b040c220728649400b03843c964201c0d64070800000c03e0007100451003500e0546401450101c558000000b444003d00a100954459540e160f0f40704441c2d800024112340050742c900d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 769135998 1250 769134748 769134761
    0x105130207050f030705060103060501090501060509100c140705040f0c0507021e0a0308190e0a05041d030301030606051216120203031b030d0b040516052503021c0806090415 76
    0x6115210016005c01000030003d1654122801540200030316600c80c1145001c2c0e940a109001c0024024040039005140955003404a0206c1c0c6c201300e89052000c0d9142019145034407143e000603085048100200c5c20f180c02802d02c00c0d05054000c01550240300009042d41c0100b800190040d060304180304007042c0641400b1260032001006480117aa9900d03250340240c0c0702440c6d110994070000c0b03441d514140078401c0140031180040c01075140d181040103000c028a2660200c8060400840e0f2641a0030400d0004501841c081e40d40414000c0c1040c2c280500c2580941400c122503000c1e0904800d400f40e45a080707000e65000c14614401d10010340002441e40c000c60320300c98035240e0002070204590000000802c42c0081f03105041c4000e00c0001c007040200c4604903007407244d41d600c6c3c01c0c501038800c0c0b051008080b62070b0000e1101d8081200c004c03c01c05248200340e000c0340036a000c005c002d0380002000222030018189032514044600d0410007180812001400c01000003e51004c8004962f45a80010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 769137248 1250 769135998 769136023
    0x904080403110307240e090f160306050a030f030818060412140307030605090c0c12130e0f0402040f060803091e122a01082409012c010513020705 64
    0xc2d0800c03c10340340194905a000740305080440c1b0034240822040c00c0c4100403c0c0308824014000c42540d8031030f104803c014264800050070165200000715407a0b403000d80c001c010318050059070091050a2034090108000a0600d00e0300340010030b0032a16400d40041c03c140d100b507002a101c21081c4034260207490114840c0c440380160000070003080011981075008a00315441140c504000b500c034410661a68400c5081e110081d40100e14201030260250006090740b000e51842048900d989404a82d8162006c0c0d52924080c15a18140003c0d0710305802808040c41c80b028082101c02e26000400742e1303070702c102008240151506404028841c0b400c2250480b4140003424111596000d0940c550321120b4031200400d02e030b904000707803842c981c6200c0029211242d041c0c4031216551500c5c06a6146108280d2007200d80c191444d007440d4090315180b5000e4020402484012201d1150b00344502c4414074030113603640543e00c514010411039481d450f402c580c2c0002c01a0050344d40d103032401c1031410058000d180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 769138498 1250 769137248 769137269
    0x911040e0a050702060c0f091c062a03060501080a1503020a090204030317011a1b010218120a080d09050309090f061201060623360904080403110307 65
    0x4001d500da00d150400d5108440c00da00399542e503074600303000b004540104800c0c040503080600c90a803032400c00020111904407428204d0341901c00c295542d205540c02c030404000643d40c03d0381f0840e040c00071026a0214010306c0c0c141842050b05101c0001d0190030300400911445803201c405c21021401e0102c0c0030040c60300900702c401c105848078155406580684021800282c13210030134030762400300030111411795204080107011401e403000ca601c0c082c1c220494101c404518103a210103030b41001d1005021490308113070440384203101d1100304209040c00444654140c0c00c01d4451800003128501161850301075050000740481c00390400601d18010010380075041404002800101103000071080e104100c2110065003003030642071b4041c2607810900c40c00000c1070b254500030181030725511140c0f6800c09050025820401e02114804420b4440c812081045050980d0490580008a1040384c08801a60102d85a00b003e03522002113200300d110103030102076070514445003a0b0f03050200c40010001c0030311 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 769139748 1250 769138498 769138501
    0x3080601110f0303060f09060f0402030403050d0608011b020d0909021b010f02030105190b030a09080d091103011b0c1b080a0b01240e010c02040b060418060e09070911040e 75
    0x421640c075071080d85c40c90b01c81c0f0300f400030701503407031a12100b811320400c405420074074014408000e000107908094011024030034184680103004545200e44001450640c0000c40c401140124460b120b07046d8505032000c540000034003040e140d2300130400300121400f4100c011b03034a4005100c03c646d034040e80b6910543d1542080f40f400c081c081d068019505848080761540345010740b040455000c0c0006204881c201c2205100041101c020765204024180c099050140b41200c0c04003040100c4169101c00ca5509062a55045090900b4400c0383e201d490b101c086000d0700f404001010f0b00c03c0080410050004c1b0040c1507410501c1d1444000780700600701c4000300c030010292841c0040303005000340101080700001302814150454095403a80030b07600d03aa10f90105d01a60301c001102c00f80c400a4050342c0203a1209041e6405807074940c000c4c8010010038480343c48942c072000c55541550003070340c400d103240c48003401802036118000c41c071081103507403004002800c0071601c040d01485019a034069100c08907020f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 769140998 1250 769139748 769139773
    0x1061e0f0c02031c02010e010b030a05071404090b041406070e0f0603060414090a0303140c030c0c153c060613050307090b0f1030090c06020d0f0206040308060111 71
    0x400c8003260400c7c0c803000340f0a036443c01c001d0503654200524054220307400080104825440d0202600115801420211701240030351a50882e400c8140c40440311105007011090300e40e03070140101e940120080c81d10300c0c00360064100103410b403001c200c03040d440b44a00001080481d540c40e842044545aa191445c11502d0000d0241d500c035480040c0960101342010394008c81010703c01c0c0d40c1803240c03030b020001c0743c11a11070980b010350780d4020038030140203481076000141c40f81040d941200c1c89101021108000d1004488001c00c0140c220300c4040d602c100c103880030602c440600e40c0203541c0000b0a0b15083e8a480c00c50400c05038801c01584017a405005002000c500c0604541018013000701c240c0c1c44000481e022010f0082d000505075070180060000345d02e00801d0001c1201d80c000d94107030f070004c0141d03851038440800c007218076002d0125150003600c0300c2040f0558050103600003c0966003081000c5601a1001944a0000074001420085417100040907a07008603008e0303410f2818003003281c0d00d44c84001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 769142248 1250 769140998 769141001
    0x2031306030e15010b0d020702012c0118050306070810090504030e090906090703021003020c033403020303060607140a05070e090307080f07060b130501061e0f0c02031c0201 76
    0x4052403d01480348000482c0c441070000c58103e03a80071070040e14140f05111004001d40044004a04200051340c4885855003101e0714020041c04214000300c04500110015008821451500c46c3e0b105907100104110358000c142254480103c4c204a10b01d5038a492017600d00c40078503000545844c1c074041c00d00061580c800104054074006560008058881204103a40c514048400034140e5101310070a00050908210100c2071040c80e04000d802d1105502c42c3c1d50850700501159002d030103c585041041c07044402800c0d2881958555910012040f40c400945a100042c03103207000e82e5001030381404010381c00c400d9900c090000015994000e016207491500d481491140c5010a140e02c0041180310700040211903070a580080c4c07040c80c140407008000c0c80d9800c1a031064806580d6180c8154a0392101222004510070000e00040d030b1390304002018000308015035004003108580c5c44141d8404c0c0d04a11000c00c00300003410b00001c69161480040d00d030001f061050000d440d020f00d00090f446405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 769143498 1250 769142248 769142261
    0x110418020c010b01170411011202041e050a06090e040f1401140a0536060117100b011b060902060a030b030105090c01020706050309191103061003210203130603 70
    0x241d8001d200b0584610011140e00710001036454480300c007080441d0000e440c14960442d1602c044c10500011600380500e0412a0042c0c0d01400301051100814004008151020f00c041d060407503800c0302c40340c24580d0003400c46030b00d0702440f44140341b144089004c1c020440c030300d610042da10003204407070301100344011806040c000c1c0c2c82c4c0d0580c20858011803816a9503003c0c03030744900c0f00d5011001c4d0201e07040000d900c5000344044440c0b006c005003000d28001c503a081c08214003170002c800d90501303d50f4900d030341c480c68114950403141c80703a0f1030148410f001d603a0001c0e044032a030317a43ca400b02e8039040c0c075801c1500050104030b00c004c2d0b000000244502c03415406070056103e029003103008010941d40c40c0020f41d1100d54122203240140c00291061050a001e80091500504207204072601018508000c14600b441c201050310040cbc1c44000001305032504002e10b6500040442442480d1031031a600d10032150003800b1141106081c010121402d64802c00541e9001000000005ca4007a5038130f1000d00102031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 769144748 1250 769143498 769143517
    0x403080403020f030109150c09051002060f070807080103020d110d200916081f271e02090d021801051f39150c030e1011041802 56
    0xf06020399070b20301d018800c1c4602ca54020f80c0c5244611000240d51000340790000b118028418194008112a25000000c030110221a0000c00090a103960207400003000141410108458842003003c10399110b002070b41120f0f815600003400300d1240c644800305081880a02d40c000f8015036060091000a045083d600628846c145c0c48201444081c0054404100c415031307249480038001c200c03118864203800b03a000700220226003140d4420f00700c3c1940c501b4254403070400c0d0030103e003200c9811110346000300303804100304504010040c452514800c1064007400700218159011078915026100c03882c085445d690b004004854009011080240700642030140c07500a1000044912400040f21507112a82405845410205d8501404a800020111002e08502c1000005031540070402103500000d54414900b8140c4030311a040900b044982d0880803c1c02c0509100100e00c3c2c290001ca40302060440d410740128204402c0224a503ea01c01c2e5400441540c0140848000015103079000d040c2c200c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 769145998 1250 769144748 769144759
    0x140705010e0714010c080301180207020604080a11090103020f09091915050f06150304060b06030a0b030d02070b071b050a06020f1501050f0103020a0c0219030c05060a050909090a0602040308040302 86
    0x3200004441d00c5648002c010706d84801000107000c0c16141002c0c11528010070312003d86010701c1ca6005c0742c0c2c140c003da4007001050380300740c40c010100180507e42d0701c12900309803465041503156400040c076810120f00841d01500d0f071071002c5907083c0030a020340444901d19182d0303019445000c1c9003524441083c050140007261410300403440300b0000038211402a07000514066000300d00405410075a80060011101c99a940004a005481d110302662098180c4000041da02050348141400c2c0582a50340400b1508901400e01040d1101001d4911031600148481d0b0b05242d007584001070324150b0381005620010001c40000c14540c002032200380f11002909403a18961100c1000340454820702520303510012403041c020641d4400c0e80135000d2000c85180c04c6810703c1090b0046100c00c40400348148604641e00410f00910511220020040c1815104c0354031700b100f080b50080a03800b0b0040742c9403140304000f0101d01c84200401143d400150401411980d4a03640c0c60000030341d6000c0d20040740142c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 769147248 1250 769145998 769146029
    0xa03050715180639060204090e15150315091e160e0c0d142a0703030b0303073002030705100f180501020c120415140705010e07 56
    0x542d00d41200401c84002c0c2c0c0303d413400142075107842d4071200c40401c2000710000c55642c0382c451011900151220403030280800603a076a040c40c0601b015600c0c1442c07120142c0c3e01006169030104452011150b00103100701140c3c0300441d089001a040c0f80c440010071103880030403000c1c044803590109100d4803002c543d496000c0340caa41202c0c0c150b16240d44201c040c5069440380810040401c100c015158000d184050703641c513104442c0001c4084864144101030109400740800c01034084400b540501c108800326400c3d5400700c92a0603000c248070780c0e0070045c01c154643c22484d2150701c042083e1003c891740300d00341c044118a40440100c140b001a040c8042617090b136064030f40d40c6070001c000c4a13461904403000d003800282e1400070300702030b281c6880c440709143da4408201011150b280c0e00140000d2083c00056a82c0fa024210240f4201300c0c80b07125901c68500f004100610a241e0b06070a251105030300340b0b01180e40c9142029501800f8107100580390354205900ca1580007804a82c0c5815959500612182c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 769148498 1250 769147248 769147277
    0x1022808070809060403031a09190501080a08030a0906060b1603030b01050c03121017010609051f090f09140a0308090f03040e090115150e0405061e0a03050715 70
    0x4445059508483c5a04044c0c01700740424840d403c100400411032101e606070807680b5000c03030800c24046a0452100c401c00480c18542c40e107a00901d4010300c0102c0c000c01c450304c42612190500d21000d8920038006541d4809001008a25040b0704010304ca554030103610307000c4220210074a2942d03240704500007490444049143e40c000c50996450403d901d006500b44401c40f080c0c090280f03409042c22840c820320000c001054002020040041c241410001c65010310f400040010340320040c107800c0c0c000c000140c10360441c080c40e21841c1c040b07030b0303040d01c006c10000c8000c0d1a0038000c10302c004004d440303120303241071801c0c1040c1c000917000001c61095071405910b540740000a501e80d034046001d041caa400821040058810241505401858501c000942160b040c1090140c14241c0c0d0320403504d0281c100d15503203034642c01c0380c81c00b000504243d07820300c030924141000600241140310b03110285000498a104240c40f00841d1101440d8014100ca82d26a101e410400c980700703400f0b4005000821040c5402c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 769149748 1250 769148498 769148507
    0x61b042c010f0f1d070305130803070c11030a080a2601030f022d010f02101b020601060c02031c0e040614030c01032a1101020307030213120507170102280807 69
    0x40d40307031104104d240d110a0710480207004003400301c80440100b074290b1004240e4200056009080ea032315401700e0b5422600d003181080c9010034445100f0b400c0544044007003030b95082142c5c3c021800c3e24102d5002c556143d20042c1c031030319040500011001001c008400c20a010b800b0464039402101c11402d0f003c0a020a02e02c105144c03029039a200c2a10600304540c0e5008020703440315404940146c41103403110740155021140040030401c05c040360112000303201c50301484000e01401311443c00101100042c2c01003540c5541c036038081c2d440c0c8040c103000756280510600c04960900001030040c40301558603c041c0d440c19000176007552003405110481265980240b099088a80d140e00f0302c0168000024003003584035240813014000d00012181c1d45101c0703402840158860300141d140142c4030925890842000030007500150381c08051070b8140c0020030f800140300310843e0f440e5100294038131641041e440c064040c4030209014070b6028142045606222484010441c00303607526081c050b96800d00c11207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 769150998 1250 769149748 769149779
    0x92e080303151c0f120e0301110d06120f030e0f130c020618120c0102090603090d2303150105040503011404110307030305030109050c040e01080a0302061b042c010f0f 73
    0x402181481318004001003204440c9244407041d818101c604000a41c042801e544080805042d810000610848004170600c18074001d016600f50020740c001d0315548200303034170508050180030300022691001059841030084804a85d010b4441000801107a00e42030241c885452498050301079600001c12147d02030346500d2203036044000414140c1100c41c4050940c0c0d2240e8884c0c000c0355001c00ca040010f0b11070100450185054200030004088072060040c10740c414250f84420741510b03810b018202c00039490a40360402c120f0b1a507140c4419145c40182c445128662100b6015400c2028400c40140c5204866104034024030b0364000001e1032100b0181c42e1815800000c000c940c007800184800c00060703210079400818040c04c68606500c5842468890400b41d10880040c0c0c4901d03c9802010782c18407815401c4207442c80c40307a003120031041506000d401503004801c0c3c01a803502034140036034450381c01c198092a96412810503543c5440100500c007900f8020160011041880020b030706012010a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 769152248 1250 769150998 769151003
    0x6150b0a0e240415020d0807120e21280c03051b060f04030f0801050919020d020a020c0a170604020f043305092e080303151c 55
    0x51941078520300030444810300c1452030454031640d0030b00c0516454509001840079001140e0074403005640320030001d2030b01c01c584064004020150052060264004000001c10f2140702c1c0301003103106007903040f145070084c107101d4501c0400c100c4000300e042d47c5100f0014000d4203110004040e0540e6001646045401e04941e100001aa4034110354007003403040002e48102c1c1810895049002560a69a450a038055811800c03151451080c4020180c0060b8842c250904034280300e8440d41c0350000042c90004000c01803613500c40d0b560311072101504158103c40412103c042c08540354061910000d43d200004850030b03024411421010400360408807892040c101c5240080a03030f07564903424802c0c40c246031036101d034025484128043e054a034a4071203488048810803800801001259800008100b651010f03000380c1504040c41a4101e00100046040380812150201d03043c03052252103010190340c1c80039120340000700900100359031175004410071755011114000011000b0124408010142900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 769153498 1250 769152248 769152257
    0x1017160f0c0c06081f0b0d0605010c0b15011107090504030801080f06130804051017100e0c03060f1224010605090f030f070e09010f110d150b040306150b0a 68
    0xc000f400c1c4030360341c6258859045001e0082024100300c550141c4907468120301080740c8080765800701d0805c2d92080c00f000300000d00e0102002035050b2200c2c0c0c03020101034688002080c1c000b214454036400b604c15181829164030807107481c82d907a044100300030441501c0840c0010446000000c10303003000103641c581c0d042071201801441e02c0f00c1600c0949614619000c13100702109100000e160b54401d0460101c0c0181c80d04e40d60944400d0701172503210b13107030014140341d0140c50020040c89442800d85040342e00484e003d803101da891f1070b268006160500000109a4040400c003005a000400810040304080b10440b000c40442c88402c0001c0038103009004003400210203202d480d400d840e015110583e000c0000d03040e00e040981e10108141005800e41120182c0d2880c00140070032a10248100e0f43d0b15040000b0030018483c21030b501102d580305410306441071540b207030b0105e2004500b020300340c0010201c0b4005155196aa40342c00380151041910022210700036050020345140c1442c1140c6064400d981d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 769154748 1250 769153498 769153523
    0xc060703090c050612090d03180605340f050403020f0910081207020a0b13060c060e030307080f0928050309030115210b01051017160f0c 60
    0x11802812819020b490318002c14000040a03203605004005003041d9480d584600d02d000f840e41441e1120248a4a00705032800e400469603c00c1012201310007940070001050a45954144044212a4a480c01c90117640c400180660729422600c141240160707480c2c40041c2e0300401400d40300e42c0550b100207900846220b43c8e0080b646821003c072544101202040714400b621070180a01c0c0c0401ea00580721001c0d4000380140c1903190084c17501b0000c00110740614905800c0298051100340b40d881540c0900c0b42241c1c40e0020080c3d10f421001f04004600101ca032207141c5614018211502a00c039074a8a10880300420450000440c1201100302820300345940c2d444512000f000d840d40721031081d01c540c00103001040c500c0d0383c00c0c0181103041c1c00701c400f1149083d04284a550584d0003055500341041a100c404000260308400b640341150011100226600c030031010941e002d52400804c4070b8a00070078400c0050018100d441015020070075070314111410744003076082d1000502403e015201508204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 769155998 1250 769154748 769154761
    0x151008011d1b090d350c0303040609030c050607080912070510050903070503180a090b010e1302090d0507051005040e0402101707110607050405061603090e070512060409080d0e070b0c01090204110c06 87
    0x20002f40065100c1c0c9030035060585691a000e0820205031115400240c0c004103100880c2c404120306603880c0c503401d02192801d401540da10341d07541d50100c0d41071007440d152000a5204107051040d44c103a140c0000c15250f82e45400034246080f511071200c0d041c45019004400701d2804010b20404881c2d03201070b1120010340d0104404c001c03407603d50b102002c0109408011220302074441040c294051031041008054181c10442084142d44100080504204040c4400c228030140c91821580058040e14040c10419840030120307840c03d0984030a0119500c90014416095441a540115000410280c0c1c00988400030b040300c25204500c20503070310a0041c084280108007000b18410824828104a004207a4850072080e91000464003200407800c0402c0f0044080c0100000642c800c03001c8804010310260f40e655404107004400480d00c0a50355a050314204601c1000228041c00c1c00c100c50a8070742031074102d103d0103001200d00481c0942d00f0300c42c50410000d901b1060b50100a110409004c030b941c3c908 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 769157248 1250 769155998 769156001
    0x19031a011808010c050306030622030c02031c080411011805060c07080d0c0b090a02060409050712020423060909010e151008011d1b090d350c03030406 66
    0x1441003052240071031000030b0325002480741a120f02095142c0035101c0c60003c042506000e0003c1c51007000c003070740c16826403260359900c01440c0101d606040500c4091180e0000c24607206c0c9409110003100200c02401000d04d03005550a88510711803c901a06400100d004649406002000c0c0040180c00c0e0f9092000c1e02d821800341040d0f415100890381e0003540c07a41c8051900001c448051b000c00c020782c61040901514541e03c5921074003881c014802e482c615800b04543d44a83c2c4118241d06541d20042141144680e240410b1403054000c00c3d0349880c3c9030006441c1800c141075051001c0d15a540d48140941003440541d482508000c102124130383c44c020744900642c400500c2500da82180c5c0000700c50b6a0f40e01c00b0074500208051f030b51010f1640c1000c82840d003100440700c00b01c0d0f0481d20141003241c0c1c0a02d0440501400e1152030005848084c1ca40220b2031a06520000419004107002000c42044001c40003100c004402024070500111180d80956640710301340c0c000086400800c00100031032082e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 769158498 1250 769157248 769157267
    0x140a0b0a0b010513140a0803270d05060106020c0a1d01030f0f08070303090209090a0f0311070f0816061b06050601121e0e0d09030618080f19031a01 65
    0x107040141c03800e6091310099600010039040080c1081d01d00c80360a4032800e2501e140ca0103040f12000131464100b14040b0012403019404490500040d0301d400d208403a1550491000c100d6440070417a04c0c10358486c10065140e203031812107580244c2940750001417480d141042814901c10b0032184510503425030712514110721807031a0550302d0b503503800759a0000907500b01c000c2c60810b001e560000740d0054203104104100e24050040240f5900c20040c03d004500520302505081d941410100307512a55901d2260426041c1c0d400070b000d00c081036030001020407011801c0d42c51200002c001c8030307005843d10b0003510407060ba8102c940498080025500c001040da034405a049241410100700703007039280d01c00c5000e907000b4107011100d0045003040340000030f555010b14010004240081c20301c450340500020038400c0380e440301070071564458546a00c00c030354100c1c048540e6500312900d0b580da680c0030b059080c810f61000a0200c20000402e0007181c940f0f01c28886d00310004105041082800140b47c01141c0b51080c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 769159748 1250 769158498 769158521
    0x160e0411030106030b011401090512061f0f0e0a06050108040506010e07030213030f020306072307170c0706110a03080106030c03061707080c09101a0d05040609140a0b0a 74
    0x581c0d100c0132000c5070848203503038000e004222080c806c20390000001425040715921240c016001610904908007008c80c0e01036101c090904060301c1802c24102035a030003000e6070f1042c982403c1805002c40c800100fa0103084c440c907030000c41400202d60300c000450300c18004540c054020340001c4014081810704130303409500020a85070150420019000d01d047c1e01c03040b5071040b45c81e6010745891808500702405000da1040d002e0800c0c000c4903403031908081030443c0c81402082000700000750301041100850a29007c82180c003840c50705c0e28400c440460341d0f11258010f0030302180042e4400300c070001d00040c40c2032195034540e9400920b6482c083d0160050320b00049503409040c0c6580c03002c00e0f0241016116504000a5002800001d141c000c0303041c00e000314548113a00841c8288104030401c05801184d40031950084181000d2030002030428142c0d006d00c2070034120b0a401c00b02400305200c900c0d0844045280522298500030009100155441071600d4008107603080200000c3e1500100358802d035038580c1e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 769160998 1250 769159748 769159751
    0x606010804080c0c10050a0f17071115010f0503060a0b06070803220c06030f020430080f04060e011805010e0d020a0e0115210903030b1908160e04110301 67
    0x40e4414009900040e400c0d09081c0043e80110324501f0055004280d81c100c100b060401c948081490111407028030070041490301030040380019264400001c006882284c038201060040c0b9503110b40034925518050b201c0c00e48280708030f0000c11491591407080e441c480d50010491854120542d40b51300c102c1c0c100412141e4000c180061040c040c4c8101d910142e0818440c1d680111441c3c10610040d080351800c40a6070fa041d44107100900c0514043c01c041c48260520081c801c06030f03000c410308880c1e0b804000394020001c403004a901602110705601402c144ca1a580b00c011458910720011240c0d032044800000752201c50000c100003950140e1589482000b0140c09001400c203980c010078017000c0315900810200013000010400c0c5c545503001c2c0340b41c807903062a014203080080c201754010721803009181325065a07904107980800d03006e0740c0b090350300f05400f5004c1484c582e042e05216080e074046100355091800781000075608000403454400075a1604500a10a501c80340c803203040c0d60800e40394807074066 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 769162248 1250 769160998 769161013
    0x118090e0a06111c0908120708060102060901090c0e0405011503032606090411060405220c050a1d04020d090f02040605041107080f09060c0f0c03070f050111010b040623030606010804080c 82
    0x4803070481142d110b004c0323641b6068841e06141c80028034090009000c56096407400003007000040c51007080f01d003112840c01c4070b0080758445041c00341c0100051003118000d030300950300000c10140c120b100081104825880c02da0001c0700031001d045c10319000c4401ea07510080c005d001500143c11985140e40703c8001070481820300303880c4c00101c1e0121002c400c00204d40021100710080c14009805050303585040c49c5003e80c100b02c01d0381406031460008401c481c14266003c0c001c0501c2d07032110b07416030384101c602610038040910f41e400c083d8054500e01d2070590180c1c0c142030010542e420640614002d0204603001d06150031070540380e0714010b8011065204100c1810404d5141c1c80da980406041074400c1072000d01010020240c072146014140845c1c00e0280d0400401080480303c0d08500c0300880e103082c01c040000510a04c405401810103252282e0320914100c00420722600410407601d140118591441c12a250b800802d5501c54040b00e4081c00120341c84001b0f000214101301030590b50300e0200844460 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 769163498 1250 769162248 769162267
    0x9060d0b0402130509010f140907180b0304110d0c14060d060b31090c051315030e15040305071a01080102360118090e0a06111c0908 58
    0x60ba40034101d41c01440720f250405201c0c42c94103a20b100d00420a8a0141c600d403450300b80060303003180c030003c002c0748100084030000d140719001d01c2094041c140d60a030036091482d00c5401d406d00e181c0080e1001d071108210200c0c403500c18109000d40700c0016801800da043e10740d10302941900080700f803001d01034000c00148000c81002c4481d00510307000c2c1c060a00419200c0000110141050043c1008ca291142d000e2100340050780560721a1415140e14039001b24000c07081d14426940d03485806c040d8200c6500d14a00045c0001d5840d00b48900d108007541d00340409440410302555406080c8a640f00018014000c00d000a0080703000300202c900c25410a8003400049859030403a1009030b0002e581ea0350001100d80401e00c0101a00d080001c20001444504c84407420b40c0041c0e05d0294003032418403840d0800301e1400e03880c468a00700101030300c2ea418041842405c81250303c81c001c4450031101c0e91b040119040802e0994416540078035040102c20700340550790100300d0082e1142c1c01c0169000b0104005144d103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 769164748 1250 769163498 769163501
    0xa08030a180501240f1401050903150703420f030b0f1b09090a1803030e0c01031e15090906020702090f15040504080c010903110105010e0c09060d0b04 66
    0x19160280c000003510710500b03426658490603030400c090440c0d113030f903000b4007541d20244008000e449441c0040c1000b1054000180c3e964819a6511981403081180044d101d400f07010030b0510500c40b69800780410050204441ca414082c3c20f05c1c19485034134004c0710001c000c4a441c40401c17005075600d01c400615a02e07218004038000c0c0b0303042a5402501c0000b0881c0d0301c0c20101d1200d4002031a084401c01d0945d00d0380c0e28410078064951020310901c1c5201c0071410b51822038110484500c2800082c60115005243c05401013005020790b02050041c0b40341c1403034640c000e115509900c81700545000f880d040c900180001800030419040c11030000400104064030070744030f40803140303204038001a51582203004001003040b009003801502185902000381e00a4001e140054480050301d0100d002c5e04c407480c11280a024403241c422141d864110f2480c20705078010440200c21840b00001c11844c0d2300c41217081e8568400b10303400e01200c1c50401003044182070200081c10201001c002c0001c7d141d00140c000380 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 769165998 1250 769164748 769164791
    0x20d0c060213050a0605030106180f0e060d080c030d0b030f0303040308090f060106030b010e0f0328050a0b070f05090d020f0d0b1f050409020315060307150c0618050a08030a 76
    0x14001031b00030005010542d04845a00f5201a8507046c000b2042c0c030b442d05405001425014140500001c48003150142d00da840c180083d50b40d0015100e81c481e5011042c1c165a900814154503046017850003440300b600300131a1300c5071841d00354000f80d40f65503a141c8040c3c4070301c10040c100020921a410041c45100014019a806401c1c0c5a9000c180600d009000421400030040e8032849025001940c0130a9640021240c032030540e401481c507840c08080010090411042e20094450701500840004000c4000c40840c81041c03543c644880d280d001e500101c4140c00342c800c41503041000940c0d00409860461010b0502c140020b10030709030701e030032540c2e08003242e10700b621200780328403c0c151254a424400e0715500c0c0a000c00b50303002c00200c40c1c0c580000ba5a903031104400c44c070204c208000701d21181c6003803100c0000340000c42c1c41c0c001c0c2a000700300000c0c0121038840b400d507042403030a1046160340340d03510101061740790004010300000116480b28011640090440c0140c3e0350307588059188450140102d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 769167248 1250 769165998 769166009
    0xb0f060f0f030f16110703060b0a0b0c06060109120b040f11030f0d080105120601140d051b1807020c09181e060901020f030705090612190c020d0c060213050a 69
    0xba50a061000f848013500c080030907884148150100d4000c40780c14002454401c81e500540d0225028280c0070208282000b640c03c891205130f17002a8010442e40000343c480c0c0102c90030399454a0385560b40c681c0c01c1c03503006412001000703100300c80003040110b0740002c2001592805140102a15034540c1e00007450140d4a4003c5601508543c14600c0080d41000300039005180c29500580c0a00300c1084042e00e43c02c0500640054840e0100590120744840781071050250b8000102c80c2054841c003858200d42456070302c118070404100843c2000784e100050101c1c06125a80c00420182d1185010820384c803000a00914102e10700b90f00e40118036000b0481510b44642c1c0714800c148484582c100c050528000600910090780101b004e0780d880400030303080300c0d400f0324540f82c0244c489118000042d00b0f8810200045495810b16050102d01a000c80080641601060003000307280c188204c283d0b29145503903402800300b0051908600420f41540081141111400019505a842c0d00009480321440e4029 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 769168498 1250 769167248 769167271
    0x5120d121e140702030309070521030403030917030424030f020a030204060e03010e070605070302071d0105010e040b01050306040207020310060608041e08040510050d06090b130b0f060f0f03 83
    0x2444500d2520b442240c0c00c00385910296183d407070b1460100341d444610b8070580c0d00505a40c02c00d503522891a5100f45168500202034954581c0d603410300808818013405551445002c0e42c51014681e100003044600310703451003001944078280322036408800319522a018050680ba250508841c1503203100074009126035850050720365003008401404803c44280c12406680b4000480c80d40100c001040c07401c8404502d891a9038150300c0c40c080b82030407642c0d0b0001100300580d60a50040495a5100034183d400c2aa00c241d2000313490010071082c0e03404c0010303250110302c0c10030205001742425001407036224000303422180c0c802d5402c02c00004035641e82d44401c002540d4101803004000c50442010716442500701c0400810322191107050040c880e5102e5144502c1c0d8807415502580d000d00103039221020072000c100f003040d81c1d800218000c0c00300c1a464a100f2040c038840000400c00354804c0c070401d50700c06009940d4150903c2d00340300171940324140c00f464184061241d0045400c00030000c500c00c1d40315025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 769169748 1250 769168498 769168511
    0xe0a121407080d09170d20030f01090e011e060303030608030c03040b030403110115030620030a0b0411040f050301060b0307050711010e0303130f05120d121e 69
    0x2400180a201a01000d420400038a03020510142c2600e101c12009900003511072180c0c5850b0004001c0c090003046510008a24140004d0440e031220004c0c8207503540040c0440115540100315120071159013042d090100018000c44249500136200d00d03a4800002131030406088006c0c80c11140003e12492140d03e401043c803c056060280600030a038030310095060001c1d013074001d52240038501440d520290701200140626114004800d4804010300003008000c0c10a00903e650301882d02054174424200002480f46140c068419080e60254078260307415500c64055500c0600b12403010b280d845920746c1141c103242c04500004000501e010301d1204070707440c035000038182940d0156200809840c0c0510070014501e4204003290812940180d04508103922200141d42d00711500342200e42512011844280c00407861460b94155400343d442030031815030b1032081140c1c0d84540c61041501e03411840700c00103881c0c0640e440040c01510303441c0219102c4138042184241c603002601c40c1c0f02041d00da01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 769170998 1250 769169748 769169783
    0x40807140a120f030f1b0308042003070501080a0f0c050a031b05090d0204320105100215070e0904242c070902180102060c0a0212030a0e0a 61
    0xe070300c4002007101d4070400c0c50340116030710b402407245000348025090022038580e10205030300c19240350301c0d48400c0744020364001d011420001c0080b002143d0484a0340d89954200100380c0840c4039100d0724810041c000c000f03103401e240046400001c060250141962151811404044203018a0070b00841a5a0382610360510a10040686004d0302502d8201061001640300d09a03204080701d41c446800d0320240014007203440482c0040443c108800150055507104c40008038003c5003020380d04108080d150816602c42007040903001c1d0220198003d80e0204421022249012440701d5102c102418100078440c107142c003142000300c0840302180e11941d00c0c06941e02e01450404420342c209290107080000c500026a040f2502800d00c1c11a00c007120f1101c0110495013040000d50f000e801051400d54499021101c00b818190000744031901500910000400703492a0070150b0342d4101a41c0c0c010b1030171005200c401c5017035502c0a400030b01e00d19101d66000440c40400c220312451584070310100780c000000403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 769172248 1250 769170998 769171009
    0x30509060705030c1204140601091d0705090114010215070503100e10050103111e09092d070905030a051b01030b01021e010b090c030708161d030304080714 68
    0x142941c05200c0280148071640300b155060320200c40080d4010811a200d03030400603600054440d10448520841d0b0000c00c03c4c1e000c51f00700d803040980c10202c408c04212105051929003480780074031900f0840380c1004100c100c0d40b40502040500040c0161840030700c1050386409080780440d403580102d0b0000050283c0108960b90000c028003040515010303078280840b60522001c4144030309410580c44000c42c075005100c40c1c00700d60300d0714055107017401103c01c0118034814541100d410107200c1d585810002d1902503000028414440702c54042052030150104070042030300002d492807080040d0783c0c03004134140c0c80401c00c0344a100e000e40000c0c07a00b080c1509030510300b111a02001d0b41010704016015100741d03000103100744158119085001c0b030580c210007950041c038103500240d81c40b91035030b810303c2900e184450095000319030540d2089529641c81c10001d0040301d8960700c44000903980342000c181c0b51602d0115001d00390f002401d5034034083d92404d80310300d820703255000706000103501702039000289401c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 769173498 1250 769172248 769172251
    0x5060613020306031e010e0f071e030503030711010912050d0606090b091e0d030c03020706030213050d0f080d06050f030c0a15090810060630181203050906 68
    0x1428081d8910301d09403011a0b11004042030070480c0003081e812500c5540800c2d0005021a8410011941c10340a08074036940d442010344161101c804990740c01000c2035000341c0e8503d05482d081001545546ca59400c00c490f0301084000d6502295078885501000030f0381c5014110b0003404c182e5900d91502c030407112450403600954003102c140300325901c040103a01710f814140c13085013070101c895680d01e4800e80e28411080e1396240006a01101c0d001110042540180c4502c00d01c502940c2201c0120351030b00826001c912544841c41949070303040508021519150f00034000c1c80b03114500d500140d840c595140142c0d0707044000ca081d08144c64500502090600c0c0100b00d10100c0c00310003d090800048011a221544034095030000500d1107244c80065030180360b10000a2076024100e035200354100c3e1424000344214001c01c0f0015a03094245008043e03085a448911807040600b0034001e005c00c0f4280e8020b100c500340c40d1010820154400008c42c001c83d5540e194400c9a0700d02154500d404150181481030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 769174748 1250 769173498 769173529
    0x905060c3d09051c0302040306050108060f15031f090606180f2304020118061e02011514012d1b0f0204050417030907090c0302360d050606 61
    0x20b030a050300e002c250009032811001030294201d886030801004200c01034480c90304082d0146051100000340d10744002030662140c3c41000c0303d42d0382c54441c0441420302c142441482a03142c3d205440c0004154020315500c0c590b000340c5071002402c40c49030b9a44009940c3c2d01c3e132101c0441c105203040800030740d03040d0284c42c145110015040180b40111101c00d0740d01c403085401c4142c0301d4203c500003421a40038901d04c1c4810703c01d801000035025511100181340d2031010944007903130146010342c00c00d028014051912036050a400c1c002d40107040c40c244415030240090240e0401010441f10041c00070440003001d00200070328403803480e01c01142000b0708004138200f260702d1a14800109980442d1305c043d290152035074115400b141c59140c90502d0003110341c01d036800502500d000410b000e46250001551021949080030600200021200a4040380030f096440d407071000341c0148190100c001084c0ca81c07110030f0340e4114141800507020115031003070b24008040380e40368064018400d0070300e000240010890b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 769175998 1250 769174748 769174751
    0x60109170f01110c1506040b031905190807060e0106090911030d020c0a09090611120a0e071518090603080403061413060903020a05010e07031e030905060c3d 69
    0x10b40a4166903100610b144405c0840035130030105d13105650b0b40d04407140d003120040441d005002d01c0401d800501911440840e840d10450b00360301c0202d101d40001c000c10f86d802152107810500161103a4004e80054201c9003415543c940700850f0640c1944102c0c450130340034a41228001040b0350901d807a0900000c22001958030044151401d81d0310300a901c805c0e1440703101c001c00c0d105540c0c40c2690280950003521948000c003c9034104014035502040c0b40309100d000710920440c600c24640540300c10160144003038503405011118060390180d00580d0a100e46140c0401c0354130b6490120300101d4800350021075202d0b400180030800d025141c0100036241040b00d4030125641451010100c00a442450040c0070944170003a000a0500a020300002250070200a22101b2030741c0d021030380c440c03089000848402c86912066400310000303c4000201c0d55043d101c240d441d5007810200107440d00f0422000000384210044000b40044103001004180350540d4144070114028041d105580c901c03010a01030507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 769177248 1250 769175998 769176007
    0x1216080319050705070b21070e06030c0c0a0b16090e01060c031d040501090204090609020c030702040b0616030f1b11091e100617130308060109170f0111 67
    0xca501c81d075001d1440c10340c10001d0f541c640c41d1900900300400c690203248580c401140c1d08085241c165103030340e1a1000055207003a2035071006415660b00040c2401c55070080360034400035006200c5900200801e0a410003210b0703075410160703200e540c03101c03007210701c180051041510910010b40105d0300d140540602c007111f6030190b041c088010a010003070080501041011483c1d01541c0b02042402e00b0707001e10203001032280390303100c8040801a602c1341c4a0080018075080000402070300c103200740d0b040c00712007002540c40d06000e6001c200242c01c40a01c11a84500d0411903486612007100d80300307850074400c0d02c8981c010b01450101070701510701020702031000f80011071607100041c000411600c52582c00c4603112841e0302e400000e850411490312003115482544400e1200e10021850110100d5580d99034800300900b60f41e540c0c0b41b2003101513851303881d01c20011020a00090043c1c01140d4440018500200456580d200104043d540202c001e04590484c524807503000a0a008468001c41103003490b52a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 769178498 1250 769177248 769177267
    0x40c0906050703080a0b040504050d121e0b030319020c0a0e040f0b0c040b0403030905100c051009080906190210050c040612090209012705040b01030210030b12160803 73
    0x103204810000f420028554002201c464059100c2d4410b188041c1007004185043e15280b03035100307202d60703085000ca0342d4400c411440301c0080c058950384c5600380c07010f840522000a10388000e01903405d0303020b074940800e0081001040100070402107800e215801400115160010310440c1b815075000000320101d0300d000c00c0042098031a400c102c1c00c1c0d21035000040e40d61041910303001c40c007894200e54410b10001038004241540404580141d403800c132a80c011030345070303c0d000307407582a030f4080300030302e44c0d0800d41404061030781950001040c1402003903e1880c1620302400542a0740c40446c86100b401c039142255049590f0421400e188214810030030809420031a40c0d00030300d409030344100810080c401c000000142d510f42c1100f180302e640034042040ea56103402c80244c0d45ca2010038401c0c0441550f885810401e0700c0b038001c0900641c0c200b070304030281da421902849445990301e0210000d254a80300c106909444507942e03070010f41004070203007040c80004804120280b045500601a42d801400072020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 769179748 1250 769178498 769178507
    0x150e10060f050c01060b0313050601082103090109060603081206041515050c1002190c03091401050717041a120c070c2102010906020d08010e180615040c0906 69
    0xd42103020b0800588074040c4100b264050a102d40020210352804001d11010020b441020610706100d581580c00982c1c035003080c603964010268050707030255003007907030340480c42c4900c0001c42c0c0047e61480081441d0b400360301d9082c02e650305580120340841c000120444418401c03100960820421a024000500c800141140d818034900840c0c10440c14071417a8403a00b0302460071a0040c801e035400351001e50340e01051280083d044001e80c4100b0b01d00ea250010703d5103200b5403120443c82d5040c1c56100c0c2c007a060404000d6660280e00010b030600c10b08000200100e49012021049102d10751481503896041421800d40b0f61102840300c0a644414001014100a0792080715070100c041c2c82040e490b014203052080114026034481d8114181004c19071007485038681105811034002c0c0c88100305141d4444040741d80d01005038040001400c3d00c40140300c03103144550400d41202210112040c2103010095490a02c0000d80301c0318640d114001443c0014101806480c200d5101820b20715801850b1540192 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 769180998 1250 769179748 769179767
    0xa0201032324040510150c0b0f070905121c1d061813050f060d0305031609080f0313052227030f030e031813090204150e1006 55
    0x420031051240d1082a096500340240400b0340c000700184950705042c004403000300303214040d1502d0581003098480500e8004c02038042d40b55031000805006036192243c070b450046024003078400f001120a40052180e9030000180351a1510030080c0501032410079000b00c101a041c4d850000b4000c001d0a000d080c7d84d603e20392482000350541c0d2030365883c0004109020403050f070342c580640c070406035044003a600e0510744c09171b445030b0307071105441803070f0b0300c41c0d80070800c4800c64070f10003c000440400020f0f48440c0f900c00030072609615800e01e26080c5407100c007110b04003003185c42d510041d0b46c80030500c020b21045000c00c070401418140c69a0b42c00c0c80d0341c0000040b0225010005228494480440403010182c0300311514aa2202c40507100c10340078a443d000b81245070100c004c0d40082c0c00c020341d5101528001c0b046640a003e4a24450403103210340d0103020324140701c404001c070a03035620f022103005a00e0340d0040c0016501c86903003111400307060900c0700c040e12202500640b40301c0e52100060040c4c0d5000003408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 769182248 1250 769180998 769181011
    0x20d05090402030c0403060929330405070f1209030503040b1b0a030204150306080c0d020d0503030a06150c03091716030302011e05090304030f0c0902030106020a02010323 75
    0x5a41d0f44d0b10761080303e19902c02c0e58030003851103203008030314410b00c41c1000c00190910710301c2003103644140c04082d406401ca04269402000e024070040100604c00b02c45108140704200c50b0040c2140c0401d203400a0700b22001103904c640852a41c849020409074004003c0055031410407003005410702640b8001c0c11404000e100601c14000303c2c2c042a42c26440d00d03c0c034000f60340340b02440c0e40e42d5590007400038040d404c1440790080e209a220048420603020307000e018151403054000b004010401401c01000d45040e100c26600048402e4180000c250240011841090600404103500e4641410301c850420496000350400102190030000a544209084c00701c030024509241d4103204c5948071401d103100380242c001404010303a0000f003010780640080451364030b191074400b0b00c038444001c082c0c180c61048031440c50355081084140000340403d00034107505402360401400321074035584060100da10a81041c00903a00c401c081808640c0d040c00341c0c882c0008003100f40305030745642c400741c4201541e0142c0031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 769183498 1250 769182248 769182251
    0xc1407060e030c1c080f090a120314010f060e10080127180b060d0503092b08030402030106060509011209110d0f02031002250c1d090706020d050904 65
    0x1c040400034100103503801200641d0a0340ca01d8132808011400100c0309007003440c0441c0203a00001c814a82e104001403003942e001300030b040345102550319081d1068809a1003400d0542e11060356804680ea020a41e001e131540c642981c41080c184500034002001041125200300d059400e2048401e5108004c541154100d00c00020085910b20079210502c2168081c00707811440d140c14045159440d0315441d80b1140a6503c480058407200309009800c604480003400c60b520802c4450301342e01b0441c3d07187c443d4009024404411070082c05100d010b000da0101c05440114002c07041c0400e514083c45200e0051006043c414946643c000000c0c00242a44031002182a130358241c01c8140080725a04540f0a800104480001c0b078140c50b004103015071588003070340248600f40e01e010381c015081c8211200c01c06a481d2480000d40906c0c81d105030b4010043e011145d0103102003001036090b41c0c3d086030445211044c65268864902290043c2c0b500815500c500110340c002c0d9447c504030364201c03003110480301040e01d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 769184748 1250 769183498 769183511
    0x12070b0403090e04030815010e010c020f0a030602120117011a061e0a0507050c0307260718020d14010509130c17010212150105090409031b05030405040c140706 70
    0x5042d250039615900c012441984030080004056000080d103200d890542828001100484011105e00e00020312450200312040320388009071605600d0b0700b03941e5000130800d10095481c1d2b0382d0b1105980061502c8240ca040c068010301a0006140c00c0c909a140d1580003040a00700c0c1d0b500e09050400c500181501920f00001e0000c0071208401040751214107002102e07558009121005219501200d0b00303640320b02030780603041c205240c0071884001302c03075100200da112500342c41e40d05040b21b1048400190240300700c41c2c0000701010300c1e0809146c0328040c020300513240c0e945424071130f050746c40080e61101012007003c014400d40d918010810340105c80501d51580d0244903141c2040400c1c0f10741c1064440040300c22102411100540090802560040e01d01050380c4500d0400e06080b6030420420303010400a02100c001400d10341d01c02401c40b4043c0c9021811080c0459892034980d009200645580d00001018046810103001d1102c001d8024904880010903901817801c007030140c1c9000070070540e02c401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 769185998 1250 769184748 769184753
    0x2060d09061d06090d03150608060a0e01090603020f03150406110912030904060b120712060308031807080708030d0c09051009030b060405010302060d0917040e01080105010812070b04 80
    0xa1200b00c0358000c2c68103951a0b8441d140c0c180380d4403841101c0100b41c51044092170106640300c1d016003018058071420680c075032801c2c10301c26280d91400520b40b03a0418244000018510500d2081e00d000301081100005c1a60550050081c004415250310380a81e000841c05d6500b840c901f081f442d40a9004a40003d100c840820a03403001d1007142c06196000c1d250322414822224048000c00e41c2c181e088508000c04ea5179400600c2c1030303000c2e2118080c6455401000264650300404c5040d03043c95807914002841078903555114100c1d0802c0e601154006c04d031505010b401c58041180e03901520300ca0000700096403910b07000760384d6032007041d4011802c503464208581602c0d01428140c005080000c110001031225040c00401c12200c0b407000380d84000f980030100b40581000d2141606803500500340300e1521101c422035002400404100711900c0c4010300c0f8068081003448090009401240072004455140030812400d4540c107030400e02c220f820054010b680d056500b012100c80c10307448038107038106584a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 769187248 1250 769185998 769186001
    0x9061222150c0302042c060301050105030a2a090e100506130f140f0702060f060a050126010f03031205130b040809041a030616020d030b03010e0a0302031e0702060d0906 74
    0x258020304608041201c10100d0100001003407190381307603011b601c40070b943d520000c045c00e95500b0300c03906405821010721600030618000011f504c01080d55000385004003240d94070512500c840e0f106000c119618440c0f40a1004180807000c0082220030050001c2d0505c030000420f411060040e010361203a44c3c0c0c10040142c0c01a40040b4078640610304103095524003108000c2c0070843c00c030740500041c040d55001815400d10910380501888000d0510600a820300005413442c0c4e800e50b4459070405071310385040c1c01109078440d110b8040d003400d82c00c0940d0703c1e2561038081c1052030300100d400d420034104001c019601c905882d4500390720340c1145030704c02c00d5207641c240600144281084960812700b002c440d001003c2968007900b04a10342070b400c41e440c0b550b40604180c107030b0707603103551100041c0c1000783e109041da4403e4000380c0180d6002400090b44429031403c881c0b40c0400d0990403000750300040b03482e40807000743c101c1501d45c2806050503245041ca003940041c3e000d00c1003001c190f0440d40c1d54144031041c400c26 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 769188498 1250 769187248 769187257
    0x16020d030b0a08061e09061510020a020306010b130611100207082116050909071d0d120206161b0c0902070b01170309090103021509061222150c0302 65
    0xc007060364994240a64880300014041170300c0c10510041a0100c0c892041c0001d009101d802d00c8507072025941d1a00302004049404041e0610861040309040805a070b401c0c00030034000e0020500d176913070381c14071001d0074110020554010010311008188041c070500c00858030072016111000d006a64060b1072034420182e002c0d02b10f8503241e41080844581b0302e6484e0b01e520602500c0c1d007500202c001031008504032810710031000319075005901ea20200b810340d4003419020303101603007590328003200f001da880205081c002c1000c0705840a0f170300007802c2070300c181d0140078a030381011841c0781c4842014070b0001c2c050580c4100c03130300011004216445506c188160048014068211490107540e0741c00581400300c7c01000c00c0c01140108220094642d60042000085a0b0050400340441c01c0300d81c41c54003040256403840075042c0d031164081041e00e045985030030040030500d40712441500755052441c0c403c4008c007444118040c40004400b140400b01e80440c401688000483c440070034120010032080b800b9005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 769189748 1250 769188498 769188509
    0x1e190e060a41090307051e01030e01020c0a06050402040b0a030c0e07091a0703080c0306132307050703021b010c26040f031a040b06010807050c0706080f16020d030b0a 73
    0x140d1001c02c880030030040c4010b0940724070450071228125141c004021500258214801e00004020040007480d4065045040102e030620001814030a16025030390410103c99400c650866031a400c000440c43d151291000340281507440c0c4004904507642d00c3c020315010301950001510840010b545030b481030104202500401301d611001d0100108080840d070031800044000c42c1e000301c0040c1810b242101030742e10070790b40240154020b05400c0c55081c028400100041420051040c0401c0d031240e803c807503180108819070314a5501d1469040c02401c02c10500d84000d1070b25011188100c603030b07a20110755003c030f61b001b405040b40f4144001e0f24801e00c03800c9900856840c2e001040001d0320066410402c4105d0b80a404246804607650b03d21005075039048900410012400020405c3d9500c00ca1891741d20442c1c070306040d458240a03000c03c900d02007450f880040011814020090500f1103685055000b07240c80d10350300c1100304d0005c0c0194030380982400030010107556071500e1045603105201c0c00010038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 769190998 1250 769189748 769189847
    0x52502040c0f0314071d060c011515030e030306040f0912050c1005010b04030f0302070b0304050607120c0806011803020d060b01092103051e190e060a 66
    0x10040e01e80507040c0e140340861400400d14003040c14101d4842e80031150320403002c0c0e550f03d40440680c868559440405240c0042d004075041c003110fa40c0c110248100c03041645420a10840c80c1d10300403007080c038007202e0140c4404050620000741620f004c000b0a490308030350101ca0100348010350a4a140051103c00c1000e0005201548281c09241e00100203028112608050390741d000408010182910428421401481402c100c10008924040242544d10381b007841500c0904d940c80c0110006034100780c40c1500c00e40c00400c140300c91079400800c1c0540303c0c800c03e50180501140800064000c0c000180081d051148400d00c245d941030490240b5405160b00811125054107c2c0c2800401000a585c1050118102c09800320354880c5410500c1c03010220004511440001964100c1d444e070050404142104150035074a070300a120300c4082c03c000304030300c81108046203070910300602c10301d16407204074000c100030803403035418a80c441d10050b5201440120400900300500c8031800c0c00b04482400d48802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 769192248 1250 769190998 769191011
    0x30506040902130510050a120204150e150310050c03160e0d0501020304120801050904240c050319020c281a07020d0302120a1a090a060f1505250204 65
    0x82e5050b807045001381200d003651790005499405000d60300d000c5010b240005900c0c20f91100c014070340783d0480d8101d1070001100042682e5900c030940c103c0035041e50003075800fa1400c0445000c5040030041c8098162003254140310324140305c1490340c0309101c041c2c6801c02a00050344000169402004120516200a40b25038800c0704507040141c003c0d04161001c891341381e80301d8040c2807103510030302c081070588900800c05078481d152507403600c00c0031091480004000100d00070100000c0c81b54801c04503854182e484007541da01d004644001d0070903407204071054041c810b009801d4544000507080090b4105100030007540c860f0b10018448005e030551005010382c5484440010031101c625500340640615001c44000c0c14001d0415001c6e8001d0091074011380c074505000420311381003908103117001420318044208007450710010420066080318071042c180e4960804120603c00e8943e0705004020314140006070181c81c200040440c41182e040c1240311007100d0180b0746903000300d80344541d01d903801402080032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 769193498 1250 769192248 769192279
    0xb070206222f040525050c0111040909050c03061501140708130f060c03020c15160302030a11010204151809020408070504050901021326030c06180a0b0403030506040902 74
    0x400c00c0300c140782c9010790f0800c8041a103030600c07502000340c03049441d50952003104644000311655003020440c00c001e507413500d50750300c0100c3e013450041001d015003c40204075610281412864a0107100c0b1460295005d482000f900300e48864030b0190703c035000d01e0460003030070304070315104440d015101d0302500303a55000868480d0010703640c220004441000e901009065503442041c0c640c000030401c0540035822a2003500003501e4021380101c0f9848501d10024181618a600c1e10014440303480c0440250f0710018240c8504c0d074000d1182008008d02070001c8d441c0500b009103000e14105840150028810342980308800800c5181c100b9024110040f400c54646070340701152541c550181c07282502941c5446c1c0401c0708102d0600031a00d451510201030014075251807a0b0119201c06070b09082c543c0c0b0001041c1600d04841440201088405400108400c3c00e2000d540c0c4034960030220706140d0703030340880c40308000506040354003540326400d03040c001543d5840d440814090401200001e40c40030750b80c8040800e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 769194748 1250 769193498 769193573
    0x9040f020d06050303030c04090b04090b0f01030b010f061d0a08150109050a090521130603090c060504150305071e0320090a050f0d020d0f0b07020622 66
    0x29602007480301401290354030700034540c4a1005559501c41c42000700700038441c0300c030190080402e000d0040d000141c04034807922414100002542c2c0d00051004440041080c440716103500784c007505802075411041d92400201401070104107291400e072a00c9901881c4090303540300700301c000910380901a91510041d003024006820030900a081220b807506c00440d842c603c4520404070515808401040107400585803c500c00001c8280940d1080c010400c991110a8080d88100140341c02e03100860b03000d5a502e0141c02590494000104100d0700380030410581c3c03a80080041600d006080010703d0342c84240044400290014080d201d800302c03500c005070b50759819032115418840890b10189250340910318030149200e80c6c810154131802c0a4010311161408444041c0108030081034400c2440c1c250340411910516a0420382e010800281400140b00d40000038540c00034840c406040d103480c2200307245000121388040100c007030740c040407481d04004000206103601c1c4203007001d010440125030138550 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 769195998 1250 769194748 769194757
    0x61203070c1e2709060f0e010612030c0f0c0e01060e03190c0b160f03050c0d0801080615040221010f0501020312280524031f0c0509040f02 61
    0x201d41d5110490b07422211120b4071503001520102c4500e500c015107036030102500208512550108942d403442c0141c0090181d100c0c4520b598074030f85000c47c2c807420340b040580c21a060381d071001621003078210b42440000e83c070410b140540341d48810000e190301c00b2402c00031070580c110740112000030308100020410a0b0440046240341d10304804844101a04003080f6040200000c03004144183c0c2010511506156030041d1030744401d04583c0021414042e210204207202e0841d00760007280700020010328600c03080c8800080c1150703030b042c040080c0d450800c0c3c0d540c5d01c200007800e480b0000c03009210140c0d82d5842d07070102d07940c000d4074400d5080301100d1441101c5840d076007842240b130703d0368499000082039400071080d03c000d0003030861203a00d030703030764541d480c683c0c1087d90080316095000220300c20410902e50310440d40103141c00c02219502c00f1811110301c030200c080385001d5100368401c11801803964003080409a0124400c0004a41c010360b60713005441e68015008845d522600340b21552900403080d034041c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 769197248 1250 769195998 769196009
    0x30402210316020a141f1103040f080118150902040908070507080609011a0d0203070b0a02070306110c1b0319030804020301240b070206090a0e040b0702070605070b061203070c 77
    0x130b11842c0e540e400300340c00302c007420030740340341c0005021400c0c080d001c10158031542c0e0920a4185400070007446d080b130500390750150300b01c8d000c50344d0142400d000820302407203040c80c00605060f00641d1440070b42c80320101030b0b101150440446d0303100c6043c002107484a400071030780d540c0e102440c05c3c0c031504146480e507102c42903400340360b401e4130600c00084d0300e41405010306c404c2001c16180c207650003490740c0d09011540120a00c180c0e0144140d84000803804c0c408401001b22615950160070644e08600e045404e031460303001d204100d00c9007803008024041000c102012907002510f90381c240000480d0100e0304100031100d000c1201b02d030500d9000c06040d0480041d6219501c224000c0000088451980201209501c00b401548c0b207015400e2100460b090018074107540000d111b941880c2100300060421107032a080002e404940c10240400c0185e185d03374507504100d10340080d1200a090250041c43c82c0161034002d0314080c150301c0803030180d88480c0b43e01d0502c2855030068950751303842030421030b80c2c0045034401c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 769198498 1250 769197248 769197259
    0x10b030609151804050c030303160306060306060801090b041e09050105161e02030f27031f1814030a081509040b070216150e0f0603040221031602 64
    0x9181c031540b507030b0000c1c101503008001a211001da202c54030076040c0000d000f11103611900c01c403082d80c0d03602000070714460148503541c0d9001c6091084000c0030b45285500c140103050401c10140034254114bc0700300d0643e030000200043c481300c12000180902200984240c9046208880b000d160b01c02c1d40116402034000c000034401c035280e10420b401900311503c0ba401c00203038440308908482510310100ca03010070081c8100d9040c052200000d58107984031840100482c7c9441115144080e408210b448912707208070041c181d180c3d100c5002440000400801000455488080e00c0040302c100c0b40382d60180d47c20400701038a003406403480380d5407a445a4900c9011030860340c000b400d09030380c600016203a5072000d010764040340c445555407101c0c58005000d400560285241a0f66441d0400441070020107101c02e140901c09052540540303849800345040340141d00c40240c0c13805ca0784807207080701d800a0741903528030b5180e04e540c0a56140b144100212803072602000861000c0c51060201c00702104c3d0007111b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 769199748 1250 769198498 769198501
    0x190b0a051c112508090f010c081204110306040c14030f070806010e011e05010507060902101e0f1b0309050904060509070905011809020a0f0915121e1109010b030609 72
    0x76900005601c1c1e10000b4401c4004200c4074840d41807030b07110030190b50700604015500c003a40f5902e1004d40d0708962b014102154000c0d040005200b258080216032070002d070050070303050a154030f980d02100d01d540225000034031645404d10080d20100150a0544050700998164948410341c06480c2e500030702c03401248400710f030b001107400e60f03515079130264060090112004c0507103060015a1950428401901c0c000da55030b270000d0140c2c4174a0004420110325a031914580d00848803041d44141d0003845040c104600c8800e6841c2d1207800c911555079850044a50f03082800d01407404560300002c85d0440340e000f0b0300280034403023040410f030001400750360014103540100340c0b115082d0048840910030002e4442829070040100314190b444151171a00180c42141501e0716140b40145031200c680c04a03007100d41e505800d051802401c81032001429840d044003034840ca99031114030880c40b003030720a801d501046061010420034180c80c54504160003800212403581d54040007541904121000b600400c00c850 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 769200998 1250 769199748 769199797
    0x708010614040c0807080705090d030e03010e0304081e01330b090109050103020d0e01020316020f010501030308010513060801060b0c060f071d0f030a0b06190b0a051c11 74
    0x101c2000c0081c0b070fa01e00c4d03001c0c0d491400840d200d083c06001c030001d120040000450f6501d60f208640d120901a0300c80b0500701b00a14145421030f03000170103210a541045c042886000c01c04038910000c040004420409071155580c15030061100c54440c1e00040401c0c2c445c0c0690702000c0e02c0c103440c8561900c01444d03031144d82c0e14020741c0902ca001c54840c0028110001030203298040d6020780010b407504000000c0411280d20301608a0303000703892510078841000c0c0c010040d10b5040117035415a6051070000d00c0707d540745640c09452030708180a4280300c0c04035000c4800020009601c801e00400c115002404016606c0c0e120300c1040d880328582d00e0f507500400e0000b40d0b000000900343d500481c80b40d030380c2426401e44c205018100003110710f0017a40c4442082c251a0310f5940801c03521208074050481522a418144208501c000201c5040500c185d0743c50700c200540742e041021b80b0000c2030242001c41d0390307400007480309200502180140010910340448121480800c0c4094081807421a02c0c4d44200b4007204d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 769202248 1250 769200998 769201001
    0x601050a09020c19050a0c033f0c03051e040303120b10140c0601090204090509070305100f0b03030a090f0605040f030f050304170a0606060e0d0b1503070801061404 72
    0xc040f00c0043e03211303075152074140c40710703121001c441c90040007903c12100c842d586880130b850b03003948142d40307020b143c000851146d02d92070702c130b45c02e40c4030722003030f03161000700c800d5240b050f030121524141040c0f0548590b88000e00d8040d4049510240c20555a4030600d210141a510b15810901081d00003c0c081907849080c1d000234418000c5152000301800d1400075a9036049503550b00da0081020080c0f814030404280c0501001135034040c00090101517211400d185034031013196001400c0640540c0030764410008076034041a00b41549518400111f0014019141c0b41d000d454444c060726050704c00040c0300c00c515940041d421040c1c4003100d44900d40250b03146030440c4d090040d03004038003030640f26030800c00004055040b0303405130503c202c060f41d09055860050011107180c40701e4192840d08280e600e02e04001035031007020081c12103420141210381c5c8800c040741101000d201d00038010300310780012603018502c0d0032014490000050403681019112544680644954400c021040300307504503018040c0f405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 769203498 1250 769202248 769202257
    0xa1716020c042d1508011a0d0b0a050907030c06030b0f0a0b0d0207151d06061905060904060504020307020708060c0712210c0807080709080304140f090103050601050a0902 75
    0x4640c44400c40c03034411003105503040314540e08200c042d0340d210b90b0005042c43c84e8002000740110800010328042c445c0110100442018034503125010030901040043d80303041c03085401c82c11018000071a9a6040c440600e41005a04040c004243d454400500c03264141c0082003010f100799880b035001203a000921007000d060780185000054140150100e40034940d003c0c05146004076241020000d40c008208110380001c028000c601200180045841008101d042d0300400c041e140355842c0804941c0c81d40b2102007a0103158840c400002d0340c0d49155540342c100b0000b6100003001191741e0305101e0360180d0782d07610768801c0c0280c5019510000780c00d48011011baa0702240c0049807003040c40c00c44581140e002d4168800b110074041d000e0780300d200e03564440c0f01d081d40340b0416455180a0741025030000e4030764a001014a41082034084040c0140b0001005540c202d5031282070f0550041030101c001510f280c0c0040e5800c0c1c10035260350000090080c0055001d048420503240c850816032203900c0030040c1c1c4078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 769204748 1250 769203498 769203521
    0x81611120f030a1214070207050a15020a0314091e0f011b0620030103030807090509090723040905030a0908030f0a080403210e07090606020c060a1716020c04 69
    0x10701480c0c900f58000c0666641e403d0858000154031603807020507540d0740106641000041c4d01c940803d01040c20b000c500c040241080316902c100820042c40c00030368078120244024200b00c407000054514822100a45000700c600900e0103401024031071614103d0311440d45050f03c01c0c0240390f1592802d50140c520502c1c0100d6801040401c580384d6113486010307064410443e080b14808106019002c1901806140690712030342e1102c10506140d0070003490050150046d6115445503030620921f0b640000342c0754116003040d003540040c480c1001460314404c0300c5420003900581841c08a104101000c402084486c80b187c0b1504035150f2a03115055481c0208514104e0220301088412022030080000b5903000b442450482842c00c01c801c05824418030380c0c00d40240d002e0311b13000c000c3c042650074040302c000340c01da90408101c4e180c9080002580c070103c1d1030a00e070247c040003440301c180070311421040c070400e04401203e0040382840300103010492039110162006014590287e400d518003400754411810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 769205998 1250 769204748 769204753
    0xc01030b0f040b0d080412022d01030e010f020a05090405092a0609040e01020a09080c0d03051e040b0408060718031101120507031d060121081611120f 66
    0x1141c0c1c0900008055a8643c02e901c012a600b40c400001e0f07440000340b015191035400074000018601c18031a2600511490044107050490006103081408048041440091030b0200c1c081501d4640d040c0107089a4048680da1400021408a5260440001c001c0c915066a0400c0030396901c040e410f456100220340401c4600484040400c41c050071107074415070b10b00080c80e0341d141c10544c000040444859982200c0c2e16500481c0c1d02c603003687c0000c4150700910812010780628100301d000125070200d81c0c0802000d100b00468580301c3c1a5440203240801c1c144821615921602d5022481094001d481001000c0c0b040300f0004900500c00c2c4461110199014040c001e03c074203540d1240d6901d070070f4115040c10032030b500c51605031220160142900414039520000303100c400000e02250b5114900c0035100441d8400d00c010458030a00441800c9410440c09a94001400c0380ca440c0036580300b41403140042c0300d03031010711005008444802020180b021035822035400c11400c0540d403143c51000082c005038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 769207248 1250 769205998 769206019
    0xa110303010e1b04050a030b0105091503251509030b0c0a02030a030e1603060e0f122a070b030a061d0105100504080102070b16090321090314010902030c01030b 70
    0x310303d42c002003101d900301000750a050030f07102c40c0422040001a482a0389152a0b08010802400e01a4030030713402505e4002040c00c0c4121101c003203582d5005900e0096182c192140c50500040b0607481c00030060070740c00030209501c40407190010001c071000e0001ba22a0714060010460302000c0d00d04966103410190051814610300400c1074005203040101040f40e03006007084150a04c071140c10402c0a180b1408002640c09140d0301e080b490007206420006155105120040c42c1c0038a010076140d42441580c6902e5502079880801c808102e00c4e5611f600300752283c0b440201c4c3c87c0040c40d0245100d038a0002c8104040d0307980f440720407030114090080c8007003522030100500041c202007114050000c0d26081039468a0b41d1503010750b0881c0c2c081103064598004807000d011541d4080c02400c0b080c00c183d0300d03008120905503201c207800307140480ca040449001070040c4880c014081d5800100440c0c01100038041e071a0351400c914003034400b1520407481fa000c0c40c0b8000001c0d40c00ba01c60172407030480141658188 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 769208498 1250 769207248 769207261
    0x6021c050d0b030a030329010516020301091e11090f07350a0c0e1c02031507020c010f0f09060e190b0403170306060d0209240a110303010e 61
    0x40341c0c00241d003000c046894005150040c0c804201002c1c049110341d90003d5070400c00c4905001c0308001620184101d4528040440c07241c0c0d0040c140c0321b43c1000743d1900c0659005a00c006401440044001445a804056042e456041d420064003102e400f409112140b010004208604400c044440c1c140c0d07041c100700440c4842e40b02c1c818482d50b0701201040c40c2d20309211741c900707501030740a5444a010410f01d540208440c4031410b028092401210f420403a0b40c01d0b5401e00002c240c1ca5054100b9202c01841034181025590100a0721120000d03403441c0078214180f902e002501d403410a0403050110710b8900206203c58440c0340c60188842d070564a20140d581450001c84460201d8a107440c2d01080d8105a048207840003403400b00109001c5d02c04075511855440d196401c440e01c99a0b941d003241d070500410000b03407100421030303480351511200143c2d100c3d14607001411049411040f40b1403080e4006030032000032a9400207019846007030310f9288044151401c440d907640b1007401851044120013004c41d12 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 769209748 1250 769208498 769208507
    0xc0b060d0803010b1305060a023f040302011e0504050111150106051201121505060d141014090c0105210f01090c020a24021605011506021c 61
    0x80000004268001414041d180c00c05140c0080e04000010b07000000c048034481c0c0c40c01980300007003505844c028100000d00001039103586074000044030307143d81c01041da085240300c1e582c02041c41c0034415811081c0c515101046e00070f500180030490200c1c04d6941a151440000380f0151003071500f0f55101c9203020f041400448411031080000302e1036106800d4030812042245000320301a0407075540b541e0b144d047c51400e03007604100c1070f4440f60400c6a840714540200c3c10b450004074400c844100007041c151180b50114005464000f00030306104500c2901031a2000c0100e0000c0c624120450140507600604448030105001514803400c5540070203440c00b01b6500401c083c2403940b09509081011b0040300840a50b400c504807403e940c58003442c00113102e0b50200388510041c6e041d07184003e0800e506c0d507607600f181d0314850040b0805c10070300c0ea07494402e0b100d40d580c0495000086c04e010a18144901307103041ca0181070f040c2081c01c002c21104802007151440050790003582101100c1150303142050000569 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 769210998 1250 769209748 769209751
    0x103080a09030f08031f0e0103080f04080a03030b03010506120303040b0402060f07050d0207060c0b06010305060a171506042903010603060911091005101d040501030c0816060c0b 78
    0x38050041c0c400004540c0828100205500403540781e642d91820500c0c011001d070207038070403504680c0e44040c14815010f5590110341580c1d4400c0070250307241e1060095a600740038680c006681c500c111034444040540c5900f0080300d5100c184d000b80095141c1004000f01e409035801450102e9200b4400200800c401e8194960010300240185103400f07038070b110000c041d0780440420380d07442c2d0101c402100c00c0340e41006001d001b04220310703180003000300a036264040581c001d00032604245d218804600e266490703032070640080c2035011060414940045c10031b0b444080b11081010a500031074000b034810f080074000d44a030200090001c152450a428180752211124000a6015940c8072000300c0011424400c0c1d1001d40e00445d2034210b001c4a0700100240c00500030038461030151240c3d000c100ca51140220010700039903504289030007141d0401510744225032044507a0344141800000400e0002c0e440c0c4078420380701c9920541d031440014410309141e030b00e842d10942e00041c001545100100b0854000d05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 769212248 1250 769210998 769211017
    0x5060f031b2b030809030708040611120417160506071509080a1101180c120201030e0105010b07050f010905070506031f09020a0e0a050f01080408121005011115010308 73
    0x200054800b241d114009a084a002c298403110815000800e15822450a82e1320200e280c1c0114a054020f0ba20a8440d000b24842e00741841400c4944855899003071214010814a5825046d291a074407501c5c004007540d483c0706500d0500070790402c1440300360340c04004804d0b101c0150104d85071800350ba5442640300d650804c542c5a0342c0d075940742070700012072407001085450314a54400c00c101154003056421140d100740c1014007020f0b107402000c0041c603210320325400c032405c403403a41041041e03900058010f4200482000025482c000000c2451000700c00904203060007030044441c0260014000b608071198590094001d90005801308807901c0d12000456200b100780c01d4642c0120109481c04510303158a800c00d40c0002d4010400358007540d8403000c45132840400711105c00e000c42c81c100100351040c0854135000c2c108145e000005043c0035a94007142d400d030407410112001032030301c500c804030099480c1c000e03580051344501d112800350b6800a9030820048900400e0300311a441d5035901452039103c00101d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 769213498 1250 769212248 769212259
    0x4030b0c1306020d08010905090a0210022404050f06010305030d020714030310090e0a081605160b0909010b0a1b020a080316120504080d180e130605060f031b 69
    0x100401c44008128000042ca40d80c0c000f04044048020043c3c403004058000d0705030b852400e0100302c48800006451100b131901607070107a110240c807501c01ca0925104013040d070091249002034941002c2a80c001c03620580c055815030380d0844070030080a84504080c840607207140d000340040c021490b031380e034010b0008a120b448404a106020302a29095810488022400700f22034031007002803c9241c018004031076083d40c080c7c8034000d1030380c1e01d40055001d039280441da20705001001e1070400404105060307030b020400098400c06a41c40391445020b81c0900291390140601c3d100014585071140142c5121021648800c403920800b0a10b00400504a070026603118001c180300140c1142c05000511030006030890a15411516040c00c0d240020114401420040c04010800800d200800d40030480d0a076460002d9003003480c19100700c1202d06d90b400141e00c0240020a010310031030310802602c400d510803c0280301d40d95840c820000c0201030b02c18669050342006c4100502c00c4031001d080c1d80115001001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 769214748 1250 769213498 769213507
    0x180b060a020a121b03020102090406150c230307051e16030f0507090609020c011b140f07061a04051b0f0a02010e030c07031515170f0a0507090c05070804030b0c 70
    0x111303141c20f0031100d03c0550160b540021444a242424002e50001d442c0c140180541c180035050010120780c0c2800d4094240080b81140314072008e2741850794824600c015007103948400041c1441a115505080e83d2800c1ea00c03d02414652080302040007420300000400c400e01c058030b90f4a07202d64414900300225028011803c000c03ca0100728881d4101816200c480140c0b202b610310085e908607816103c6407090409903940c0f0300031081d403182d10b50003000340d16041c1d0303501c0b280c1664a0a0060164440c010141f80c00c0c00c0c0e0011011449018252900100316800e001544490215510110f171050040c82000e20801c403c12100300b445004198110301840000384039420101c4407030840d00021111000358004800c00c00c140200b004528444180b01041001f910145051131200740450f0304c00c1030b06003400b540b000c0c01c5008060001f014044202001c1d80c0d021810340c03070803075120300b45402610025868500e600c0f04141c0b0136003c0e1101c00da4450100c62600f41191101199040020405041d40b00c0401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 769215998 1250 769214748 769214777
    0x20a030209040f051803030c0406031d0d030212131203051009050103080c060c0a0207120c03082a010b030a0602031308040303030c021506100c08090a180b060a020a12 73
    0x20030b01000050050f030010744c50810b440d510540c10228000e282c2d0980c000d0081c8054451440120340c2100c0b200e05001800e0714040c02d507441490031380b410340c908a0248012402040e074040e0001c252410100c440c2c803000c0c0e513541c2640c0740d804030004409800e505118115507030300783c02070b4421a04007203102c1d1160030032507076103000740c0a88400740c101f11840b030404911070400b07000c00c00210360400791022a590401054400c02175482429124010300f58640785504010300450f0f004481c041c50f0004006551805c640c5040c2d00d552909442e4110f015a4290326400301c12018071411a40ba0700c0180602080c50164407007030041e40002d46422814410603c0140000d14400018001907210f40c8004c9507507100710038060f04051054003da0364008240040080039078495401d40c2d1f0880503400c1c000b0080151341802400c42c040d0400c0d19400c840c50310000b182d5007940441c0700250361903a05041c000088210706000c240e000e24014000542e02200303c50700040d0841900f580c10024901c2e10f940d2104c41c0d00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 769217248 1250 769215998 769216001
    0x1b0d0b0f041115070203010f0b090c030424050711061303080a11030103050d0f0914220e0a05071415030a02251406040209070e0d0f0c0e0112050c04020a03020904 71
    0x75101d00f200c07010000790001141001e024055900e00081010056820702d400482c1508000410f0340034440b100000050400c50100015000710041900c01c00d03080b40c1c3c41c500c1c0700081805850810210700c1c50324030000d104c01c0000c2d2280c85150024480391001c1010380d016144041d000d480d6005550301c6017100203051032200042d60086000704000c21202d032052001a18401a840b00300341044499501440b01c244440d02200c0050015620505404018210840d85c060b1107001b03080b40034203003003515045102c0000c0406195014809481c1140c1c6e81d40c540c00c01e80114414284e80280d6030820400001071001c2c00f640e88034600ca1000341c9441c0e00315190400d80e054101c5840380482e50b0100c94424172244861040c00d00350144010b08407800d0980002c0c00c41e16009040170204000b10110b40c0082d210300483c120300a901858841400d103192400080c41030b998050601c0b80c5948000018032200c06095441d0030390b4003c40036101c0c6640318001d00c800313940840e11103024907408200510080d11035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 769218498 1250 769217248 769217269
    0x610060c0602300c12040209180a080c011514010e030f0109080d29060c0c0307240903080f090d1b080601080309031b12030a021b0d0b0f0411 62
    0x41c40c0500307400700c40d002440c00c5a02026291142e103134001c0c04100c000104030381c5655000b60301121605103030b40c0c3d03e26100c080305a0302000003610b4050321108004001004010b0680c1c00c2c1400000e0000b140d20b400070400307072910340c0326070361040e80a0075055002c1e50203452000c1c41148064181c0e208400c1d5004100d0235141c003800212210b0f040000c040ea40c50a0610941c1c0214107101030a154416602e03442081c1210100c01240c86070380009802100e4034000c2040c85100325014041d075160a90703901c07140b82c412400580b0700e1001207400b40001000b41c400d81e20301d001e0366403050101382802040040680c0b80d40042d00801d403c0114000e26101003040101e03a0610200e200400c4101e190810050605285042e030103403070990b100340200130f103507680420610702d04089444e0040280c0300040001d002401e110b0408052404005200400c6903400b103840c2e080564180d0100a00f884c0950500888420004001d010300c996140890403103580c40c0780403608680900246042001910001a140e050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 769219748 1250 769218498 769218547
    0x213110f030a1a01080a1e0c18060309080403060c020304270e01021e0d06120c08010c05090a0608090a14160506070206040611011401030b01170610060c0602 69
    0x40441002034550710350243c0072525031802440d061504120b0006025503201402108000780c03901d40c00085d040700e00d2646011455803001c04c0c411901c80440160166403500e0b00329018503240700d03020072494000e00030340190a91042e80e03146080d1650300d403000140101041801180420400010755482c0042c0074104100c0e400b500080194400b04468125048218522000c1c1d0040c040c0456041c54000010b1003c030384550b401356581e014201160040081d500440ca11005805151080c000721410303000a9811400c02080300d880c00c00415079903400b82d0b0b2400d80c0e0240d15403070180035113449140074942140c040c90480340c2c91081d555408040805810a4034050f0303203c030506e0098034940940c58001018180e030750a240080300d030049600d611590040d84140480a59401d04c104000d600c582d000994128548015503103a1511640f2a0028801e40034a446000050910b240c40414882d01039001030800104003440c1c50415a03040c0350305001942c60031360a0090881e614603080f40061002d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 769220998 1250 769219748 769219777
    0x705040602060a0608030a03150b03040b0f0a09110d03180603020d060f030c060e030a060204080a03120b0102060115050403060203040503131d0a0f060302060c0607020f0c0904021311 80
    0x34203015000b450070800810441c403450034000c0030010f005000c4120342d00c1c0001d40c0340202c0d2003c0c40490701c0140342e035154420101280000100000c6c460078248060260822100400f001d8070f602283e0b00564020700800b41284104a01022003894285680c160840c400e08107020342001e000703130092145105030b0002c0c001c2900001c07020f10101e100c2c07040302c0107059902d10395400d842c1151190904402d090240d0024001d004d081081e4550b0208000209154019015503441e030b111500980c43c0d1040c56402c030f0104407a5411030014204500030002444030680c0200000c5c2c0c81d04095548851041d880441400406c20010021680c280025445640100c0085a41d01310203038003034070702e0b03000303540040d22040e440d40191f580000500806c1c1d13004509544042081414038000c00001d0510f80d100070b5000340001820441c0c4440401c09502ca40440d1b025a5220400100500c1e224011302d55480d03030104020002070300624000c220741c0284840c60100103070a080d0700c1d041707114540c8485048203211 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 769222248 1250 769220998 769221007
    0x50123030a1d120412050114040501020d1104210201051b16050307050d06021804020c011b030e031e0c01090b33040e120414040617060106080a02040e0705 68
    0x9411803030b07414258a0020010607800803100c4000440d801103000314442c100c60081c200c828005e094026900d5011850003400c03650a2928000b03001b9071005540c01e44403420100c0740ea69840400742901d007250600c0500035040400000c1601c1260f0070030b030007241400004d00107480300a40c50005c04050b1007000d402001545101d034000410f1000a500c80d911035408907105015689510070403507682c55101c6800750b1585250201030401140707142c80903030064404502030200c0c42d01500b02140040801004a05041000c602103040c6e91404840c074000d540104410203059040300302c5500040354112255042c4280b403c0e6090070358691a2055662580c0c0500340649101401214081040d2010f1031706980107206019110300704400c40158440da40e41d050100121405012000c00f40300008a4103175030302e4640341d5120303032443d1105006002d540361140101c0c982040501038071071500010000d0010b603191541c21141400020000101039800f400005082c400010005000c2c4445845050f00e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 769223498 1250 769222248 769222271
    0xf0610031a01031109070207031a0f060901050a061b15050f0f040201020a060507020c12070614070206040302060a11030c010915200a0c0b1302030f060709050123030a 73
    0x591a2400750260000c0e10318004000241c50079844410129007030b540c1c1d00c40c0d0340c1c0340d401c01c1e0300b404250703032000d0001216826106034583c0003112041c450000f1892004a036203030f0706c00303200d10204c00b401003a40010452509000641c003500e12480d00c00c1c580104080060400d43d602449a6051420010525200c0003440b075100114803c00b039100041d00c00c50a594030f05600000d40d01c4d101e841c00034111030350b21000315075020320070300200075402000f070000441401c028001030340d180b65522900740004c90040b00c802281c0c89500459400c01d40051010382040d040d50200134044d401800440240310b56020074402151041c8003400b1115016400019042124141000c00d86900203034120701514002680f0721440340b4000000f034140000d85101e07220100418281d400700d4104101600b1080c7d05410030549030941c454070508584241c082e6005107182e1030405950704800d848000101c0c6074031500748442c0d4460080312449801c3c000703565145290350784c007030b006c598029a43d100e00d0544450f1140030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 769224748 1250 769223498 769223513
    0x3140607020d050319230603060105010903150b04020903190209070801080a060b031609240807060507020a090203070305060f031207020d0f14070312080c0409020a020f061003 77
    0x500114500140c0009024210b000f40580b00041101c4020845c40c03425018126a50340306070108508000040341c803100c0e80401221910003141e0320741c400d120350340000c100307540305402110441382c0c84050602900110f10801014102c41d0700b845400c1a403d00c035407c0d013540c08220308401000100920030300d1510a0043c07020184004106105002c001b400410400c2c400040d102c1000d50846000600f59110302c0000381080c5100740101c00c2d1410500d0b011130300e180c1c150300c10449503890807141c440000340e84140585c914820721503084582c214000411845000b04020b01d407d904c001e065999141d00c882c3c0c003d00301d80040e07840c80c001076914010050b0340d0412a4405c2e046a600320010407503d4524480d80c2924441d40c0e40090242804009038030800401d06020b41c121a440350855240142034142150780e4442c5100a5484200500f0490025801044414000c0c1e80064030039190074240278042010350301203401c107001c5100311041c4101e420b0301401160f000e022960350240308940745050200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 769225998 1250 769224748 769224751
    0x1e050c0c031e1002070c090c020a0206040b0c10051e090309031204080c0d02090127021603080a0605011b0807120503100e090d0c0c09050f0f0702210d06050a031406 72
    0x500c000c0c03041014001203046c101e908000c490740c00c9004200781525400032030404030105402504618045400318047e01d00b080540354180044040703840564a07880080c055640c03d4840d0707504580803410420b58008007017160780c4d001c0b1510046074500307056000440d180c41c421002b50244840041414403050206201c841548d0100b244c600c1110300c46c41e000100c841c4818070841c0400c403000318000c1d45031504c84c2880240c2d121842d00442d02c5800400845444041854046001600b1140011034006c2e00c0c0c800c0740d042c1d40e41a9140a600c5e2007035144001c4070049010242c1c0c00a00a101c074400041ea01c400d00c500d1500c007a920b894030713400d01c83e40019115044e03070000312480c82480100505030100003005040d0305601e00e4075201c01007440c188441c5e845540d40000c3e1303240307040a0070094658040200780340a8081d0910094580d500e0700350803130311090000070081c40403070f4603004508004072001c00390100503c800c00004d40f459070b840011740c0da204103034012640300c0351401c44034000103814008503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 769227248 1250 769225998 769226023
    0x908030307020d0807020a06090b15090c0d02030c0c0f0703021c08090d020103021e040612020304020f04052e05091005031e070f0b0c010506011e050c0c031e 69
    0x21810341c14841006501c0c3c00d0714a41c0d00080203640390009614510030090b4030041600848208945042c0b400e00340f0700d0040c22240c0c59400c40e00c101c1d11801605003020b1907482945401081c40c02d2000b80818003020b0f51014280d0042050709022110000e0010700201800d40142e00041c075010745184148000c00b08480407000b03581500ca02c0300800301e0040030484208041c1200c0f0348030300000610050b4000e000780c2c0e040741c00d00302d04000600001d598500043c0140c0b251070701c1c2d807803058008030b40f00000e911080301c000f500011200c0341d21189050580240350043c0360314001380c801441600118690134401a202844040c0a9004200d141055140c4030340003407100015180e8242481301081d6103188421450001c00c469800340c0a030b003d818803406024000a60207424a16980c1d0303a104065008205040340e55440c205c0415119070042c0310300f00743d112601c110144481d468690607182d03500030b188001254040c1d065081901c0d60207216100c070503061180c501c0360114104001518044000107007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 769228498 1250 769227248 769227253
    0x3110604170c15130e1e1608060f060d0c0314270f0a0308070201091a090d030b010207141201020c031c0c08270703080c0d0305010509150a080a120908 66
    0x18450001c0c07108130003003076400701d06102850340c80309000048005490a41c075980b0129000034003006403080107064651004aa4604005403284810011901d12448200c0d40c0a001001600d400d00c403103400c0044103554504000807034055400714804044400c581020100e102861038075181500035004034001000035004114042c120080f450380c40f080d08102805024205000608092007500050300442c4e100c05034161010328050030401c00401a112180c442c007a1154400242c0e200f07108202060714142d00500445292551080352007200702161608020b8050814040c000b0900051182c3c0450038010f40e40c079185102c00c0d1221000316031080c94107504020100180d117502c25141500008072201090340c0341c25441024607422403070300704000c060084280c0081030000300009004440c0512041e2182105100300c110100c850900070540e0090803080810702e200100d81c2d1582d824a00900300103000b40c4c030740004030b26120007003e085650f400007552540001d548041c8040007090440b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 769229748 1250 769228498 769228507
    0x20d060f052103030403030203130c030309062c131820030d0519030b030d080601090f0e15011413050a050d0807060c090b070503040f0e0c0403110604170c15 69
    0x450f0307181d1002800140070103070044085204a000e404c003924650354032a400b01241507a078a000740030b58100388104004101c4000d401c1010383c4503200c4d10002d207206a90380801052041d4100f00a040d03115a003843c45503aa800041c03c101188492420914040c407844180c1d001c170054102c01d504032008085010350001c003000c0620f03d4001c016194110703200f00401d0504520318404a0050142d018034682c103200d06c3d030b0302c070035102e03042505180583d000380d03903114409880d111001c02d05002403081c601d005020070000b41003482c0c81042c03401461740500d07111054510002504505800c4013403601044000301c24100701900c2e00b03081440c02088141c0e50b00b040400d182d1a4616a070140c0703c0d024041544800c0074019251203450640054242c00100a4564003d414056907a40290256078940020288041401144104880d10900e0003c00003440c01c1d04640c1c0702003040e128545c00e142c00031010301c8041742004c110142829007a0756040285481903945080101a8200c10000b4007411001c20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 769230998 1250 769229748 769229809
    0x1503010209060403120e090411120d020705061e190e0405130b04060603140c190b0301030807030e0402042409230303070605090c03070e16030b010201020d060f05 71
    0x205582c00c5030b0300071050050108801c40b00b81e03181c6c0311200c0000e500c281120200400c2003094102006820801e0315560a004016a038886d0b81c1e444944450004da4001c8000300154a011b000a005d840d0210400c1e82c8021152482c1d500d00785c21071300941009140300d08000c3d0756594861000a942c001c02c0318144003a080507480d0494804201d0342c003610741c001c0400068140720b06e030b8010034029984481140303207101192400340c0d102c2100c0581c0314840c1e0304030010284141030118080d0f054803050071305a4510f07407850361000c801d94800e000c201c0034440c4021084010f50b84510280c0001c7c0800e16028007035610702c01500340c0203803c440980052040c0804203002d518094a141c00300b40300c02c000303413103406003000001900c1c60103060402030040b41000304201d20300c1c001040c859031407502a0b0444130b029498000e150b10424044443d50f11028802140781c007654466007040c42c08100600006243c5841e03c042e220070b80e0013640214400307000e0f5207810415805c01018101075804210300001c0301c00c1c001c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 769232248 1250 769230998 769231009
    0x180905091203070905212d06011a03060d0b0906071413030602160803131a010e160309050a05150604021602060a14071a01060503040b04020d03021006030b1503010209 73
    0xa0081d10301851044407820640c040c0320302d50700c2d0122200400c031000314503982440e00c030200c103900b250047c0515440060110086c00507005041c0c4603e400110010f8120b07407460344964000405040c3d1000c5a8082180803031000e207841ca00440106010742071038501080e014141100040000030007450410452418500d00c1c5403110980c1d41c880005030b036440c1d0410540200000218000d0400040007041c0b041340304044c0b4518441074403071650961075110b0412040c00d41c0300c00f40b04000100c295030001960700325000c81041c1c0b014100d42000211030b0581c0d11041c0c0b4100141c0400c81e1185d0009111103141ca0000708900c0d48100121801c1d45002d0003c41c0450200110310002030240f423021402408042c028000f1404440300640c4882d2036003060304000c00007032074909415680c151a00004203401d8810720440c1e00c169000310f11581c0684480c1d0901c90f9238180b0304d001b0b400714002c04e080003841d6119809a0001036020b0080d1703207001d042065030150351102c2422214403e0788104034081064440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 769233498 1250 769232248 769232267
    0x19030b010c050a0b06040e0708011e05010b04180603120e0f03011815020c010c090e060f01051602010207051210230f0a020d14220c1518090509120307 66
    0x155a2442c0ba4a030b11000c1401f91285039064407131070045c904007040310a415030180410a200c086031801e44000c01d8886000ca4034203005080c1150720801c01400002006030283c00d0326081c0950018100c4d5994490a0300078550402801c000740081ea00508146448c1d15116000c0b44114000c0118400e000c1c050f040d50401880d0041c000720039071941d0407095080741d040d544a2004100240710000b09000014000c4c0c03d6401504c204207a90341c007260032400c1441d042c845403030041e12103d2806142e10030000c1c840000c0d00c0121304620541c0000700c2e00d0344940d850f43d942c03090144014606208c04201d20800d80d14401d401e50500c50307000344d4140550039031251031a000300d01c6150461a548403045c10b24080c0c411841c035040d266040100c3c404504c0544079030144608078445c41c2d000d10180b110038040c00030240740c01c0030300100f00d152810700400f40e10f004141380b41c000e14240356408404e104001e140b25031607940501d80f01680c9000b0071007601c40038032a01c220300b0441c0e0401c5245291055014100404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 769234748 1250 769233498 769233503
    0x6090c05041422020111061612021e070609060c050c0d0201050f0a0507180b040f050609100e04090b0408070b1308190903023708030409180819030b010c050a 69
    0xd07900024821359014906401c1041151015114685059032880b201d291071b0940940014407111018200e010b80f52007602c00e480b42c51003030803e51941405802815800c507410030382c1c09941c0d40070020300003400c52240354016025a01c070a500c0c0d8800103280c2d03040c048071004c050156410402084013903010b8050155004184000000d0141c464600403540c42174164041c00b20102003140104501c0d00e4480a0811203030301101c00440d198540c41442840c1c00741da12007030341100d585510300e8a83c60160001c1811100050300c0001c605000343c0307403440171000948056401a40018842051280c4003031005c0e84581c4541d080000f40d9140c0d91340c00300364422000d070400a4852600a02e011034406c001c94001160000e0241d50301c152212200d44e4200712a00e520200c0f145442c0114811058516141d02110a04405503081628004055018008a01c0321042c43c000c100e8400d0001340e41000505903010502611b0689400c00d800082c1c22a00a8000d0905000c0380c8d8200701c001031000500c20900c2c41e0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 769235998 1250 769234748 769234801
    0xc0b0304080403172226192004020301051c0c0e070503070f020f0a151508060106020c09010e070509040e01050a150504020a02061305070306090c050414 67
    0x191607040000d9640101d4000804d40c104a40c84481c1d40605600039141c600c804604060020000c000c01e07410448003441140022079a03610300c0910404102d0310440b504160700c064404500c40c206813201e402c10580c03411a903c002c41c0120400400c80e50141d0701c2080f109880440c9994109400100d05034907510741119101b42c1c0507041d000300400480918000e00c416000d00c01035041070540603020b900100da602001515500b84883d020344001b071000f000c000c000d80504000222926050b40e5443d50f0801400b4803600c400710490040420a800d500600800000d8101541040002810218010f680310300c00d4100c41c0052000e109461012504248181032441d41e80d086074000c20003a00744001c0285244d440c0c4020810700e40083d03041a025000f050001c05086c40e01c4504001c100e0141c01000750050340058002810b601f40380400400f0180100102c5a41660f2951040e064030b8113014201c800990850f02008241020302850b101406040800b10943c58003145901c0103900c035080c0c400004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 769237248 1250 769235998 769236001
    0xf031215030c130608030a03062309160309170403140c130e2406040612050715050c030711040c030e1203070e03030304050c0f0901060804030e0105120a06210c0b03 72
    0x40b07619030208000704a54000e46e41c13102100000a0000d10b05481558029003003e84010245038060f070300000c804400511044043d2181c0005071b109144007024001815501c1041a011444814201500c15911040f25aa407800d61a1410021500080280e5140d212085200f0030384c1c3c4510441000217281d00f0001284140d082c9902d240c042d02d4255285415045480c0c0c04800405081051113a40191024446a0303a241180300c0000c00f254806045904001c4081c27000c0410041c0310b40b41c10f80e691420604204d517203003209003140e2010f107040b14201503001145d0020704181c0204844680346080400c5220760704843c05450791074900a4a0101d9800000500202d02a101d03146076203038041c0c112500c80c40c240c41d01c03e07520b641c1c103c0c00305e114281ea44541182450007468442c1030310300c035503a0305900792140e80d010340d8204070a81415040c440c0c1401606201d299294245100d60301c0c114001c104280780c01d07031044484040310384051241c811052400302045400c004442203e05806c034441c0d59 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 769238498 1250 769237248 769237279
    0xf0606031005060a030606030c021603080a02120d09020102120406170a0e1207051506130f0f020a0816050301080c130204210308060307060e0d050a02030f031215030c 73
    0x1140c80342d07040301d68402c501184180d00d00758103611550903940151400c0010840641d010f9079a06a031107541c208a8143d8a010720019101401501800d803603070048a00402d06072400c90644d400580c08001c1d1555100080825503a04001000203c0c03400004a031030181010001004c201c11a11a41040e51047c03002c103214105540c4030218282e2000c059035074426131000c0c018001c1d408002c059410b80b00340d4070b03c0d030001e82104d903481e4000c07000140200065101ca0a803c406491041d44003a10320b952101c1d40070b6000c1282c00206412202c5550307a0f009407030841c0344070f0001f6218110740c2e400c1000034401400000c00004a0340e0352600b044426880700134140c0003880180c8130b00c1e0404110301714004c1c0c030180d003504150748450712517103c1c1c0c55a4207640c0d43c4000340b6554407500c1c8603000001d070341001d80c1002070601e4265a940c09001d2000c0e0740c454802034001c42d160100d0310000800645c00001d04811000009400e990440202e03094410004d180c070f0000303996034555103c00752046c068010840c1c2d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 769239748 1250 769238498 769238521
    0xc17031b1602130c0315050d0b07090b132405090f0609031002091201090218041a1005040f1b180305060901150819030e0f090109020711090f060603 65
    0x1e1803540200001c06801440e86280701034440e00302c888000c0390504001e6028404001c2c6000d00f501e501501d030360410840c5440380880418058442020300030316010124000036041e00401d132140c0305c0c0c02d40f40441441d10000524a1030700d074003007240c0310764100948542d8591001c100d60304841c00b03d0f0400041100c1d2000035031503108000b801d47d4503110b0034810180c405c10076009001140c40450b88000e1a861040245098442e092002540280c004200c1c05154242c443c1c0d680d0003d00550341003024000030365101e101d41e40c2c00d503084030f01c9011405080100d850705003d02d0b0702e0090303c40d90a0141e000751542c1145150b0059040c8000d0110f0600d6a0324883e0b408900301000b9500b040845405007014402a4005d0108480d1044280007050000c641c44400240e6440c10b590749990300c1c3e00300404c0e0b440c120f40c0860083c2c0026800080000b010005a40d0452842d000e0070303951000680d2400c4601c1c0c08480d20070401e0034640140c0000082122409000088541c081825a0310030307529507c40300c0e41070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 769240998 1250 769239748 769239787
    0x10902150c1002031f0602060f0f131401050a05060d0503040b03040219030c03020a051f030e0309100e0f191406090d12020105010f0f06051305040c0c17031b 69
    0x4181910100404c12030704500012174403041156072505c0c2629489040881c0c82d040c08640c203401650b19140803d03840703107400100681c03080038100f203c03550b40310b5582c0300d110351028180d5008440c1e440e24140a280c4001d0b01c542ca8002d0307011956003d151915a80340d64407400f42d441907208170040400080c080d51030350b0158254210358140555009500c0703140005464185000507406802510000700b80c80c00d00680c0300710181450107180304e90700c01006040740a1b000d5540300f600d490200340403402150300c1d02c1401002011441e180c07448d586021106005480b00c134400803612507010f81d10407100300c080725240c1c1010382d02c60340e00d801403010300b0002107181442004107064108002030060030500420f501446000c102d580d00a0081d6681ca0100344d041192038054800402c0c491700e000c0090500070b000519554221050b0b0056980d5903200150480c1d05460400f00440c201c10796000410400c0624032508210051602d802d40c1030070742490004175920415100d0225000518030282c1420040e080c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 769242248 1250 769240998 769241023
    0x20f030114180105071d0f01020f10142401050d150308090111010c140d0e07060c0213050405032506330509040b04172703010902150c 59
    0x2061a0300303029040303078540614140d82d64007030351070b1001107520a445650900041e9803500000f406201001c02040010b04000f000141941f02e00300040c1c1030400188020501c0a8111100040f4024410814000010024801d0a144c040300d03080e80008049580542c0c5410820b180603a10351081e1401c0d10000e10b612105900c60714210040002001079410040008010a90722482d201c1c0800c0c20084c01c2c1c455950070103001c03901d10202c42500881040c00f0740b421001027a008940c07089284425030601e011a004240068589003010055052603d03205419644c4814200b01038034081e15120348078000c0340c611010560109a0340204e03108042c5154500c2038015504001c446654026550200d044090b6201d01c02c660720345040b2030072040100c603021900b000c2c004801a80d510780c0d901109950007802110001503120700602410447d4016110b510001c0070818021240d041000309207900489401d4460781c144150503005840d0000c1804105010352404e503180c1c7c0e81c0c100460308000380300d00305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 769243498 1250 769242248 769242281
    0x2030d11070b04121205070c030605151906080907140103181e0c151b0317090a0312020903100b0f0d0c03020a14010f0806010903152a0c020f0301 64
    0x404c100d29902202c0321080d2060021442c0481803450580356402010340182010112030002c001050082d04410703408401071180621280d404400150441030794211406c0c03041a2032400c2c40030a4000100b035070454010802499081d140c4039450800a540301d607294101921200d101200d51344c0910100c0c24140c2c026180c910441c00da4034110b0244902c210166501c400709403000461009007014449500003960303800d040c0445207402c80c104c44000a50480821200908000c00202c26080607030181e821600540310030310701401d0041840011005e645c40c2c01d807040100201e1540c00140d400c8455a09100101d40c500c40b4600103400401c0f0b14940c140c00040f2a15140100b18410140b0000c3c1c901c00c03a0308008a5444650b2000d86900040da280d01143c100d4050721140390240c41c840d42c4c8001c0c145455914941c507651031000c0d12180000c1c001915407101c21585060404030b0b407180a0b9420b280c00e01c1034201c280712000b860a801c01401074024002a00070700700030346080d00130000d00e502c25942c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 769244604 1106 769243498 769243507
    0x507140f0f1602040612051015060f0207090f0603061a030a17090d151406060f0f19110708010203060a1511010c03020a020106050d02030d11070b 64
    0x900d0700030740d681c002860069965001c4c200c0600303090010f03c2d0301389000e843c03e07a2502340c004821624450030242d090008628000c0c0c068100c03402441c09900c841201d5400380d04010301e44d004505028100180804041c00325002b607000c032445110208010340102e10030030340c80749e04140013507450b0304944200408a0368200c01005010f404100a034903080001000844c2c103100c54204662040303801010240e6954280b150103402c40a0030380c1d0b190140b91a00000e92648a94102e190303c0c10070104840c10035080302c5091ba80b0300100c1d096048200345070604050b007010840111200703070344500000803808110600a890080e003001e41140a12400d0060301079416800304850000c002e005080c0040505090140c0f456184a6480045e540e502082c4000e0030b440171038100300c0c0038107060103a510040c2c4000803200030302340750391810781d402800700f884042c2000040d40c016200500080fa = true := by decide +kernel

theorem cover : BRFrame.Cov 769064748 769244604 := by
  have h0 := BRFrame.cov_init 769064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 769064748 ≤ n) (h2 : n < 769244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
