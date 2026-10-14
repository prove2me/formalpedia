-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1355
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:32:40.93684+00:00
-- url     : https://prove2.me/submissions/beab7f0b-4d04-441d-bcdb-13cb9d7af568

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 243525179 ≤ n < 243705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 243526429 1250 243525179 243525197
    0x3080d02090a061407082109010603050115140f04060b070818040e0a02090c090d060b04050a060f0303080705130303120506010807090b07060905120a1d0604140301110a0f02070510 79
    0x21ba480d05507110b00b42c80e40351012684440701c2c8520840101e180108807050001c215549142005c81c00d4030502203506060680c00c2c0c0f070070001c10800c039009403c04a8180c8542441680980000340280660361000030115400a140820402c0c150000c201820300703510548040d29520040c4030480e01c000d040d038003050380140c0d164005031420202541e4449030703040303806240a00c10808112005000340044a005803954500107075481c003400f0305944481004010403400e46480c041c90342001e003520010b0284940c00000c601d91030b00c2082114000e1820000202e002a6a490010008200f4440d101c1540385400d011611961046411034002c618980d00e8107072641c14000b140c8803950209000300d40c0e1a65603500038002031414012880e401e0800c22401c6d0320707080c1021000d0b018010420b032001952000c0f00d0410180c0e6116000c0d03034241c81900500c14540c8680c00040b0380100312800c0600d440010100d048501a9401a18010480800da0a40703611a030769400344550304408114132004984281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 243527679 1250 243526429 243526433
    0x30c190318050a090f0b1c02091b030c031510080106020610050907200109030c02010207060c03211d062208030f07170103050303010317031b0f0403080d02090a061407 73
    0xb4101e400740200005c000a140000480024040c42c000e0891200812a1324001e6055103032000c919a4445810304601910300c18050381c2d01400d100051111144103c0440817440202c0842041c500c4114050014007051106010180000c44244643c0300103200d004002488081030141840440f480500303005110b46616400303952040004030340d50440d10307010580d16940c99090040c4101c1c2070003616100103e0070300d400024140341454101006002900f901c950020354022900d00240006184c8140040901085140584140042e40100c0d848001d50032030030306400310b03555010b03885400d82c002a039002a44c4482540204420150411405000040580c010650406e0780031905142c4103031b0002c00703060924040007003030304182d601d54004801030042000550301c1644545908401e41c0c20751a112481d6600c41c910022982d100c04c0d0082606982080e141d0141c40146030f01040f02625803440d502d400000b0b4009415252054400c0c0304001002400b8090780b500a00e000c030300c840c1c80d04031030b5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 243528929 1250 243527679 243527681
    0xd050d0509032821020901030612030e04051509070e0102060a060506030103060209190305030406020c0d320d0e131803080c0f070501051609080d11030c190318050a09 73
    0xc021200b40b00d5280124135180f0000320030719900415800f80141c4409441d000107044800b1600720b03200105a031030b10303200403035000030002d0684001281c010509580712210000c0591015824035081031226040c0a02d02c3c2d00048a10040300c0d0a900f01c4441e0f5458800c03800c103948461080e240c00c407900300014004941a500149110031000c1c00400507458140384c1c80d0916455640700380ca00344c0010505006042d81407050441d030708000c8403030010824150321002d2841c40e000c0c000001e0081501c045040303c0307451500028101c2811410b59041d12601c55002c2c1458140c002201c1c0319010351404041602801d00c204011415226000200742c1d045079070941c3c8104001d040f03054521428414180c2c90301c000e0f0b00070052a0b110301d0004c101d900704510031440d0f4442c500c861005008070100103000d054400207940341180c403249821a0f08840341280700e41588203004010b51140aa03901048420b0710000d40440110712954564844100c0c0c0e10b11504010500d00501c0d0307104540080400860010b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 243530179 1250 243528929 243528997
    0x30601080c040b0a081005061204120518011d030304090c110304060905091503030703030c081014060f2208070801060f032009150a0e04020d060e0f0d050d050903 71
    0x8201d10b01b802032625000054219040501800b100a81000400082001580300580704003c10708040e42410116880c8401c3c12183c0100181045884c51866252420640421007145405000e50366141e4803481d00c040502594000c0380e001c01e965010031034003140f0000855088803aa6900d88010608200821400400140c048180804140121b030200e070340034001040c0544c07003a1000548418600c1014051f903000401e002080300c041a02004031608642032506c0c0d101c0100d8805907982d4070649035681c1030084882c001c4204000151521035042c3c050010340c162210202200c2c115540c0d940824240c0d503080c05100811560b0060800005d90030001c00300301e00114001266281341c94801043d0100c03421500a211546d806581000030f040c0540141c000d8800180f0041c01032030a40c0100d43c13a0760b08084020140c41e900c0c0c0004d21a8030003401403907130500c1daa80c10390702405140b003c000c1854014061a0141f245410049081100b0010860320030780e000c06540c8640e19540c010710580003d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 243531429 1250 243530179 243530191
    0x102030403150501180c0206060f04020d15140603090a020f060d023103032c10080901180203101109040c02011a0103060506120703061703030601080c040b0a08 70
    0x12051001000060300c20740034260005805800242540c0740c4100d0300000c5005030251090280741007020000c0700d0313010903000d51101b002e603542494207081c180494020700c580030f10007200c030b4a443c0010002c3c8840801c0030b0104c4144007110307080000f112080012601c000d845141095010301e000c1c0c001410512141d0315080401040d00d400c06c8a10300d081c6060f0303444820390350781c281002843e00c54031210395030341c0b202040c1d00c01c5400d503110340c00c56802408088007440400c40708442c0140c021006280d145824010b8600527204080c042d071165030103000240d040d5202801c9500f04003100c80d040129950321482140c004004000c030404805911000b45240c01107140b600b40300700100c540e02d850b18005e40c0601c000d65400042d83d032300440210136810804032070160405007428002c001d00d5550405031400155003c846030b80300e0701c500c0e1041d4024101070f0701c40c0030b442071211a14034042801002a510038042030725004816501c80c41c40b59000d209030700501910300800c0c4101c15059204001c40350b8054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 243532679 1250 243531429 243531433
    0x31a0913030c030516111f12020304020a0902120f01050306060a270c0c021305070c0215220806181e19081e070804090e03120412091d150102 62
    0x301d02110b40e440c0e8034900b52080d12401303440b07501e0721b40a041490403849074010200031503400701c6c2100c800802d1070550441004040341c01002040955071080c1c00711004001c26142190382d149400b111406840e0212500d031900d070304001c000a42801c011680d188110707030080c07110441d603003080160404456029840e182140655190b266004074900c00d1000c0a415902c1d410041c410500c1040014025880c1f000301460510052024042d0041454070020340d0460f000ca51850010350a81c0c6140516540002c0c4644036041c00b25100024400442c1901d26100940d02559240740c4550412200401e40850036881007000301401024032502092900c03014065a165807038030045500c00d040ca0a4040e56402c1001909081105941c032942e8110905910117074140019925815124003442c1700c3d030b02030541c907181000c01c420340038001c0311440b010004203440c00d400e1030308042128814a51000e0301194640c000441c40c100c0d80d082500400c0f000c3d2814a11300c1d07444800c40303120112052620f80c10b40c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 243533929 1250 243532679 243532687
    0xf0a0201050a0f0302160b191a0f012a110108100b09061c0c02010c140d09030e03030a0e0114040e011e08030a050702030601050a0b180f10031a0913030c0305 69
    0x800c0508103e4a0031801403921854901340780008140c6502351510000300186050b20720340e100c16040304210603a550807a001b01505905a0060300c0c00d0307001c0d10b0983e002c04042c10b0480c1c1c066026008200e41207014440036039500800c8401036810140c01c0c0c2d090310152040c03100070042400711900800c0c188101034040390410b09055024a20480d05c001143c4100352501c82080384141d09221b0b04400041034031700200a500c00d00b070651414410740a02a541d56156090788090602803c0002c8800901030112039545003050401030111398451070050008008400480401e02c980b0203030303029120580c003c4055646888a000e403120040c490817401d0f8240e00d54001071000b07090000e000086c00d151140707a030f1241030384101420aa0142c0200d84a40108101804100095800d0341d0f142c040c030b1000c800d144021032000820320098038011560111610903c02d01e20759064202115a010030310036444003450031820041800d008807a00c0303400046041c610004284228140e0364cd244c02414400c7c60 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 243535179 1250 243533929 243533947
    0xd091409060a0f12020f03011404031b140a03080703060605090105180d080d140411040504050c0310020c010e0606031216080412020306090111031605040504050702010501080f0a0201050a0f0302 85
    0x514041c5620000c4a4600500304c0d03019400e14985220702e032501200200620000c0d80030446a06901900180400809668030050855603040c0d0800321034100341030b0001001ba603c041565444000360480000f503c81020030501406400350f80d050f60195100c503414500c130080115802c0c2c00c001001100d03030103030304038000b1203403582c108a203a010b002d95100f556920f000020401551001d016540f10b1000e01030030480801ca20402e204842c003411500440e181d00d50b814617518011082182650600840d0942c80b900c0341a0b500501445008400074402c0031440e106841d00c0d00d0b4100c1c0c0d0107400d034100c1480a07111088201c0181722655211031400703080c000a454507080c4c0d0300715810803032601d000d00c0103110561904000c140d0f400350b81203000b40503448840b407900076540000b4101c0000601c060003d036031650300840a640c09004050000c000c44c1c505410024080c040a10415226000300c40031980006800300364400740540685480d4600699600c0403900c140c820302440040540c20300607414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 243536429 1250 243535179 243535199
    0x200c120a08060a080a02030601051e040c051b011509091502040305031e0304020a030215090904061d07150f0504150324030c03111813050d091409060a 66
    0x292603101c0d51070005618020060000d01d002540000c00154440e001020050f940011403c0c1562010f85907904d420000e10700c500d085081c545480365100b424107a140f90701c907a219000d092046020040f15410007200b60b0340c2400c070b0f1903400d402c03030103803540b02c000f0b020612481c1c000c10a8984500512800300003c20804030403600a40c1086455400000b029000c0a1541c42e00c100700412110b00346155091030381c0052240e04481c400203018605881c01c000b08c010b103840a60308165006040c20b5910b10380307440c001c0c1c014112000c2e21141d010070210354512401000513284181d910346010b00b99900a90318064a0342c800fa21030300400c01c54200b0000c281e0450a0980c404410821b440124034200310051100f01c13410101110410745000d41420070128070059080e070201c2e6000044408892620404a8204503002c0f041040320a4400305100402c1a91055000345501030000e072075503880314241c12101c29090380301c1d004c0c080781d450311040320500d042c01101e5040900181501c000584c0d40385404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 243537679 1250 243536429 243536437
    0x1807030209040813030b07030c0801080d030903110d0804050f030901020a060906061d15100c02010e0d0c0b1201120b0406050709030615060801050d170d020f0304060e10200c12 77
    0x41d40420002c0a0101091309030250812200c9c440c144102d640d814590f0096650811154010030507848192000c2030501481c102d2560340d1840c0260750b07600714048006050341c40d0a079000c0720b183c0707e4180080c2180300c0200650300c0c100c805038040e1002c140142c0b140c002802400400307442440c0c0c3c0344000941c000042c6c0e950a210080400d02c00d615191969408036201440c0b182035000d1140c0701c110081c00e6030701c48025030b43c5aa0900b0100e400003811000300c0e0701040ad1b41c41c005d100951018003c035440c640000075281c0c01c032107005d5001c61681c071912071081102e900d0100810000e03240d40842c00142c1e03940c111b20380c0204d2501d0001022030f0f494540009491003010100c00303152400302d060000342d03131100070baa02400003030b82c0080c500003443e80c0f07403036590f070815090840075640482d90020344c0504e50111085212548246074582c1014101080200003c03290f400c07291103143c44c5a030a0004900541759410818004a94801003001901115500060a201d002d005d40030300750540c811074101134 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 243538929 1250 243537679 243537683
    0x1a01060f08060a030c12170409060806070306030c05041805061f0e091e1002210604050405120306040b061305090718050f0f060c0a030305180703020904081303 70
    0x29509803898510141000401a10050040d000d26038240003117900c400001c001c40da01c056904d1066552818038940415022039451900d1800041c00a0076000640040f015100080300752030490b00c034580c00f501202c2d45840000d08034149940100503a1605074090f00c40c0d00c0359048410b48040043e80c89900700101220813030605010074090080506000ca80800a405101c0030a403041c00c00d680742e156900644010418401e03500c4104610b160710620002810344044102507445040111040c40c5681c0c1e1200400d418503513038000211146890f0040c0c6009642101c0586a01081c0c0c800b48413155100400391504162591165007036902c0702070040c40c3c02c00c5070071030384d868071402e000402ca04884017500b01e0b0100a886402c07564852848052041202c50460b22b0140130f278a4540402d102810951950b42e106201150007840100b002c9441c40780f152082d07400300310540c0c42c0c00000070a203041c007402520303582c043c031b60a000500300f190110303411500401040d41040140f50600720031114507042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 243540179 1250 243538929 243538937
    0xc0314071101060815150f03031303120c200102031309050a0605100203120613050108010f151d0a090804031a0c03150105090a0b0a0c0201021905060103020d1a0106 72
    0x150084154007845180f010b080c988010702000b4224214900754010040c00f528030928040144181d9a500c45455141050000e01500c0c2c840c6a41d01d000d140801c00303071209a8025121410f03c2100d07510488a480300d1a5000038107000d0310325090b07025600945801d1103103046d8031042003445941107455414400030801044042501d241c8606910203661440d8405801022841580b03c1455000f1056512110001562401540e200340018088820000d00755002038900000814403000642200302120f00c180c0c4248a4082418400303e0b000100e1b10038030360003c0010b295412101c0e41000843d401c109a040042141c018544800e403803030340142d000b1200c03406000081d05d505061400c62a50240c08182c8150030752501e0b1580001480c2103455490420100080c815403941e0380f0304100d0045c0002d07501d215264a41d1000240c01c1c031030f1500040c4e000d48940e012501c811152480c000a04540c000068102130340385a090000031622035204aa030143b9042c40e4844400c44401060300800b50707955 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 243541429 1250 243540179 243540197
    0x50c0709051f0503060f0c1e0a051908040c0614040306060e04050d0306030b0a2414010e1e010c14010c03050703060510020a030807050912151e01090c031407 69
    0x380c140900c5081d82c00f941c000d4100404100d001100320b805280c3c800c2c5903e201956640062103c3c064090001d4818808010302142076660a940040a4911005403000b0b90410900d40d21090328482d80884d0024141c001128003800700a00c52480c42c222550080d131454101900d03669200c041d50082c4c4c211040c0a041c00c01040284103041081c1450707a07009040801c0747c40d0458440c1c40c581e8600501800e0030301e0702c9651600303e104503121a900000e070b50041000c091900d58403000c06492071030001c0d13030002d0084202100140782c03110380880c84040020540b40170200e081c006448001c5001802c2e1410300a4820b020440d400030f000c1c13803207132400d107940c0040c4514000801804940301a0000c50041e90340c1d00c80b03090301e9500003070381050b55034150400d10007907510304008449030310038104400c1c0c000001441600c0902c0002440d084852240701082050743c2d64001d040e90421610004150031281c2040101714072116a07000c1c80300c4100314500403482e80c4003c0b841e1011405c040c0c44482c001900704c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 243542679 1250 243541429 243541471
    0x50a060c030507080c0a03020f0d1b08060114160515150307060c033911090711070303050903070f080c030d0f0504050103020d0905010c020f01050f010501090303050c070905 76
    0x1100d250f078824004e0030301c0d09090804416800841c0160178a5105250f13001030303202c000007a004207403046cad412190340610000c45210400c40da181d8815040c1ca002c10b04510202e54150f0143c07240c01c0703028410034038081c10248403689484858079116026640780c05030018425100d6848013500d0304ca8100c032580303840501d001320300307142c0b4203074155201c0002c00010040c0706001a0b40310103540c3c500e0010451400d211010a444002d045240483c0390311f02081d02301416040103d0403d407402c101804843c00d694a6480110540b02d41040400140c4160040c960920001c0c0c040e1004d0412107a001d070841b808103890300d03c81e90802c10179070401c1c01d25600601c0391440e245800c21400924511520f42a070b00c14030301c410301400c14080e80c0030342418980c003c12651541d01700ea40c0440002030f0400000e00481140001c007a440321421504425154207080000380c058440c030810324105c803070617550319011a00d19102100c0d10741003e070b070045080c05001c00000d265441e40c05501d0140a1020440030201180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 243543929 1250 243542679 243542681
    0x309150108030304020904150e0106090603020306180d05030703140106031a0d0b0a09140102040b04050109140d030c0203031308030a030c090f150c0f1505061e040c020a050a060c03 79
    0x141e000d010780380c0c07040080000580b01c8010094010340c0c031030103210360030001c8843c80c809850300c0254001d09610b4000c00054491080e082501128029000c0c0c0e5000d485216085994102c10a1018500e51000c0e5a031008640b2640046900c2241898001005054036a80c640011020391004001035151105661009148500000c5070101103d281014041d955650426100028003081c2095910b8207100144401700c050344c001ea1142c0da001315500d50311004e01603995009406510700041d030744400400c00130f500480750704550400500303101e5182605da42c100c4000424403c204d03010300007481040d400c1c3c1110f05411000d08a00409142c851000c13060007000c031a004403800f0304000ca0044100724541e0403042482c1aa094190483c00052400005850b1040061401042d12015a641906022054001e000c00401c07610b020300c519181d05080102d40c0e42400001a040c440710004054246401e501c480780009940c0107441341030b20581c0b40d05003400401c1714180e801c2d50321006000106030741 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 243545179 1250 243543929 243543931
    0x8030609010b0c25080102030123010c0b060904080405030d08090f010c090e0a090812041704060840140a031b03020c0907020d030f0b060702040f0908030915 69
    0x2070501000d050081c40102550780310364804e40f0107490302258649100f9507803ea00340f04003824058000b950303030756500ca02a100b4071689030a940c0caa414000400002988212420314956401a81c080c1d100c2d1504010404050805032007214550410000080e4684091215003041c601d540c4422704686059040f09080c000302218041003645804144131885400c00f0104c41600d85803040500c45644684110380108000e50014103c8500880c1c1064048001c803180c6118910884420195003c0141940c09600645c003602001c60f0b41c0c2d50002d203007030702445074a0007400c070221500080b200e003042002052481007448400c010864407003103c180074a50b403940114428030030040000c0e91340d41d10b0042030a03078103550f40c414400c90340181c1014140308102000c00a00c00404141e1a07040614001c0d59480b48141d035000800e0a01503800d1081c07185100b0008150030281410386803c40e2582040010400144100c0e00b45075103483c00e2011420907006180314241020044c030400c040499603a1140f04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 243546429 1250 243545179 243545189
    0x51c0c090e010b120a02162003060403050307051c151e050a0612020d0516030f0c08070f05130603020421080703050c0a050f100b0402130605090102190803060901 71
    0x1014401080345032802d1046501501100707402d280304d910380b086903001900c103616001810790045032525051040020340403400342040032500074407080c0314061685414088402a01142c01480068204c3c1d010f600204000908840002504408041070000701c42e402c0301442c43d40e9405d101c3c02e0001c0307100e40b08121903203103890252126562800b00000c41c1003070786000700d1003009007080e01c0c0e803912a078980564070302c4c0000d0031051000d0700c0c02600c0355030601000801e00000a092201802131440c4502c00c03408148100e03543d9444a03a140141581c00c0701d0000f1102c410840200584181d58020361101c00c084c24499401603034440c58041484080c41a0b462034440440903c0050000070b1640c004480080c1e44c0744c105a5200c180350b5042d14104109640d01030003502541004189189010845020100e9071010401c1040d20783c00604c0120700a000650b04207503009602441141e0080024003d03501051044540304955007401d00b100e0089007004417029500441801041d113450070510303000d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 243547679 1250 243546429 243546449
    0x1031212141012020a090b0d0f0308160e10080702030d05180d020d0c0b0c091002010b0a2102090901112101090911121e03040801050606070c0b0a051c0c09 68
    0x40040e4001a500c8005d0303100d2a51501d64414905515403601c5042154a40d0042050006548079090140050320201e48644c3c0600d54900d102442d18040c18803a84070f000050b08860198400080907203400d10090441070541c4414401119030503030314007485d4130030500d0113002c0c081c10580c2c40505140c0b00c1004410020740d0001c4014400c03640d44103183c00100b50300440081440d0320340b01c5a80402d489001d0302142c004d008208a072403803c0d015001120f207000140d407459109039403564000300c2a0b801c0500309140040c0c0d540144090b180980b0241d40244c0d14600004d110b600406852400307030320540340c0d6072401180b04034811303600d80324485031401002c4900007802490500e0365106c241400350f00030b1a20641c602882c0c1d48101404003d006220310000d6212604100d00b946080d640b034001e482103103050b41c200400220142840d10a460307582d684916213490050400954010075041070b528071003000030600010b01e084a4071030701c84002000b1014005401992014001c260002c1a08508018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 243548929 1250 243547679 243547709
    0x2040314150c0d0c0c0206070602030708010e1b031815160206060901120309030203070605220506190e03060c070b0f06220209040f1508011103010312121410 69
    0xc000e02c1c01c11241480804080026024201c0342d09403103170620786002030340151020840100304461540111f000d100183c07599401c680c0c4e155100340440c18101e80002c0300b10b500381039450480344400082c2d60003c2c50120350500b58101041950700d03258070400808085900001032080c5501c070102d221003008005e00c042c2003d80340a00109200a4044c495810071001c44140e01c001d041c425a6208080d40c0d00805446d1785550320503004020b5080420854040c01c0005051803501c000c0349002e00c100d0f034000d44a28100040c01400c0741100544105c28402e020b2a08248003140e0b83c24000d02c0d114411084410761501e0307160510005050001b8003804d00c9030a03403000d104c059a5080d8540034007444841c25100c0d10f1040642039406030054800c40744d045800e2903841401d00f071080d08032152480503900035005071542c0c1d400560994210762041d81095200700014004520407807041c000c10440750524206025003502664229104000d4009a100030802401706200250141100a08400c1c800b0408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 243550179 1250 243548929 243548941
    0x10020109021f0c080304050a0b0703060906090207170c03041809060f0c0e04150e09100e06070e04110f0309010e010b0a0509011403070b0c03030906070311030a050405030d0204031415 80
    0x700110000702402d21360004c40000c0c01c00c0000c12194003803e50040801c0c03424200213001502500c0540215110b6609064004c00c0410851080c0d0f10129006410981e0005250b400407000381d02051006021303000800011817480d50048000c405400c145800003800c440700c1c20104200d41e1650b1810134118105250361408070351040304202582003c41c0c0000d03c8214040c4117540342d03260307540320b108031a96110070400004401f003001c4900361201c2d54184a0401c0c00107020303480b1300085582c10f0124465801742d0360035040a6008086401d1800c1071540380515000e0b802520f60402c581c2a03841d40e45555000720241004e000c1c07004045000d90740039114604007800110501c2050180341c11805d02a440c0e00032a039000c03c403a1005015041d40141d8600c000c0a802c3c2c0c9980c412641e50314a4400c40700403c088612a10074405111180c0842c10f043d521006295405410040c0040d501803100381300700781000901f80b0041005520890381c0d400c0c4000f143d2251818404220310001c1c0c01c039050020860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 243551429 1250 243550179 243550187
    0x90d0e04050112201002030309100204051e0301110f070203070905150405060d080304030c06050912120a14011409061203030103030c05120406030b0102010b040b031b04060510020109021f 82
    0x4449034015460303106014000e103646284d4950034140783d07000c01030b084129001500030009502138050481555500c0b807091010070203074407480c450550485441d400c0700125802a81401644c04001400450022402c20580c0e146e0380004001040030280043d10b80c0c00c42c54108007440051500003401d002c18907010211550000400300e07518080d580b14800211543d580448443c016940040030030f4803400c050400410701070300c0e10300071654146020081850410000707503001d400c04062401514002c02e044910340744034000307070800c610380d6141c5003400300c001c001041c0346000e07000040081c4c07440840c0400b00415034102400c00380c0202034040c1032842d00000070089a0551750503040000e1401542d1501515000181542620b809804940880c0e102d50503040300090040c01d070300a00c1045a224100001c9a280030100c0342d040c1c0c8101205408140304880d81c0d0034603074000b030000522039615000f0440c008040003010005075034590f4640d0851410040706e00c0d0664036002c00150112607010094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 243552679 1250 243551429 243551459
    0x2070f051309020d240608030a050f0d0914250b09121c1d0904060f020702040e0c01020d09080303060603040f1a06030c030111030606031806090d0e040501 68
    0x20303025501000c800701c0c1d100c0300c0b80c02030b501e0550b01901d603620240035400d00c100460a5003040103c5148085261150505940611400d40f000c0310701862403c0c11600094550358000c0b040407030103074002c0c015032040700300500c6010541d41c065407028800780160700c1002d041400c8081c107440d00d404003500503031031611610005000c1d035845060b9144c0e1120618009141c3c220081c0c483e01452003031a8510108081145680c40d82039500e80302d211840e06204000304003041c542c08450b402c050308500050200340c807500102c4544140c0c90700145401032507004101a500c000400d010780303500160400c0c11550703041180688001161074a000c0c61402d14a0b10b039100c0c80060304d0a1f00c510030110200e0b00344140e851105ca84c041d07008004c0743ea43d040f01100c40c040901c08072106842802242300742c1e0410b08041c000c002c030110180115034a1030341d4001c00c010240d000a01344818000d4aa21a13a40b494800c20265009440035402030005211a040c02030440065400590041f828800104010b9252404071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 243553929 1250 243552679 243552689
    0x150f090c05090f04020c0307030c050105070f020a020f040b1305010f0506030112060f060906080109050c0312251b08100c080604020d09060c0f12060311060a050c0d0509030d02070f 79
    0x1800c3c81c0185040001d020303000c1e2104100041c08000345020030103401c0790950030340c0d1384a807009110030764074030320252a180e0000c1d079420056000000d0120051070848959002114010300004401c00d164010840604c014420001690780c0c540041c030444103101c4905d001480d0441c2c1051a640c1804421200c044161000a003483c0d1500034002c0000700941009003d4200d401c02040342070341d1030191501a1403201c030306581c140200c01e09071019003404207002014000c500c450070310308050300101181c00a0b4840e641048850240c105400040c0120340411121038400d015841443c00c00c0019424000c12a00701041103240141c0444036580101c3e000d03500002c115801a25414040444000f401d00c2c540d0003007a1500e810701d1420303225004000b5100d00f10f03041d503505100b50107010400c821181c136800042c0086050280340380c058a0100300078000590545403039170070311281168a500c3c00c00d07042c4003000030a9020607068001d09080028039a815400d00c000c22040e468030400b801d5a072014010303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 243555179 1250 243553929 243553939
    0x9100305030f0705012a030b0301060308190e03032107020a050d030c030219050d0f0902031b060705060a140a140c030705210109240e060f0301150f090c0509 69
    0x503c81c00e00c0000c1d0310048001140c03802044560308070300490300c80b10780d454402c140800e19100c03c0080e64203051064070150b80d40b04100d1443c10640b0084070042052400e9600c3c01c1000c120b4405050361401d1004e811082155021100356200402240000300402050b42045500400080f00841d60000d04910340b45200d05002582d404100750403006031141c90507486064207202c000010b9150f20500070010608a01c40c01c1003401c0700c0b819041c0039611103550281d0726a1014003e079051070701c00200d8002d10140180b0b1540307006281e80d00c982c14402c00b140c0e8442001c0d5118039031202c01e031002071030a07071080103c1c81c20000707182c44884241c1701c288082c082260752a80400007400c840d000301c00b101c85c0c110350000d80b202e540c0b00400782e0841400c001d02075041410305100d654141c08405c1300e685240254a4561511403605040d01898043d100a14a0354018204110045c03283c40c00e120b01c5112008482c88064020f0514581c00742d1504980d200d110070038504a1600c0c1043d82c01420365a03841800c5070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 243556429 1250 243555179 243555187
    0xc0212070620030f0f180304090e1e07050906060306030604031809020f041a04030308010b03060a05040f02030403030b01110c0f0607050f1606020606090601081008120909100305030f 80
    0x2841c002070740748068090301030042c0002400f1440b00b000302c160f440341080203006a11541c0d25811b5603480d10503603c40208503401440300303000c05030558100c8460703070711328400b01d40000319100440501068000c1815203107400c03022040c4098148428180d0b0f020f081554844d2850508001080e503401c4000e05c017404103c0701d0340c13290034181200b0082100501c82100155124400102000b09a81c031a1046c03041d90340011404080105030501a1401c881c0c05480d5854a80c0ca4103c10702201d6200a01c07031584001014004105651544600052034046840040e01c900e010b26001d0304581c030848419051001400044002c001d0015040b288034030240c98080e00614008040350560140301342c02880c41c0075400844506001c0060300c6000c2d041c07455281c0b50b400d941c03a103090b62107803429202c01d0707081400007002500c0740d40101130302900305140a5400d10308958542e010350400e000c1e14511034441d440010709a489107008450b180d0404403074840700e01541d15550f2065030380c0c80740500002c10f01e10042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 243557679 1250 243556429 243556451
    0xc37180b0d0e030a170108060108030f0f09030a0807020102010c1d040209010e030102120403080c030c040b07020d0f1b1d13020105070606031101171506090303040f03150c02120706 79
    0x9007095216802c4070046984862107a100600303101c5440c0d00d000e0301c20030144000150341d00d0000d1803c0c125141d20001d035142a030b00503424a0f03241e02500003406081c1c01048207070400e84081004c003069600410005403140b4161000a0a45200b002c5520802c00d80c0100c010021350044500e0300d00c0328003110b00680c1d4841010040c2d030840d00882c61a1b074954804141400d40c02552006e45200c0c61003561541d0859951089101d2240410703164620141000c2c042800f0340300700036006041060009021209601c80f550340d4100c000d440308011103010303201c42500c040c0c400e080000c00c0c019014000b0b224146038400ca13581e400e500c00c0207142944610b00208070a080da4064000c481c0c1c03850300054284a443d40343e04000c519501d40380d41203400160700401c112001580d00707032481d0161541420f07042c1101c050380208841d54202c189215414002000005000f028100c1c0e09001503116200100d1a0381c0e51244002c11507c03041d1703220f8155005002005c032407c0031a02100d072025402840000d00011700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 243558929 1250 243557679 243557681
    0xf0c031e12110304060b030a050d2a060b0906040b06070f06091a19140403140d0e0a1401060e1b07240f110a080c37180b0d 54
    0x2003070100d10303168030340a000d404011040340250b1185010f11802c0c411030388030200380340c0d86075024007014186400c06002c50400600c03c031102c007208070340800450142c003822614078041c44240c00c01290490360b910076407002800c1044107280e024408440421142075482c000c140c907481151402862030505402140810189910155030240c000782c2204080d80c6c0510b0402804400b55140030300101075104454510305180550110849060b56440e025122507909803030b4400c1500e00c2c034080d0803081c41052501c000d2481125403421680c0005e10b20481942000c020291100c955418540d0600d8414440c4040c0e00c480d11fa00803131800300e00d00f450100000d580c8098017402100504644841ea040458103038484001c079150402a1403c22898205001403011034080040614641d1400d0003802000c0d4016241c150b8080f06442c2c01c80d02c0e00143e000c105190303070f4600303e0080e41c034064402d4891040f51481c0d2501102034072800c0284140c11000d040722601c050b544038a030048880064610740c00251 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 243560179 1250 243558929 243558947
    0x9010c14090a091e09030f090519060e010311160309080106141e03030304080702040513030926010c080f09060c030c0a02010e0d050c0c0102010207082d03070504060f0c031e 76
    0x95880800c1000c1781c91500030100c1010b074a81900040c0c49400c0450700e8a420b0600780c442400014222803141c0ca05141601c100402c01e940034141a6a41404c400446100b0000c001e03007038840d520034030031500030b00e4080c02c0e007005600a084180c0c500141803154100e80c000c5844481401c48405051282000021400d2409803404640601020051104028140c809091014400ca4080c401d580d680c0e8040b2880c6449014082c00203828008100201c43c00d0303c6000405800105400100c010601960781c01c1d64040520400041e4a40301000016082c455000e600051542d000c0c16540c103044034500c10f2400054a002038170b440c0051007640850007580103c480c06075100544800d41300c9800c0151803900303c2d40c9488198000d641a040310366206200f1103005980c030083c00c6080003450281650703481070300a07001510111250f403d1140700c00c980082c52080b2119a1216619030502100402440c40140d0f21010310001401100029030801445000019220303914824105605422900550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 243561429 1250 243560179 243560231
    0x1410111204032117010303080703090203150108010b01050c0d05210f061c03141615020a1d091317040306060f050303030f0406050606070b09010c14090a09 68
    0x40005000010040e220345555052100c0c01c40f0400800b807121403d07122107001902d1200d008000f80014000a4080d60416400007840d2400041d25151640401d1402c00031712803e819400d1104010000c2c1842405054400300b000e00e03016051948520017035588006030900b03c028020007003442005108045024009100403080006c164208001200003259003540c0c1c503802220042d1050000001d000c2d490950141d00d56203181641a1040c020222034010305121040440c0170300b00940842c03ea6507403006074004001005990740354824001d0710752807289001c103010015146540106035101511198006001d10050b032a001d41c40c0390500c1c83c0304810030960740707601d80031801000780010b070343c4048107a030304143c48880e42503154800c03d642c9000403a5a040451610b070001800036406400260704054040d1020303041074240d64600c180c03a42c08545c0060a0380d5035580301100513a00c01e99030b811540300550708614012852012955800c040d001d0340034500c3cac41d02c00341c4070111510004000056 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 243562679 1250 243561429 243561463
    0x30408071509030212130504050405010b0306100e0a0903080403030209030703140703060509160501110703020a0b0720130c02190b01230f01030c03150915141011 71
    0x30101d50540040074503980c16001441100b084140002d015070032034041003481d610030304016103002c00b01720180000030411070350755403984d00080d100d4034104a01805580c107000d6100440703083c2030394448200802403140c14580c0c02c092160001c660014900c2c1d402581501d80546d88002d140b010034644106544010401ea886140707038020041c0103d28042641c2c810364041c089500c0d0b0441d0380b641d41020a05500400300d0030082088a0340c01134681400c03c40030201500d4005542c0c4d0006012501eaa51040400d03c1d8000340308420030841041e4500b08a05012218280c1e22640020810304400d13580e91134809a996140c0458041c02080700308400301205000c40840c2c0b14918024030240428400c19100d20801000b40402ca03502c412000f400c0c000c0504424000b052000045010b4011030785401c050541d68441c0343c7c5860b8440d01c2550140c600c41101040c42801c0d220403085c0190142d0007280c0d090f140e45008482a551903210260f007900d00e161012104442000c814100f040e02181d8410329 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 243563929 1250 243562679 243562703
    0x32601060201230907051c081306030b04090b010504050a060909050f070f0e04170f070c08100b0105070b250314010b031e0711010f0515060c0604060203040807 70
    0x910340c1504107952152881d11406406080003c078102c100030261944851034126240078001800c0405075240d0302c050100b41007545a805403900c8003954030403460030407803e015440070b201e804c0e05070140c0004014103841c20002682c2a4488031803590060040c03e105580740c0700458401c0d0426000800504050b12040000d02001c4c5400d9036610241c42180c2c80d1400348100004034103094000d41000c49128020b5455240e032150b03540000c041516400b40015402800401c074445034901c094045a2b100f10b4001d43c1d800d085c0f141203403800c990f61000d0b9456604220700f1074031590b030000540c0e0141d03900131308601c3c682d281c02c100385141605c215000680003451200488400381c1c1500201c994104261220079a0b03621511240424403080301c48403072241401c1e90040c0120080300c00180e0003a218a040d404140d4901e01035030940340d082c603084001d03644074802d010484004400f0400d540c4801c80d140c620300081005a1030300c80d0030003000076223010390220005041c0907018044421055101e005501c07a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 243565179 1250 243563929 243563939
    0xf020c01060509150102060106030f09120210060b0306030c063f090102030105010c030f030b03120c07050307061e050708072010201903020105220f032601 68
    0x2841c0511540344503180f50800725071860030070400c505190b03a0682c00341040d40e00f001e81c10f034042d00602990000326030340c5588070740100381c45c0b07801c68200c8072482c0e003d040c0245207056141c055800316084403800300d10070806e104060b900024212400d600c01c0d1041030b141c500f56554695030030010580721540012000d91031140700303d0317244130105030f01d20080703c03542a40300d035400a400c174003090040b140031a126840c0032011a01031090b280d19a5443d2801162600e0210003007414641ca44e01c000103034000100718030704c10300b400b4440c0802400060b001043d41c03a00d881402040414600540200394a1400d400042c03d8443c0080392441d03508020030315aa40400e1802e80f00500034038180000700e524501020030945803c80400780010745a030741e024030b1003203140c82040c9400c0101c11115818850b500c840495182c1010284007120700a03000010f0510700656044000b1400710340181c1d40100f00d80c6010b000841c0352442c0c1d065a50103103003da004d000018a2801141094114030b010310180742c0001403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 243566429 1250 243565179 243565181
    0x5120622020406170d11010605010804020f042306040c0809030301050d0305040b0f0d05070c02130b180f01210b0703110408030c0109120c0b040b0403030207080a0807020706170a050a0f020c01 84
    0x100f05005a86d482c100c424040030042c00ca414034000c59000680c0900458054506185420040078004000050340d5441201c62080007030208030301c81c0c0403800303c0100041d5141904c41c610300030b0301340d0400064924003008403644903c01409a984113020f40410f9105040c41001580c0103010402e081c2552589a111350340781980050043d108000c0c01c180c00100c0e038a01c50451038031116806009184408004030780b400c0a026000ca613180c00040242d0014500c2c904a028103010310100c01034850254181070408018062441e44004002c3e5040a1030740002c050a030041d030301122900d80090341c65140c8041d805244220b40c0559654440490003074106001903100d07458440c82445080304143c22480e0581e0031210100c0c011f8031046103480010f01042c1c4039202d02d03a10074480c0c41e00620300f00c10703a621008250444028040090700000030002683c0d0108800c07400b60445050039980c0305030745600240324000040c0000025074a03400460b40281da00d8001d4818844c2c2440d00b951600c80043e040783c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 243567679 1250 243566429 243566443
    0x16050a1a010906060f080711031e03090c040501030201080a051312110601060201061203031125030906031107260d1e060605070b040f0206130512062202040617 70
    0x206039454601c0000d490b50084007010350945c110b40782c0b0102561460810b949808901030030070044e010030048a17400d5a8010b20454106441518036502c03810000300d0719291801e0001c2040c0110b04d42001440541c0c3c1103c40300364001100c01c00403a00d59140007a0220250204078000d20f10350440280054507500210450003690003442140c40c2c43c2c0e681c901c22801d07100c0341d00c116101d2420240080f004a482900041b2000c203c04a80034a490801f0505044046280c2044c04009149805a0f0105940b0569100040c1821314080c010303c44000040030032403250b00350041140c04080900e0a00b402d0403459041c140c44a100e0b0151598a001c10320310103852100c45403600405650a0840304001d64854981030703642d5a41c1c3d150502c00b0390b80d64054051000342081e2140c0c100c480c401d00040ea5030200034100c00700801c0200c100d052610301401000e104250b40765070720350040c1041140c25842d13000361a180900c002c80261132601c050002c0740007010550400d0400310004100e14071421000581c030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 243568929 1250 243567679 243567689
    0x70806010806030c09240307082103011d06010c1a0a06121203020903160f03030305062d0f030a0605010e01080a03021b0f041a0a090902010516050a1a01 67
    0x80c8056035502d604058461250706802c541c899111030205038683d4401e50300c813800c2c5469001c4101c00f0f40704900000e00d0300c80c15900881450344400e000150301c16072910510000c11000c1c03061400c46d41480340c40e9000c014030980440e04500f6034070003e02282c0c85a940e6400890b0045201965860011840984140200c0350480380d04d091400005890345125064000a034018402e00c0074900581e0088020f0b6000c04e6102d54140709400c2d248445220501006000702001008038902c685035140160035030344010705030b500c02c81d0000200c811851a1042040300000c00c8584a80d82d02c0012001443c4e003c590554244c142c41401e01803010054203503c0141624040121008103a80e515880c0e9a10208424000c006130086d19401943d902110758030b903400351006046030264004400401c080b1540078841c3d02d0040303040c2211400703609040361604080c5c0780024090000044580000c0c00b2841a0442c090304000081f000c2c1c8240002803280c1d9440607402207000b116410300018880c0e5410081c020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 243570179 1250 243568929 243568937
    0x2070303140106050a1b030216080a0c05090105031507141201081c020712030903020405070f0806030705010f08040c270e06060d0318080d0c05010b09040519081207080601 75
    0x102c0c04034091010b4940351411a906d0006940141c803080c040351000003070480540c403d900d40600c1140d00740b10703902d0143c000000200030104041c1444205600c3c00d0344000d004004103401030000341c80201d512104c1200b256503452403030700c0d0000c08684141b007041d9000ca0085012aa4800103124a110306040740e4056085500181e6449903903034003807004140030005640041c80c100074100fa00c00584001d1406410281e40c020b0b501d07004103050320b200f21404c90000e104038404d850120303000040c0b5500000258010001c681c201000a404010408140001c0c844007100107800c010040001300050b02c602d02c0e007030f4250f546107030402e2941c2400c103c00030741582c1003190703144000c040000d04612544008002d4121600940c03810f9440c4685240e10b00300c005045070000c00c82402c1008225041136060351141c9400d1618142a405c441d110b64031580301e0b410b80b0302400f020480001e1040c0c201c00d4a030024a40c0004245402e541a1064001002c6003800000c1040b001d20b8001140300c8c07294200fa00d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 243571429 1250 243570179 243570181
    0x515040506040b0109050919110c0d0f05180607021e030d1106060409020402120103050c01140c031e130f06080f2703040306050f1f06080406020f0403060207030314 72
    0x7081200b070303071020941180022140740e000c000310300d000a060b68014131030031030300110448050000341c00e071050b0400c84140c502c800200d001c09014204072180c4070484520b01281010303c01100144240b003140d60304240002480400003040d41c50f4022284415801425440d030191250500007140c80c2100041c0c1c80781c0540c181d0b040d030040c000c107000c1041001040c05407805640c0c2d032040100401c1c0002d41603030490340c24840081e8a924902d41640618019001024800e036044001041c0c030350b036642201c0c0f10560a01030034801c4c9400200391002d40002c00800d000004542426180c14016865103240c060b4800708001907096521011034180d030000d80d10900c0079030b41c0c01d103030146610f402d0340d651303181c0d0304983c03c40b40e640c4054600d0b42400b881c5220699103882d55a0710f032282541c1c0d00380c92607000034459200f4130014003603e010508961520340c113803414046c40c154000d0642c45c3e0003040604115000100350103100c4e0b40c0c0003250301a55002404544608007814010020f005020b904605091000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 243572679 1250 243571429 243571441
    0xb031006060f0f0c030315050402130905071814030c060703030e100e03340302011406010c0c030318030b0c0901030c1b03030b0402040f12052a01030207031205150405 73
    0x40c90741c024a420b0b901c50550101c0340350717412801032440400c0d00c2608900e030100443ca80c3d407103000030406c845c064051085410f040a07482411200098400c2c0d00344000000c5070000454055140400c4a543e442c09440c2e02032060302280c180342d4400c2289a008200107490402c064040e4017080703480100744c04a505454403000d0003000c50b140d01c0741650080d4070074401c4500390800703c08403080f84400703554203541403028410900c1100300002411000b6035180d04d00c0c80808440e58840f554002402d103420003030010180c94100c1c04551900018040140d01c03080380c541d20500c40201b400540c0d01c080c0340c510728603100d402c51440381c000d000d1140c0003c0c00c00c0888407070148581405c00880112043c44c00c18807105690680090207001c80168006400340000a0100d601070f00e00300042403030150110341c0b40101d00d8039600300a00499a50200741010354190340d9682c0e62440019071440a00b00182d0b100c5d51404d041e251400b03881c40e40c10900c3d0426082042170b101d00c4030520410f02059a0a0265490b00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 243573929 1250 243572679 243572687
    0x230c060405060a0c0810031101020a0501020a0905010201151203050d0b030604120e0d0b1501110303010305030406200303010b030a0e010e07050102070f05100f0c080708070c0e07020606040b03010b031006060f 91
    0x281d584600d08a0f406d8028400700300c604941c5083e42c0014012503014145a50724103080e0303044550401c01082010320104080d5130203020716012103050001d003c1b165824002441f0462258220260800c40041040c10552045a12080c44810014100c4409152514200c090380001441013070004808155120701d606045408030011076106141d0445940d03021030505401040c0c1d66451304105200e000d984a100090000314040c50060015595981c20030b44003130581c490222200c100c2c0d80c43c101410718a1507000c8250390560300c0e01d2200646c0c903110020500090080c1110702000b82d480c041c9154080000014441d04441081e020748100301c0c0d50b6401900e4108252003450340260030030031001e22031031258507140041d038030500700029503101d20346a81c41941c100c0e0030b0850310100001004020300c420400341c0030091646085a50840c078102000a48800c07025150501482d1030b024090760300d58003034000302d01e41c0e40c001c0c0407070f5130a028074a1401e000c1c00c0c640c410708000c0b0342101102c0521600c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 243575179 1250 243573929 243573931
    0x1080402030c0906030a080f041403240c0903100605011b05070b280c02041503020607020d170c03120907120312060b0c010905060a0c230c060405060a0c08 68
    0x5010341141c0380c2d05402c0c000f400c0d40050405074180a0b0241c031314002140d01014020703480e040e482007521541028000003190511402c414441c1d480141e80c88102560400309a50b0400d00031410a610f481e801d510426a01420681b20f40c54020f201a40031603c038164010021a0b100b6604c10008081042500c140d102002e44090450f8001240a0020000c010000c00300c6c1c04524040052520b0705080101500c2400b002e5a40069500d1504206602e028010103141d040001340703141c0424510f500003420380c45120002030140d0006412001440804001e0030803001100d8180c694030b10300c000c0207640320390240c046001d0501030340d004a140c0780400180702007504e81810f01c49445541e551026150280343d10070091a990b203540022424141c4240600484040c40c00040784240141c07418034100b000040c6110314503480c101c84004c80960041a08148081608003012030312141d20040d00c2c9486400028034241c030544042c40100800010f2581c0701f0182c0b100d0800071250045c20444080d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 243576429 1250 243575179 243575183
    0xf0609110a030207050f0304080703050606040204061e091806090612080717090a0f031202010c020715090506160b010b090102060a020a170a0c090501020a170c03040e01090c0e010804 80
    0x1001d21405801c40d000e40e00070441180110104c400001071400383c1c614682c8150020402504804810420450104040b541180e0210303000e60600341052401000130702e000200e0010740d0f1800201d0003115008280101c00780036080601c12400a038440680b0181109106448c0a5441c1110024540d2101e4103c80e5a040e801070b0881e203410043e48034812451046002c071400000108042c0e440f568810340b0080c002e0500032540c0c00e00d61311f14101810742d40006a03070304e811369041c01f03c40c010031a408100350b405c1c2c991500c005804020402c4040f540388440740c00050f0031840000384d0b8400030014952440b5030742c1c4100c444484680e21801054020b01601207424003580c44070010841030003054000d0900c0c8015841c5c2041036400c0340d4511401c43d503050710380d0000c07180d407541208012540032207001c000c1d01003800144098040c41e6100c00e0030440c3d0380c002c0340a540303000c259000400028400c4500410500b080d00c4015619005420020302061010b500070404542104000794085c2d004141b0446d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 243577679 1250 243576429 243576461
    0x30f01090b06060f1201180b1207030b0702030d05090f160b0405090402040b031c0305010501030e0303010b031b0c030405040f141801060b0c070f0602030c0615031f0f0609 75
    0x186910b000c1c0041c54100003040700304108240100c82081d00354104545c0241101200030345201910781013002190600b42d0200e000302c2c16500c50442d00d0307a0020342c542c1142e41c040e9030340742d00344d9406000701d003140070f806600c81c8528104018003e00500003c1c4504450034540c0507607695078500c82d2070701000d038110b10a04001800a000030040e9240c1441a0b5a000d80040c002203031a0060400190401d00f00c1030b08086050780e411a0380d2901503140c81403902402c4c00b0f0030204045200c0d0000141d0300e0005110700e84080c04000b00141030a5210300c5410030807200340800341e45520351000110b40b00e40007405042d000d02e107080d40c3e084d0030410034010b601a80c450081503a8079a2180300d80b5002030904016901c0b080c0d07494500010f8208200c0b001840036000c19005000549e0419009601c568410741c0000c0440d4014080c0821a60740450900c0e04110103902444d18000d00d4070100c4d080c100ca0070b080303031001180610020090006c6402009600781d60101c01c120042d21041000100d6969002c42207060b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 243578929 1250 243577679 243577681
    0x17160c05041b0f0e0d30090b1b0a26041a0903250e0f040b1f0f03060c0806030604051e01060306090606030b070219020906010507051b030f01090b 64
    0x14000c032850524440d0b549020903030b504440c4003154442c41c00c014100c070800003150340c290300d54441710168071746c491100e07526050310601d40c0303002402415280114205800c1c0010780341182c160b07a4414481070703000c07901600c1c55104141404015140030001d008100d18003518520400c0300c001040382d003524042000c0c100001c0914000c401c41d5040700610607094815a4119654a00003000700c0c0d6500903481d56204e101828540e040c00d0284d006814403210301200c50030721000404e03103401181d00c241c844042502180e01c0500c40134400c20550300480541c85541d0020042c4001782e00401303d01000f5403220821510781400b403640e20542141c0281c0350b80c00440340c4a5005070300c00315400607109c2080021403940d8880e15480d0407a07543d100100e6034195034003c00c00400491030700d0281d2000680c0007030310300000c07101c0c1044000828550028480c1111302d0014200c0c2c2c1c0603401380c031202504002100c02200b0741c0c0c41c507800405100580148030b4801c0780ea1198900b0f5050180618640c3c0c000c1204076a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 243580179 1250 243578929 243578981
    0x912110109120509040e06091b01020f0d03021c06060804030906180e0901020d15090b060403080306040b0604030b090109050c030c060f0d09080c15011d04030c17160c0504 75
    0x90f07604030428041c1c0c4203481d0742d5800505c040c20068940204080e0000d080c00c1001111070146485c1024421810b5400c100400c0345100c802207041c002450701400e01507501c00c0d0074520316080d00c28100005d40b549203022008603044c0e0b480000c05109620a4940c88445519903a082d1a51112541c3c070201d1400d80b11014042051880710140e00049401c0025003017010b0441c0c01e906403909200e8000e03000c0007007101008054054040c41580c90740a691441c546401c680340e211203440300034400c80c0241d4455860f405541c44480482d801160040d070101020b05040c040c0038064144004181c89030320503240750540c145004104000065002400f251802c44114100121500203000c1c04403540c5e03541802c070b0b004c515140010070b000b07491031003d0640060048003000014a040c0c005000d05c84007419201c43d0404824507540d041a05400c003428401414a401c0008240b100007045c54160007182c0b41e49010340f00d0101110b05449801c4901050340c6650500007114040b03500701d07510340980740390114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 243581429 1250 243580179 243580187
    0x1e05060601114209060408130317130906081005040f08040b03090105100f050f03070504110a02070e070c0b100308040b03060f01090302090106031d01091211010912 72
    0xa4400c1038080e00d1407100c00c42c007410041558800c0d81c501e281c0c0c1c000071640401e110511502e00d4883c0524040c0035034240143e14070342e50360004100921120f00000c84032003032000b658410300250307848000600c809589980030104c0d43c115100c0076200516118001c9a20070490190100390703020710000b04030305e104001074000a04005001610311020f440c048001041080000700b010300140024980d890810001407030071180000c1c26686000d4080b002400030322081c174440701c126039080b24185072400249002a0500c0078aa0003694000d19001e094882d089103400500040d10058003503c4949079280d0801c9005407003142c0040018110104000020320184e0307040d40c20860205080700703426103941d205841503200d504428148503000c02008451b20b003501001481e00d000b071074540212495580412001c1c0e406020308410705403245188880780b94088022220000180024411040c450500001a0501d654030b500000d1a01c07683e1104520305006400040f0362100800c8030030610310108507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 243582679 1250 243581429 243581447
    0xe030a0c110303030c1c09050c090c1210211e0320030301030b0c070b0c0a03021303060902040506120307080306010c05060f0601020d0f0e040e01090b01121e05060601 73
    0x403001007089610510325141000a07500c51035143e0b000d517940d000581200100722281c0c034071805540d4102080174000a60119035009021401d0340d0560060712400091120303400341e6140003020010980405c14032000106411003190701c0084074025801c4040342c41c3e203910740c0c5030034090b2200400100c52042044085070708000b95010703241401e14001020542c1c04810b01044000301d4580c0b001c0010b0090007000309843d40c014443c002624a0700e412030303403600801c610091608518200100d40b507440d090083d0110380803c61120f078942d0700c2e0368403860b00c00c00400019070203a00551070b00f00000c1c2c050524403910407140c1501c0c0300540c1000002d6441140b55840142058100900e110314030001030010081140508086c0314820200d00d803003800240750a255003880700400c60304800d204c2250790440e0784150008026240807542e0600c5100700760241119040003020f12030344034000a4a0080700c0c6052a0b40d52080b0f86410b10100002140c80100c01c2060010700395801400c041441580548244 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 243583929 1250 243582679 243582683
    0x120c0302100f1b1707030503040213180201080a1e06030b0601020d12020a03090212150f060109050d1412041806050627190603110406081603091b15030e030a0c 70
    0x1000f0102406280304d016042120b080b008202d020041c0011032a181d5500340c80e0b02c0803014204004098181100d80a041800c0c01030b06200c20707040814082c03481d9400ca200081c00c0b0451010021240b00f00c03910043c40ca920090341e110345420081280c1d0340c80443c4070041144141d0383e01d0040014800400029848502140e05040e41d500003840142c84220024070b900309aa005001802d11880c0ac0c40ea0405005081c00c554000d08400c20080e6a0070005205c1030760026030305d22050326801d01c0c0c0781d00885036441d180d5207240704550054103030140c030100500584404400108a54103a01d401d0015607002d030007241d60102081c0201c401c942c5c4921500e216001451218800d41000c020200d886038401019081c00102039600c18441c2541502031690151030b82108503240c00c0c541000104403540181800700c4850708000c409480c10310075040071444d10b40056101ca00059543e5200d0540740c0e00d449056400e580c426036100150340030b881070012030244032002d54502400d0000848000e1882581 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 243585179 1250 243583929 243583943
    0x10b0306010b030402011115100503211b0709140103051603020108010b0306042904060608091005180105070905011b030f0e190308030a1107080d0b0406120c0302100f1b 74
    0x2d910123500751100f032180201440c1c41c00c00a100c0c10701041c1801c0c44200c00820410011102c1c6200740d80c424101210280603041907000400c20030f090b0051b05000d40780d80180e00309802c0c840d1040f4207804110341c00c3c0c1245c0c4258100d0720301e20b02c401003024140390b071440081e0101c0c15a5004003c1c00d07044c0c4005603480fa01c01040084c2100391420501c04078840203001c0255580c050b09042c100b8202441003401500741424004040e00d001c10541d6903d00c1205031a1101c01d071110046006103010b10745000110304d41c20000e028601e40280d0003448000c40340306081c0054103c2d40d4001002401c07854105000d60140d54078a00700a0303401c025100800d00795130440c0c12507004078100210b103024002e0316010710b1141c1e040d56581d081000369a400e90f25420080e011102080081d0400a032800317040351000c2007a80b001190701d50140001030010070050f4401040000555100c6040190b000b81280c152803084900801d0b040d483c120880d84e90906081020100c0c441000c03095413659001c02d4032280e01d1080f00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 243586429 1250 243585179 243585193
    0x308060d1e1520070f020d08070510020309030a23040303020c090601050a020d2318041410051306090e0a17031902090a0503070605070302010b0306010b0304020111 72
    0xe10552021215070301c1c9101c04040c41c420341c081060420925100b0801c1c00d000740b1a0200e403d512460701c4991000301001c12a00040001c108004074080072840358000345a09480112030600036040d6000920844041c0115020803003000e20034401e40c5d008000c0c0318011400e085589405407a0500e1004507070403095904440801c1200c00300e80280082c1d8400d80c06084403c01840601c21010b10107441981031107018420023581300d90002d00c000d25101d11f480d00341500300110440d07400f04031590040354005080081c450343c0e0341180300c5846203440c1059404025294100c14001903600066403103a240355a40b00d010422454140b402c00070075154141d00054195032106440111380c0da09111490980001c480841480544094404007080c025980c0d4034600c1d054140c202c0d408090700b04e41c42c00c41d6003c40d0101039500d4103010000685805411611001d0b110314016040d6005030608030019820000780318070606020544504848200c6c14860654440c5d60040d964542d82890400d80e03441494 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 243587679 1250 243586429 243586433
    0x20703080f0d0924060b0901081b0706140f070305063106090b0a0b03010f09020f073306030c05040b01051e030402121c050d0b15090f031203040308060d 67
    0x40d00d00e48001c000405025104d144111100b05403925540040500c04040c41700a4699811481d000d921442d0b0505c40d002c0c0c0d4203ca41116114021141d000c0c110501d0300403026a03004844800703a002d84100c4c0903040080d62100003c80c1901d908075181e40c3c001d80017034032400300d036086030860203c078a10000c0302c0c20005c2c942c0e12030801221559030010000d140c030380da500900c82c14101a150050651102c5507031131581060b11100d545d0348107204828015a00082680c4c092155205440c07600c0d5102c6601c8903007503110075103806040009198007511400c60b051000103400035204e080122a0f01848103d00245000100002400e20255890510508220a001c107070380300d00b017120500c0b5101072202c1c1c07603042900522004051018a4007155408402c0484079880c04120002c0d002401c2d00c6d1640e40c03540c039a66600042c00c400410290001d44868407407000e080740c1c0d4081c26000e40d082c1c2d001d0781010a4a010180c0e0366614085083c40d81c14100042004203120302011035010f40d015004080112040d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243588929 1250 243587679 243587693
    0x402031b0c070317040510020a0b310506090d11070506090103021306030e10060501320d0501081501050a090e030906030a05090d021b1e04110703020607020703080f0d09 74
    0x11104c901030b450002414422858540c82401022665200410b031111440d62000004032001e071008040351030b440c100d5800704002c16403031500b0310014100e0701482c20a6241c03503a038480d000e030340310b1401d400b9100810709075901c50401da0641c010824024803910345000140480303036000c4005c0a04264003002600c2c5102c51030385180c00108100ea80c00518045407002240c140140c4110030803946040190402079680d01c042e48840c08500341d04030f1200c043c41501560034100c4c01c640300ea0034032400460250040344181d03202d6030480c1c66074802c0d00c10048480125450a10090040c0f6a10040d090800d00256503284d0040d9060400d0f0400c4929100e070282c00900300e6002180d21188060b250810846c8101060180d07a4909216000400d61340304602c0200c0b00c0e00052041680c090020340410181c030b10040001c03200040f0b000fa104200103001c0311080d0b140356000d084190058840d020105004510000315a801c40b600903000320f05090000c480040c541c6d102c000031429170307070b2101c50b01004a000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 243590179 1250 243588929 243588953
    0x806030a02060f0a180b0a120b030d020708060f0903042108040e19050702030a030902061603020a0524010b090118090509010b0603060603070804210512060402031b0c0703 75
    0x700000301a124030350501c005000241c2e40c41710401c4a01c110504100100f0f000003543d10300105402e1490500c84e40c43e8000e40202450b042c4207905100b0001020703c0c481d008948001910140f20a466403960381c3d481c094880b02c0c2c2518500c680d035200708000c12001218010910580007506011686240f503516880c0444d00640c00445908403448248942806050310802d00d070450072800b03015525008038081d4603401040641c0d0185600e540c1c6030800c41d0349507812a800e5403861360f6140408601e5046c000e66510009008a42610407600c001e0701d00359100e14002c1c040f03499160316031180c2e0308080d030404141c0c02020b84503051001c0c121203481101d4502d00301d40d0192090750b90004540c5845d581c50f900f982e81c0c1100d10b030f014417000c00500020381c45800031039610070154180a00152103500c2d10030b04008550f40740c0e00c00b100303404441c111000e61160050031583c0100703d2034041522010100401c070b1200707681c4003030a83c01d51440c00d0002166a0060b00800c080d8006880896a50b074540043c0182 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 243591429 1250 243590179 243590197
    0x1200601030506060108151e04060305030309030a0e0111060106120f020c0d1404060e150c060103050303060a14100c061d151b0412020301110a02010e070e090307030806030a0206 78
    0xc60000c000c4c0550748008100c2d804044a46081031409000c8040360455140e08640641901006d4100120340c035150040d40017568000103d0790b0b0b902d4604c01c0d01d0703202e4020035014400144042c0407150198400c000c2d0803c1c607801280030340400d03480c10b00f0a50f48110f1490900c528035480e12001410103556102504070540000701030300107122240d1004120345a0785a2503414450140014044180e01002c1c0c81e1080c501942c904585428580103001180124031182a90b40f040380e00100030024044085e50046405450f072411403900c4001c102035840d03400c0602c5410050082c04d146105109450340c01c416805030800241007a11140c445126000303091100b5456030003215a1a13180001420b402c0e8008042070700c0c07442c94550309412040a00c518821b5030032140b94079078410155a001c0d0b0104180c0803115040f81d0b07617200031540180c0a0030407060000341d5802120000503035a007400c2c410901c600b0840d0091444c0c04403035502650000750180000e50584500821400142c07140c8008003a200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 243592679 1250 243591429 243591433
    0xe0105130c0e1003150e0106200c10090612020307050d051519050102060117070303120f020a08061206150d030908030c0313060903030c020409020f04090b01090c0507020609012006010305 82
    0x2500e2001500740401741c0da84412420a000001005205d90003284c0b00300760028051450010028007140c140b4215282d099143d01c045d14001c41140d030b6800c0080c007000c640c019100d0886551402450030201d00040710b0100116004000c031040e1401103901683d4070038040200541402c0d000004110340c14058030807040032181d80d134010720566804012160050100020a0f000d01e000019001e480c2c0400788401018814004500d07004081ca50300710b1308421745252811500c480f8210001000400142c0d11180682201d4610540c00000460098402c009615090344811150420300c00a04c2900800350104075268002003010f000a01c001d1503d031140301c0086848806407180b4500e0441ca81d440304040c8401500100002900401020340440e012500001e039610035002195400020b0400c80741c0c0700e49030007024070810240c01e8003c3e050760200907040010045007001500c2d01d00c580200654000c4080c0142004c56205503100d0b10f1071040342c6076002d0000075544140345400003c1e08100c07403035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 243593929 1250 243592679 243592691
    0x11505070611180a150f050d020d0614030c0a0b13080604060510050d0b011505041223120f090a080d03020307171603050a0e0d0206100e0105130c0e1003 67
    0xb0651500c280d1110003103c01612043c17070a51110840c3c028445038905000e103140a030f04c07100e8002d50a490700344806031010b540e035003140b0070141c0042815000e180170410713103503081c107619041c0056008a10303a409006201c0050500f4510046600890f58180d04421459408601c249081c000280a148292008502c1d030402d40c007a0f010444050300101c3c0503000400e00c1da00410340b042c1072541140c80e40d01114030344c1700074090100e40c14415a000340018050401e18030040088002e8000b40c0d411000c0700004c4c035940000c0da00ca898030f001480c507035811030342400f03504010340d0544000c00710387c0c0c40201418107041e92440118140310304e100e001401320754040100070300150000c5c401e809240c0052042c01c81894901b000040360015078501a040691301c500041d035241c595403105c030041103108110b07041102e45d007000031368030f0b4400c8a10f80ba0364800443c0000d07007286021000381c1650f03401005c0c1c40712580a0281c2d400106030004d141e008000740c1300c4111443e52500e2001c503030807610f955408130b10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 243595179 1250 243593929 243593947
    0xf03030e090109150e04060b0a0b09010206010609050303092205040f061a01050f03150604180f02090607020d030302041e090507080f0a09030203072102060a060e011505070611 77
    0x1807150140d104442c40c50802c0004d0302c1e0200c10007150403e4403601d0000c10030a88550400300004e029240b02540c01c0050302c5030203d5144204409021802026070803584c00380c0c0c071b5000403155000103110301e030b403d0ba106104810240c0f502c800305020603034081030b01030403883d181c0c07800c2c100792041680c1c1030b1400a50401420248041c0d0b019103012000c086401c002203684060000308184103002e19501d0f1b0344030100c0030805084903840814041003004119a032a651a01408003640c441a826410007900e0001842100030700b80c000e54140400081585051400030f400388500031210080440405070300f044040b40031506002030000039001c0358682c40c0b4007810420040100c8002414403020320001d1001c1103001c0c102e00c02d0f99a800b6204210100352075807107142c01c0c1c0c0365004d801d40080084413010030710380b401c40038070800e02e10030810340d42180c0d0142c403002255021690310740a851013420401005010030802c200707188030008128038210307281903c9078a80724121403605811310b101e5036000590301c04c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 243596429 1250 243595179 243595189
    0x60e10121404050f01020f040905090a020409060209190305030702060c1510050906041806150b0c0a051903050f09060706091407090b1c0305090d050c15030c0307080408040f03030e 79
    0x811131034640001c41c078003090071007810a603020300d00c04d070b10711aa2501c0004402105c1485100b007410341c0503000780030f81d24103032510300044e4100c0420140030301c155006142c141c3c0c48681010081780d03008400f442c9466020340078080d140e80400407140d1035200b500c0c002e41400184c516218030540c58205c040145900704800c0168201020700141c1c4518284541c44c3c0283c0d46903c403010b4202d9100a000585a5501d814035032454080d600046008a0124080c003111300c0110b10b01c003040b44070b50103a44030031180c441e0b1034a80420340b00e80980091780c24050080d0b000507500007803032502c000510281c2000c00781da48030425541594002c903421380240074a50041c5000304812005808413400521403c89481e002c540c500940c280300000c0744815801e0b5100303040c0694100c0f550503001410011204401d420215602d004910529000c0e103191420030305402458415030303010f2080101002c1c91901c034900111508480504141e4146e1420800000c040ca005020380340154072a07100c041c221198042002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 243597679 1250 243596429 243596443
    0xe0f0f1f0506010816110307080408010606090803070308041a09012009030a0f060b090f070f0302070f030e0a0f141201060303021c111005090f07060e1012140405 71
    0xd52a41c20300c41441016a00300c1d40310395108849103403680160b03001c0c0b00b08851101c1215130311503c80c00b0000300340040c090100020015688410024032959949000480b2030300c10303030700c594004c40e003040c810400064030811030300e90042e001d000340780001d940d0a8891004000b0503528010315a5403400d161146943e03507114115042c2062982e28104084400441d40f1084040c034014032104124040b40d0030480554020841c0c4040540b1803d154070307200c503113a0000d80b0103071101004141000351040001e0b22034000c5034840f41e400b10303100000c11340076a010356200d170811190a510500c03204002ca041e50f11140740304000c0c100380001c40aa00020828001304100b0144030001507410800c0c28004290001141d030b034a0b108406a0420a0703085001c22180ca072804503000f8103034000e1114480d2105070b039410040c09400c00708195001d040800e44030703554890192180c07601052421b5000e0f0464504000d02001480d1141061103040140b038941c4403c54008499450000011406002c10b00c00e082100ea = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 243598929 1250 243597679 243597733
    0x14280b0a0b0102060712110d021309060b04121e060b0f010206010b04330801050f040911041a0612070e060a1710030f0f0b060a050607060e0f0f 63
    0x40107035080d1040000d48451004200c2c00511070b41381c0001072025040d41c801c00c000344104840f180c07554144420030000e5481402d0070150141c402c0030202d815201e130300c50a002c032030b0b41c04803007441d2600d44001680c43d02c04055095405c00d59568410074400380000700c00709050312610b0b0000391005140b0030403d460101070020741c110b52100303005002d8000480211800e446054503600707260b414402a44c210710b604015040003465010311f152205941018006050300c80480784542c490b078001d41031004650850001a20035821540c0b61451400c140d804412960000c01c00c22102c080d0034008502d040d48101640400c5c03040c00b800300301d60315522140d0003004c1041210514a45036101d136005041d2454040318000765000c0c0c07404181c003164100706140003550301c80100b100f07540301400c0c5552004800789080e502c260454000400e90301d003211141d000d4480040c40703241059100d48511004140004541015120348022002c03005010044031249010420007072030700391050b400c2e5000000b0358481c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 243600179 1250 243598929 243598931
    0x90c0305040b0c0a020a06020912070305010c090b0a0e010305040804091103040b070f0c1704050901030b15010306050319020a1a030702010b030c100e0312030106030c18060c14280b0a 80
    0x134554015501155000b03440390080405078480c100e060004443c510414980f030118440c030500001004019000180465031a03140e42400694485481c0d002d8402c2440f9407000895004c0ca00d06198025400300c3d8000b8003403201a4101074445900a0840c1c000c0404000425008010407041000c0751041c0ca0b80517025280112440d1000b0502178085040c0403802408020080d5100c0920814042601e0007410010004d491550f56800e2100280200790b50400815070030720302070741695019000703210858102400074583c2815188465030606040c2504a9003e03500b01400500a0408660041621185015107560b0304110310040c0c2141d544544580c000c1d04000d54507600c55481d24404400114141808410120020000303414010003c1e1550b815010100000c21040e6040e0f011f8442c07030355103403a41e102c00503144894072800010b900c98440068030601000b00010b211a45642c51500f41c140bc0310105000010300110421004041090196030003000d03c0501c20081c0c5010b07080144460 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 243601429 1250 243600179 243600187
    0x7050312130b042709020429090f01061d060a210612060c0507050d360902160507080c0a05040212180c041407080714041509090c0305040b0c 62
    0x3c0e00460b41140403030031010850b05813080350a003113060742140845070350081c0104030412800408001c00b05900c04c00c000c1c1c4030403c1c5403080c0c0078103161294038003420306503031151400ea2a10104a52082d54400704000c119048804510340c0d865010262402c0b40d100d03221007003003510b0100c01c080e500b05440d41040701c2a081520030060690707082c100c81c0301c56801200c04545100b103100d082c0c91600c41e4000043c40b074403c00841d1041030394040312003819a10741558094010002d40c03a550020b00c0210424007440c85036903000c02c060030b206c3d0b0040000c00d04e00500040482040e44551741804903691103045c240e04250380b410020f103440709185000c0c10003100c0450070702d107281d064103410140c010f0440501131b003030341d03001c0640705002c1004030f126000c018414000014020030342c0b401c1d0241902c070b03031010480e000702054030f40e8040d03072404410640d114001400c007450203100d844a60800c00c0d00300240021102d0225901e02280240a01d0342c07907075200401c0034101864911140c540041140320159410700c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 243602679 1250 243601429 243601439
    0x30f060d0c05010503070c08070c03060b06180405130c0b0c010c0c12080a060f08010e010509060f0f0712020c06041202030405101d09090d02010b01020a0f060e07050312130b04 77
    0xd050390082e01d10a203481a01c036500c41200b5103100c11a401e000d07011881c04980d220820003000900c5040c0ca116913410300030340c0b6401d801d0005da80504071508440c44186690074102e820300c1c1d442107038480e0745111840a042100e071210046410390b034000120140b40000c50090741482401801d42c0040c070780c80c002240c2d030401d0312000d031540f42c2c41400c04200001d4501090640180d5009600032384805001c0511295580344842d00134245940030800c40e5080c02e001410700e01d00030074200d210300300392035099202d5900d04076a05001a4014140e0052204102641c000000684013402502c840c8100506c06c900700b07801c0c4414110354490114003150310400080c4196100d10345800554106401d041e04005020318010720501c9035050040d8001c2c0c0e8520412401d42000a0114400f0190b07400070000c100d40f080c0126150135003e100074154a01700f2031700f51b00180701a442070301041015810384109544a40019050021604030041c426101040d21280e41c0203d680e100c0c010000c0065452030310340f501d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 243603929 1250 243602679 243602693
    0x12020d0e060703120f0608030c070b03010f0b031906031a090a080a0c0201050705010c26010b07020f0607120509031b100e0616060204030c15080a0b040e0303010b030f060d 75
    0x520b0000d041000d03000c0f001e1001d100c80c1c4c2000d066600501c1e024001d950312001400d0b601c1d04420b0000600c0d105090700001d01e01100350482e030503968818000006503003083d02940c02a4005000051711070f003a0000c088981c907103403040c0c2014510030000c90900c9a090448a2019000944849105d410030007500d40000c1c0b4003400c0318028036050505420b04a483d0006942d24003070b0742c402500c07035402d1101103401c45910451842c840d5151a8040d2030004003165025007400007400303460740b40b0008001004c050f1400c81d8210016070340003800781d03288c034041e50349090313054041c01c0b400d101040300801da0515a2509100d40300600c1c401001090808420000007209c4441d0344450906012681b00602c48a8841c8000c5640b01c0103845030587e081c041900c1c1c018001e44c0688019141003052000c0403a800c0e650808050040110b41d172641c0c0c0d00e45a81c025500200200021aa44190741d03140640807060140041c0d0700030480e0508942c0c0303d181444039100907541c003c00d0f40d4410b44904145800282e01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 243605179 1250 243603929 243603937
    0xb010e01021e0a0506041b1a03040609170a02100b1e090a0207120806040c08090c1207120807050c0102010c0207030807080f03011413022b0609050412020d0e06 70
    0x40e0845084005201201450410f44030000160042c0240e074100414030a00c1e9500300111005082e00f6014642c0d81d00043c14080016101d100103818100041070105003541c00901c186030060f44661384014070103800e00060741c0001c0b2004051303003101800c11780142c403038440c0d00d564039000e6400030140d00440b104521b005490704c81e000d22414001c0045180144940d05940d1000d60240c90100048101d420240c801002200c01502c1203003052024503425101d80d401601803188900100804240c030400c010b04102911510040c0307103d15540041c000c108403540003c440d00a034500350b512940c60504500f0421134032000c0c0e055a0415056010351540012a1403c6a42140701c0588411032441c000d41c0c548034442000c03080700340220001c1105c03c40ea01c03102c225070b10201c81c000100306c0c20b0440c850607401621440481004502c0054218141c840001c00d002403c45400081050316000c5120407a80c080e6020b075090064034114401294042204004024041c00d2a0701c0b024000f000007040340c45 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 243606429 1250 243605179 243605203
    0x106140a030311030c060906090c0d0b060904020f040614040612050d050d09230609060709050609010909021803060c040302030303040f061b3209121006030f060b010e0102 75
    0x40708505805824800c1c010b17581c0303900428090340e485041140c052036030764400b82e55040f41406420050080d916086080d640001da1055610f200c540d0394008101e801c11009100b40c2e082120820b01800503501c92142d03002901000840804010000c01440110f55041d080310011070124100240401c100013810500d081079850042d40d250142403a040c05025033030030040c030010390707109250a00107840c009091070a49480c2100e6041d92041031656541034250744100104007013103018806414501c00500c0b0155040c100044000ea8074030302281268407615a4000300724030381507100558a0706002c50b0b0b030007000c0c050b102420103056400103600ea210140c070040201c080840e1520800020ba00b1284650105403030010748078844c450007401c0c15610741000131060041d41c0c041068840003403c4407040301400d05046003490700c00802d10401c00b510b204008041d106503245103543d200c1c00c0c001e02001c0d500c188407950144103249400700640b003080081505018540500880c141da0004035030603055 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 243607679 1250 243606429 243606437
    0x21f02070b131406010b040e06030a110907111c0905030a0b07051c050703050f0108010c0801030212010e0a080901020c0105040b16030e190e16090b22080f0106140a0303 74
    0x2103051611405030758065900d820b030b0f13000f80800040d450300c905c0e014004980c2c2103110319500340d54120815031600c0b000b40c0000d008907a070600c0c2d6070590801c500d4103641b2140e5810514460341c2d0904041d8074140c44600d0a0050120080380e01c01501e0340514001e005000c20750052044102580c0c0d4622041c10007018041040000719020101c4501070789500c5a200c030000c41000360b8101520010701a100444038244158000400000c141105204409004565554040140e4259801c10460a0595002c4121076485030140e0b20091414044181440d02c201010b6a0f40c12250b0700180c02c111800307850701d050110a100c1085a100140119500d4000d200540c04107030942d03190954142d0080801c60740c00802ca465182000c003c3c040d45003003601d5020000d6980c45c1d941502c0c2038800b016500c007000000302091010040c6480600103040809850701c920811315210441084040c00640d0080550780c0c003001d10036120101c00e104400c00307455101100b0b080f074120880803d08807600307403000401700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 243608929 1250 243607679 243607711
    0xe030d05090319020307030e090114040203090c0301110d06091802011b0b130b01050603010501020d08090a0f062315010e0f040e01020415050909010e0402061603021f02070b 76
    0x880000d000b15075070080f0000488060390750b0500001e41d2500301c284110045070701840038071220703d409454241212003445021950218410500c80690409040100c1c1442420740e0342c00160340a014111844103489c0117251500e00d0403a028094946651080510394581000c40180707100c10b0500650381034081c00d244450b40d1541144214000142c00302521181c1071805004010400081c065500c07401001261196601c1c0c9003001080d02c000e00c6440e01580c848010030b1074041c01000003e0340416180b003542c420340c0c0c81e91194201076040f04001c895081d40d0342c28002004e0183c1e194803403605101c00103148645040c00c5450784228488d03002c035041c8403074048609103940d50180d0460002c4005007051000c808140001c5010790014082c541980d8143c28441600620070000d56007030602c02000c525880c1d182001443d1003080181050ba000003040000a60003818013032040a801e10a50040075500d21204e800403d9503207940d100040c1600411085022440080d141034110000c25104215 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 243610179 1250 243608929 243608941
    0x80f070f020c0d022707122f040b030108010518160314190c090c050703051804021207090602011a090411010219060207020a0501080105090a0b01120213080706030e030d05 75
    0x8418220680030110500045e00c1c504d074545d8089906011310ba580d02c0c2c0501d1004c07804e84030f0703050b240078482031040c100b0070740921301e4542050051043c1610b960800181303040d864404601241d4000d0b086107190ba03445409024078101079415408804403c03034003914000381034044105503a030705c078400600f420b2092010b00d60207000501000941601031019058071310035500c1c000c0c15444040c070a400b41245025140d843c074a0140e011100c1c0300b40e00d82d0b5a54a0440704908410402141d031100300d130829800c0c449034030700c500f00b0300b500da0141100743c0315a510249020002420340702c9072401c911880b000400c840a80e611601966900300d80d000900e03211403170311540104c1c604040758408940c27030041181d080b401e110003940202056070081d1044900f264403200191400c20003031040681090b074042c00107907512041c0e0b104804100c01450180c042e103107014010416078100c403c440c107203050307680c00820901d0307410030076a8000d0a29060034404030300c0912021303403a40100d242c3c49490a89070400109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 243611429 1250 243610179 243610189
    0x114061204031b0b0906090115170316081903060501050703050d0b0303041206050105030604020d03030e0a022d030a0201050301050907021c0e010e011106280606080f070f020c0d02 79
    0x10200c0c0c951000c5504000721424845404c000650301080c1e14090785e40032030218030040c020680710740360b100903680aa03032070a0203084d0100b03000026403006000900c07902100110440f5200100f07802482003a48440e06e9507080918410003510780c0e400d040c60075604202c4e507604403058641064041c1025515010300f40c0d481005402d8808205a15000c0090b01099190031a20801a4580141c90070003082e030700c0350145941d4050503203000c0d60260401c140180082e10a40140341c040051078156408a0185d80c082856100d900c91440380307620350100030300c40d0412050f8028004c6802240244101d001070740010340300c0d10041c05014041c6511100003422540200304540706032580b00030201c801e280980b00180034040c2d22008600081011251442e903610400c8415090a0704901800f041e4888004a4104010040c0e1f017240085100c0000c169502040c42034400030066a21103100a1400310032410b0503034001040705003400700800c0301c84442503000a503405104030586e8119110501400010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 243612679 1250 243611429 243611447
    0xa05190f0602030a120915020f0c0a0312140609040611040305060c070c15140a0225030b0c030c0409050612030a27080c040b01030e0604050c09011406120403 69
    0x202a59004000101d80d030b03000008041c40c0800781d41d0741c411080125051420780311109000b0300400c0d80100f5482450620358001d11200c456521082d2806a070b0324041810a10a9003095000c503000768030075003d842a07401070b4800d15503450410026441d101700056210200500054401983c540306598000300d01c00440f40515000011100546007052440b56a980501000c4a410301131020000d002901498000c807160000c0e2a032105a0000390203503601c640211131001c0440c0310380b40820005160384080322056004a4241103540f0382541000c820b0140050011190b0b980201f0401c44809a85002e0742d0540b250303203102081544941c4005410103100d0034190346035000000b001143c65800c40c034007000310034400000010000a100b05a11120894480c04c3d103143c10000710300d82c00e440c0543c040f810740e0405050014074060008115803030070108480445040c0d0203121040c400d441e000704014010050190265205140320f03003c5105030203410907440300c5203210784c003103410140940045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 243613929 1250 243612679 243612689
    0x15180612120e03100b04110f0a110705100201090b090a080406031808030c0a1e090e04020307150810090c1209060f0c05041a09010806060714071814060a0519 69
    0x8408224949081303c00811416040c144035900d03080003460b450180105454407400740b88069824401e00890582e03000070f460741500d0044c0214800400d09948400300041421226030000404601c28a40842da95202401012032544040d4840f030029440004030707404e4918902c3d001c6031100d0030403810b08840900c01e50080020b0340110801084811030005449805115903070210052011025501c0c091186a40403000601082c41030040c88400e101d0281c01a10107002c4400780c80d82c2e281114048115028000001400c160034469900701480090015045003034003007200085545020346000074408143e00c100da26030b041d401c02d2081c0c69210b0500304400420600c141c1d0b0380d040300103020340d00034050741709541c3c0d0050301403c01c0d00c04c03901962811003040e110601c0c2506d86104100e003682141c8000c561100340c2c001048425030040c000312004020400210008003000000c50050707407000e081c3c0e1494820190308108480d81c80009403812501c0940d1111a003201a5031990003003070a5803c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 243615179 1250 243613929 243613933
    0xf03020d060f020f0a0f0e01080a020705070e0a0603031e020703030e010c0c140a06030e0705060304140d080115210b0102010f0222050a0b0909070306050415180612120e03 75
    0x44c00d07450349040144440c1501d070780c412404000e26141943d079800100102c9002402c0ca900141801c4c525500030410140680119404680d4484185805900840782e659141740c07500e20802c00c240c0c000d84011031200010309040300703c280c030355402992411284009002c01c1b22a00d04000980d02606152540da0303000341141e2641515500740001030392401c0c01940c01138140c84030000302a0701c01e120390590320b020b600c0a030a085103040200909074101030003d07a50018001c40d0781c441c02d4001c2000c2c1340c0d442855201c40ca2158074042c3c7c52a2940c000041c00424004486c1e600c009030412403040307026800d040200042c98400d07110040b80102192448a85d80910010300c4144402c813500c0c014001a00c0400400e03070058a501c24002070402c58031800c0e10400041c8460702480c60300c0c01c40c0c00d5010b806403600080850f030700c00c000380503164094069501100203c038103020000c698122038540c0301c1941e105200191814503504501010741f1005007a8545000015800138800e4103038005041005003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 243616429 1250 243615179 243615187
    0x1d060304060516020309010c082a0a030e0609060a030e030409060605030109050c070209040b07030207020405040f03080a1a010c020402040308120108191509051f0c17010f03020d060f02 81
    0x1d400740041809440c41012030b2001985410281c0c400002c0340d01c80c100607903c510510000740c3c1d800d4a107400140a000c00e0101c0450740030540910380c0c1080c6030041e920301c0180307503003491400d0290074004450301490142c0c000308000c2034241c480030110390505400b8130700003413048160010170303003035008030b8200100080c2040b100044880d4450041c50688040e14410842c640702c0450b040858807407040c0083d0020b08500004c0d0200c0c0c1c0d0694019409005414054540103017079000900b02d82d001c55048500c1e40b02e801c13080c400e01d17a1009120b9400b442110041110740d4410340072120040715600c1250410070200c01d00c500710744842d0140d0300299484a03d0a454220030350320708600100034000e050052088940c2c0345900200050b03104460741c4c00024010380382d8000000d0318050001c800c820748840c80b030040c40c00f030b01032a581c0c005407400080700400204004000e81c003c180400c40690045180050700c018001c1c0b80c006801c3d5421290304480740d4608070441c1c6064800780940000e407040740c0c0c0c8046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 243617679 1250 243616429 243616433
    0xf0c07140703060e070914010e1b0403050a0303050108010c09031e0204091202010c021c0503180a05250f1802030402030a050d050403060c0809060109020f0c01150504060e161d060304 80
    0x10301801900e0040401f807105911222650160030b0f801d1155503a000b4401012a5007081c108100d00f03244110080c0943c035081d1292242441c1000e001c0c8100d000a0395030004101c004000e2082201d85070b101d280c500d807080d103035844011900045046101d41900d910451000315616588419502e542c050400510100c5800020b4028141610070301c015000f4050310f8284941c1c05000760414148030f8981e0350a40d283c011007043e0040350640e041090f48240031b801c00204900300110b001140f600d0343d4181440d55010540e0714845001d0707028407110b130022030050005a2030074034280260910341c0e50040e12a911400045d141c404d036a00040e1050058075880307540554418020016a07025900510166021400071a071541c0e0440d440149500078500600020349a50020070300d40c00740c00c02003818512800d83c082d08680c1c07049015401c802001c0c0c420052410203009000003000c01400744181031400901000c503c0440c51880c10400c68034042c40190980340c064445818500030702419100c1c94a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 243618929 1250 243617679 243617683
    0xf0310050412030b01051303030f0509062d09030604200a0e040b07050909070807140f07050c0a0303020a060e12030412030605120a081810170f0c07140703060e 70
    0x500c00e420000713060103107050555000d40102c030110b000010085041c2c0c1d2660710121a4020100090301c200203080002008507a150000340c10b00342000c600c1980300034140b4414100c1c40700c0000030340c0c1c00c03100f0500141e00c0c9a500882c500c0d901030b4006045070b4409460381d007100c1a040e9641c6040b80c2c44a21103002050184480281e144500d00c5070500d84001d84403404e007076038103000301d4284c150710041200002d802188140e0300560804201d00b0003500200c80c500140889802c11100c3e48040c803c04640b000030300108124101a400068584403d0740303040d030310025100c441c2d01101402c45e035122030114400400801c421507a05036800c3e145502c038103040c5006482402d150390a0340c002810a030000c100d610305090000405100e4400400259100da03035a44069044280000341035003502901e10000e4440c01520420203101d030b91003100420700c15081401715071000d0f181281c2d46580c1d078200300b0714030110000c803070b0144c1d0070500c141403c44046038220320b4454250401486241001702507000701c600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 243620179 1250 243618929 243618953
    0x604030c1508220312110406022409060c031008060a0504021905030706140c0a08040f152c040f02090f01030b130e1c08010f0602010203060f0f03100504 67
    0x8a9070740d048003030f1038080c0a4030201e1142210040d2074411a40e400000070f004840382c4c0d0f0700f00150b110109510300c8500b0303245201c0e04036510030070260300070200c03d00c2c03080b031803c040e800c9120306840380162a05003881c0095803a000103205180792a400030120327068002080b00400104000c0342210010b00d41081d00e01c000c0c0405075000c0380204180b5012111071100d10060300c064174005001881d500380b0340340342112100b034041030b0040b0b514410040c0240131441070221a180300e00580c50175903605e1802c0700a0445150580c49008541c0201005401c1c40c0d60041c02d82c4006034001000d5801c408494840e020540d4450f0f8665030320034580310340342d5009001038001c0c1803401d0080390a0fa0105074100015002d13507004410b11580702c0d00880c1c8110002842d85e0204040390080c0044403c0c440c111038990140c0d00780180f0340404501410b00400c04c5004000c880c1d80030707150920095007982032400100380200f04000303900d40703d0101c6c00a000c0c95900c08028603604d041c0c42010502c0b8a0034181003d41804013 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 243621429 1250 243620179 243620219
    0x609051b03030702090703050703020403080f0318060f07082503050405100b0a03060906021e070c15021e10060603060f060206061f0c0b0c12060a15030b0604030c 71
    0x440d011540080c1d10380801503aa1041d00500842c580d650380c080f040f401003c00508220a040c2d00f404003002064191014240c01d003d000415a9a800c0440c851302040e02c003401c03410745581c850810010308041c0c00c0700030307500400c8a0070420034039121520221300c11121200e81028072890041c810842e40d80c50340106004501a105984080d480312160800356044121015000a0840c0c410000205035900164906004940060802e0580b030403600503180c44650040e018500811a10280003100d09283c009000d440f200038603800260b00040d45074401d00e400c410000d0141024042021000e0200c5443c03080148000c003e1143c075010041c0043c4240d0184106d0003100c10700201d220f50000503282d005607402040d40542070400c0d00b9100c5030b03a584000903000c100841c0303400380006095820303440c0900300740d101e919229442c0c84000c0c0754010b0010400c038410110084104130040d201e014000c60300445180c0400c000c48180c0100d4110b20565000034050080380c90005180507451109405042c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 243622679 1250 243621429 243621463
    0x12080f0c012309031e0c03070807060e0307020901120528031709120a020c21061605091011030409050405060709050619031401170c030303090d030e0a060905 69
    0x10210182c08408803000c940b4111968030400043c00d80d08105641400709a00b121152850035076400001800c40d048010101c580171004144101000300d1400f0710040c01d40c43e83c00075802c0000341e4001821111040c820ba44c7c140b842d80000c0014082d050007003a4016070000b5041c80c1c03140c0724000d16031004e400c11000b40d0000f24940b076501031043c855049070b4002c915010081540c840745080350140c1394003c6045c0000d6108140305680203485101603812800300d209400221181101ea07924101383e8000c00c4034440190312090402c0031a00304e0151280b400e008e440085c0d5034400717241300f42c03215070b1180c22401c040d110101d000104800f2a80003180f050f440f0380155909a02d03a004141d8100250b8003400d50303c003a0a00140348681c1240041d51001660b510300451320394591800a40d07030081c00c0c6c01220318138840c000b400009d90000c000c4524100c50030380c01180303180b0301410580c0d102da4040341d41100701078480d041748101490403c00da44103280c2120042044032001c2c60903a9403124a03401f900104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 243623929 1250 243622679 243622721
    0x161415090118020a050f060d0606021c0e03060f06030109080313031e0203043f1103070302010e090a0905030a0206010e0106140a210f0b0406050402090a12080f0c01 72
    0x9141d1014000b80c96010b000d55450341e05100400018101441c12580c0080c001c0c4001c2070700c06100d00449004113a981c000d4121801c5079010405441900d8240300d040c01400100d00b14940c500003056a070041c06403414aa07191240380c00203014042003800034045180100034068010728028000304058400d48420f090711a0b500000c1c80315072000309a030405a00103000c00c02900e400c0300c649828111041e450310074002c43c031500a01400e800d01c07282c41111080740c42c4950801a943c400010606812030040005c0362440d0700003400a050075800034001d40801000c42c060300e01682204002c69800001ea079180e1281d1800296500c009200d03050740d0040d490000101a8043c1500050b940f4000c6c0000386080070071301c0c0640d201c10100c201041c5010507890544070303100b11440344040f103104400010513030700320007000c000a0b1042600500d20a82c810003803440981d5880300d9001c120380c3c0b1035503000d5034140d450405520a008103c1c00c00c0a4200010b51014520350650002c40307581c0707030f4440e0304c602 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 243625179 1250 243623929 243623951
    0x50f220b0a1d03150403050a020109120f141318060308070f05120f0306060a020a21120e19050c04050c09100c0c170a21120c02031614150901 62
    0x1441d13800c84120014a8030580200780868841c0c0004d0203143da15000220301052655540095851201c081000090500000412840d40480745580a400d42141d80e400c10f41c142d03d81903200c5c2c070684102d904030700c01c03c08044070880c01500201d0013103070041103ca4035503c036800c20519150074400200e9590142c1e003482c0c03034400070303420035a50444810040e9074110758800d030510080380d000c0314071a030551081800c900005401200219960303144240c038042078400c0808054850101e00e4059000c40d420088209084000044c030100109600e02d0042c0d4011518244103040074015412241c101d4241030130072207004446001800d10711420380f103054401c20310707203c2114101c0302400018110b009a58080000e92010b00442000c0c3c00004161994400b00f90ba403078140410101340d1400008040d446a03100d1070b00304030102c040d283c148600b0310a0f2090303030308025140e10603d80c800031222501940031080c00302041070003410f51103030422150006481600740d80b803a40100c1750940783d50f08000413055 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 243626429 1250 243625179 243625183
    0x70302121821060408090f0405010b130603050910090312050702150708130209070207080604140706080702031c060302060d0b0301230c0304031107091506050f220b0a1d03 75
    0x42d0b4114070002412454a032641c0302c0800d588180c3c030b900c0d40703d00782400c50070250ba1944580c500030510b408200340c0d2400710028204e000e41d16944460181440d00013085a0b00c1404501442039940d240c20009490b11390303207815500d40340c4141001d40c00501c0c2808000302c580c2c000621554000324000000742c181d03912141100c2981c802c5074a901c400804480c030300014140800c150b0b42144460069511150700c99100c1880d0400132242aa101240c0d00c0b50074a1806090043d00060301e45803030640042d02c0d00c4940a035480c80b82030280810041c41056000e884156075200740040e43e4018256a074686110303003154050f00005040d2486946007a0000a000b40c03036030703111900d08070002c0d00d580803555648aa0300079030700010420307010310241800e613115900b010321240c405040300600000381402400c0341409480c030150400c40c1809410006000d01c1d2003aa019101f4808107030008d04500b0044070300c0025803682d95446100f10203c00303e0781c079000704d402c802e500c0b11452008070205044004041010303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 243627679 1250 243626429 243626479
    0x12050601020a060e0304051c0c0f050108070503090109230106080c01140309010b12031305060f0919080706030f1802010834050304030807081b0703021218 68
    0x250159220541680000d070464120480402c0b425090780d090569560100e0480c01d03030141c03400c0560941c21003150400120300d03444400703030150032032030540c0500f01400605003020151042003400401b00c00200c0402094100c00d5426a010303110b031964110030048008240001d46481d8055400e104000c00c0c5003a0002d91002c1c01c0d08142d4440070420700404e40e940103688080d060000c15521981c82013210b8a4144041c003c180031a80115a540b000120007103d00700b445e0001071080200b00020302c1003040c00700c04d5072080f400490341c0011540c150042d00800784420307440716206004101d0001569900742c1d10140c201e500c6c4050920403407880c035a08041d80814004004d0119050350023040c200c04442e8613500030100500c4410540c1e0500102e42e250b400c40c80107082001550001c05c00007016440011035411101030b04044589090a5094042c02d01c00480180a0450040741100a043c030030092249035811182c81280d41c0d40038000000208407030b41481030b025084650001408120303002e500c0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 243628929 1250 243627679 243627691
    0x30e011d031213210308130b01030212010209030114060102120310030b09253003030b03030d050f0f09060403020304180f0213060e031b0603180a050601061205 70
    0x50700319422540102c1e4280c1c0c012550f00c0d030510005040110381410140084401000b11010f50142071840749001000100300910325213086002c02038060000d071400301c80c9419654120f0b0914200c1440e220040d0090040c0c20600d41c0c1582001c907200101511880c0740740c040c01d0281c0c20340d080000e0224150010344002d6034003032104928002c080000c07943c50004940c020000300192404116070f80100c102c01116040382201c02d64201c001003001c024403000070036100d100c1c101480b8503035030807410301c0000c0020a14060305050301e41d06801e0f0583d80510440341c03021148070041059040c207045461100204846a82c407040c0c6400101c0c001120014400340302d16410790007546020700300003001d1890580380040d501030075110100340c8440082800540f1080b0511b6076981441c0b4a0090018a01c5c51a0141c190090b00000104103054004000014200009803910340e504d860f8000714504c2c4075201c080381c1d0280e007c3d522111040010204000d412514556111b110340c4035204c2c5400111242a280 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 243630179 1250 243628929 243628933
    0x907110c030a020f0d0519060c030c03181b0f0902030103050706050c031e0409091208060105090325030b071e02190b070201091e020a09020a0203030103031101090609030e011d03 78
    0x900c030b14084040610340c034480d00540350190300790941201f1350180d07600222425030310740b01c03001200c2d82d0502c515610721096190500c040c9100c4c00031320000b601034402c007801c846081541d2580396810200780600501d012034001100540e00c90807030000350001c2c081141c0c80e0140c0e50001510a00c0303107040c1c6a059615001561400c15141e03080e010350389100740c8006000c6001d000004100c0d4461151008042c064460130504003038404c001071451500030041e5040c01f609110380c03140303600d0000d025212041c0e400444402c401c110000343c030980c0c05030b6100420b44c0e24203204120207d90700074042c80310051000c10204003000a08800d0741c0340c1902d10360b0441c0c100302c640c0742403000ca601104c00d90b41000c0140000181a0764980320b04501d4011a29603500005461100030f08500380016070310002c0080ca0800c40c1441d41c801030003901c80c44117101c082c0030048105c0b0584c049810a512034039115a1100d4104805052854041c0c035044041800a01142800d4440324640300410b0724090ba04d040200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 243631429 1250 243630179 243630199
    0x3070b0909071b060b1c030807051309020d060f06050f09011d10200f060127020c0606010e060909040b100f03050a0501060803190311090907110c030a02 67
    0x105010151000401200421003d9003080102e00d02250491250f030340520808201d641c1d8100034001c079141d42c204c0045c903c020103010400400c3d80844c0c055080119482c0440c0e07642d840318071503109400300c0d800013004280b0004490041c10800d5110004541c03550381001e8105940e140705903001e0007814a030014817801001118001d602c6054002c058001030170b482c103400302081c004038070042e240b10300d24000f0039118880a040031601c03001e4114660724910013030818500f44e4a0454940c1c60621a1a045d0304031841e5030080340091003004403038402d1414085454811102c203456072940207a038024041901220940e11354142101110000c0002a00c200d00300c3d110341e80d41e040700850050148084428000021134828410303120f002c01140148014900100030b42481d9007185c0c1d13103031b101880a5108025001841a061880c0300051045003000070717a80d214100e441e8018420b0120541e1701118501c204500c1c150407020000700b5180030b80c1180c48480300032090690303800f1001d0000c0e51104043d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 243632679 1250 243631429 243631447
    0x3141606021603060c03022109010513110415050907030614010f1d01050c010606020f120717090a0f06050705010c030e070311060702040903020303090105090607140705150a0b010e03070b 82
    0x5049555100b17550714006280c14200078001c005400c500d501e4005c0d030f8866606100d1b005009014150b00440000925650001b659a4400c24140440c0c040d81c020368407a0780d1200e60900c5118260001c2402a01000303103031805040c000d00405450007020340208038121641c015500c2113000b61141200358072124200b04030442c9001300e000c0c02c001802c1c1000001c2103181e00000f003c3c040c0c41d00030141600100000661100128208201d034a0f81002651b01801034201203050040000e45020034200c1d266a203d030040c0111321551642e030050300844601500001d801c0303500400030801140204002c11010384130880c2142590781700c0720040b000d0791180c2014000b246071080c60081003100101074600d001c0ca1a0b010405440301d068064000d41c10100c20449001402c1c00b65a03480600000900b109140100e405000c2c10a038030700ca0481c00300049400410001c041155420505040500500c0c0c0d00e040000384001c0c2c02103140d03260010390541d03440201400c1c00542d1000391840c07416010701f808101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 243633929 1250 243632679 243632681
    0x405070f080d2f01110408010f0912080903070605040f030f03090b19090c0902071e020105070f03020102090904081905040807060516060f0902040c0806030a0305130314160602160306 80
    0x40c0c4000c81815a031039101035000d83c800d2240705c426070b110719042d9440c0c83c6410819400c403441e98012040315170901e488080040c00c01c01401448460b0f03070030244050b4807907401c1ca52450044080c0100043d03e01418001442410020230024503c60366404030b5007c1d2a400c01c60545000c004014444600c4001195182d00c1d031a41d2100c0c43e6000e00c0740042c0b8070106403106501c0c0d0f141a400b0300c0d011980040c106040c003004000c48400385c0034140c42411000c4240e03000030594812003c018055040341a147c10400d403007901103521448009000b1080743c2400d00300020140d05c40e8a00d070181c000f49500e9407084500560a0300c00322411000502012494428140c5d013550000481d0840f4164900c0c3e8040011410311503210561145140003d55000501c14402110240407540060003030220401610b0b56000039811555545464030716101e00b2440c16552800301e00d60401482124402d4400d0100c0c2000039182019448908a003610a65980010b0f6195001e0341c0781b2a8513040d02e80410f00c040b41d69 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 243635179 1250 243633929 243633977
    0x2070210051204140a060207060b0102070501230904020408160527060f01020a050d0519050415030905030c0a080903070e01030f12140301090207060507090518100504050405070f080d 80
    0x4e0841030b207162000030742c2c80c00c08913400108101d4903959940c00308800355a040010b003016002c2800c1c521346d43c4981070407680d2602a02803403991600c2000a1440e02038449405580042c034405080350007002301e00c007603210001d181d8020300f0b014002c001f80e0404070031840c500030b060400314020844100d80310141070010310f801503842207065101d003070424000144104a00e00501c540d6a5a15480322072040c1c540750014010a074200c2005018481402041c40449500303030301001c58200011100f200d440d20b02e085008040b80802240036034102c10040c088004014840b10504400766080c0030b03140c42000d010304600b0301028242849000702d00000801480d2404000c240303a080940413441151542000340c2c0c0260801c9000540109a031010000c20340a07041c3c01528a003045600030303050402103140c0d0724166070140c2c29109440302040a10000c882082c01a0501078002c2c0102d00e05410b20310307904c040600c0303685410000d0040c0004d00b80d80104201030081a141c0c2c895200c5181d0120060300c0900c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 243636429 1250 243635179 243635213
    0x80606090a14041b17010806040803010e1f1203030e06011419120804061d01020d0309060f060603090b0a05060f040f0b0d0b160201060803090405070c0b0103050102070210051204 78
    0x991034000301304d400e00440c0b0745a0b12001a50721541c44400c1c0e9107000c0f401c004107134000143c5030320807800c0c040052580c2081c0d07815a00da0200c0f140480c4d44002183e00c86501c4c00d00d4202c0d0305020715002140106009400d0390400c1e000e40c809004c1000c4801031140d440f41c00b4480c03000c40e0501c1320010f109034900b07510a180c0450880f00c04010360b64a4009a9062a40b070b503204440324100060108a01c5412030803004220380070460001291010704000b03174441000e0030326101007641d6a21014200501c0358010f402c014410402001003d44601c0c01400a040400c0144d50404c4040d00040c50034125000d118401c44001d442c04280030380d000b090001804204125012807501d54201988944071036100c40c4015000d4000c3d14984d0030322006030415440580308103421a410301c5000d1211180000484210400c01e88000031140e0f11100100c1d0700d600c660b04000e101c0300f0f00c10000014000d054000d0034445008559502626450480603142c5100d10b0744092909018440083c000c240103502080b40d410f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 243637679 1250 243636429 243636431
    0x307031211030324010305060102070b0c121c0e030f0a081806091b0118030f0302010b090a09030801050409150f18080408010507050903100b150406020d080606090a1404 74
    0x244200041e900b160800c07101030605215682500302207070300070843c8181480007800c08002504000380001e403220843d0280b1540c0e840002003420281c00708001420680c2c4101c281992910741a0b00e1440314100c400403016000707810910b000030166004400c0b94004140440c841c1c0c900300b81210250b07501e0300001c142c080006801c24440607a0041032166520030001030300500b0043c1e00011441105050a4004904007c480340c4140042144000041c040d40e4010282022220307451508901405504000c1600070101e803050104914040d040190214070a88486007a41c0c2c880c1c041c04101d4004c0c40014203551484040108100ea86e030b4040340c0d5516051a001c9403135905101c40c200082484d003400c944414002500f0850b14100303224194010300d9900c0e01134a006641c1d0002a500d0f1424641c0c111440e036a458146003582e181c0d8100600346510818654a499072654040e4484070112000e10204020b44005038107841c0000445820403001040200c1841c00c0080180010b14500c462030303005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 243638929 1250 243637679 243637697
    0xf010e0606030705010f1704150f1d0d020309010e030c0a0b19030c050a03020c0703081b070e0105031c02010e060c1225030b0402040302120105060102070803181c0f030509040e07030203070312 84
    0x1489c510f008000942940d16000305440203003601d44a181603400001001540010481d016490303808811900320070380c246800d02e9040401c00c000782c14180c0001000e54410f0101e000082e40d00350000103410728225034a1641e100d401c0c604011350540346803803103c00018504018085246d40658060002030f01014108c501450300c03941e80700c47d0766100c40c80f001c20b00031041d484854085420407003a0040c010f0440740c9106545005c02281d640d841109280c0d901880a64200190030300c01d40c0a62080752610003140d02d0760a20030710b0200554000414468400c80100000b030307445240c4074900c4187d050603449a0007104c03509078104c00405c0c20203002588903408110003c050b035542e00f202d44900354200c2c000210f5040c00000a480c222680c1d008002c075400500200c545611990030740751040c042942c8401c1250511800e81120507030001004140e01c000c00d200001b4181c0c0040500000325040d602003140484030140c46907101806d00c402507060340001400e1001800039074081c46100f203141070000d85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 243640179 1250 243638929 243638963
    0x10e450706052713020717270d0507030204110d050a0e070f0f03330f1802130e031902010506091b070b07020f010e0606030705010f1704 60
    0x5044840c1d01c1a40040d001255115800e0403d08990322526800031203102c2d10004603000c030342d1404d0964a900d010310380c046a00801d0248003500640464078030a841c6540f15581c00507181c2c08101d0784052452203000a00035412402c26405a41c010303900304000304a0103156508110180c020002c5440600741d0038441440e9400c0b09014150003521400c0002c968a16210002d40c13400800c0e0b400410924140b035002c100b07080e000345c1c04000741d81d00f145042811000c0e40d000e0100c8100e000c03140071407410171130f5401c4032070110f00e6002a0301c80362689420700c003c10380c265140c803000104c08800303940320540c510035191080d000d80c07008100b105288282d90034441d00000c485501044400b040c80540d440e2410001d5074500303600115886040c01510070049007103098040032034014a000201505011340120300c81c1070081041a0340009081c0003880503000c04000d00c4c0d112801900e8050003445401f0b408a5030750702500400b0041e04150755240142507110100c03000c9c146003d4410303a4020110214007134 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 243641429 1250 243640179 243640183
    0x91207050d0308160203040f181e020306030114070512040c12050601080723040903020a0b0126010203090606190906061d010306060f0f0e100305010e45 67
    0x100c6280a525105080c1c600108040400ea0041601408540041005004600c0500d841034295451100350030800c0b0008092080204404030814ad000007e1014560a001c03060300250301ca02400d400a0181c00301c0c1200c00c50403c801521020041201031042f110b113808108501d65000d4051081403901d03580c0e40041c006410a0b0b01e17401e440c29008900144140b09040110034002c1c011001e009a00308040b00e001d4001c1c05900081c10711131601c40b022181894820040c3c4110306400503031603002540e41d85034010121a680c8408502428000c0725020104418401d40703214107915000740c0019620385080109501c80c0110010403031090300400704150b461840f51001500d19074a542200705080c1c0814824290354003600390405050010a01c00d81d5403040001d031913214641050041ca980a07501a03854142210301c0c1a002a15035a9840300943c0c56040700381250210350000c0e8258a88101d002e2002d0114900c0300f2603042c05101115070904900d2441c184207503100b4002d80e05406880e030b014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 243642679 1250 243641429 243641449
    0x7030b0f04020c03070c080a0506060409080910030b0f0307050d0807020d200a080f0a12140c01090210171303050712030603110415052707120513050309120705 70
    0x10f0b8143c0c80404c0410800801400c84405051484000c12154110707903141940c62600070a094019a05c9004600030004108203032000440d00070200040104c004000030002c008440c62603101e00c3c07001c00b0383c038098240854640c05803400503004010311640317a00d94100641c410042260042030300c3c05418042400300106d05020100360b4004403104100ca800c00c10b0130000c1d40c000100a40040c1e107240072101000580395030f00c5500094480081000310001d8412a82040c03801407404800601881c1c00720301035201500441c421203592076051103419049905520700c0098661203a5401d02155850171400580320300340c1d00c41c0c40e14920302000e80d41e40a44881c4200240030101b030b01d0308170134070030001c0382008840d032907000742c03020030015806000c842d02d09010f0780300700c1d405640426140b0000345507003192103810100030403502046040a0f000105262442070756104118940004035810300616041c8894040e0804c0040d401e0a100c0b80810580f03002e601040d0b1310346e11a0080000381c51310b07418025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 243643929 1250 243642679 243642697
    0xf0212031c0b1c06050406061208040e0c04050a0e0424051006050a1d06070f1b12020109180617010204030209100e07110109060501090e0f0c0907030b0f0402 69
    0xc0c01c1c0d9800591840c1a07401c009002485200c0804107481907840c0700550f00c1c40d01d90000008981e54a0f0740c10250028203454002d810210081006201400b100348020011101405030588903565140482c090500442c05002e503c0815031104000b044500d00200d0b0b0010b0196044074821403002241102144a10340d030030142c2501c64040010641c02650160014401410664038144500c3c02c000c1c071180307408807003505181c01032109980548540c001d9400040d030041d00d001181b01d481c244100d410340078910080c0101140f000100d003814880b941300c030040b0341c103031210030004c0e0070015800c4000d005492070b500025552103000504c01030010144402421050006940e9400e50041c09541c1a00818049501c40013103020041c2c0c40400d1380141d803040e0f00c0e1428000d01e511202072240540340a400103000c075400c1c04004654600140d2100041d50092001c9840002c0807420351910782450042c04c030341c0254404001101c044c0a5000103e010400070401102d000c02c0400081c200d801803086 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 243645179 1250 243643929 243643957
    0x10609021315030501141c050d0e0a17060126070621020301030c050d03140a0207060f030c020c040b1207120b250c02010e0306071101050a020a05070f021203 69
    0x4100400c2d440d107440094506101d2900313100a60401019135841d9074264007090281c079031100c0c00b035a03c1e00f0650b8900d018542c0a410f1707500340c00050380014103141211603072030703c01c8051040c006000c60f050400b0075131407034420010345450f03032811102d1640c400441d4094060741c070078000d803010081d805205280142c43d581c0c03524001c040160204407043c00d03845e0740c10001540704000500105103454030781011a00100c8181c0b0340d41c82d440c6401c40b0340c004650043e0754092004034001c2401c5401045660076115640c0c1e03600074070400c44800301c085d82e074101c00c0c240c09070304180b011a60030b003820341008020400180054403036102401d07803a032502410341d2008402e00c1040718954100b0030b241980e5504054880000c00e00c2114000403c4a5051000d01d00024005408402401c40e4002c0303000c2c9080d4140201558014542140c01400219580c10b210440754a4140040d88400040c400da804052803592401c0c1420f201e40e4500785031480e215000e0b40d01a00c01d108043c003283d02040140010f00c1c00b014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 243646429 1250 243645179 243645217
    0x131509050601080703080708030a1e0b013c090f0902030f0a06030308070e04150e1506130311030a081b0d020615010509150c1501290a0201060902 64
    0x1429400e08030182c209085035042644c1c104007050315002035400c00c07500181c0c181d03500d88a600b0303058024880901e00c0885640c103900c905d806864280e1106207175031020b03212040d04030607104605240d4103000004040c441c02510000d5549580c7c6101c5602c40080d5003003a660b01500e400d01c0d007002212a0303100402064000042141c1c41401c41c542940040300b010f000d11002c0e0850340c000e02107400080800081000c5031514411542d29a00108039840154051010a07500ea01140b51aa1022949445010f030540305240c030508180b0b00311980d01114140003110503040d541c1d4202d202000f52904c3d40d1500c01c03e400385020a20400c0280f800884991842c60451000c1d0281c50610319000e045800b5900540e0400c0301c64026110492400310342460036070758800443d40098142d0708081091101684085191641a0303000035003010200690410070601d81e9176001d542c40c1041c10f140381821401502181d00d51a08150000307442140a03900021501640300c01d8807604030f030407640d41406a00e22100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 243647679 1250 243646429 243646433
    0x22061b1e0201090302040e0f1b03070611210a030c0e10030e2a01120c09120302030c060114010e0616030e0303071b030201030c0518130b0303040308030a0506010914010305131509 78
    0x60300c271801c0d428000c1c0000390100200007620341c0d000344204011710010078a601c0600800340059110745511094031400400080207003411038000008403c0400c1c94001c81c0044240151410040c1d4400103000c1c0710b14841d078240407400f806204200780841d101d46801401d444440c030b00045200b01e05082d05000182c880350004200c480e2001c801048070f46000042281140d001c135010b0149c0d103624078409010b45892a00b207242d4420011155120b00a520020691403032200c44203070340c030b00d099981d40c0071008400200100c51003000801c09a0a03603032480040000d02039100103040081c0201920700b400c1007610340030181540014442d0404040c15018011580c1512400380c42c150280303007050425030300c654410610040402741c1c61150300ca000e104101078203143c0050700281009170580e0b880b25502e141140150700165400c00c00f041c01d000001d040b6502c941a02c40849601c1c800c002c4504503200c0044d4002c0802508040041551005400104a002c0500542d0008802001420039001c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 243648929 1250 243647679 243647683
    0x207060501300206120702060f0903160b25080f0c030f0f040c0801060b03060f01020d1403040503070b09060a062106020c0322061b1e0201090302040e0f 67
    0x142c005079850350350079003003400703141003200c1c00528800c4204040290540500004d6100d014052080100440350300800083e143d021641074041d00100c04142072a13203901505035160300a03880c540302100400000388000c5030889114a070000e040402200301300c60140a01d540c0603c500c4100000300c1c60078402c1c0165011019095544110080811740c00c50905d1041d0b9141d402c805070030b0504500a00300800d00344030b5a10a074100522000740200620745e6070b901468901d802c2252010720492000718414420350000c20f83e41410b1499a49491540801d0081c809298101400695503480309000650000340842802da0181c00b4240042c029071406002c01410748609801468216070001c01e0003001804281c6074050140c0d00031000f50303c8240c2c082000e0300d9401200705079401d52070059060a41550b800d51040305981403952500300c1179487d00100c1ca800c035001507004042078903046020220202e441c89080a6500c145814400640d0b40d40008044d9040c1410a8280390007045041c1910402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 243650179 1250 243648929 243648931
    0x3011203051b15150a03021806010e060417150103030f05030403020c03010f1e090323070f0b0105030f060601021902040219080a0e1b190b0a0903110316090c03110d02070605 76
    0x1049589855046c01c59001c1031413101940c41c203401c80c00701c0001040c003580c0600fa203e029060301400094075640d5807114449a000c07891000c0038103020740780400ca180a00c815006060700c0d00b584541815415804080b2407a6000500c1035046000b002d001000c50b40e03080c0100500001410404104175400544a50500721180c41d1a8082c514200d10709001036044248010300032851520304022402030585500340b0301c692a4000d01c4145881140c0c020480c40015460603140b0075802c884240d00d61841280e0744010a54205000d40d1102d004458041220100c81c80c03914030181004d81003201c81320b000b030386c803270480c0421070080b407000010070a4803032841c0308a81080c41c5041c0148810035070b408e000c80035030014100c414000d950b070716038904c075284514400c50010b1151500d155518001000002c00104542c00200c1d4242c1401030000b140345000074101c032103503601060040865141812160040c481c0015050178035407100e51940e100c400703075405040c4aa814000c0544e44200c0c501c0d11904450b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 243651429 1250 243650179 243650221
    0x3041505060619051c06090203071412060d031e0306080f030f07021c0503030103050a0506250f0e19090609050c070b0903121303031103011203051b15 66
    0x1c00f4458201d660001d07845101800e0418100345603900c0030480400da0214038000d00900f594200b07440021907054030b60003580702e040345560310803001003042c102034803901ca40154070800300c0307550011481628042610030a95446401c10803600302c010b103001c0c030b00000592110000719960b8401000300c50024810007030300f00785400241d4500388154580801034041c808029000d41000d26410610005c00c04a01c008980c0000032a901d03581d407490300340d9941d090780c10120307805d008071008a140c104415605003070711500e40005620340b681d0131204440c100074603011041000b0400c5154162515500c07541900c8c5400b050307880a1a60514407054191105688280805840c1000704a000b0038031005841102e07511900c40d840c5504c95803841891401021400ca4032000c61409001e16005d505c401c02e0741480c401e4905020520005400c182c50b40424800d543e90015041445000280718130b00809807a21010f003140b00002603d482c092500410315141c07400303040f451003408249018002c940705091 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 243652679 1250 243651429 243651439
    0x60603050f061018050603010207020607081c050f01050105030a06030209070f030e0708060c160204060e06090906040b1501110a0f140604031202030a0902120c130e030703110708030304150506 84
    0x1450200404030540810400880465a6030040b4131b841d9020340440c0d042e81c0c2c00402e11500c1d2011030a054020754400649d000c1608035042009020103194051103205458400d004002d5a107400019a0f660380020007100d00d00381d0314140400165179401e113041c01075007255500d80f0000c81c404000b404035030143c4807200c105d511556003000b0810000420680c40000d408a1645a00403c10410300000906400950040c1480030104801009000c1c062242c4c01c1180d1403019038880c0481d1070b0f00c940050380c0c09090035508900181d04660111616409034406150040d550303a5140811420030740080c4044035403404908601e41401b103c020500c13504607915024001d40c2c1040d64000d0b109940c801c90840d40b4503004800155055001d5009507569074001e412458040ca42c210100e03141c080e00c10034a0300c20060800c1d0050851018030481500d440a00011803a20782c060710191403681d00742481d02c0f418030031040e0100e003804003400914099403183c18410706ca80b14070410007096500c000c003018065 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 243653929 1250 243652679 243652711
    0x14040e0c01180b0307050304060b010c030909020f0c0a12110d09090504060e0a03020109030212120105060f09030f010603060c0e0607060f0609020a05071101170106050d09060603050f06 81
    0x10004100c204000c003090901d60120400c0061140c4100b040394815003d41202004004403690442e000b1440346124040130010154240015660b00044ca1000350004003500303c244030440d040e40c0281015411602d81c1410100c00711500d502c8c1010001c401c54102c800304040c00c80342c030707002100c4100840610000e07001984206000604650051080f410196110b83c041424444194044a20600310702c00355049012541006030180130103503c100e0051141440e10045103290318261250400c007074100c8c0c4116440c0c0410000c10760130451001c1181c00f420403000545070341c200b10303100282c5064400403a00f01d14501300724045482c182520410f02034244c208020a56840702100c5003903500c190002002032480704208002c00d8141c000715050b031300c00203000744002e8016001c2d000980c8254201140d0b645100c00445241c1000c441e982018604280107001c143c2c003d4002d090a0500700500060070303400c0ea240c0c04241c030440d51059034a50411004030b040943d007441481e03030040c80020a1442d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 243655179 1250 243653929 243653951
    0x30706060e04240b04180308010f06050906221d010506070b060d0609050303070c060f0608030405091f03080408010e010e031605070807081e011803030c12060b041404 73
    0x10f0208002807540c1030f207800652680e07101200c1e9200c00c05038a400303041041540030282e580c03511400c0c1e0384400d902040c0000d0001503a4100081d0b5039050321281c0d9142410604400240035017a000800d01001e140201001c3c02144603045c050400280000b80310502401c004070a0207003000e0060b00514041d0b00f0800130000490020107001e50000e4007583e0501000d03006090480080c0310008004000d400004140080550720081e01d828043c05190200003e980c905560030458600d8428801d0030b410a01c0304104500d00240b59581c803140c810f003060401180d2400c0000e9a0406030801c0324081d01c007003400e000b4140700b44038414800e8514002005464602aa1a45d40b40100c0844107200200d02d030441d410400306004440c01003c0f0b04040316800350b1596801a2512326820314007001e880c0b03440040614030014041d01c00c1245800c1504030145250b5101200a40892100d0030140b001c40288001802c17010302c58240240700e10403819480d82e0502280c0c03280354404014080c452428000c1e0b05007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 243656429 1250 243655179 243655193
    0xd080706111e190806120a060b0f03060f04030807090f030309090b0612041401110d050109050702060705190e3a020303030112060b0a27060308120a020d0e030706060e04 74
    0x101c1c09a03d0f04000c0e001740da52900003480038842804071035290080c0104003040040941040444107130441d03a00000c801d254080c5541c2d0541110070075005165800481d0110703014111142d00f103a403d1505114158440180e420200b0181d40102c0004038211000c1007101e01911400c1c840b0300d03088548614080c101c83c2400c00030766020b4006051000b051510020b03942c025440103490000c40c0c2c18282c0c5074007220b207a040082100344565400c0d1410103002a140c2c03031020800a10030005c5485484c2002c80740c01603800f403454142488001d12101c251560f441e0303607400030340300e45c500e8176940d01d0303014049011480304404142c4010507c4041000d00c491005940100a0380c2c19078070340e0003c03420020703041d00342003000d01801001950014200365010560124221600c100301004d5182c202c0c3e02381580842000b119094800600b00800038001c6c481d41c90802d10311150054030b8158058102480c0c060310500300d0700000e2421819070710000c0c5640c1048030134040e140082011400b00c20f2285840d44a840c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 243657679 1250 243656429 243656467
    0x10e060915010c11010201021303060501080d020a0f030302030703060b0d020c01060618140f090c03011a0a0c0b04030207051909050c0a02060106050f12010b03040201080f0105010207050d080706111e 87
    0x4e084003011161611941d10035419076070b68140c480b21000c08a0f9481c24200000c00b4203004945950003499181c1007910300014050501590011440d040c00d05039440881c002d40000d8440b008060301c41d01d001404182c00d00241022000c541c2d0010390f50403001045d0b90031517255900c01c0080c4500c1512103110540c040c060348045515000c03260318050718920008900381c040c0c0703504662200d45502801340c2d0208110245058030741a013a6140c500a012100c589280698003e40d000103843c0400c40d00043c004200e9690401e10070b0045540c0b59448800203020812481489040b494041c0020081920b0b175000386600712044811a9182c00110107009488560500482c028401e00050b01d41c903a140c541d0032500c06500045816406507142c203c0c14030194400d44050380090500d0f004642c00c010700b60a118100c81c41600144451032812050044210010000381c907a03503414064000070441e280510305498240034038070b99840c80032403000301044030401401410a10184082c14564411601503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 243658929 1250 243657679 243657683
    0xd02040f0605031801050412030911100906020d0e091305011d0102030a06060507020a17030714010915050f04020103050604020904050901151706060103090c090c020a030e03031201140105070209010e060915010c 92
    0x2141c2b41589040c40300c42000584511030300b00815047c528415079000102c0d40c2540c00e2682900e901b21100e6400320b902c1d900b07424495600003044408200d0086511001c8001d0303520410011030304005504c5040710450038004041d200b42d40000c00c0141d0b04e049842000c01900450a0103401d000554001c6020802c883c003078102c030746007002c018a14140041082d25001540b0000c00140940c1d0407100a000c1c0024200440f40048080d0120f00304091a0041303910400400b60200143c0d5030316001100604009810756410603800c00403080280c5a034026244611000d07400490b003240082c048101d055030540c4403c0c0d00f0001040c0c0204011004180c46801000074a00456118040d0509090701c50469100070701051400b1440c0c0541034020800c8503046000703441c2c84c085d202c0c079030302030648070b2160119801c1c140e0040c0380107218200c449580c1602c1484107140403030070400035030b02003260001d080e00044610178182d02007001c0d901e041065439501a844100302148281c081b000a40100304038640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 243660179 1250 243658929 243658931
    0x60f0115031e150b070303020705010b1e01030f150e012301091a090603040302060f0c0f04091509050f090d051806030612100b040b090403080c0d02040f060503180105041203 76
    0xc1840100340f5107849401418810743d09641d6441286000350080d8410703641110b0319400e00c5481c0d04207207411021200300030080d6962000c44241c00d40110f004110b001082414160f40c0c41c411400302404540c000003a081500e104800740d41040e0f0740b5040264038450b240d002c40101e01503000940d80c441c42c0081150740b00b0180407c1440d841442d880c69000d81c120003500581c000c41000149030780020642d005031800408100940c4030f820440382c96204141900c401e042080004200180207640040201c0761041c2501c000c50b0f0b00c2e2001c1d1026100161402d52009d000d450900c440441c00b800043d5040381241485c0e80780c0640110000d1400c01c0c4020b02520a800c0800020156240d40d6021440b070b10480094500c090002d00e8a02d0081c0464140b02d4052490301080c200f040c2807407140d05001d45c0c0c150700e8090241e61a988451115070010710030180180c0c0074040001c10302040d0b030241d0054201500d55640764030b4005e20000c40c01c91640541030540e81000f0071320010de061506003416940480c50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 243661429 1250 243660179 243660191
    0x605150301290403080a0804030e0d0506071d040c03050105031506030706030902030c0d050f0d0521190e070905090c090c0307020a020312030702010516020c0402130305060f0115031e 80
    0x124524083c000c41d400078020160024006060729400440d03544103d1007a1507442c8801c5d27461091017401003410340001c002d0f0780328101140461740039180f02c9511103414a03080f846502004007040a440b903528140010980b0780340144001d14082c807480490701d6800c43c41d02d10a244c80310000380e0302d0a90f4452182810f80d40c010a00075500c040c131070543c9100020701441341d007031a90300d012030b0386002a00300c00308140180015500000d124104032011103c0c404e0491600c0061032080c00304145024240030714905010852588107041c901481c148440701c84060a481032924440c001510001445400c480c0c02c0240e00082c01e40d94280310715007052000010070707240d07a00c0b440c0c01c0c0d29120280001a6051040c2d000d11800448035400445c0709124681c02440541c130f03080341c190281c0001300300e13900241c0c1204135040ccc400e00701613003d44200c4042c0b400c0c0740308540da039803201401c0c85400d0310f004000c00c0500d4010b0110410308206150152941c0c0f404000002d9146104960b11020500e080403060700e5507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 243662679 1250 243661429 243661499
    0x703091809021c020f03010c0203030f13170c06070915030507050417070512070501020a0f02041b0810080f0c0d02040905030c16060305010510080a0f0204090605150301 74
    0xa8030a06003281e01810010200f020791110038040841d8840491164241c40100640c1d8101070182019000040d0019070560b12040c500441c0100e00401d68070b07241070050400c0c0041800078626040c110380100e001545c50148890a500f41480100401c00b40046c04030100301d03801001703800c5028110b840c0790018450f11491001c0703e16101d00e0b4810001c1004050342c6c64802c400200c0e0213801c03030300125410101d43c2c002d054119220035980c03098601603000100078501048041100d444e40a1004000207016603006100003c8020b00103e0840028500e8040000c111500035100c5e01a014140c018600c5170142041c10f541c0700c8079400c0040c00740500741d418004544440d00305502c65540182130f282c8a05440001d541c1e5a0f40d4003003104140d01c0704000c001000c40c001e00c1403034141d0700040e051203000020808181c401080c080c1c0954a4a907a458035901e20600a01c050009040c10100c040348007484d007020092040640f24694036010401c0004200c4081200c8006003228110000c481d4103501c16 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 243663929 1250 243662679 243662681
    0x4080f0d090b18120705210d0c0812040b0115020a11060f0c030d09030813030203040608060d060507020c03160b1b0f0106060503011d090606130603051903030c0507030918 75
    0x52503450304002c020f04d000180d0200455074609a41c400c2c1e528802064102d542c01070340c000044610141034100d2481c0f800d07070318401d090081246000b110391900d40035030461441e0a410044406888604448005000c10585800e00f140c40450382d10081c00c1305905500c80c042c0c0e00751078201041c41205c00082e0603503000800425210381c201c030707042600e03100c426101c810070113480002d030f0840026004900044213440d441d410720b0301060305580110304180c01d000c0243c42e000380280540f41d1009401481c503000400d00d0140d079100b81d54075800b400d00c1c2c98941061628040311420b890002c5004504280705071015030081d600141540c2c0044403100503c1403d580c104100801c103241c0d40d500707242011403651b0300300d001981203540c0c030750640102c24000614100d5030102039991003c0f503006400481c3c510701e81140040c4468681c5a000543c0540c0c0342e490340d03e8440c1e5000494107000c810b44540d010302d50148140c80a500880c01c080385003031610b07500207112007124092942030310040d418494440700d00d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 243665179 1250 243663929 243663967
    0x2100e010c1506050f010513030b152e030b090f0a0e030406050406120501080309221a0301062c150d030309020f030106053a0804080f0d090b 62
    0x441462401c400c04150020b0281800d0301455000791400d40c0c400c1841d5100f10100e541c0d804610340c0307020400342141d540f000e046a010700400007862650b0f0380c13501c01d0395070003807600e1503050302d0801c43e8070003625a0346c0028104020916101410f160119080e0181c64920407507900680d0408949d41c150f64182030800104410b4920b840c075031001040c08104507401800400903660141c842d4104c8201d200c0c0c0e00d5054941c01d005400c080d40040c403503400e40381044c104114060a000e065105440038440800d81101c0910304200c40103d010300e40c54102d0f00f828030a010180008121454000c41182e81810690484010a0000b5803c480c00145224070103105040348e090b0003407a1015010484c28014058207450206078441c0071842404400340ca4144514000c9420151660741e260040003201504178000411042414004c000715004215043d4400110184603c0d03405498a0400c01c807145000103602051b0800e0303000404011001c0d40294491084806c401c0125545182c21440b003410005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 243666429 1250 243665179 243665183
    0xb041a070f08030711060108010510050607110402030c18121519110a020d110c190e010906030c060e06270901060305180714010f0507080c240402100e010c 68
    0x1003c03050054456100e401c0b1080300079441e08840540e40c8a0385028200e41098134100c3c1c0205601104000506011019180d118050300145074101441c82c00315003a43d20403500500c85140008000442d80c6a0b003001e44449a02915202009900140c240741d440448000c40c661980c04d040006440714221146400d4280c91040180202500840ca04607160000034041c40540251030f00a010503124007900b20700c41a42000901e480c0c4441c00900c9142d40e44008031000449140c030021400980707d036401d5008100102001a04d00d155003040060b03c01d06402c450108910800c0403400c581e2200142d0b52003403900d2800c00c650f01541011000452000c0c151650400c4412000044080c0c256100602c9120182040c500080d00c004010351103080754018500c26040212110b8010351095030b20100040060410a1409041d521717a081d498100c880580c0c0350384d00503801a440c41ea10301c4404a030900e200c40c018103003030810381d000814201e41404103400700401d1180d0070b680c3c0e078400c4074201d805507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 243667679 1250 243666429 243666443
    0x70c0e1003060207110418030e090601120e06040302010b18010b13050405150a090605151308060109020702032103040f060605120c190305060703050903070c0e0601090b041a070f 78
    0x800103185c2048100c42d60f6401c14411440d094002c0c8603a2629614034040c55495a00c080d030500c1039004000d004200500a18104104100305091005017441007002c05a0504014003217883e007803400a00f1b407400384144501403a030107582c03000c1c03011440d47c00754199440d1000e019280d0700401081494801607901655006042c00180000c0c00b114010702c0078464015900d030084151100000001d850103449010b4006510700355021403118440c000d041d072a804075601000d810b517500f0060f45420420b030000f420aa03070011f440c0c400c500e005c104941c0ca9500e8501341102c100050f541c403160301d0200a1004d050f06070f103180000204000d560090001d008000c1c1030039000c0b40d850b0b40259032a10605501e40c0500034101c41c817900b585c00d150740e078011030740c0c0000240050340e01c103841100500702c041d01c2c0184030701c4144124800504030702c48a0003d0b09080582e4241e0380351000c0010311526050f808100540740070403042c005010701040702640c000c5500e000e203507078017032528000d117411080e071101404030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 243668929 1250 243667679 243667687
    0x19061d07120c0804061113090902060d06030510060905100323100b03010506030303090c0d03110307030305091605030d0e0109121a0c0306030601140112051006030e03070c0e10030602 80
    0x641143c86940520302032281080501d07204000b12201348500e80c07040c44101c2c050141040384000d1a042081602c1c405400395082004030f50090040c1c0c1c5040c0c10441340f07030300003610068040625102c0c080062034001c005000714141010003800174091030001502890000541c490400d1482d00e00301c0c80401c0310b000b1582d001d054850306800518004c80024425400c10000c9603080c60008140c0340241e100030003070400905080d04102d0a0707400c1010440521590b00801905680c050010742546030003514089003d00d09a18030500b0038102c0e5405a810107000c0b14244941d03240003a00d400d03100c60f107003015843c4068140058a1080032640003c46030841082d6902c1040302410b04083e10700c0010200c065140ca5042c4a0b00b0140403c40d00660580c2c0a0401001600d010b0098503134071410605089000c1c0c50b2043d4414103440040b5510b291350340e04054100b12465241c800c002500525801440c2803461541d5981c050156030b104d003100100c0b1500c0421008107807202e00400450b8061411559 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 243670179 1250 243668929 243668951
    0x3020f1006030f11030340050f060c10020d05180d230c030304110a230603070306050301021207020f0307050a08090a120c03060c080c03060103091b0602010519061d0712 74
    0x2400085426607040000300a1602c203281f1a0341c408280c4d91300400d10001381216405100d0140c1019054003c6442002d810f1426021148000c0c040c00308484008a0145042941c0d0039048000b141d440c1c0882e44a6040000c44580c0408420450144c03001d03202042950740c034000303034603026840120308039000c00014402000300c000d8070440f00c410141c0d2101c191070f6690b0100141d030550044810b404801083c0e1040c1729241c504010f55000e0a03504001602584880101e822a00714440400a1304040820301c0300310342c1c04000045509c184440158902201c41d5141a2a2507130004c0c000c0c80c102d0301040d504050740c0e5400b001000741c807010400314085101c0f402c04850b550315910007911458034141680341040c1c4502d110911802d80000540c2ca552221401100248040c0d00c00b81e504043c00c144038505021031440d0f0b1002400a42d0020401c0d050040d60110380343c4d07984140c120503510740101005804124088010f002e1468108244596a061802d4801e41304c1c602031242c072185403c6011032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 243671429 1250 243670179 243670237
    0x9020111070b12091615021014040606210b040f02092404050105060414040906020f0a03060b090904170706091a090d050306060d06030f03020f1006030f110303 70
    0x180c400c0007000341c1d10503481c3c3c1d12060b1745541c1c0d000c0c00b095840345010814401103904020520b51252648102c0304102c18440a8404680c00c02440b200d40000c2d1409000078029180154800750003100700b0079035604e03401104005d02d98203210b4020300c01410300c0c00040902820030b010f08131440d0082c10000c05071806c26031049403010f040d040d43c41144150b064004290030a8810396059802c090100341c0790038140b4043c039061107a80304403117612a4454003031000041050003d890442072041c0c001c1d84540c5007010190503030b03d0035000349104081c1031018500c03965800d803916070856000185481140c4001c4040580741c40b4218000c0d0110b41000451420022281c01c105038000c0100c00b4080349440307403444140c6440f00c59940c0000998140042211803800340c1c01803a45c0f076644030700007620341d0341c0740d60720605030040d8081900075820030fa030620404941130002054529090804008880c02c641d5101200802243e010749041107410800141c1c5d20100212400500d4604031184d485020152040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 243672679 1250 243671429 243671437
    0x5010f0611210705160b090d060e1e24060415150c1101020f1002030606070f05150f0405030301030620180f030a151505120304091b08060409020111070b 67
    0x302c06204500040ca0110802030000781a1b86148500d245403211040030406035111440c410365001c0e84c0d60079040d0b452035007003041203004915804070414410190041c0d604046180003003003001e0100780e014815404544c1e000e19030100007101c00180e00a0940e1426090358415001040c011040340d098007503280d08110b44840c60b038401c2d03040c0009034000710300490f02c51181c0680b284c02c075400903803490207540140c3c014507070100c40a020340b0305040580c4c490307080001c500741c0705650942080d4840034440f1404c03164184c0c480344030805078080c2c1c14155980f5503030703100520014182d666500713400045541c81204000c000c00540d009161600500c6280368952090091a14480c0150740b01e81005420017249003042180c01c04260f28a4006064440010b03100700d070950000d01070003903000300d541d82e0340f29034070200d070300705d42000750349550401d591a0101d80e00170011011415040c01c0b80301400340c0c4256510341c004415070740410340010310f10041e5a0645100c103019486d00501e00c01180c98000c20700a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 243673929 1250 243672679 243672683
    0x12090c0b0a050415090305060723120a0e010b030a0321021206030d0e1804080f030f1005220c03060305060c070215041505070510020f030105011205010f06112107 71
    0x845071a12204d02c0940349002244002002c5802c0600058100f034082c0c500c90101715160014a106c000c0140701c1e84c11254081c50360300301000d40038404e010b00340080748141940701d030610001300813606020000039560300041c0300c020108907902c40d402c0b2144d0800a204084605c80303400c03e64461142004142d81c02c1c1c1e044548600a100d4500070200c03051048900300014003028112130071401ca803800d06150101d00074000d80c1c1221007000290500038406000f18892408007441c26130307504001b441e884501d401035001a1140e032044c1041c400660700c1d00c0c9151107071080240000380c4410180400e40203440b480d03001900d05e01440e020091924038140040200d24400c503030000d520455046810418001e901560340e50b0740d510500c58507035501840042500b00d0160007260f500414051201e42643e015402800603090040010411960030050680d02d101c00c059007070240390704001440042d0542841107804120040008845a0b6001e00001104e820407140c07000030508421005040b80d070000f103003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 243675179 1250 243673929 243673949
    0xb13182a050307140d1e08190801031509050c100804050610051e030109020409080a03060609080601030b13060c090e070201020c1f09020a03050604020a0f030b0a0506180f07080106090612090c0b0a0504 88
    0x202300802440352213064181c0b0b5016002da020804480700b500d00602401008071544d1260f814200155500d100d41715000c8180c03641c1d207125074541403514504200015041c012018540750003030040d59256a80700c1242108050a000301e0043d44000071b01600034581c0103500700740b501542009108280c0d008245002c8592070a102c0a40d0b0783c0c004899400b0b0341d100d080e8190b0005001400010154014144c03c8007002030b025040503035030b440706821500c400415102080340704508105101c45070180f140d000c45103000844c01c01c1070300c00f45513840c2d1230340c0d2801c070443c0c41014034034005100856002000094020340644030450b20713071402581d503641c19038080e44280f0110710001181124000c01d581030f00d80c0600c503045a501c1c4d051440e400791201401c1154402ca440c140700058480006030a0310401c90452208207600344064090320300a4107070091400c00c10054024022683c12940c2d00b000d0031760408000074000302500344800c03a100c180e00000c00c65480095040c2d00380340e010000d041580d45c8421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 243676429 1250 243675179 243675217
    0x140105062a03120a050f010b0304030f0c050709090804230303071b150203090909010c090e100f0f06120b13182a050307140d1e08 57
    0x8100940ca0103848101405040c40408055034407000303407401c40030074440d030342183d09191421004034440c040444064046964440070002d0a9290a2405004041070400b85245080c6910010503101c0d01034141d44c01d010f40c9481480801100700001001040a000f040041c0e460515000764251700034070070802c6401c0100032240018811091081010a0082c0254500b28081d41c800f0003256800d5240f425503100408005584040c0c002900d91480b40c950207940d442003400200400e6400c0078015601d0743c0e1621410102403600710f076480003901c800070100d140d255a454440c1450380b405800c0204041681d07840080c441214003e2002551500e0f103810000302d01924000c400c60b02807003503180d444160f455006c45022943e0380501000360242556540b1058181c980d420192000f075988401080c0100800032001d000e4440c040282104074041c042441c03400c0311401c50081ca0030001e51203034050700104020081c3e011144080000d045ca000c410315260360514290a403c4240d682260364515a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 243677679 1250 243676429 243676439
    0xf090d230f121e09060a080a0507031a06090319030206100e09121804050403021f0605060334080106090b090a0b1308060f09070f0303020a0206071e05011401 69
    0x402d9401c880503800511a0820118150140c206600e030076045108003030811810415450300ca00030040d0601540703962210307081c50703142141125402010039040515000c012084181c0c012060b04034040103d41c5107488a0000d4002820310070801c02c608030306a22040007004050700030842c0c81c414490642c0c108144c9580340c408140610b8100c03003290381034001a0141034407c111401501140d420001c6d100d494500f0301e800b01d4103c450980b4142c001d45d02202c5000ca10f90340400d500b2455014962007800880c0c508000300e0001c0c0009048460348030003440000c417004004030700b203405091303100c40c3d401d44641500d0000307880094280112030004801c2c01d000328110500d131044540c03100018001d068900d260003041d1074240c1024280e82d2025401020010314100200300c0c460103007151002c8280907041c0180c00e2841d04500d94000d05030405400703c1080801d0300400e0b200d244a4054510941e034901900e000d01c203582010904140710007510301c00360103010055201c2907200c80031140d00042070347c0324 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 243678929 1250 243677679 243677683
    0x10e010e090a0c05090c0909070e090c04050f0d0602210403080c0405011704080408070e011d090d08062d1318021203090604030f1b0b0f090d230f 64
    0x81800600040c50040c0100240d04100101710392140e40701c51405e0034010418006520854103440007000100d0300d07142c54045d440c2607000749410001c0344201070300c0d141c039203c0411010010041081c1c400d0713500390708010a012554040b620350b01c00900158101031141e40d481c3c49104000d45040d4005019500020b0160234410111400ea600503100c9141500200c141580800d100400c1125201e405020020f1103190400c02c410142083e50181c103959030426100d01600e45403066512002074880d000c0c030650500129422103040003518140795a40c0c0c4000102d0001d4420b500c2c6040224160b001c5a802244550607240c50388500b12103200305440c1107650304017641c000c0c5001c1c0c224440f2000c00301c001441d01c04031030001e0401c441c09590600c0410000696a50059442601d211130918101030400c90b030030704240f04201c40704410740001c40c04c101116441d40940306098a40b42000150300d08a55034148202c40019405020300710f4403c41c0b0403400e24024200030b00040300b485440072400d41a500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 243680179 1250 243678929 243678943
    0xa09090b04020313080a170a090212010606050910050405090703090b13020f13090605040807020901081f090f0507180605150a183201020a0c030201120b09010e010e09 73
    0x2c0e541c45000b04061394950000d40c0e8007803d016800d000c20301502458244034076061760b00c20502c0e02c1c4001100c103140d0044c4500d00d045070b00007810b580d141c802d081c8581500030094030110358060702d003640b030880003031415240d41c401c90f0409544541c2e44820044450f515421080c00e540c410041190152183e1910004411000100962205480807011103e04000d150a10080d461040c0403c2c200d01940720a01100d0050741c0c2038410341000a0008254180f1510650040850320010700b04004001c4840c00640065064003244586944010051000e0b00502820303007070b00401070380c1d01c0590320003100ca110024145450002d5080010018940c64003101361006d03950860780f05860100e6000048883c6550220f11000388010741d0b0700410b8000030714101d07518943c80104101d1821007038a040324000c0482c000402d0441d4403001e6a500010039101002003140c2d4203007000f004a8800101110241400480060f00003e901d000041c2c05480c0d03030b000d20704807410a05442c11a86421146540740c2c1e03d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 243681429 1250 243680179 243680191
    0x40c05010f021c03110f0408010e0c09010f0605030711010f0b03070f05030c0402070f150f060f03030f0f0306080a0318090203010e040b060a35061006050c01020f0a09090b040203 78
    0x4410f80c2e0705001c83e8069085410503034800680189005205a120300030341d001034125a24030303907540b1100e00c25140304000000c500001140c08019546c9402002e520045030790242d002042404030101e00c643d8002e04a42c540307a05410002d20040e41281c1c620f000824201c2d000500c070f8440d106000400710600c491140035103030050094020340c0500800d00000e94010301c0112050102410003001103000e421981040703080d1440049114490300318102d0036588240c1106002480d500c800700700080e08031114001c00c03200d03070030300c0c4070030b00c61210f01500140b241c1c2d0711400413401780c50189020907a211030f00042e4482e111980c0424640c13101441c0c801c90009002e04078401c545040803502242400d80e4190380000014021b245094490241044801d2400c0074103c900600800c00080d0940c10070b2050403400410005003c1880c0103c00070815000d03900c90002070040c00108080c0e0700c1000c0d0100c078184800741070115a140c2119000500c3c000a501c640b02c5807502d4038182c2600361905000700c902581d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 243682679 1250 243681429 243681463
    0xc0307080d0b010806100e010804051c0c0c0902030c040302130b100f09080c150f0906122d060d0215040e04140d021b190f0503010f090503040915030803040c05010f02 73
    0x7c181c89006546001024009849501c66481d03d07410ba40286201c0740c01c0c80c41640e48008815081c2e145c003100300343c0c031070b008003090b50300501c200241031038843d042e20308076601103900c403016070900e40e1010700a1807200d40140e00300d55018076031000e098200031568900440390351543e00746942c44105541362400001207651100019042c03882e485035a00c040c102c010344400c240c6140012100014034643d00415880b106185820100030510b0510400c1d00001002e4048095104428802000e0707881070003008944901e1204021034103645400010300140050007005136526501e5944055584030110350450b07151365001c44925081c900450081801802e940007418640310704044894605000c052854100c030004064520003a440c6111710001c0404401116400b4184410f06095a102c079040c14408c138209201203001801c008115030131200404400100d15070030901501005030164000b07801c0d01004406d000a0003d030442d4070040340d409807105c61600c0981c42c41603840d41c1c0c2d01000709400d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 243683929 1250 243682679 243682697
    0xa05011805010e1305070e01180e0f12030c0412060203160c08040501230d0c030b0102010b0f04090f051c02061e0a0b01050c030d0905060105060f030406020c0307080d0b01080610 78
    0x42c0c443c40c1340710070002d881034081c0c4010f01d49440d01044243c10903800190760144143c18808506103d21401c02c20f044280c014005120001c0c08590365054031030b8112140160004c0003c1c640c54080d020703a400380c158014800881c0c1c1c0316003030210103500143d0f035100e103032101c60003030810340c034082c040c0c10308807992186010f070400d4a041c1c0190307103110080d81c14065104180404902664002d030080502c140d0f41040012540443d0b50020100d401d5031602c0340c1035a14103043c5960b1943c0b202c0d140d0803960001c6502103845901c1e442c00030713141818254014040e1041c0040503c010400c088401c400f009141e08407281035647d4041d44059044841c1007030490345200001c14002602c0f40c00c040c02d00711042c100035203019144034502e4030310ba021418107600c1325a540450020402c05001742401040b0403035142d800c2c00702400001d80e203484043c10080c89d45600040710716000905000b170350501604259000d44803500b05200d100585008011540040c9504000071158902007050302c460148070b999074001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 243685179 1250 243683929 243683941
    0x23040807031506050a0324020406121e020a0824090a020a020708120c07090b01142b0203010608160905010c0510051609140303030a05041a0a05011805010e 68
    0x146006182121960b41c0d103568021840c0d4640406240c0194031509030a0f5210450810703400c811b0550b14410030342940100800c10440740e0058505401182c072200014650604141e11a10075201a110859441c0040b034080078403600041d081b481600d10540e89640025006404c0240b1404d00b0a41c990040c100d00108200720080d901030441006240101c2c2e001030784aaa001e450f114080411880c0303030070009070214070710307205201503001005448410b0061121240020b000c02c410074084076044000442c20841e180d08405c003808400040903580400c200c0000300f0100654400d0142c003000ca40b0100120740c0f01142200300254a102960382c0005103030420004540617100080d065880c1d21900301620404002441214002d02503100c406035240f01c4250058100c080f1075224190070683c2e1320f102d10701c61b10080110390b03200001c1c62000610b603071145009090031030011040e0045003864020441a110303503030720490680d03a4032800c0e50810a00000d00d50240c0c2c0702400ba00030340600003408901 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 243686429 1250 243685179 243685193
    0x9060402360901060609090513031b02030f0105160806031015230a060e150c01060b0c060403021516080703020f0a02010608060604020708041521050417040b18030c0307062304080703 80
    0x40d2801c50590380c1c9818015330700024035280c601c085202999641e40f007030040401e01c031541c41c00103c45070700303280100349000300000b911200c0214080e039103a80c50340d04001b040c10f03045e01c2100c060070040750712075010121100c1102c2d80e600c0e2040058000d80b2007000200c0c52501442402e2400900100b000d8800505c074040c1080d6904240c0314a070361507484110102d070320f11075032018150141c00700b001000b0358900707814002e01d0000b941441880c0010000180b0800000d04612510510006e081040041d214401d0450081c81050000002651b01007071702441194107412000840d0003d000312005a211042080121710420400030300568003000108580326295291000c54411414441c02072124110341c14922001d00c0140803000340d65004200800c0040f40c400790788007078031100351824141040c3d40c0944030300c00c03a07002d00903c4401c42e10b01969507508005002e8400000b80c103450907030b5038804001e0300501140c1c0b0a6990a5410380303182c07568400010030fa8040303030462030040403454030b10b4580300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 243687679 1250 243686429 243686447
    0x2040b0103061206050402310e070b03040515070306060516020604050a121205090907031a030d0f02060c0a08220501150801050906040236090106060909051303 70
    0x50501d034440e000003a8100111151401e1103018100100d42c5180c80c0c4100700d54101c0c0700d10441550000580c1d00040f80e00388000300b42c103640e6113643c0000e070707151400580c5241410991280003a40d1000040008000340420070460300c1440f12140c4005888001098044c0c030554020500020b034144a14910034480f2a20745210074009071946280580340c43c0801c0b112200307a0020002d04145c458031104001999105520050942c41c000c1d0900f00e00000003091030300080c10100c1010349901074940c05170060b58802c54104802821a450107140707040140c0142c000f161f4400260280f100090b0071454208c2c00c8410b40103040d40c51107a41e540e90030301c0c80c83c819000e1051840c03651901101c000001c00901c221042011180c181c094031614215029094680041400b036164210205000041c2c41d0702049003201246813058000da42c40300098045c1911000040071651803000d002d10220010650010068a03103e61712b10803400c0d2103000c54800d070b450986492f580001e100100c0004680310b45005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 243688929 1250 243687679 243687701
    0xd0b0117240d03050a0f08070c0b09100c0806010905010c0203070e1305030d1e0b0d030e01030f1d060c07030f08151f0305150616060b03070b030f0c160204 68
    0x1200010700c0010104191044250040340421000550842c071150410706d02d2140d8501803625a00625118200900f0301e031a01a000740710340408004100501c00034410180c1c544910841086085654907000308030f800196a00390104900b000c2c0884c0c60b500c200d0300d410300250054000c02c4070340e141c444241100c06008204101c10350800c0d40321000550b0a000a1100e56001746000c511101d95004141034240031143c031308919854444080d4003a201c1c0005040c000b5003501302101590300841c01031b0060300200b00055034803840d00d2800b0311000b001111906e0441d03c80d45c01c0355142d40d12442c8028081c031a101014010403900380d4400002449a0291540139460910010300d100182010600d242040382da0a04004007404510100540c1481103961082c4240c0e0400c4c0400304e0030b00468280d100d42001d018040703039402000d1083c0304a6810003075070204060100c070035180e9100e0904c1170b580c105603080300203546004007084515041c0d5041d80c0600580c1800d0103003c0c4020341c00c210040012400d9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 243690179 1250 243688929 243688981
    0x6090b1f050f0d0b070e0604060f0e010305220c0f030f1101050f04140d02041425050f1b0a0302150f010f0e090f01050705040f0b03101a040503030703050d0b0117 71
    0x85c0d00b07442c3d11440081c05c01040d80d612840c081c0d01e0106009800c25141c0244bc1c0d040501c3c080030094040c6031071600e118600da90490316610310140e800c05640040d02600301c1c800e43c80d46498004208103c414075a58a05e004075901e02d06d9041c91801100c1ca8424800c81c0c511640c2e081c0400d010035010010680e00b48080109009440d000580c046009d846103803454500700410700040151004111501e02100d1650040c0d420341d42c8906003014005016598142c45008000b0480071400a60a044d07088008003510841d01680f143d450000d42c1c030704040901c1c5c0b00c40010000400d481c52032410b00981a00d24000034054014200b8080c0d440c050b07030050160040788182c0030a41b014010a07c2840d000e800ca40c6d031010781e2036007070400c2c0403d628060340c010600542c08004101d4240702c803250000c295105103040019000c00c1d40d465041170300a42c0c000c50342c580000100700040540090090203c6460000c061000600910055409030525100d0b16001d205c600005140001e411000201348685014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 243691429 1250 243690179 243690197
    0xa0302060c07050418110109030b0c1c1103040215120601030203040510140105010207050909031602210a060e01021911012301061107080a030c06090b1f050f0d0b07 72
    0x7a080e52075080e41e099201c0300c030103480300600c48001e06c00c81702c880303007800e2007100b5616640d141864185c00510710441c00ca00403c0b0101c2c14000d84a280141c06581e503408e0180001002078201581d000f508e04904c02c1d406804152110004502511f4252140707079810341440d5a407800541c080e61005008507014000e284d0b4407042c0283c640718124849000c1032000c452503041400285c54400070760403031841003051300c0c10000450703400000ca409850360810000d0588030700b4030209048081010708981d5455060030030070b0000a0016170001c80e680100d005000e1020700c407401c0d034203c1c81091070b040d540458120f6440b03900c0703001d40c07101c8600300c81c01d03000051150088030100e0383c0c1810b841c1c1a032000e02920030040003110307841400412590b8440000c0e0011601d41083c40e540c1e4213035418001c060100440e8211b05100003507100c601510381215440c100707072070075844050b594051310400081c1c5001c3e03072901080506048901da04004005410850504403e443e02c440d1224010015020800f15030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 243692679 1250 243691429 243691439
    0x210f170d0207140c030a05030403141608010b0f0109030b0f040c0b0a030501080f03190e01020312130c15050a050c030904060602100b0d11040f06050411090307080c0a0302060c07 78
    0x7100510446002d9501c20019510074800b00303052007440d051045c03090b444010090b020400200c110380031a0361081b00003850000c3d1902c401c0c00c00345a80c584180320405040300003240034043d048200d044c02d0803181006610346100041d52079440c2400b0142030040341000044251001e401c0c0705130006d004e50444240e55a0b42c140d04410766000100c0040044e85900040081c0c10080005440040e80b030005141404d90a00e20f02c564520350802040c03c010120300315000c0d5900a0045680d1002280c1300b10f130349854000140030b02d1981c881c80440310070741d1800e0001072611004c600a03160040d036640705403400c4000b100c101e66a030801c0c0c0ca44055400100079000803030361107203d0100100b03241e0700076114000c882d0700208102e61f00d100c40c0318010303001d8540000010750b9080c04824014011100000c8003604505903074020075964204a402030718208040d400c05890901816a0200807800c0f50310729904c0d00841902c540078141c00a4020011440c144014a80034000d40000d00098007110300d050ba8036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 243693929 1250 243692679 243692681
    0x2301030908130504060906030b13030309020d060603020f0907050f0904180317130309030803090309150408014b02030c090406170a03080603010e0a050304210f170d 72
    0x1034400b5090300b84258070030801420b2500072400103100307480003001220302d15140c120902c0f000922443c4000300b0b289540d01014000c0e4000300301240c0140c01d400340141d0030b181500051490380000d80c45180c0303076960510f80703161203054075102c4c3c4c140c4e82da06400c2c0381c82c0e00009003a40d000341860650203900c40307002030002421980300c4001c00c0d020b950f42200040590f80071781025800a0001150701c00720560721000300303410850010031607a000707c0d0650b59945030700c600d40c1140650000d07260b00c4401004056410318201014006862180008100c0442495041c40d03031a02030010000303020011503520481c402480f00780c0060340324a0b40901c0a080d413207020280807a401207a440c0e019140100d1a400302d800e107446850080c001096040f071480e00041c0c58250b69000060008040010b8500014800d44007034004104441c00744045545202251a2650302d86c0c029004417034030a011038410514844110f0b1100d900a9084012741e4180402d9458000110740030600c4403c013188100040e02520081d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 243695179 1250 243693929 243693937
    0x2280b090322120209180624010c050606091b03010618050603040816080f0403080304120f0c030f0203130b0901090b13090e010e0102030907061106012301030908 71
    0xa805181d40d4040d0a802c05000405034500001a052510052000f20b040d03000162909404031070700c05c165078840c001c002001603081002195070040e01c003404410b44070100c00f00020390000b2000d102440c0348000440e06c45030f10b404054910340c031600100e48181043c4644540081020400c00c0411980f000010b100313500031b0344144000781007103207008150b100b41220f01010340001c8072041d2942c00e041e1500601d500658843c0ca40001c03681940004014602c8111058401c08607a000e4503a1b035241081180c2d03810865043d03c0603168201030221a922909800e00f60000988440a01c1c10030b03500c00f03d030340009038413450041d80300030801080c15062240c04c02c070051000c004650b50303034003000e00014210502684020442c010911200d80280c600032904c00c2038842e030000c006030100715807500324090400c42080c404254030000500008a40c0480d010b0300b525010780740c1d00010800ea0381c0c2c16913624401d00c1402120806654102844030811400403000c0205150100e913209448e16080060b81c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 243696429 1250 243695179 243695191
    0x120319091a06040501060f050c0a0210030b040e010908161b1403010e15060609040204091104151704020f041d0303071106060d020103020705030d0509071a090102280b 73
    0x1c0010711581c14000d110040e41e2085042d2010b00195151001c00382000555004007401d100c004692040c845404101803400c242e0000d28042e00d4095256001d001480c143c10042d005904045400b079407202c050040981c001d501510707441c40c081c44003212080c1c44031004421200c01c0365080c003164003511500300d41030183c51514101c2c050b60b40904201400c480900c0301c41c001a4000c10b5940d0380840700b11200d548d0203613003500c60660700c425020000e0b0007403146801564403e46000742054400d207103071025205132510080d407415950710740c66041e1188001d042204580c0a000c0000400604000c00c041e030081d140a00003207000345400c900e40c030102c084c0942c2451903074008000c00449903031002c0030082040103400901424101280442e42c40c0d82c01060181c103251300011040c2c1003200800845035903596421080245e030030014031481e02c50401c0e100f01d66000702c21502851650110b141110303071a103c1600200016560704401c000101d40380dc01c400c00400c550188030000c5546c01ca41c05225203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 243697679 1250 243696429 243696443
    0x308220305030a1e0804020d0b06031018120c0503090103090804050d050a120e01050d0e030408030d06060207050402090612060102120a030b04110a050409050c0d06080606091812031909 81
    0x4ca40c0c610f01203210006010b2132040090f09014440540c07500c003d581a140e070002220240307944d030803001c2031804000200403100b2600d08001c4550080c40c000d1000556407040515514140c00d0340c40c00c842c11303c035120340501182c00401414050398040c0c0e01141031544102c1039681031541d42e40c00a403e15025180c02c1c1c0711504240b111804003c40d4440340100b1401c1814030051259038a800208103008025004040f1075072110300702c400d44000c00a580003081c018040f65070b140c440c680c1d040301801c0640f15900c090300c41e400000c50700e41741c07a00030340e81ca81d11701501b01c41c1000c040d076051007003a0740090b03c80b60640c010ba402c203032462500c12000304200007a54401150455152080c0400c03114103442d40c0b1400380701070089000040d4000d080f034013111000704020519485030200904584178085500403000e10b00800041c0070f0001091691003a48200d502001681e1940e440c680c04101c04420100035403c04801c5550034480c0303c0c007950b08a9502c0c04070320300d880e018200410490b2200c4000369505 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 243698929 1250 243697679 243697697
    0xd0b0a090b10060509010513080a05070e0906010509070f0c0203010626030304081603030605100c11030705060a0c03200c130c0c02120a151e02040308220305030a 71
    0x4016041411030b00888503120755060285080710003401c41c003410000d641084000036a407585040078201e84030107400c0e054241e030361000085c038100b80e4a0205202e0b2405c0c40860070006200e440021034818104e40d40031306455513903070350314000301c0d0800711040000080c00140d14074000580c40910940c40a000d14580c51005a502100d440c480b08050503200304407540200100000941e540c01520440c034828a4a0048144c00349401c1c0c0140c031440c0c005036000098400350740781d01e690100580312514003a850404102024400b410345420a074060150000010402e02d9440b9200b080b001d05918084e1404140c011203400340c695070114140030511141c4c2c01035651400514042c80007803419070117840100407401035280064400350004402034451000080301d048110300910401c08410361141102010042d00c10402d80101005c9100000c1881c882102c400c000c101c5e48212015241c001008a041c26080805989190040c1c0340900c51140c16250010004804002820121072980ca4906903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 243700179 1250 243698929 243698933
    0xa020603042415080729251a16110c041b020f03070b0402151b06041b0602060406050907030c0f050102010b010302070b0a0b0102160909120311030112020d0b0a09 71
    0x456a9113802034280d0b904104c4040003140112101000c2e1b01d0f040d20000840e80c101e0240b400e0035030080c0001341c0413a14255000041c0e80900741408400144507021036000d000350b003140007607040401c807420ba140100c19065900c465008180e030368041d5004c0e8080710701c40c164040125080e100f0032484076844800301100c0906050301445564118101d8000071405c141090f01c50380a4654041d0000e4040c1b1151843c4811803c819411108085901ca82e10392104031030007545692034204403020340310303600e040000e02905404540d115085030140d034001c08143e291521007100a060142c0380300f040d441004400000503696402010090038500708412000703281100183c207445003003403481e042610401c44000040d690544080c3c10040710b07100011448400720040c2c0c601020300183c4190202c0386600000c4081c3c59400122080d0b108030b1014070f00000445082d002c0c1e0350440950619075400740b0040c0030101000001c1e89200b40002c1c012495100f950b199040000000e480e00ea0141ea100da8a82003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 243701429 1250 243700179 243700211
    0x50a0e160302091501080c0a050904060b0c0105070e3d020d0216180504060902040f0c02070509071707021204030309170a0213090201090801110405190302030a0206030424 75
    0xd4030016480d00c0460a00740d500009001b180024800702001401040440b403040c03081080c1c40b00f22501900130056152200b020f0001d64018029600e0340f5802c0c0130004100394801d105610342c07410301400e040703464004134165544610740b050070610641d1900500540c041d400c0500c2c1c02254680740c018060349505804003d04010021042040240360705000300194500040501410340d10f12200094907199460030f00007801c1a044040c1d403060400c0c2e0302000030307c0350398070030203180c407407074007181d01059451042c0400300404881e490041200350101c10a804085264540e1280d01403064520054681c028847c4940064009030001010028144030050ba1203482e007002e03e00e040002d00364445c203540020901510340030311403080380c2c60300e107450210390040d031489020344134650082c019000e19500007842d54005200d0144203404843d02d110070144d44054001c01e580d00a40549442d040740c0c2c003070003060f6001400c1100c20b0500b050340c01d06c9000000311003000ca002d0750040071610800c1070761421 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 243702679 1250 243701429 243701431
    0xb030c011209150c11010b03031e12090c04240317070b040606050109120b01060e0d0503160209010e09030909070507020405180f121b0102070209040803100b0c0d03050a0e16030209 79
    0x1c5c010341c3c50b00c1703411a01590000103940c0128085840100b000c2e100041d6102640100e280310440c40c00c45a00384003a50102003200c1c0d01005050320200a4001c802000c3c0000341c5410a44514641e400c40c001d0000c61345054102045480d01d0b0b9149240142aa50340601d80000b107409039251951020140090743e40714070050000c0000340c103032a40c0c010300364840c254920b41c10311401d02881b190441c008441c0d06c4400707001c1041034001c1c0c1a203072612a9100c0c200200f04c001c0c1000c034130445090700042840c1c400d903400035005401c014001c6040028020900000d04d20190480c2d0030311400307001800040c2d40303c1c010140318484404c0410210002041ca052030284040300a03c000c3d0018580202c03e89100400d030b40b80368266945d103a810082c11034046009115551010f5080350a11040201f0301c00d46c440114020450302004045090382c0e1440c0c0ca0150003100c2c0d0413030480c1c112a4000c11414844c7e00155004242d03618000382000031940702d0b0b480d00d0220030210307405d210404001c0083d03241036000b031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 243703929 1250 243702679 243702707
    0xe01080606090903190201150806090706051e0306010c0f050307030801081903081f031410060e0105010302130e13020312090906190e0109061403010b030c011209150c 73
    0x100c40c1c50511600e01612406070745100f000f61082c81754020744a40c401d4000e0f0003c901d000004001c500c0e01c0b5203560303880300403c6410902c20f100d1100f0026686104030200c42106541948600c03903204034102c2c102c1c5030380c0080c14007410010807644000208102280c03810b42c0c18419070040d6074400e11481d014212100c168042c204e10740188000614410500009802466061a00380320030b070b0b0345102403184c40d07070301210081d0014403200c4003000300440385000c4654202203204507548280560101c6003a00c14038000c549a00e03640c3d000401155000c1c0d001340c0034540030840c41003440c6440e07051902c1000002c60f401c0892882000d049000e505050100c1c540381c4d2004d00000d840c18602101042441d04094242c1d400b4803030300041c440003026502d003080081d21401100d41420750750f44883e2406032103140070b040250303100c0640e9042640b0f014401d16000c0d5802402600d9510042401590303800101040c58001a88602e0f03080e0015088a1200040d45c0204030006184513011354001c100e00d25035901 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 243705035 1106 243703929 243703939
    0x70305060a06030318182c011e0b180c1902060709050402070c150507150c0e060310150c12200d050301030f030903020a0e01080606 58
    0x2d80308882c020750320003218580c05401c2243c0301a5901c00c41600202c0400032a510511582080d0440303c0348a01c0190031034040a015484140456040ba216940d11944c002404c01150001040250015410404410801d001c51900c95000c00d0980d2000d90900015000c06c0c0c102c400ca4158007821190700c84100d4001c800a903403581d05445c03000201c1c260f01d4010030607007000e10903124001e40041c005107010307185c41c108189007440e443c800c804108080041c180400d004503c2c0c07085e1200d21000000b01c102003001c0042c01201c481015900c111010401e2023540c904408051043e41d80c0d1000314640111202da0070b172286250b800c00180305401c100b61103c02c0c65000065861100b40750b48040f00112400301c0c555803900f01800950011400500062010807004180099100e11905092220580302e40000b2881282c07544440d14803d243c2005001508040c07124580241041d0b80c = true := by decide +kernel

theorem cover : BRFrame.Cov 243525179 243705035 := by
  have h0 := BRFrame.cov_init 243525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 243525179 ≤ n) (h2 : n < 243705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
